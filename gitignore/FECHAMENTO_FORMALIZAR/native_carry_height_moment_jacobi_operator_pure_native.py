#!/usr/bin/env python3
"""Construct finite self-adjoint height operators without zero input.

Let s(z)=1/2+i z.  The construction source is the closed native camera,
not a direct evaluation of the classical Riemann zeta function:

    R_{b,M}(s)   = finite native camera resultant,
    tau_{b,M}(s) = exact cutoff tail from the native bracket Mellin integral,
    kappa_b(s)   = nonvanishing camera normalization on the sampled contour,

    G_native(s) = (R_{b,M}(s)+tau_{b,M}(s))/kappa_b(s),
    F_native(z) = A(s(z))*G_native(s(z)),

where

    A(s) = (1/2)*s*(s-1)*pi**(-s/2)*Gamma(s/2).

The exact native identity implies that this is the common completed
characteristic.  The construction itself never calls mp.zeta(s) or a zero
list.  The logarithmic readout is

    m(z) = -F_native'(z)/F_native(z).

Because F is even, write F(z)=F(0) Phi(z**2).  If the height Weyl gate is
positive, then

    q(u) = -Phi'(u)/Phi(u) = m(sqrt(u))/(2 sqrt(u))
         = sum_{gamma>0} multiplicity(gamma)/(gamma**2-u).

Its Taylor coefficients

    h_k = sum multiplicity(gamma) gamma**(-2*k-2)

are moments of the finite positive measure

    rho = sum multiplicity(gamma) gamma**(-2) delta_(gamma**(-2)).

The scalar Jacobi model is cyclic: a zero multiplicity is encoded in the
corresponding atom weight (the Weyl residue), not as an eigenspace dimension.
An eigenspace-multiplicity realization requires the conditional canonical
amplification described in the accompanying research note.

In that multiplicity-preserving realization, Y=T**(-2) is trace class and

    Phi(u) = det(I-uY),
    q(u) = Tr((T**2-uI)**(-1)),
    h_k = Tr(T**(-2*k-2)).

This script obtains h_k from Cauchy coefficients of F_native at zero, never from a
zero list.  Positive Hankel matrices yield the Jacobi compression J_N of
multiplication by y=gamma**(-2).  The finite height operator is

    T_N = J_N**(-1/2),

which is real symmetric and has approximate positive zero heights as its
eigenvalues.  Reference zeta zeros are queried only after T_N has been fully
constructed and can be disabled.

The same construction has an exact defect-jet realization.  With

    x_0 = sqrt(h_0) e_0,
    gamma_N(u) = (I-u J_N)**(-1) x_0,
    x_j = gamma_N**(j)(0)/j! = J_N**j x_0,

the feature map X_N e_j=x_j satisfies

    G_N = X_N.T X_N,
    K_N = X_N.T J_N X_N.

In fact X_N is exactly the transpose of the Cholesky factor of G_N.  The two
finite Weyl kernels are audited directly:

    (u q_N(u)-conj(v q_N(v)))/(u-conj(v))
        = <gamma_N(v),gamma_N(u)>,
    (q_N(u)-conj(q_N(v)))/(u-conj(v))
        = <gamma_N(v),J_N gamma_N(u)>.

The second kernel is positive only when the shifted Hankel form is positive.
Thus the ordinary Green symmetry identity alone does not prove J_N >= 0; the
positive Green/Stieltjes energy is the additional sign input.

Global positivity of all Hankel orders is equivalent to the same unresolved
height-Weyl/RH gate.  Finite positive matrices and accurate eigenvalues are
numerical evidence, not a proof.

No Newton iteration and no interval arithmetic are used.  Independent Cauchy
circle evaluations can use all available CPU workers.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import math
import os
from pathlib import Path
from typing import Any, Sequence

import mpmath as mp


DEFAULT_ORDER = 10
DEFAULT_DPS = 120
# The pure Mellin-tail evaluator is used on a local Cauchy contour.
# Keeping |z|<1/2 also stays away from the removable camera-factor zero at s=1.
DEFAULT_RADIUS = "0.4"
DEFAULT_CONTROL_RADIUS = "0.32"
DEFAULT_SAMPLES_PER_ORDER = 12
DEFAULT_TRUNCATIONS = (4, 8, 10)
DEFAULT_CAMERA = 3
DEFAULT_CUTOFF = 4


def parse_int_tuple(text: str) -> tuple[int, ...]:
    values = tuple(int(part.strip()) for part in text.split(",") if part.strip())
    if not values or any(value < 1 for value in values):
        raise ValueError("expected positive comma-separated integers")
    if tuple(sorted(set(values))) != values:
        raise ValueError("values must be distinct and increasing")
    return values


def camera_geometry(camera: int) -> tuple[int, tuple[int, ...]]:
    if camera < 2:
        raise ValueError("camera must be at least 2")
    if camera == 2:
        return 4, (1,)
    return camera, tuple(range(1, camera // 2 + 1))


def harmonic_prefix(maximum: int, s: mp.mpc) -> list[mp.mpc]:
    values = [mp.mpc(0)] * (maximum + 1)
    total = mp.mpc(0)
    for n in range(1, maximum + 1):
        total += mp.power(n, -s)
        values[n] = total
    return values


def finite_native_camera(camera: int, cutoff: int, s: mp.mpc) -> mp.mpc:
    """Finite native bracket resultant R_{b,M}(s), with no zeta evaluation."""
    period, radii = camera_geometry(camera)
    maximum = period * cutoff + max(radii)
    h = harmonic_prefix(maximum, s)

    if camera == 2:
        return (
            h[4 * cutoff + 1]
            - mp.power(2, -s) * h[2 * cutoff]
            - 2 * mp.power(4, -s) * h[cutoff]
        )

    half = max(radii)
    if camera % 2:
        return h[period * cutoff + half] - mp.power(period, 1 - s) * h[cutoff]

    return (
        h[period * cutoff + half]
        + mp.power(half, -s) * h[2 * cutoff]
        - (camera + 2) * mp.power(period, -s) * h[cutoff]
    )


def camera_factor(camera: int, s: mp.mpc) -> mp.mpc:
    """Known geometric multiplier kappa_b(s)."""
    period, radii = camera_geometry(camera)
    if camera == 2:
        return 1 - mp.power(2, -s) - 2 * mp.power(4, -s)
    if camera % 2:
        return 1 - mp.power(period, 1 - s)
    half = max(radii)
    return 1 + mp.power(half, -s) - (camera + 2) * mp.power(period, -s)


def exact_native_tail(camera: int, cutoff: int, s: mp.mpc) -> mp.mpc:
    """Exact native cutoff tail via the bracket Mellin integral.

    This is the same closure encoded coefficientwise by exact_tail_series in
    native_carry_r2_height_operator.py.  It does not call Riemann or Hurwitz
    zeta.  On the default local Cauchy contours Re(s)>0, so the integral is
    absolutely convergent and numerically stable.
    """
    period, radii = camera_geometry(camera)

    def integrand(x: mp.mpf) -> mp.mpc:
        if x == 0:
            return mp.mpc(0)
        bracket = mp.fsum(
            4 * mp.sinh(mp.mpf(radius) * x / 2) ** 2 for radius in radii
        )
        weight = (
            mp.exp(-period * (cutoff + 1) * x)
            * bracket
            / (-mp.expm1(-period * x))
        )
        return mp.power(x, s - 1) * weight

    return mp.quad(integrand, [0, 1, mp.inf]) / mp.gamma(s)


def completion_factor(s: mp.mpc) -> mp.mpc:
    """Archimedean completion factor A(s), with no zeta evaluation."""
    return (
        mp.mpf("0.5")
        * s
        * (s - 1)
        * mp.power(mp.pi, -s / 2)
        * mp.gamma(s / 2)
    )


def native_completed_characteristic(
    z: mp.mpc, camera: int, cutoff: int
) -> mp.mpc:
    """F_native(z)=A(s)*(R_{b,M}(s)+tau_{b,M}(s))/kappa_b(s)."""
    s = mp.mpf("0.5") + mp.j * z
    finite = finite_native_camera(camera, cutoff, s)
    tail = exact_native_tail(camera, cutoff, s)
    kappa = camera_factor(camera, s)
    threshold = mp.power(10, -max(20, mp.mp.dps // 3))
    if abs(kappa) <= threshold:
        raise ZeroDivisionError(
            f"camera factor too small on sampled contour: C{camera}, "
            f"M={cutoff}, s={mp.nstr(s, 20)}, |kappa|={mp.nstr(abs(kappa), 12)}"
        )
    return completion_factor(s) * (finite + tail) / kappa


def height_characteristic(z: mp.mpc, camera: int, cutoff: int) -> mp.mpc:
    return native_completed_characteristic(z, camera, cutoff)


def _cauchy_value_worker(
    task: tuple[int, str, int, int, int, int]
) -> tuple[int, str, str]:
    dps, radius_text, index, sample_count, camera, cutoff = task
    mp.mp.dps = dps
    radius = mp.mpf(radius_text)
    root = mp.exp(2 * mp.j * mp.pi * index / sample_count)
    value = height_characteristic(radius * root, camera, cutoff)
    digits = dps + 8
    return index, mp.nstr(value.real, digits), mp.nstr(value.imag, digits)


def cauchy_values(
    dps: int,
    radius: mp.mpf,
    sample_count: int,
    workers: int,
    camera: int,
    cutoff: int,
) -> list[mp.mpc]:
    tasks = [
        (dps, mp.nstr(radius, dps), index, sample_count, camera, cutoff)
        for index in range(sample_count)
    ]
    if workers <= 1:
        raw = map(_cauchy_value_worker, tasks)
    else:
        executor = concurrent.futures.ProcessPoolExecutor(max_workers=workers)
        chunksize = max(1, sample_count // max(1, 4 * workers))
        raw = executor.map(_cauchy_value_worker, tasks, chunksize=chunksize)

    values = [mp.mpc(0)] * sample_count
    try:
        for index, real_text, imag_text in raw:
            values[index] = mp.mpc(mp.mpf(real_text), mp.mpf(imag_text))
    finally:
        if workers > 1:
            executor.shutdown()
    return values

def cauchy_coefficients(
    values: Sequence[mp.mpc],
    radius: mp.mpf,
    maximum_degree: int,
) -> list[mp.mpc]:
    sample_count = len(values)
    roots = [
        mp.exp(2 * mp.j * mp.pi * index / sample_count)
        for index in range(sample_count)
    ]
    return [
        mp.fsum(
            values[index] * mp.power(roots[index], -degree)
            for index in range(sample_count)
        )
        / (sample_count * mp.power(radius, degree))
        for degree in range(maximum_degree + 1)
    ]


def even_characteristic_coefficients(
    coefficients: Sequence[mp.mpc], maximum_u_degree: int
) -> tuple[list[mp.mpf], dict[str, mp.mpf]]:
    even = [mp.re(coefficients[2 * degree]) for degree in range(maximum_u_degree + 1)]
    odd_defect = max(abs(coefficients[degree]) for degree in range(1, len(coefficients), 2))
    imaginary_defect = max(abs(mp.im(value)) for value in coefficients)
    return even, {
        "maximum_odd_coefficient": odd_defect,
        "maximum_imaginary_coefficient": imaginary_defect,
    }


def log_derivative_moments(
    phi: Sequence[mp.mpf], moment_count: int
) -> list[mp.mpf]:
    """Coefficients of -Phi'(u)/Phi(u) by exact power-series division."""
    moments: list[mp.mpf] = []
    for degree in range(moment_count):
        numerator = -(degree + 1) * phi[degree + 1] - mp.fsum(
            moments[index] * phi[degree - index]
            for index in range(degree)
        )
        moments.append(numerator / phi[0])
    return moments


def hankel_matrices(
    moments: Sequence[mp.mpf], order: int
) -> tuple[mp.matrix, mp.matrix]:
    gram = mp.matrix(order, order)
    shifted = mp.matrix(order, order)
    for row in range(order):
        for column in range(order):
            gram[row, column] = moments[row + column]
            shifted[row, column] = moments[row + column + 1]
    return gram, shifted


def jacobi_from_moments(
    moments: Sequence[mp.mpf], order: int
) -> dict[str, Any]:
    gram, shifted = hankel_matrices(moments, order)
    gram_eigenvalues = list(mp.eigsy(gram, eigvals_only=True))
    shifted_eigenvalues = list(mp.eigsy(shifted, eigvals_only=True))
    cholesky = mp.cholesky(gram)
    inverse_cholesky = cholesky**-1
    jacobi = inverse_cholesky * shifted * inverse_cholesky.T
    jacobi = (jacobi + jacobi.T) / 2

    # Green closure in the monomial jet basis.  Multiplication by y is the
    # unilateral shift through degree order-2.  The moment functional fixes
    # the final column uniquely, producing a G-self-adjoint rank-one boundary
    # closure.  Cholesky whitening turns that closure into the Jacobi matrix.
    monomial_shift = mp.zeros(order)
    for column in range(order - 1):
        monomial_shift[column + 1, column] = 1
    generalized_operator = gram**-1 * shifted
    last_basis_vector = mp.zeros(order, 1)
    last_basis_vector[order - 1] = 1
    boundary_feedback = mp.matrix(
        [[generalized_operator[row, order - 1]] for row in range(order)]
    )
    boundary_pairing = gram * boundary_feedback
    rank_one_closure = (
        monomial_shift + boundary_feedback * last_basis_vector.T
    )

    green_boundary_vector = mp.zeros(order, 1)
    for row in range(order - 1):
        green_boundary_vector[row] = moments[order + row]
    green_defect = monomial_shift.T * gram - gram * monomial_shift
    predicted_green_defect = (
        green_boundary_vector * last_basis_vector.T
        - last_basis_vector * green_boundary_vector.T
    )

    cholesky_feature = cholesky.T
    whitened_similarity = (
        cholesky.T * generalized_operator * inverse_cholesky.T
    )

    # Defect-state jets.  The finite gamma field is
    #
    #   gamma_N(u) = (I-u J_N)^(-1) x_0,
    #   x_0 = sqrt(h_0) e_0.
    #
    # Its normalized derivatives at zero are x_j=J_N^j x_0.  Moment
    # orthogonalization implies that the resulting Krylov matrix is exactly
    # the Cholesky feature X_N=L_N^T, not merely unitarily equivalent to it.
    cyclic_vector = mp.zeros(order, 1)
    cyclic_vector[0] = mp.sqrt(moments[0])
    defect_jet_feature = mp.zeros(order)
    jet_state = cyclic_vector.copy()
    for column in range(order):
        for row in range(order):
            defect_jet_feature[row, column] = jet_state[row]
        jet_state = jacobi * jet_state

    # Positive-energy factorization.  If K_N=B_N^T B_N, then
    # C_N=B_N X_N^(-1) gives J_N=C_N^T C_N.  This is the finite algebraic form
    # of the extra positive Green/Stieltjes identity needed beyond Green
    # symmetry.  Identifying C_N with a native TFVD energy readout is a
    # separate crosswalk, deliberately not assumed by this script.
    shifted_cholesky_feature = mp.cholesky(shifted).T
    green_energy_analysis = shifted_cholesky_feature * (cholesky_feature**-1)

    # A nonreal two-point audit of the exact finite Weyl/Green identities.
    # The points are fixed independently of the spectrum and stay far from the
    # positive height-squared poles.
    u = mp.mpc(mp.mpf("0.125"), mp.mpf("0.0625"))
    v = mp.mpc(mp.mpf("-0.09375"), mp.mpf("0.03125"))
    identity = mp.eye(order)
    gamma_u = (identity - u * jacobi) ** -1 * cyclic_vector
    gamma_v = (identity - v * jacobi) ** -1 * cyclic_vector
    q_u = mp.fsum(
        mp.conj(cyclic_vector[row]) * gamma_u[row] for row in range(order)
    )
    q_v = mp.fsum(
        mp.conj(cyclic_vector[row]) * gamma_v[row] for row in range(order)
    )
    denominator = u - mp.conj(v)
    m_pick_kernel = (u * q_u - mp.conj(v * q_v)) / denominator
    q_pick_kernel = (q_u - mp.conj(q_v)) / denominator
    gamma_inner = mp.fsum(
        mp.conj(gamma_v[row]) * gamma_u[row] for row in range(order)
    )
    jacobi_gamma_u = jacobi * gamma_u
    gamma_energy_inner = mp.fsum(
        mp.conj(gamma_v[row]) * jacobi_gamma_u[row]
        for row in range(order)
    )

    outside_tridiagonal = max(
        (
            abs(jacobi[row, column])
            for row in range(order)
            for column in range(order)
            if abs(row - column) > 1
        ),
        default=mp.mpf(0),
    )
    diagonal = [jacobi[index, index] for index in range(order)]
    off_diagonal = [jacobi[index, index + 1] for index in range(order - 1)]
    return {
        "order": order,
        "gram": gram,
        "shifted": shifted,
        "gram_eigenvalues": gram_eigenvalues,
        "shifted_eigenvalues": shifted_eigenvalues,
        "jacobi": jacobi,
        "diagonal": diagonal,
        "off_diagonal": off_diagonal,
        "outside_tridiagonal_maximum": outside_tridiagonal,
        "symmetry_defect": mp.norm(jacobi - jacobi.T),
        "green_boundary_closure": {
            "boundary_feedback": [
                boundary_feedback[row] for row in range(order)
            ],
            "selected_selfadjoint_boundary_parameter": moments[2 * order - 1],
            "boundary_parameter_residual": abs(
                boundary_pairing[order - 1] - moments[2 * order - 1]
            ),
            "shift_plus_rank_one_defect": mp.norm(
                generalized_operator - rank_one_closure
            ),
            "g_selfadjoint_defect": mp.norm(
                generalized_operator.T * gram - gram * generalized_operator
            ),
            "green_defect_formula_residual": mp.norm(
                green_defect - predicted_green_defect
            ),
            "cholesky_gram_factorization_residual": mp.norm(
                gram - cholesky_feature.T * cholesky_feature
            ),
            "cholesky_shifted_factorization_residual": mp.norm(
                shifted
                - cholesky_feature.T * jacobi * cholesky_feature
            ),
            "jacobi_similarity_residual": mp.norm(
                jacobi - whitened_similarity
            ),
        },
        "defect_jet_realization": {
            "definition": (
                "gamma_N(u)=(I-u*J_N)^(-1)*x_0, "
                "x_0=sqrt(h_0)e_0, x_j=J_N^j*x_0, X_N e_j=x_j"
            ),
            "jet_feature_equals_cholesky_feature_residual": mp.norm(
                defect_jet_feature - cholesky_feature
            ),
            "jet_gram_factorization_residual": mp.norm(
                gram - defect_jet_feature.T * defect_jet_feature
            ),
            "jet_shifted_factorization_residual": mp.norm(
                shifted
                - defect_jet_feature.T * jacobi * defect_jet_feature
            ),
            "positive_energy_factorization_residual": mp.norm(
                jacobi - green_energy_analysis.T * green_energy_analysis
            ),
            "minimum_jacobi_eigenvalue": min(
                mp.eigsy(jacobi, eigvals_only=True)
            ),
            "weyl_green_test_points": {
                "u": u,
                "v": v,
            },
            "M_pick_green_identity_residual": abs(
                m_pick_kernel - gamma_inner
            ),
            "q_pick_energy_identity_residual": abs(
                q_pick_kernel - gamma_energy_inner
            ),
            "native_tfvd_crosswalk_status": (
                "not assumed: one still needs a theorem identifying the "
                "height shifted-Hankel energy with the native TFVD Green "
                "energy readout"
            ),
        },
    }


def leading_principal(matrix: mp.matrix, order: int) -> mp.matrix:
    return mp.matrix(
        [[matrix[row, column] for column in range(order)] for row in range(order)]
    )


def height_spectrum(jacobi: mp.matrix) -> tuple[list[mp.mpf], mp.matrix]:
    y_values, eigenvectors = mp.eigsy(jacobi)
    if y_values[0] <= 0:
        raise RuntimeError("Jacobi compression is not positive")
    inverse_square_roots = [1 / mp.sqrt(value) for value in y_values]
    height_operator = eigenvectors * mp.diag(inverse_square_roots) * eigenvectors.T
    heights = sorted(inverse_square_roots)
    return heights, height_operator


def construct(args: argparse.Namespace) -> dict[str, Any]:
    mp.mp.dps = args.dps
    radius = mp.mpf(args.radius)
    control_radius = mp.mpf(args.control_radius)
    maximum_degree = 4 * args.order
    sample_count = args.samples_per_order * args.order
    if sample_count <= maximum_degree:
        raise ValueError("Cauchy sample count must exceed maximum coefficient degree")

    primary_values = cauchy_values(
        args.dps, radius, sample_count, args.workers, args.camera, args.cutoff
    )
    primary_coefficients = cauchy_coefficients(
        primary_values, radius, maximum_degree
    )
    primary_even, primary_defects = even_characteristic_coefficients(
        primary_coefficients, 2 * args.order
    )
    moments = log_derivative_moments(primary_even, 2 * args.order)

    control_values = cauchy_values(
        args.dps, control_radius, sample_count, args.workers, args.camera, args.cutoff
    )
    control_coefficients = cauchy_coefficients(
        control_values, control_radius, maximum_degree
    )
    control_even, control_defects = even_characteristic_coefficients(
        control_coefficients, 2 * args.order
    )
    control_moments = log_derivative_moments(control_even, 2 * args.order)
    moment_differences = [
        abs(left - right) for left, right in zip(moments, control_moments)
    ]
    relative_moment_differences = [
        difference / max(abs(moment), mp.mpf(10) ** (-(args.dps - 20)))
        for difference, moment in zip(moment_differences, moments)
    ]

    full = jacobi_from_moments(moments, args.order)
    truncation_rows: list[dict[str, Any]] = []
    constructed_spectra: dict[int, list[mp.mpf]] = {}
    for order in args.truncations:
        if order > args.order:
            continue
        finite_jacobi = leading_principal(full["jacobi"], order)
        independent_jacobi = (
            full["jacobi"]
            if order == args.order
            else jacobi_from_moments(moments, order)["jacobi"]
        )
        heights, height_operator = height_spectrum(finite_jacobi)
        constructed_spectra[order] = heights
        truncation_rows.append(
            {
                "order": order,
                "heights": heights,
                "height_operator_symmetry_defect": mp.norm(
                    height_operator - height_operator.T
                ),
                "height_operator_minimum_eigenvalue": min(heights),
                "height_operator_maximum_eigenvalue": max(heights),
                "jacobi_tower_compatibility_defect": mp.norm(
                    finite_jacobi - independent_jacobi
                ),
            }
        )

    # Firewall: references are evaluated only after all moments, Hankel
    # matrices, Jacobi coefficients, and height spectra have been constructed.
    reference_rows: list[dict[str, Any]] = []
    if args.compare_count > 0:
        references = [
            mp.im(mp.zetazero(index)) for index in range(1, args.compare_count + 1)
        ]
        for row in truncation_rows:
            heights = constructed_spectra[row["order"]]
            count = min(len(heights), len(references))
            errors = [
                abs(heights[index] - references[index]) for index in range(count)
            ]
            reference_rows.append(
                {
                    "order": row["order"],
                    "comparison_count": count,
                    "approximations": heights[:count],
                    "references": references[:count],
                    "absolute_errors": errors,
                    "maximum_absolute_error": max(errors),
                }
            )

    return {
        "schema": "org.native-carry.height-moment-jacobi-operator/v1",
        "status": "FINITE_SELFADJOINT_HEIGHT_OPERATOR_CONDITIONAL_MOMENT_GATE",
        "configuration": {
            "dps": args.dps,
            "order": args.order,
            "radius": radius,
            "control_radius": control_radius,
            "cauchy_samples": sample_count,
            "workers": args.workers,
            "truncations": args.truncations,
            "compare_count": args.compare_count,
            "camera": args.camera,
            "cutoff": args.cutoff,
            "root_finding_in_construction": "none",
            "riemann_zeta_in_construction": False,
            "hurwitz_zeta_in_construction": False,
            "interval_arithmetic": False,
            "zero_heights_used_in_construction": False,
        },
        "derivation": {
            "common_characteristic": (
                "F_native(z)=A(s)*(R_bM(s)+tau_bM(s))/kappa_b(s), s=1/2+i z"
            ),
            "native_bridge": (
                "R_bM is the finite native camera; tau_bM is its exact bracket-Mellin "
                "tail; kappa_b is the nonzero geometric camera factor on the contour"
            ),
            "classical_function_role": (
                "no Riemann/Hurwitz zeta is evaluated in construction; Phi is only the "
                "even coordinate F_native(z)=F_native(0)*Phi(z^2)"
            ),
            "moment_weyl": "q(u)=-d_u log Phi(u), F(z)=F(0)Phi(z^2)",
            "measure": "rho=sum_gamma multiplicity(gamma) gamma^(-2) delta_(gamma^(-2))",
            "bounded_operator": "Y f(y)=y f(y)",
            "height_operator": "T=Y^(-1/2)",
            "fredholm_determinant": "Phi(u)=det(I-u T^(-2))",
            "resolvent_trace": "q(u)=Tr((T^2-u I)^(-1))",
            "spectral_moments": "h_k=Tr(T^(-2k-2))",
            "multiplicity_firewall": (
                "The scalar cyclic Jacobi realization stores zero multiplicity "
                "in atom weights/Weyl residues, not in eigenspace dimension."
            ),
            "global_firewall": (
                "The positive measure formula and all-order Hankel positivity are "
                "equivalent to the global height-Weyl/RH gate; finite positivity "
                "is not a proof."
            ),
        },
        "cauchy_audit": {
            "primary": primary_defects,
            "control": control_defects,
            "maximum_absolute_moment_difference_between_radii": max(
                moment_differences
            ),
            "maximum_relative_moment_difference_between_radii": max(
                relative_moment_differences
            ),
        },
        "moments": moments,
        "hankel_gate": {
            "gram_minimum_eigenvalue": min(full["gram_eigenvalues"]),
            "gram_maximum_eigenvalue": max(full["gram_eigenvalues"]),
            "shifted_minimum_eigenvalue": min(full["shifted_eigenvalues"]),
            "shifted_maximum_eigenvalue": max(full["shifted_eigenvalues"]),
            "gram_positive_at_tested_order": min(full["gram_eigenvalues"]) > 0,
            "shifted_positive_at_tested_order": min(full["shifted_eigenvalues"]) > 0,
        },
        "jacobi_operator_y": {
            "diagonal": full["diagonal"],
            "off_diagonal": full["off_diagonal"],
            "minimum_off_diagonal": min(full["off_diagonal"]),
            "symmetry_defect": full["symmetry_defect"],
            "outside_tridiagonal_maximum": full["outside_tridiagonal_maximum"],
        },
        "green_boundary_closure": full["green_boundary_closure"],
        "defect_jet_realization": full["defect_jet_realization"],
        "height_operator_truncations": truncation_rows,
        "postconstruction_reference_audit": {
            "reference_source": "mpmath.zetazero, queried only after native construction",
            "used_by_construction": False,
            "rows": reference_rows,
        },
    }


def mp_serializable(value: Any, digits: int) -> Any:
    if isinstance(value, dict):
        return {key: mp_serializable(item, digits) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [mp_serializable(item, digits) for item in value]
    if isinstance(value, mp.mpc):
        return [mp.nstr(value.real, digits), mp.nstr(value.imag, digits)]
    if isinstance(value, mp.mpf):
        return mp.nstr(value, digits)
    return value


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=int, default=DEFAULT_ORDER)
    parser.add_argument("--dps", type=int, default=DEFAULT_DPS)
    parser.add_argument("--digits", type=int, default=50)
    parser.add_argument("--radius", default=DEFAULT_RADIUS)
    parser.add_argument("--control-radius", default=DEFAULT_CONTROL_RADIUS)
    parser.add_argument(
        "--samples-per-order", type=int, default=DEFAULT_SAMPLES_PER_ORDER
    )
    parser.add_argument(
        "--workers", type=int, default=max(1, os.cpu_count() or 1)
    )
    parser.add_argument(
        "--truncations", type=parse_int_tuple, default=DEFAULT_TRUNCATIONS
    )
    parser.add_argument("--compare-count", type=int, default=10)
    parser.add_argument("--camera", type=int, default=DEFAULT_CAMERA)
    parser.add_argument("--cutoff", type=int, default=DEFAULT_CUTOFF)
    parser.add_argument("--output", type=Path)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    if args.order < 2:
        parser.error("--order must be at least 2")
    if args.dps < max(80, 9 * args.order):
        parser.error("--dps is too small for the requested moment order")
    if args.digits < 12 or args.digits > args.dps - 12:
        parser.error("--digits must lie between 12 and dps-12")
    if args.samples_per_order < 5:
        parser.error("--samples-per-order must be at least 5")
    if args.workers < 1:
        parser.error("--workers must be positive")
    if args.compare_count < 0:
        parser.error("--compare-count cannot be negative")
    if args.camera < 2:
        parser.error("--camera must be at least 2")
    if args.cutoff < 1:
        parser.error("--cutoff must be positive")
    if mp.mpf(args.radius) >= mp.mpf("0.5") or mp.mpf(args.control_radius) >= mp.mpf("0.5"):
        parser.error(
            "pure native Mellin-tail mode requires --radius and --control-radius < 0.5; "
            "this keeps the sampled strip Re(s)>0 and avoids the removable s=1 camera-factor zero"
        )
    if any(value > args.order for value in args.truncations):
        parser.error("every truncation must be at most --order")

    report = construct(args)
    payload = json.dumps(mp_serializable(report, args.digits), indent=2, sort_keys=True)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload + "\n", encoding="utf-8")
    print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
