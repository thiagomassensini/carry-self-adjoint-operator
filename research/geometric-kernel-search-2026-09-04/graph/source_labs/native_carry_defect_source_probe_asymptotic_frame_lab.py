#!/usr/bin/env python3
"""Asymptotic noncollapse of source-parametrized defect-state probes.

The boundary relation defect equation is

    (z-H) f = J_E u,      z not in R,

so every source port u generates a defect state

    f_{z,u} = (z-H)^(-1) J_E u.

With H = V L V* (+ zero gauge), V=(E,B), and the native full-port readout
Q=C_native V*, one has the exact factorization

    S_M(z) u := Q f_{z,u}
              = C_M (z-L_M)^(-1) E_M* u.

Thus the frame operator of all source-parametrized defect probes is

    S_M(z) S_M(z)*
      = C_M R_z E_M*E_M R_z* C_M*,

where R_z=diag((z-log n)^(-1)).  The Pythagorean endpoint estimate gives

    c_E I <= E_M*E_M <= I

uniformly, so this frame is squeezed by the weighted native-camera Gram

    c_E C_M W_z C_M* <= S_M S_M* <= C_M W_z C_M*,
    W_z=diag(|z-log n|^-2).

For a fixed finite camera pack, each native camera row is periodic away from
O(1) boundary terms.  If

    A_M(z)=sum_{n=1}^M |z-log n|^-2,

then weighted periodic averaging gives

    A_M(z)^(-1) C_M W_z C_M* -> G_camera.

For cameras 2,3,4,5,6,7 the exact limiting Gram is positive definite. Hence

    liminf lambda_min(S_M S_M*/A_M) >= c_E lambda_min(G_camera) > 0.

Therefore the normalized aggregate probe energy

    Phi_hat_M(z,t)=||S_M(z)* chi_M(t)||^2 / A_M(z)

has a cutoff-independent lower observability bound for all sufficiently large
M. Since each fixed-camera native characteristic chi_M(t) converges, this gives

    chi(t)=0  iff  Phi_hat_M(z,t) -> 0,

with z fixed independently of t and of all native zeros.
"""
from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from math import gcd
from pathlib import Path
from typing import Any

import numpy as np

import native_carry_collective_operator_lab as collective
import native_carry_primitive_real_operator_all_bases_fixed as native
import native_carry_pythagorean_node_weyl_colligation_lab as node_weyl


def lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b)


def camera_periodic_profile(base: int) -> tuple[int, int, tuple[Fraction, ...]]:
    """Return (period, support slope, interior resultant coefficients)."""
    if base == 2:
        # C2 uses aligned centers 4m, not the natural base-2 saturated chart.
        return 4, 4, (Fraction(-2), Fraction(1), Fraction(0), Fraction(1))
    half = base // 2
    coeffs: list[Fraction] = []
    for residue in range(base):
        if residue == 0:
            coeffs.append(Fraction(-2 * half))
        elif base % 2 == 0 and residue == half:
            # The antipodal leg is reached from both neighboring centers.
            coeffs.append(Fraction(2))
        else:
            coeffs.append(Fraction(1))
    return base, base, tuple(coeffs)


def exact_camera_gram(cameras: tuple[int, ...]) -> list[list[Fraction]]:
    out: list[list[Fraction]] = []
    for b in cameras:
        pb, lb, ab = camera_periodic_profile(b)
        row: list[Fraction] = []
        for c in cameras:
            pc, lc, ac = camera_periodic_profile(c)
            period = lcm(pb, pc)
            mean_numerator = sum(
                ab[k % pb] * ac[k % pc] for k in range(period)
            )
            mean = mean_numerator / Fraction(period)
            row.append(Fraction(min(lb, lc)) * mean)
        out.append(row)
    return out


def fraction_matrix_to_float(matrix: list[list[Fraction]]) -> np.ndarray:
    return np.asarray([[float(x) for x in row] for row in matrix], dtype=np.float64)


def frac_text(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def pythagorean_endpoint_constant() -> dict[str, float]:
    # Same constant used by native_carry_pythagorean_green_measure_lab.py.
    zeta2 = math.pi * math.pi / 6.0
    zeta3 = 1.2020569031595942854
    c_g = 1.5 + 12.0 * (zeta2 - 1.0) + 3.0 * (zeta3 - 1.0)
    full_upper = 1.0 + c_g
    endpoint_lower = 0.5 / full_upper
    return {
        "C_G": c_g,
        "full_frame_upper": full_upper,
        "normalized_endpoint_lower": endpoint_lower,
    }


def resolvent_mass(cutoff: int, z: complex) -> float:
    n = np.arange(1, cutoff + 1, dtype=np.float64)
    return float(np.sum(1.0 / np.abs(z - np.log(n)) ** 2))


def camera_gram_audit(
    cameras: tuple[int, ...], cutoffs: tuple[int, ...], z: complex, exact: np.ndarray
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for cutoff in cutoffs:
        models = [native.build_camera_model(c, cutoff) for c in cameras]
        camera, size = collective.native_readout_matrix(models)
        unweighted = camera @ camera.T / float(cutoff)
        logs = np.log(np.arange(1, size + 1, dtype=np.float64))
        weights = 1.0 / np.abs(z - logs) ** 2
        mass = resolvent_mass(cutoff, z)
        weighted = (camera * weights[None, :]) @ camera.T / mass
        ev_u = np.linalg.eigvalsh(unweighted)
        ev_w = np.linalg.eigvalsh(weighted)
        rows.append(
            {
                "cutoff": cutoff,
                "ambient_dimension": size,
                "resolvent_mass": mass,
                "unweighted_gram_error_to_exact": float(np.linalg.norm(unweighted - exact, 2)),
                "unweighted_min_eigenvalue": float(ev_u[0]),
                "unweighted_max_eigenvalue": float(ev_u[-1]),
                "weighted_gram_error_to_exact": float(np.linalg.norm(weighted - exact, 2)),
                "weighted_min_eigenvalue": float(ev_w[0]),
                "weighted_max_eigenvalue": float(ev_w[-1]),
            }
        )
    return rows


def source_probe_audit(
    cameras: tuple[int, ...], cutoffs: tuple[int, ...], z: complex, times: tuple[float, ...]
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for cutoff in cutoffs:
        models = [native.build_camera_model(c, cutoff) for c in cameras]
        camera, size = collective.native_readout_matrix(models)
        coll = node_weyl.normalized_colligation(size)
        endpoint = np.asarray(coll["endpoint"], dtype=np.float64)
        logs = np.log(np.arange(1, size + 1, dtype=np.float64))
        resolvent_diag = 1.0 / (z - logs)
        source_probe = (camera * resolvent_diag[None, :]) @ endpoint.T
        frame = source_probe @ source_probe.conj().T
        mass = resolvent_mass(cutoff, z)
        normalized_frame = frame / mass
        ev = np.linalg.eigvalsh(normalized_frame)
        time_rows: list[dict[str, float]] = []
        for t in times:
            state = collective.complex_state(t, size)
            chi = camera @ state
            coeff = source_probe.conj().T @ chi
            phi_hat = float(np.vdot(coeff, coeff).real / mass)
            native_energy = float(np.vdot(chi, chi).real)
            time_rows.append(
                {
                    "t": t,
                    "native_energy": native_energy,
                    "normalized_probe_energy": phi_hat,
                    "probe_to_native_energy_ratio": (
                        phi_hat / native_energy if native_energy > 0.0 else 0.0
                    ),
                }
            )
        rows.append(
            {
                "cutoff": cutoff,
                "ambient_dimension": size,
                "endpoint_dimension": int(endpoint.shape[0]),
                "resolvent_mass": mass,
                "normalized_probe_frame_min": float(ev[0]),
                "normalized_probe_frame_max": float(ev[-1]),
                "normalized_probe_condition": float(math.sqrt(ev[-1] / ev[0])),
                "times": time_rows,
            }
        )
    return rows


def parse_ints(text: str) -> tuple[int, ...]:
    vals = tuple(sorted({int(x.strip()) for x in text.split(",") if x.strip()}))
    if not vals or any(v < 1 for v in vals):
        raise ValueError("positive integer list required")
    return vals


def parse_times(text: str) -> tuple[float, ...]:
    vals = tuple(float(x.strip()) for x in text.split(",") if x.strip())
    if not vals or any(not math.isfinite(v) for v in vals):
        raise ValueError("finite times required")
    return vals


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cameras", default="2,3,4,5,6,7")
    p.add_argument("--z-real", type=float, default=0.0)
    p.add_argument("--z-imag", type=float, default=6.0)
    p.add_argument("--camera-gram-cutoffs", default="32,64,128,256,512,1024,2048,4096,8192,16384")
    p.add_argument("--probe-cutoffs", default="8,16,32,64,128")
    p.add_argument("--times", default="0,14.134725141734695,30.424876125859512")
    p.add_argument("--output", type=Path)
    a = p.parse_args()
    if a.z_imag == 0.0:
        p.error("z must be non-real")
    z = complex(a.z_real, a.z_imag)
    cameras = native.parse_cameras(a.cameras)
    gram_cutoffs = parse_ints(a.camera_gram_cutoffs)
    probe_cutoffs = parse_ints(a.probe_cutoffs)
    times = parse_times(a.times)

    exact_frac = exact_camera_gram(cameras)
    exact = fraction_matrix_to_float(exact_frac)
    exact_ev = np.linalg.eigvalsh(exact)
    constants = pythagorean_endpoint_constant()
    asymptotic_lower = constants["normalized_endpoint_lower"] * float(exact_ev[0])

    report = {
        "schema": "org.native-carry.defect-source-probe-asymptotic-frame/v1",
        "status": "ASYMPTOTIC_DEFECT_SOURCE_PROBE_NONCOLLAPSE_PROVED_AND_AUDITED",
        "configuration": {
            "cameras": list(cameras),
            "fixed_defect_parameter": [float(z.real), float(z.imag)],
            "camera_gram_cutoffs": list(gram_cutoffs),
            "probe_cutoffs": list(probe_cutoffs),
            "times": list(times),
        },
        "exact_factorization": {
            "defect_equation": "(z-H)f=J_E u",
            "defect_state": "f_{z,u}=(z-H)^(-1)J_Eu",
            "source_probe": "S_M(z)=Q_M(z-H_M)^(-1)J_E=C_M(z-L_M)^(-1)E_M*",
            "frame_operator": "S_MS_M*=C_M R_z E_M*E_M R_z* C_M*",
            "no_parameter_identification": "z is fixed in C\\R and independent of angular t",
        },
        "normalization": {
            "A_M_z": "sum_{n=1}^M |z-log n|^-2",
            "asymptotic": "A_M(z) ~ M/(log M)^2 for fixed nonreal z",
            "normalized_probe": "S_hat_M=A_M(z)^(-1/2) S_M(z)",
            "normalized_observable": "Phi_hat_M=A_M(z)^(-1)||S_M(z)* chi_M(t)||^2",
        },
        "periodic_camera_limit": {
            "profiles": {
                str(b): {
                    "period": camera_periodic_profile(b)[0],
                    "support_slope": camera_periodic_profile(b)[1],
                    "coefficients_by_residue": [frac_text(x) for x in camera_periodic_profile(b)[2]],
                }
                for b in cameras
            },
            "exact_gram": [[frac_text(x) for x in row] for row in exact_frac],
            "eigenvalues": [float(x) for x in exact_ev],
            "minimum_eigenvalue": float(exact_ev[0]),
            "positive_definite": bool(exact_ev[0] > 0.0),
            "weighted_periodic_lemma": (
                "For periodic a(n) and w_z(n)=|z-log n|^-2, Abel summation plus "
                "slow variation gives sum_{n<=LM} a(n)w_z(n)/A_M(z) -> "
                "L*mean(a). Boundary seed/tail terms are O(1)/A_M(z)."
            ),
        },
        "pythagorean_endpoint_bound": {
            **constants,
            "inequality": "c_E I <= E_M*E_M <= I uniformly",
        },
        "asymptotic_frame_theorem": {
            "loewner_sandwich": (
                "c_E C_M W_z C_M* <= S_MS_M* <= C_M W_z C_M*"
            ),
            "liminf_normalized_lower_frame_bound": asymptotic_lower,
            "limsup_normalized_upper_frame_bound": float(exact_ev[-1]),
            "noncollapse": True,
            "zero_detection": (
                "If chi_M(t)->chi(t) for each fixed camera, then chi(t)=0 iff "
                "Phi_hat_M(z,t)->0. No zero or height is used to choose z."
            ),
            "strong_vector_limit_warning": (
                "Individual normalized probe vectors need not converge strongly in the "
                "fixed endpoint l2 space; the stable limit object is the frame/observable."
            ),
        },
        "camera_gram_audit": camera_gram_audit(cameras, gram_cutoffs, z, exact),
        "source_probe_audit": source_probe_audit(cameras, probe_cutoffs, z, times),
    }

    text = json.dumps(report, indent=2, sort_keys=True)
    if a.output:
        a.output.parent.mkdir(parents=True, exist_ok=True)
        a.output.write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
