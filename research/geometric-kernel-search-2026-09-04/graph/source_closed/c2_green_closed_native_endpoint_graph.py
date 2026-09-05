#!/usr/bin/env python3
"""Native C2 prime-power log-jet and closed post-T0 graph relation.

This audit is forward-only.  It never selects a representative of the J/H
coequalizer and never attempts to reconstruct the historical pre-T0 endpoint.
The two independent axes are kept literal:

* ``d_J | ell`` is the Jordan/gcd channel erased by ``Q_JH``;
* ``j=v_{p_T}(d)`` is the C2 prime-power tower level acted on by ``N``.

Consequently the enriched forward carrier is a tensor product and
``Q = Q_JH tensor I_tower``.  The number operator descends to the quotient,
but the centered one-leg A analysis does not: an exact two-divisor gauge
witness is killed by Q and remains visible to A.  The result is a canonical
closed post-T0 tower relation, not a reverse lift into the historical A fibre.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
RESULT = ROOT / "result/c2_green_closed_native_endpoint_graph"
TEST_PATH = ROOT / "tests/test_c2_green_closed_native_endpoint_graph.py"

REPORT_LOGJET = ROOT / "C2_GREEN_C2_PRIME_POWER_LOGJET_GRAPH.md"
REPORT_ENDPOINT = ROOT / "C2_GREEN_CLOSED_NATIVE_ENDPOINT_GRAPH_LIFT.md"
REPORT_COEQUALIZER = ROOT / "C2_GREEN_JH_COEQUALIZER_GRAPH_RELATION.md"


MANDATORY_INPUTS = [
    ROOT / "C2_GREEN_NATIVE_A_PRET0_TYPE_REGISTRY.md",
    ROOT / "C2_GREEN_NATIVE_A_COMMON_CODOMAIN.md",
    ROOT / "C2_GREEN_NATIVE_A_ENDPOINT_LIFT.md",
    ROOT / "C2_GREEN_UNIT_MASS_RESIDUE_INTERTWINER.md",
    ROOT / "C2_GREEN_ALL_ODD_FIBRE_DYADIC_GATE.md",
    ROOT / "C2_GREEN_NATIVE_A_COEFFICIENT_QUOTIENT.md",
    ROOT / "C2_GREEN_MELLIN_LOGJET_ENDPOINT.md",
    ROOT / "C2_GREEN_CENTERED_JORDAN_KREIN_REPORT.md",
    ROOT / "C2_GREEN_MOLECULE_GCD_COMPATIBILITY_ADDENDUM.md",
    ROOT / "docs/c2_lambda_cutoff_peneira.md",
    ROOT / "docs/c2_formula_reduzida_canal_lambda.md",
    ROOT / "script/c2_green_native_a_endpoint_all_fibres.py",
    ROOT / "script/c2_green_unit_mass_tail_boundary.py",
    ROOT / "script/c2_green_molecule_gcd_laplace_jordan.py",
    ROOT / "script/c2_green_centered_jordan_krein.py",
    ROOT / "result/c2_green_native_a_endpoint_all_fibres/summary.json",
    ROOT / "result/c2_green_native_a_endpoint_all_fibres/manifest.json",
    ROOT / "result/c2_green_centered_jordan_krein/quotient_coequalizer.json",
    ROOT / "result/c2_green_centered_jordan_krein/mellin_logjet.json",
    ROOT / "result/c2_green_unit_mass_tail_boundary/cumulant_tail_current.json",
]

FROZEN_RESULTS = [
    "PASS_NATIVE_C2_A_BULK_TYPED_PULLBACK",
    "STOP_PRE_T0_PROVENANCE_INSUFFICIENT_FOR_A_LIFT",
    "STOP_NATIVE_C2_ENDPOINT_NOT_IN_A_FIBRE",
    "NEEDS_CLOSED_NATIVE_ENDPOINT_GRAPH_LIFT",
]


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def relative(path: Path) -> str:
    return str(path.relative_to(ROOT))


def json_default(value: object) -> object:
    if isinstance(value, Fraction):
        return {
            "numerator": value.numerator,
            "denominator": value.denominator,
            "text": str(value),
        }
    if isinstance(value, sp.MatrixBase):
        return [[str(entry) for entry in row] for row in value.tolist()]
    if isinstance(value, sp.Basic):
        return str(value)
    if isinstance(value, Path):
        return str(value)
    raise TypeError(f"cannot serialize {type(value)!r}")


def json_dump(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, indent=2, sort_keys=True, default=json_default) + "\n",
        encoding="utf-8",
    )


def witness_paths() -> list[Path]:
    return sorted(ROOT.glob("result/c2_green_carry_current_audit/n*/witness_*.npz"))


def previous_historical_paths() -> list[Path]:
    manifest_path = ROOT / "result/c2_green_native_a_endpoint_all_fibres/manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    paths: set[Path] = {manifest_path}
    integrity = manifest.get("historical_integrity", {})
    for name in integrity.get("hashes_after", {}):
        paths.add(ROOT / name)
    for item in manifest.get("generated", []):
        paths.add(ROOT / item["path"])
    return sorted(path for path in paths if path.exists())


def snapshot(paths: Iterable[Path]) -> dict[str, str]:
    return {relative(path): sha256_file(path) for path in sorted(set(paths))}


def integrity_audit() -> dict[str, object]:
    missing = [relative(path) for path in MANDATORY_INPUTS if not path.exists()]
    if missing:
        raise FileNotFoundError(f"missing mandatory canonical inputs: {missing}")
    empty = [relative(path) for path in MANDATORY_INPUTS if path.stat().st_size == 0]
    if empty:
        raise RuntimeError(f"canonical inputs are empty: {empty}")
    witnesses = witness_paths()
    if len(witnesses) != 54:
        raise RuntimeError(f"expected 54 frozen witnesses, found {len(witnesses)}")
    tracked = sorted(set(MANDATORY_INPUTS + witnesses + previous_historical_paths()))
    previous_summary = json.loads(
        (ROOT / "result/c2_green_native_a_endpoint_all_fibres/summary.json").read_text(
            encoding="utf-8"
        )
    )
    if previous_summary["result"] != FROZEN_RESULTS[1]:
        raise RuntimeError("frozen previous result changed")
    if previous_summary["secondary_result"] != FROZEN_RESULTS[2]:
        raise RuntimeError("frozen previous secondary result changed")
    if previous_summary["frontier"] != FROZEN_RESULTS[3]:
        raise RuntimeError("frozen previous frontier changed")
    return {
        "schema": "c2.green.closed_native_endpoint.integrity.v1",
        "Genuine_First": True,
        "mandatory_input_count": len(MANDATORY_INPUTS),
        "frozen_witness_count": len(witnesses),
        "frozen_results": FROZEN_RESULTS,
        "historical_hashes_before": snapshot(tracked),
        "forbidden_methods": {
            "reverse_section": False,
            "Moore_Penrose": False,
            "Householder": False,
            "minimum_norm_representative": False,
            "LP": False,
            "solver": False,
            "prime_number_theorem": False,
            "zero_data": False,
            "external_completion": False,
            "Green_to_zero": False,
        },
    }


# ---------------------------------------------------------------------------
# Native C2 unit mass and the exact finite prime tower


def v2(value: int) -> int:
    if value <= 0:
        raise ValueError("v2 is defined here only on positive integers")
    exponent = 0
    while value % 2 == 0:
        value //= 2
        exponent += 1
    return exponent


def max_visible_depth(cutoff: int, odd_core: int, epsilon: int) -> int:
    if cutoff < 0 or odd_core <= 0 or odd_core % 2 == 0 or epsilon not in (-1, 1):
        raise ValueError("invalid native C2 mass coordinate")
    depth = 1
    while (1 << (depth + 1)) * odd_core + epsilon <= cutoff:
        depth += 1
    return depth


def branch_visible_mass(cutoff: int, odd_core: int, epsilon: int) -> Fraction:
    depth = max_visible_depth(cutoff, odd_core, epsilon)
    if depth < 2:
        return Fraction(0)
    return Fraction(1, 2) - Fraction(1, 1 << depth)


def visible_mass(cutoff: int, odd_core: int) -> Fraction:
    return sum(
        (
            branch_visible_mass(cutoff, odd_core, -1),
            branch_visible_mass(cutoff, odd_core, +1),
        ),
        Fraction(0),
    )


def local_mass_coefficients(cutoff: int, prime: int, order: int) -> list[Fraction]:
    if prime < 3 or prime % 2 == 0:
        raise ValueError("the native C2 material tower is indexed by odd primes")
    if order < 0:
        raise ValueError("order must be nonnegative")
    return [Fraction(1)] + [visible_mass(cutoff, prime**j) for j in range(1, order + 1)]


def newton_power_sums(coefficients: Sequence[Fraction]) -> list[Fraction]:
    """Return P_j=[x^j] x d/dx log(sum a_j x^j)."""

    order = len(coefficients) - 1
    powers = [Fraction(0)] * (order + 1)
    for k in range(1, order + 1):
        powers[k] = k * coefficients[k] - sum(
            (coefficients[j] * powers[k - j] for j in range(1, k)),
            Fraction(0),
        )
    return powers


def richardson_power_sums(cutoff: int, prime: int, order: int) -> list[Fraction]:
    low = newton_power_sums(local_mass_coefficients(cutoff, prime, order))
    high = newton_power_sums(local_mass_coefficients(2 * cutoff, prime, order))
    return [Fraction(0)] + [2 * high[j] - low[j] for j in range(1, order + 1)]


def richardson_log_coefficients(cutoff: int, prime: int, order: int) -> list[Fraction]:
    powers = richardson_power_sums(cutoff, prime, order)
    return [Fraction(0)] + [powers[j] / j for j in range(1, order + 1)]


def formal_log_coefficients(coefficients: Sequence[Fraction]) -> list[sp.Expr]:
    x = sp.symbols("x")
    order = len(coefficients) - 1
    polynomial = sum(
        sp.Rational(value.numerator, value.denominator) * x**j
        for j, value in enumerate(coefficients)
    )
    series = sp.series(sp.log(polynomial), x, 0, order + 1).removeO().expand()
    return [sp.Integer(0)] + [sp.expand(series).coeff(x, j) for j in range(1, order + 1)]


def reference_global_mass(cutoff: int) -> list[Fraction]:
    """Exact Fraction version of the user-provided global odd-mass constructor."""

    mass = [Fraction(0)] * (cutoff + 1)
    mass[1] = Fraction(1)
    for odd_core in range(3, cutoff + 1, 2):
        quotient = cutoff // odd_core
        depth = quotient.bit_length() - 1
        if depth >= 2:
            value = Fraction(1) - Fraction(1, 1 << (depth - 1))
            if (1 << depth) * odd_core == cutoff:
                value -= Fraction(1, 1 << depth)
            mass[odd_core] = value
    return mass


def log_basis_vector(integer: int) -> dict[int, Fraction]:
    return {int(prime): Fraction(exponent) for prime, exponent in sp.factorint(integer).items()}


def add_log_vectors(
    left: Mapping[int, Fraction],
    right: Mapping[int, Fraction],
    right_scale: Fraction = Fraction(1),
) -> dict[int, Fraction]:
    result = dict(left)
    for prime, coefficient in right.items():
        result[prime] = result.get(prime, Fraction(0)) + right_scale * coefficient
        if result[prime] == 0:
            del result[prime]
    return result


def global_odd_geometry(
    cutoff: int, mass: Sequence[Fraction]
) -> list[dict[int, Fraction]]:
    """Exact odd Dirichlet-division recurrence in the log-prime basis."""

    geometry: list[dict[int, Fraction]] = [{} for _ in range(cutoff + 1)]
    for integer in range(3, cutoff + 1, 2):
        geometry[integer] = {
            prime: mass[integer] * exponent
            for prime, exponent in log_basis_vector(integer).items()
        }
    for divisor in range(3, cutoff + 1, 2):
        coefficient = geometry[divisor]
        if not coefficient:
            continue
        for cofactor in range(3, cutoff // divisor + 1, 2):
            target = divisor * cofactor
            geometry[target] = add_log_vectors(
                geometry[target], coefficient, -mass[cofactor]
            )
    return geometry


def serialize_log_vector(vector: Mapping[int, Fraction]) -> list[dict[str, object]]:
    return [
        {"prime": prime, "coefficient_of_log_prime": coefficient}
        for prime, coefficient in sorted(vector.items())
    ]


def global_odd_convolution_audit() -> dict[str, object]:
    """Reproduce the pasted 400/800 construction and compare it exactly."""

    low_cutoff = 400
    high_cutoff = 800
    output_cutoff = 200
    low_mass = reference_global_mass(low_cutoff)
    high_mass = reference_global_mass(high_cutoff)
    low_mass_mismatches = [
        odd_core
        for odd_core in range(3, low_cutoff + 1, 2)
        if low_mass[odd_core] != visible_mass(low_cutoff, odd_core)
    ]
    high_mass_mismatches = [
        odd_core
        for odd_core in range(3, high_cutoff + 1, 2)
        if high_mass[odd_core] != visible_mass(high_cutoff, odd_core)
    ]
    if low_mass_mismatches or high_mass_mismatches:
        raise RuntimeError("global odd mass and native two-branch mass disagree")

    low_geometry = global_odd_geometry(low_cutoff, low_mass)
    high_geometry = global_odd_geometry(high_cutoff, high_mass)
    corrected: dict[int, dict[int, Fraction]] = {}
    for integer in range(3, output_cutoff, 2):
        corrected[integer] = add_log_vectors(
            {prime: 2 * coefficient for prime, coefficient in high_geometry[integer].items()},
            low_geometry[integer],
            Fraction(-1),
        )

    prime_power_records = []
    for integer in range(3, output_cutoff, 2):
        factorization = sp.factorint(integer)
        if len(factorization) != 1:
            continue
        prime_sp, exponent_sp = next(iter(factorization.items()))
        prime = int(prime_sp)
        exponent = int(exponent_sp)
        local_power = richardson_power_sums(low_cutoff, prime, exponent)[exponent]
        expected = {prime: local_power}
        if corrected[integer] != expected:
            raise RuntimeError(
                f"global/local prime-power mismatch at {integer}: "
                f"{corrected[integer]} != {expected}"
            )
        prime_power_records.append(
            {
                "integer": integer,
                "p_T": prime,
                "j": exponent,
                "global_log_basis": serialize_log_vector(corrected[integer]),
                "local_P_j_R": local_power,
            }
        )

    expected_mixed = {
        15: {3: Fraction(1, 4096), 5: Fraction(1, 4096)},
        21: {3: Fraction(1, 2048), 7: Fraction(1, 2048)},
    }
    for integer, expected in expected_mixed.items():
        if corrected[integer] != expected:
            raise RuntimeError(f"mixed global coefficient changed at {integer}")
    mixed_records = [
        {
            "integer": integer,
            "factorization": {int(p): int(e) for p, e in sp.factorint(integer).items()},
            "global_log_basis": serialize_log_vector(corrected[integer]),
            "is_prime_power": len(sp.factorint(integer)) == 1,
        }
        for integer in (15, 21, 35, 45, 63, 105)
    ]

    return {
        "schema": "c2.green.c2_prime_power_logjet.global_odd_regression.v1",
        "source_algorithm": (
            "exact Fraction transcription of accumulate_c2_mass_exato, "
            "extract_geometria_c2 and 2*b_800-b_400 supplied by the user"
        ),
        "cutoffs": {"mass_low": low_cutoff, "mass_high": high_cutoff, "output": output_cutoff},
        "mass_comparison": {
            "low_all_odd_equal": not low_mass_mismatches,
            "high_all_odd_equal": not high_mass_mismatches,
            "low_odd_core_count": len(range(3, low_cutoff + 1, 2)),
            "high_odd_core_count": len(range(3, high_cutoff + 1, 2)),
        },
        "prime_power_restriction": {
            "all_exact": True,
            "record_count": len(prime_power_records),
            "records": prime_power_records,
        },
        "mixed_channels": {
            "retained_by_global_inversion": True,
            "not_part_of_the_single_prime_tower_jet": True,
            "not_identified_with_d_J": True,
            "records": mixed_records,
        },
        "interpretation": (
            "the persisted (p_T,j) jet is exactly the prime-power restriction "
            "of the global odd convolution; mixed cumulants require a separate "
            "provenance axis in any enriched relation"
        ),
    }


def exact_logjet_audit() -> dict[str, object]:
    source = (ROOT / "script/c2_green_molecule_gcd_laplace_jordan.py").read_text(
        encoding="utf-8"
    )
    literal_feature = '"base_feature": "phi_(t,d)(n)=1_(d|n)n^-t"'
    if literal_feature not in source:
        raise RuntimeError("the frozen J/H one-leg feature changed")

    tau = sp.symbols("tau", positive=True)
    records: list[dict[str, object]] = []
    for cutoff, prime, order in ((64, 3, 6), (96, 5, 5), (128, 7, 4)):
        low = local_mass_coefficients(cutoff, prime, order)
        high = local_mass_coefficients(2 * cutoff, prime, order)
        powers = richardson_power_sums(cutoff, prime, order)
        kappas = richardson_log_coefficients(cutoff, prime, order)
        formal_low = formal_log_coefficients(low)
        formal_high = formal_log_coefficients(high)
        for j in range(1, order + 1):
            expected_kappa = sp.simplify(2 * formal_high[j] - formal_low[j])
            actual_kappa = sp.Rational(kappas[j].numerator, kappas[j].denominator)
            if sp.simplify(expected_kappa - actual_kappa) != 0:
                raise RuntimeError("Richardson log coefficient mismatch")
            rho = prime ** (-j * tau)
            lhs = sp.simplify(sp.log(prime) * j * actual_kappa * rho)
            rhs = sp.simplify(
                sp.log(prime)
                * sp.Rational(powers[j].numerator, powers[j].denominator)
                * rho
            )
            if sp.simplify(lhs - rhs) != 0:
                raise RuntimeError("number-operator logjet identity failed")
            records.append(
                {
                    "M": cutoff,
                    "p_T": prime,
                    "j": j,
                    "a_M_pj": low[j],
                    "a_2M_pj": high[j],
                    "P_j_R": powers[j],
                    "kappa_j_R": kappas[j],
                    "rho_from_JH": rho,
                    "number_identity_residual": sp.Integer(0),
                }
            )

    unit_limit = []
    for j in range(1, 9):
        coefficients = [Fraction(1)] * (j + 1)
        power = newton_power_sums(coefficients)[j]
        if power != 1:
            raise RuntimeError("unit-mass local power sum is not one")
        unit_limit.append(
            {
                "j": j,
                "P_j": power,
                "kappa_j": Fraction(1, j),
                "h_coefficient_at_tau_0": Fraction(1, j),
                "N_h_coefficient_at_tau_0": 1,
            }
        )

    return {
        "schema": "c2.green.c2_prime_power_logjet.core.v1",
        "native_local_series": "A_(M,p)(x)=sum_(j>=0)a_M(p^j)x^j, a_M(1)=1",
        "logarithmic_series": "B_(M,p)(x)=x partial_x log A_(M,p)(x)",
        "Richardson_object": "A_red=A_(2M,p)^2/A_(M,p)",
        "Richardson_coefficients": "kappa_(M,p,j)=P_j^R(M)/j",
        "Newton_recurrence": "P_j=j a(p^j)-sum_(i=1)^(j-1)a(p^i)P_(j-i)",
        "rho_provenance": {
            "frozen_one_leg_feature": "phi_(tau,d_J)(n)=1_(d_J|n)n^(-tau)",
            "literal_specialization": "n=p_T^j gives rho_(p_T,j)(tau)=p_T^(-j tau)",
            "not_used": ["p_T^(-2j tau)", "a fitted normalization"],
        },
        "finite_exact_records": records,
        "unit_mass_limit": {
            "formal_local_series": "sum_(j>=0)x^j",
            "h_(p,0)": "sum_(j>=1)j^(-1)e_(p,j)",
            "logp_N_h": "sum_(j>=1)log(p)e_(p,j), a rigged vector rather than an l2 vector",
            "records": unit_limit,
        },
        "axis_firewall": {
            "p_A": "analysis-A camera prime",
            "p_T": "native odd prime-power tower prime",
            "j": "v_(p_T)(d), acted on by N",
            "K": "C2 carry depth k_eff, not j",
            "d_J": "Jordan divisor of gcd ell, not p_T^j",
            "tau": "Euler-Laplace time",
            "identifications": "none before a literal endpoint-support identity",
        },
        "checkpoint": "PASS_C2_PRIME_POWER_LOGJET_CORE",
    }


# ---------------------------------------------------------------------------
# Hilbert scale and the zero-time rigged endpoint


def partial_inverse_square_sum(maximum: int) -> Fraction:
    return sum((Fraction(1, j * j) for j in range(1, maximum + 1)), Fraction(0))


def hilbert_scale_audit() -> dict[str, object]:
    partials = []
    for maximum in (1, 2, 4, 8, 16, 64, 256):
        inverse_square = partial_inverse_square_sum(maximum)
        partials.append(
            {
                "J": maximum,
                "norm_h0_h_partial_squared": inverse_square,
                "norm_h0_Nh_partial_squared": maximum,
                "norm_hminus1_Nh_partial_squared": inverse_square,
                "upper_bound_inverse_square": Fraction(2),
            }
        )
    if any(record["norm_h0_h_partial_squared"] >= 2 for record in partials):
        raise RuntimeError("elementary inverse-square bound failed")

    exact_vectors = [
        [Fraction(1, 2), Fraction(-3, 5), Fraction(7, 11)],
        [Fraction(-2, 3), Fraction(5, 7), Fraction(0), Fraction(9, 13)],
    ]
    isometry_checks = []
    for vector in exact_vectors:
        h0 = sum((abs(value) ** 2 for value in vector), Fraction(0))
        image_hminus1 = sum(
            (abs((j + 1) * value) ** 2 / ((j + 1) ** 2) for j, value in enumerate(vector)),
            Fraction(0),
        )
        if h0 != image_hminus1:
            raise RuntimeError("N:H0->H-1 isometry failed")
        isometry_checks.append({"vector": vector, "H0_norm_squared": h0, "N_image_Hminus1_norm_squared": image_hminus1})

    tau_re, p = sp.symbols("tau_re p", positive=True)
    flow_norm_squared = sp.log(p) ** 2 / (p ** (2 * tau_re) - 1)
    scaled_limit = sp.simplify(
        sp.limit(tau_re * flow_norm_squared, tau_re, 0, dir="+")
    )
    if scaled_limit != sp.log(p) / 2:
        raise RuntimeError("positive-time flow blowup coefficient changed")

    positive_time_records = []
    for prime, time in ((3, Fraction(1, 2)), (3, Fraction(1, 1)), (5, Fraction(1, 2))):
        q = Fraction(1, prime ** (2 * time.numerator // time.denominator)) if time.denominator == 1 else None
        formula = sp.simplify(sp.log(prime) ** 2 / (sp.Integer(prime) ** (2 * sp.Rational(time.numerator, time.denominator)) - 1))
        positive_time_records.append({"p_T": prime, "tau": time, "flow_H0_norm_squared": formula, "rational_geometric_ratio_when_integral": q})

    return {
        "schema": "c2.green.c2_prime_power_logjet.hilbert_scale.v1",
        "scale": {
            "H1": "{y:sum j^2|y_j|^2<infinity}",
            "H0": "l2({j>=1})",
            "Hminus1": "completion for sum |y_j|^2/j^2",
            "continuous_inclusions": "H1 subset H0 subset Hminus1",
        },
        "zero_time": {
            "h_in_H0": True,
            "proof_h_in_H0": "sum 1/j^2 <= 1+integral_1^infinity x^-2 dx=2",
            "Nh_not_in_H0": True,
            "proof_Nh_not_in_H0": "the squared partial norm equals J",
            "Nh_in_Hminus1": True,
            "proof_Nh_in_Hminus1": "sum |1|^2/j^2<2",
            "partial_records": partials,
        },
        "number_operator": {
            "map": "N:H0->Hminus1",
            "operator_norm": 1,
            "isometry_identity": "||Ny||_(Hminus1)=||y||_(H0)",
            "exact_checks": isometry_checks,
        },
        "positive_tau": {
            "domain": "Re(tau)=tau_re>0; Im(tau) contributes only unit phases to the norm",
            "h_coefficients": "p_T^(-j tau)/j",
            "flow_coefficients": "log(p_T)p_T^(-j tau)",
            "flow_H0_norm_squared": "log(p_T)^2/[p_T^(2 Re(tau))-1]",
            "blowup_squared": "log(p_T)/(2 Re(tau))+O(1)",
            "blowup_norm": "sqrt(log(p_T)/(2 Re(tau)))(1+o(1))",
            "scaled_limit": scaled_limit,
            "records": positive_time_records,
        },
        "checkpoints": [
            "PASS_POSITIVE_TAU_LOGJET_GRAPH",
            "PASS_ZERO_TIME_LOGJET_IN_HMINUS1",
        ],
    }


# ---------------------------------------------------------------------------
# Exact endpoint support and the J/H coequalizer graph


def valuation(value: int, prime: int) -> int:
    exponent = 0
    while value % prime == 0 and value > 0:
        value //= prime
        exponent += 1
    return exponent


def h_at_zero_over_logp(divisor: int, prime: int) -> int:
    """Return H_(p,0)(d)/log(p) by exact finite convolution."""

    return sum(
        int(sp.mobius(a)) * valuation(divisor // a, prime)
        for a in sp.divisors(divisor)
    )


def endpoint_support_audit() -> dict[str, object]:
    cases = []
    for prime in (3, 5):
        other = 5 if prime == 3 else 3
        labels = [1, prime, prime**2, prime**3, prime * other, prime**2 * other]
        for divisor in labels:
            coefficient = h_at_zero_over_logp(divisor, prime)
            expected = int(divisor > 1 and set(sp.factorint(divisor)) == {prime})
            if coefficient != expected:
                raise RuntimeError("H_(p,0) prime-power support identity failed")
            cases.append(
                {
                    "p_A": prime,
                    "d_J": divisor,
                    "H_p0_over_logp": coefficient,
                    "prime_power_support": bool(expected),
                }
            )
    return {
        "schema": "c2.green.closed_native_endpoint.endpoint_support.v1",
        "identity": "H_(p_A,0)(d_J)=log(p_A) iff d_J=p_A^a, and 0 otherwise",
        "convolution": "H_(p,0)=mu*(N_p id^0)",
        "records": cases,
        "literal_identification_scope": (
            "only on a nonzero support channel may p_A be identified with p_T; "
            "the axes remain distinct elsewhere"
        ),
        "top_2adic_source": "k_eff/unit-mass carry, not the odd material logjet",
    }


def q_jh(values: Mapping[tuple[int, int], Fraction]) -> dict[int, Fraction]:
    """Q_JH tensor I_tower: sum d_J while preserving the tower level j."""

    output: dict[int, Fraction] = {}
    for (_d_jordan, tower_level), value in values.items():
        output[tower_level] = output.get(tower_level, Fraction(0)) + value
    return {j: value for j, value in output.items() if value}


def number_pre(values: Mapping[tuple[int, int], Fraction]) -> dict[tuple[int, int], Fraction]:
    return {(d_jordan, j): j * value for (d_jordan, j), value in values.items()}


def number_post(values: Mapping[int, Fraction]) -> dict[int, Fraction]:
    return {j: j * value for j, value in values.items()}


def sparse_pre_records(
    values: Mapping[tuple[int, int], Fraction]
) -> list[dict[str, object]]:
    return [
        {"d_J": d_jordan, "j": j, "coefficient": value}
        for (d_jordan, j), value in sorted(values.items())
    ]


def sparse_post_records(values: Mapping[int, Fraction]) -> list[dict[str, object]]:
    return [
        {"j": j, "coefficient": value} for j, value in sorted(values.items())
    ]


def coequalizer_graph_audit() -> dict[str, object]:
    exact_samples = [
        {(1, 1): Fraction(2, 3), (2, 1): Fraction(-2, 3), (1, 3): Fraction(5, 7)},
        {(1, 2): Fraction(-4, 5), (3, 2): Fraction(7, 11), (9, 4): Fraction(3, 13)},
        {(1, 1): Fraction(1), (2, 1): Fraction(-1)},
    ]
    checks = []
    for sample in exact_samples:
        qn = q_jh(number_pre(sample))
        nq = number_post(q_jh(sample))
        if qn != nq:
            raise RuntimeError("tower number does not commute with Q_JH tensor I")
        checks.append(
            {
                "input": sparse_pre_records(sample),
                "QN": sparse_post_records(qn),
                "NbarQ": sparse_post_records(nq),
                "equal": True,
            }
        )

    kernel_witness = {(1, 3): Fraction(5, 7), (2, 3): Fraction(-5, 7)}
    if q_jh(kernel_witness) or q_jh(number_pre(kernel_witness)):
        raise RuntimeError("Q-kernel invariance witness failed")

    return {
        "schema": "c2.green.jh_coequalizer.number_graph.v1",
        "forward_carrier": (
            "D_JH^fin tensor D_tower^fin with indices "
            "(p_A,tau,d_J,flags,role) tensor (p_T,j)"
        ),
        "coequalizer": "Q=Q_JH tensor I_tower; Q_JH sums d_J contributions only",
        "number": "N=I_JH tensor diag(j)",
        "commutation": "QN=Nbar Q",
        "kernel_invariance": "N(D(N) intersect ker Q) subset ker Q",
        "exact_checks": checks,
        "kernel_witness": {
            "input": sparse_pre_records(kernel_witness),
            "Qx": sparse_post_records(q_jh(kernel_witness)),
            "QNx": sparse_post_records(q_jh(number_pre(kernel_witness))),
        },
        "quotient_scale": {
            "H_Q_0": "completion of QD_fin in the quotient H0 norm",
            "H_Q_minus1": "completion in the quotient Hminus1 norm",
            "Nbar_norm": 1,
            "proof": (
                "N is an isometry H0->Hminus1 and N^-1 is defined on every j>=1; "
                "taking infima over Q-cosets gives equality of quotient norms"
            ),
        },
        "closed_relation": {
            "definition": "R_Q=Graph(Nbar) subset H_Q_0 direct_sum H_Q_minus1",
            "closed": True,
            "single_valued": True,
            "multivalued_part": "{0}",
            "section_chosen": False,
            "representative_minimized": False,
        },
        "typing_warning": (
            "summing the tower levels j would be S0-like scalar synthesis, not Q_JH; "
            "that forbidden conflation would manufacture a multivalued relation"
        ),
        "checkpoints": [
            "PASS_TOWER_NUMBER_DESCENDS_THROUGH_JH_COEQUALIZER",
            "PASS_CLOSED_POST_T0_TOWER_BOUNDARY_RELATION",
        ],
    }


# ---------------------------------------------------------------------------
# Does the centered A leg respect the coequalizer gauge?


def a_descent_audit() -> dict[str, object]:
    # Exact witness in the frozen divisor-sum coequalizer model.  d_J and j
    # remain separate: no tower level is used in this A-side test.
    tau = sp.Integer(1)
    leg_n = sp.Integer(2)
    jordan_1 = sp.Integer(1)
    jordan_2 = sp.Integer(2) ** (2 * tau) - 1
    phi_1 = leg_n ** (-tau)
    phi_2 = leg_n ** (-tau)
    a_weights = sp.Matrix([sp.sqrt(jordan_1) * phi_1, sp.sqrt(jordan_2) * phi_2])
    gauge = sp.Matrix([1, -1])
    q_value = sp.Matrix([[1, 1]]) * gauge
    a_value = sp.simplify((a_weights.T * gauge)[0])
    if q_value[0] != 0 or a_value == 0:
        raise RuntimeError("exact A/coequalizer kernel witness failed")

    return {
        "schema": "c2.green.closed_native_endpoint.a_descent.v1",
        "test_space": "pre-coequalizer d_J module at fixed p_A,tau,flag,cell,corner,orientation,role",
        "witness": {
            "p_A": 3,
            "tau": tau,
            "ell": 2,
            "leg_n": leg_n,
            "d_J_coordinates": [1, 2],
            "gauge_vector": gauge,
            "Q_gauge": q_value,
            "J_(2tau)(1)": jordan_1,
            "J_(2tau)(2)": jordan_2,
            "A_even_pre_weights": a_weights,
            "A_even_pre_gauge": a_value,
            "nonzero_proof": "(1-sqrt(3))/2 is nonzero because 1^2 != 3",
        },
        "kernel_inclusion": False,
        "A_even_pre_descends_to_Q_quotient": False,
        "graph_bound_after_descent_tested": False,
        "reason_graph_bound_not_tested": "a quotient map is not well-defined before kernel inclusion",
        "interpretation": (
            "the tower number respects the erased J/H gauge, but the separated one-leg A "
            "coordinate still detects it"
        ),
        "required_enrichment": [
            "p_A",
            "tau",
            "d_J",
            "cell",
            "corner",
            "orientation",
            "flags",
            "role",
        ],
        "checkpoint": "STOP_NATIVE_A_NONZERO_ON_COEQUALIZER_KERNEL",
        "frontier": "NEEDS_PROVENANCE_ENRICHED_GRAPH_RELATION",
    }


def native_comparison_audit(
    logjet: Mapping[str, object],
    scale: Mapping[str, object],
    coequalizer: Mapping[str, object],
    descent: Mapping[str, object],
) -> dict[str, object]:
    rows = [
        {
            "channel": "C2 odd prime-power logjet",
            "location": "post-Q quotient tower graph",
            "status": "canonical forward class ([h],[log(p_T)Nbar h])",
        },
        {
            "channel": "seed/coarse/bracket/center rescue/carry/cutoff",
            "location": "native C2/full-even graph before J/H gauge erasure",
            "status": "must retain enriched provenance for A-side gluing",
        },
        {
            "channel": "inherited/top/hidden/loss",
            "location": "historical post-T0 prime-power bundle",
            "status": "comparable to the quotient graph, not a pre-Q A representative",
        },
        {
            "channel": "top 2-adic level",
            "location": "k_eff/unit-mass carry and DN-to-T0 route",
            "status": "not generated by the odd material cumulant jet",
        },
    ]
    return {
        "schema": "c2.green.closed_native_endpoint.native_comparison.v1",
        "rows": rows,
        "post_t0_logjet_graph_constructed": True,
        "zero_time_value_space": "H_Q_0",
        "zero_time_flux_space": "H_Q_minus1",
        "closed_post_t0_relation": True,
        "native_A_gluing_constructed": False,
        "full_native_endpoint_graph_lift_constructed": False,
        "why_not": descent["checkpoint"],
        "not_emitted": [
            "PASS_NATIVE_A_DESCENDS_TO_QUOTIENT_GRAPH",
            "PASS_CLOSED_NATIVE_ENDPOINT_GRAPH_LIFT",
            "STOP_NO_NATIVE_MAP_FROM_C2_LOGJET_TO_ENDPOINT_GRAPH",
        ],
        "frontier": descent["frontier"],
        "Genuine_First": True,
        "Green_to_zero_claimed": False,
    }


def build_summary(
    logjet: Mapping[str, object],
    global_odd: Mapping[str, object],
    scale: Mapping[str, object],
    support: Mapping[str, object],
    coequalizer: Mapping[str, object],
    descent: Mapping[str, object],
    comparison: Mapping[str, object],
) -> dict[str, object]:
    passes = [
        logjet["checkpoint"],
        *scale["checkpoints"],
        *coequalizer["checkpoints"],
    ]
    return {
        "schema": "c2.green.closed_native_endpoint_graph.summary.v1",
        "result": descent["checkpoint"],
        "frontier": descent["frontier"],
        "passes": passes,
        "stops": [descent["checkpoint"]],
        "frozen_results_preserved": FROZEN_RESULTS,
        "phase_status": {
            "C2_prime_power_logjet": "pass",
            "global_odd_convolution_regression": "pass; local jet is the exact prime-power restriction",
            "positive_tau_graph": "pass",
            "zero_time_rigged_graph": "pass",
            "JH_number_descent": "pass",
            "post_T0_closed_relation": "pass",
            "A_descent": "stop with exact kernel witness",
            "native_channel_comparison": "blocked after A descent",
            "full_native_endpoint_graph_lift": "not emitted",
        },
        "axis_firewall_preserved": True,
        "post_t0_relation_multivalued_part": coequalizer["closed_relation"]["multivalued_part"],
        "endpoint_support_audited": len(support["records"]),
        "global_prime_power_agreements": global_odd["prime_power_restriction"]["record_count"],
        "global_mixed_channels_retained": global_odd["mixed_channels"]["retained_by_global_inversion"],
        "reverse_section_used": False,
        "forced_same_Hilbert_synthesis_used": False,
        "full_native_endpoint_graph_lift_constructed": comparison["full_native_endpoint_graph_lift_constructed"],
        "no_Green_to_zero_claim": True,
        "Genuine_First": True,
    }


# ---------------------------------------------------------------------------
# Reports and manifest


def render_logjet_report(
    logjet: Mapping[str, object],
    global_odd: Mapping[str, object],
    scale: Mapping[str, object],
    support: Mapping[str, object],
) -> str:
    return f"""# Jet primo-potência C2 e escala de grafo

## Resultado

`{logjet['checkpoint']}`  
`{scale['checkpoints'][0]}`  
`{scale['checkpoints'][1]}`

O jet nativo é obtido da massa C2 finita, sem usar uma função externa. Para um
primo material ímpar `p_T`,

```text
A_(M,p_T)(x)=sum_(j>=0)a_M(p_T^j)x^j,
B_(M,p_T)(x)=x partial_x log A_(M,p_T)(x).
```

A normalização Richardson é o objeto formal

```text
A_red=A_(2M,p_T)^2/A_(M,p_T),
kappa_(M,p_T,j)=P_j^R(M)/j.
```

Os {len(logjet['finite_exact_records'])} coeficientes persistidos verificam
exatamente essa identidade por Newton e por expansão formal independente. A
feature one-leg congelada é `phi_(tau,d_J)(n)=1_(d_J|n)n^-tau`; portanto sua
especialização literal em `n=p_T^j` é

```text
rho_(p_T,j)(tau)=p_T^(-j tau),
```

e não `p_T^(-2j tau)`. Logo

```text
(log p_T) N h_(M,p_T,tau)
 =sum_(j>=1) log(p_T) P_j^R(M) rho_(p_T,j)(tau)e_(p_T,j)
```

coeficiente a coeficiente.

## A inversão global confirma a restrição primo-potência

Também foi reproduzido, com frações exatas, o construtor global fornecido pelo
usuário: massa nos cutoffs `400/800`, divisão de Dirichlet em todos os ímpares
e correção `2*b_800-b_400`. As massas coincidem com a soma bilateral C2 em
todos os {global_odd['mass_comparison']['low_odd_core_count']} núcleos ímpares
do cutoff baixo e nos {global_odd['mass_comparison']['high_odd_core_count']} do
cutoff alto.

Para as {global_odd['prime_power_restriction']['record_count']} primo-potências
ímpares menores que 200, o coeficiente global é exatamente
`log(p_T)P_j^R(400)`. Os compostos mistos permanecem como coordenadas
separadas; por exemplo,

```text
n=15: (log 3+log 5)/4096,
n=21: (log 3+log 7)/2048.
```

Esses cumulantes mistos não são níveis `j` e não são divisores Jordan `d_J`.
Eles reforçam a necessidade de preservar a proveniência completa antes de uma
relação enriquecida, sem alterar o jet primo-potência auditado aqui.

## Endpoint de tempo zero

No limite unit-mass, `P_j=1` e

```text
h_(p_T,0)=sum_(j>=1)j^-1 e_(p_T,j).
```

Esse vetor está em `H0=l2`, mas seu fluxo `N h=(1,1,...)` não está. Ele vive
canonicamente em `Hminus1`, pois

```text
||N y||_(Hminus1)^2=sum_j |j y_j|^2/j^2=||y||_(H0)^2.
```

Assim `N:H0->Hminus1` tem norma exatamente um. Para `Re(tau)>0`, o fluxo já
está em `H0`; a parte imaginária produz somente fases unitárias e

```text
||(log p_T)N h_(p_T,tau)||_H0^2
 =log(p_T)^2/[p_T^(2 Re(tau))-1].
```

Quando `Re(tau)` desce a zero, o quadrado da norma cresce como
`log(p_T)/(2 Re(tau))`; isso é a passagem controlada de Hilbert para rigged graph,
não um vetor `l2` escondido.

## Firewall

`p_A`, `p_T`, `j`, `K=k_eff`, `d_J` e `tau` permanecem eixos distintos. A
identidade de suporte auditada foi

```text
H_(p_A,0)(d_J)=log(p_A) se d_J=p_A^a; 0 nos demais d_J.
```

Somente nesse canal não nulo se identifica literalmente `p_A=p_T`. O topo
2-ádico continua vindo do carry/unit-mass nativo, não deste jet material.
"""


def render_coequalizer_report(
    coequalizer: Mapping[str, object], descent: Mapping[str, object]
) -> str:
    return f"""# Relação de grafo do coequalizer J/H

## Resultado

`{coequalizer['checkpoints'][0]}`  
`{coequalizer['checkpoints'][1]}`  
`{descent['checkpoint']}`

O carrier forward correto é o produto tensorial

```text
(p_A,tau,d_J,flags,role) tensor (p_T,j).
```

O coequalizer age somente no primeiro fator:

```text
Q=Q_JH tensor I_tower,
N=I_JH tensor diag(j).
```

Daí `QN=Nbar Q` literalmente. Em particular,

```text
N(D(N) intersect ker Q) subset ker Q.
```

Não foi escolhida seção. Os quocientes `H_Q^0` e `H_Q^-1` são completados
pelas respectivas normas de quociente. Como `N:H0->Hminus1` é isométrico e
`j>=1`, tomar o ínfimo nas classes fornece

```text
||Nbar [x]||_(Q,-1)=||[x]||_(Q,0).
```

Portanto

```text
R_Q=Graph(Nbar) subset H_Q^0 direct_sum H_Q^-1
```

é fechada, single-valued e tem parte multivaluada `{{0}}`.

Somar os níveis `j` produziria outra operação, semelhante à síntese escalar
posterior. Isso não é `Q_JH` e violaria o firewall `d_J != j`.

## A perna A não desce

No core `ell=2`, `tau=1`, a classe-gauge `(1,-1)` nos canais `d_J=1,2` é
apagada por `Q`. A análise one-leg tem pesos

```text
(sqrt(J_2tau(1))phi_1, sqrt(J_2tau(2))phi_2)
 =(1/2,sqrt(3)/2),
```

e portanto vê o gauge como `(1-sqrt(3))/2`, que é não nulo. Logo
`ker Q` não está contido em `ker A_even_pre`. Não existe mapa de `A` no
quociente atual, e nenhum bound de grafo posterior a essa descida foi
declarado.
"""


def render_endpoint_report(
    summary: Mapping[str, object], comparison: Mapping[str, object]
) -> str:
    return f"""# Lift nativo C2 para a relação de endpoint fechada

## Decisão

O jet C2 possui um mapa forward canônico para a relação pós-T0:

```text
h -> ([h], [log(p_T) Nbar h])
     in H_Q^0 direct_sum H_Q^-1.
```

Isso prova `PASS_CLOSED_POST_T0_TOWER_BOUNDARY_RELATION` sem recuperar uma
pré-imagem histórica e sem forçar value/flux no mesmo Hilbert.

A colagem com a perna A nativa, porém, falha no gate obrigatório:

`{summary['result']}`

O gauge `d_J` apagado por `Q` ainda é observado por `A_even_pre`. Por isso não
foram emitidos:

- `PASS_NATIVE_A_DESCENDS_TO_QUOTIENT_GRAPH`;
- `PASS_CLOSED_NATIVE_ENDPOINT_GRAPH_LIFT`.

A fronteira correta é:

`{summary['frontier']}`

Ela deve preservar `p_A,tau,d_J,cell,corner,orientation,flags,role` no lado A,
enquanto usa o quociente somente no lado do jet/endpoint. Isso é uma relação
enriquecida, não uma seção reversa.

## Classificação dos canais

| Canal | Localização | Estado |
|---|---|---|
""" + "\n".join(
        f"| {row['channel']} | {row['location']} | {row['status']} |"
        for row in comparison["rows"]
    ) + """

Os resultados congelados de entrada permanecem históricos e inalterados. Não
foi emitida conclusão Green→zero.
"""


def generated_paths(result_dir: Path) -> list[Path]:
    return [
        REPORT_LOGJET,
        REPORT_ENDPOINT,
        REPORT_COEQUALIZER,
        ROOT / "script/c2_green_closed_native_endpoint_graph.py",
        TEST_PATH,
        *[
            result_dir / name
            for name in (
                "integrity.json",
                "prime_power_logjet.json",
                "hilbert_scale.json",
                "global_odd_convolution.json",
                "endpoint_support.json",
                "coequalizer_relation.json",
                "a_descent.json",
                "native_comparison.json",
                "summary.json",
            )
        ],
    ]


def build_manifest(historical_before: Mapping[str, str], result_dir: Path) -> dict[str, object]:
    historical_after = {name: sha256_file(ROOT / name) for name in historical_before}
    mismatches = {
        name: {"before": historical_before[name], "after": historical_after[name]}
        for name in historical_before
        if historical_before[name] != historical_after[name]
    }
    generated = [path for path in generated_paths(result_dir) if path.exists()]
    return {
        "schema": "c2.green.closed_native_endpoint_graph.manifest.v1",
        "generated": [
            {"path": relative(path), "bytes": path.stat().st_size, "sha256": sha256_file(path)}
            for path in sorted(generated)
        ],
        "historical_integrity": {
            "tracked_count": len(historical_before),
            "all_preserved": not mismatches,
            "mismatches": mismatches,
            "hashes_before": dict(historical_before),
            "hashes_after": historical_after,
        },
        "frozen_witness_count": 54,
        "reverse_section_used": False,
        "LP_or_solver_used": False,
        "external_completion_used": False,
        "Green_to_zero_claimed": False,
        "result_dir": relative(result_dir),
    }


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--result-dir", type=Path, default=RESULT)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    result_dir = args.result_dir
    result_dir.mkdir(parents=True, exist_ok=True)

    integrity = integrity_audit()
    historical_before = dict(integrity["historical_hashes_before"])
    logjet = exact_logjet_audit()
    global_odd = global_odd_convolution_audit()
    scale = hilbert_scale_audit()
    support = endpoint_support_audit()
    coequalizer = coequalizer_graph_audit()
    descent = a_descent_audit()
    comparison = native_comparison_audit(logjet, scale, coequalizer, descent)
    summary = build_summary(logjet, global_odd, scale, support, coequalizer, descent, comparison)

    payloads = {
        "integrity.json": integrity,
        "prime_power_logjet.json": logjet,
        "global_odd_convolution.json": global_odd,
        "hilbert_scale.json": scale,
        "endpoint_support.json": support,
        "coequalizer_relation.json": coequalizer,
        "a_descent.json": descent,
        "native_comparison.json": comparison,
        "summary.json": summary,
    }
    for name, payload in payloads.items():
        json_dump(result_dir / name, payload)

    REPORT_LOGJET.write_text(
        render_logjet_report(logjet, global_odd, scale, support), encoding="utf-8"
    )
    REPORT_COEQUALIZER.write_text(render_coequalizer_report(coequalizer, descent), encoding="utf-8")
    REPORT_ENDPOINT.write_text(render_endpoint_report(summary, comparison), encoding="utf-8")

    manifest = build_manifest(historical_before, result_dir)
    json_dump(result_dir / "manifest.json", manifest)
    if not manifest["historical_integrity"]["all_preserved"]:
        raise RuntimeError("historical artifact hash changed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
