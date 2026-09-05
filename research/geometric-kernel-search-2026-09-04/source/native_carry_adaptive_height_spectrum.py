#!/usr/bin/env python3
"""Adaptive finite native-height spectrum without spectral input.

The mathematical pipeline mirrors the formal finite construction:

    completed even characteristic -> logarithmic moments -> Hankel pair
    -> canonical LDL whitening -> positive Jacobi section
    -> inverse-square-root height eigenvalues.

The completed characteristic is evaluated through its theta/Mellin integral.
Only exp, log, gamma-free quadrature, matrix arithmetic, and elementary
constants are used.  No root finder, height table, t-scan, target spectrum,
or special L-function evaluator participates in the construction.

The expensive even integral moments are independent, computed in parallel,
and cached as decimal strings.  Repeated runs with the same internal precision
reuse them; increasing the requested order computes only the missing moments.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import math
import os
from pathlib import Path
import re
import tempfile
import time
from typing import Any, Sequence

import mpmath as mp


CACHE_VERSION = 1
SCRIPT_VERSION = "1.1.0"
LEAN_SNAPSHOT = "ab18c6a788e3e66f22f2a15cc4f347b1991acf83"
DEFAULT_CACHE = Path(__file__).resolve().with_name(".native_height_cache")


def _mp_text(value: mp.mpf, digits: int) -> str:
    return mp.nstr(value, digits, strip_zeros=False)


def _theta_kernel(u: mp.mpf, tolerance: mp.mpf) -> mp.mpf:
    """sum_{n>=1} exp(-pi*n^2*exp(u)), with an explicit term cutoff."""
    x = mp.exp(u)
    total = mp.mpf(0)
    n = 1
    while True:
        term = mp.exp(-mp.pi * n * n * x)
        total += term
        if term < tolerance:
            return total
        n += 1


def _integration_ceiling(k: int, dps: int) -> mp.mpf:
    """Choose U so the transformed double-exponential tail is negligible."""
    target = mp.mpf(dps + 35) * mp.log(10)
    upper = max(mp.mpf(6), mp.log(target / mp.pi) + 2)
    for _ in range(8):
        rhs = target + 2 * k * mp.log(max(upper, mp.mpf(1))) + upper / 4
        upper = max(upper, mp.log(rhs / mp.pi) + 2)
    return upper


def _theta_even_moment(k: int, dps: int) -> mp.mpf:
    r"""Integral A_k = int_1^inf psi(x)x^(-3/4)log(x)^(2k) dx."""
    mp.mp.dps = dps
    tolerance = mp.power(10, -(dps + 12))
    upper = _integration_ceiling(k, dps)

    def integrand(u: mp.mpf) -> mp.mpf:
        if not u and k:
            return mp.mpf(0)
        return (
            _theta_kernel(u, tolerance)
            * mp.exp(u / 4)
            * mp.power(u, 2 * k)
        )

    breaks = [mp.mpf(0), mp.mpf("0.5"), mp.mpf(1), mp.mpf(2), mp.mpf(4)]
    if upper > breaks[-1]:
        breaks.append(upper)
    else:
        breaks = [point for point in breaks if point < upper] + [upper]
    return mp.quad(integrand, breaks)


def _theta_moment_worker(task: tuple[int, int]) -> tuple[int, str]:
    k, dps = task
    value = _theta_even_moment(k, dps)
    return k, mp.nstr(value, dps + 8)


def _cache_path(cache_dir: Path, dps: int) -> Path:
    return cache_dir / f"theta-even-moments-v{CACHE_VERSION}-dps{dps}.json"


def _select_cache_precision(cache_dir: Path, requested_dps: int) -> int:
    """Reuse the closest available cache whose precision is not lower."""
    if not cache_dir.is_dir():
        return requested_dps
    pattern = re.compile(
        rf"^theta-even-moments-v{CACHE_VERSION}-dps([0-9]+)\.json$"
    )
    candidates = []
    for path in cache_dir.iterdir():
        match = pattern.match(path.name)
        if match:
            candidate = int(match.group(1))
            if candidate >= requested_dps:
                candidates.append(candidate)
    return min(candidates, default=requested_dps)


def _load_cache(path: Path, dps: int) -> dict[int, str]:
    if not path.is_file():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    if (
        payload.get("cache_version") != CACHE_VERSION
        or payload.get("dps") != dps
        or not isinstance(payload.get("moments"), dict)
    ):
        return {}
    return {int(key): str(value) for key, value in payload["moments"].items()}


def _save_cache(path: Path, dps: int, moments: dict[int, str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "cache_version": CACHE_VERSION,
        "dps": dps,
        "moments": {str(key): moments[key] for key in sorted(moments)},
    }
    handle, temporary_name = tempfile.mkstemp(
        prefix=path.name + ".", suffix=".tmp", dir=path.parent
    )
    try:
        with os.fdopen(handle, "w", encoding="utf-8") as stream:
            json.dump(payload, stream, sort_keys=True, separators=(",", ":"))
            stream.write("\n")
        os.replace(temporary_name, path)
    finally:
        if os.path.exists(temporary_name):
            os.unlink(temporary_name)


def theta_even_moments(
    maximum_k: int,
    dps: int,
    workers: int,
    cache_dir: Path,
    use_cache: bool,
) -> tuple[list[mp.mpf], dict[str, int]]:
    cache_dps = _select_cache_precision(cache_dir, dps) if use_cache else dps
    path = _cache_path(cache_dir, cache_dps)
    stored = _load_cache(path, cache_dps) if use_cache else {}
    needed = [k for k in range(maximum_k + 1) if k not in stored]
    reused = maximum_k + 1 - len(needed)

    if needed:
        tasks = [(k, cache_dps) for k in needed]
        if workers <= 1:
            generated = map(_theta_moment_worker, tasks)
            executor = None
        else:
            executor = concurrent.futures.ProcessPoolExecutor(max_workers=workers)
            generated = executor.map(_theta_moment_worker, tasks, chunksize=1)
        try:
            for k, text in generated:
                stored[k] = text
        finally:
            if executor is not None:
                executor.shutdown()
        if use_cache:
            _save_cache(path, cache_dps, stored)

    mp.mp.dps = dps
    values = [mp.mpf(stored[k]) for k in range(maximum_k + 1)]
    return values, {
        "reused": reused,
        "computed": len(needed),
        "cache_dps": cache_dps,
    }


def completed_even_coefficients(
    maximum_index: int, theta_moments: Sequence[mp.mpf]
) -> list[mp.mpf]:
    r"""Coefficients phi_j in F(z)=sum_j phi_j*z^(2j)."""
    cosine_coefficients: list[mp.mpf] = []
    for k in range(maximum_index + 1):
        sign = -1 if k % 2 else 1
        cosine_coefficients.append(
            sign
            * theta_moments[k]
            / (mp.power(2, 2 * k) * mp.factorial(2 * k))
        )

    phi = [mp.mpf("0.5") - cosine_coefficients[0] / 4]
    for j in range(1, maximum_index + 1):
        phi.append(-cosine_coefficients[j - 1] - cosine_coefficients[j] / 4)
    return phi


def logarithmic_moments(phi: Sequence[mp.mpf], count: int) -> list[mp.mpf]:
    """Division-free formal recurrence q*Phi=-Phi', solved at phi[0]."""
    moments: list[mp.mpf] = []
    for degree in range(count):
        correction = mp.fsum(
            moments[index] * phi[degree - index]
            for index in range(degree)
        )
        moments.append(
            (-(degree + 1) * phi[degree + 1] - correction) / phi[0]
        )
    return moments


def hankel_pair(moments: Sequence[mp.mpf], order: int) -> tuple[mp.matrix, mp.matrix]:
    gram = mp.matrix(order)
    shifted = mp.matrix(order)
    for row in range(order):
        for column in range(order):
            gram[row, column] = moments[row + column]
            shifted[row, column] = moments[row + column + 1]
    return gram, shifted


def canonical_ldl_whitener(gram: mp.matrix) -> tuple[mp.matrix, list[mp.mpf]]:
    """B=D^(-1/2)L^(-1) for G=L D L^T, matching the formal whitening."""
    n = gram.rows
    lower = mp.eye(n)
    diagonal = [mp.mpf(0)] * n
    for i in range(n):
        diagonal[i] = gram[i, i] - mp.fsum(
            lower[i, k] * lower[i, k] * diagonal[k] for k in range(i)
        )
        if diagonal[i] <= 0:
            raise ArithmeticError(
                f"nonpositive LDL pivot at {i}: increase --dps or reduce --order"
            )
        for j in range(i + 1, n):
            numerator = gram[j, i] - mp.fsum(
                lower[j, k] * lower[i, k] * diagonal[k] for k in range(i)
            )
            lower[j, i] = numerator / diagonal[i]
    inverse_lower = lower ** -1
    scale = mp.diag([1 / mp.sqrt(value) for value in diagonal])
    return scale * inverse_lower, diagonal


def max_abs_matrix(matrix: mp.matrix) -> mp.mpf:
    return max(
        (
            abs(matrix[row, column])
            for row in range(matrix.rows)
            for column in range(matrix.cols)
        ),
        default=mp.mpf(0),
    )


def finite_height_spectrum(
    moments: Sequence[mp.mpf], order: int, diagnostics: bool = False
) -> tuple[list[mp.mpf], dict[str, mp.mpf]]:
    gram, shifted = hankel_pair(moments, order)
    whitener, diagonal = canonical_ldl_whitener(gram)
    jacobi = whitener * shifted * whitener.T
    jacobi = (jacobi + jacobi.T) / 2
    values = list(mp.eigsy(jacobi, eigvals_only=True))
    if any(value <= 0 for value in values):
        raise ArithmeticError("the shifted finite Jacobi section is not positive")
    heights = sorted(1 / mp.sqrt(value) for value in values)
    report: dict[str, mp.mpf] = {"minimum_ldl_pivot": min(diagonal)}
    if diagnostics:
        report["whitening_error"] = max_abs_matrix(
            whitener * gram * whitener.T - mp.eye(order)
        )
        report["jacobi_symmetry_error"] = max_abs_matrix(jacobi - jacobi.T)
    return heights, report


def automatic_order(count: int, digits: int) -> int:
    """Conservative engineering policy; it is not a convergence theorem."""
    return max(count + 6, 2 * count + 4, count + math.ceil(digits / 6))


def automatic_max_order(initial_order: int, count: int, digits: int) -> int:
    """Finite budget for adaptive prefix-stability refinement."""
    extra = max(12, count, math.ceil(digits / 2))
    candidate = initial_order + extra
    return candidate if candidate % 2 == 0 else candidate + 1


def automatic_dps(order: int, digits: int) -> int:
    """Budget for Hankel/LDL conditioning plus requested output digits."""
    return digits + max(70, 8 * order + 30)


def stable_decimal_digits(first: Sequence[mp.mpf], second: Sequence[mp.mpf]) -> int:
    if not first or len(first) != len(second):
        return 0
    relative = max(
        abs(left - second_value) / max(mp.mpf(1), abs(second_value))
        for left, second_value in zip(first, second)
    )
    if not relative:
        return mp.mp.dps
    return max(0, int(mp.floor(-mp.log10(relative))))


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Adaptive finite native-height spectrum with no roots, t-scan, "
            "target heights, or special L-function evaluator."
        )
    )
    parser.add_argument("-n", "--eigenvalues", type=int, required=True)
    parser.add_argument("-d", "--digits", type=int, required=True)
    parser.add_argument("--order", type=int, default=0, help="0 selects automatically")
    parser.add_argument(
        "--max-order",
        type=int,
        default=0,
        help="adaptive ceiling; 0 selects automatically",
    )
    parser.add_argument("--dps", type=int, default=0, help="0 selects automatically")
    parser.add_argument(
        "--workers", type=int, default=max(1, os.cpu_count() or 1)
    )
    parser.add_argument("--cache-dir", type=Path, default=DEFAULT_CACHE)
    parser.add_argument("--no-cache", action="store_true")
    parser.add_argument("--signed", action="store_true")
    parser.add_argument("--json", action="store_true", dest="as_json")
    return parser


def validate_args(args: argparse.Namespace) -> None:
    if args.eigenvalues < 1:
        raise SystemExit("--eigenvalues must be positive")
    if args.digits < 5:
        raise SystemExit("--digits must be at least 5")
    if args.order and args.order < args.eigenvalues:
        raise SystemExit("--order cannot be smaller than --eigenvalues")
    if args.max_order and args.max_order < max(args.eigenvalues, args.order):
        raise SystemExit("--max-order is below the requested or fixed order")
    if args.dps and args.dps < args.digits + 20:
        raise SystemExit("--dps must exceed --digits by at least 20")
    if args.workers < 1:
        raise SystemExit("--workers must be positive")


def run(args: argparse.Namespace) -> dict[str, Any]:
    validate_args(args)
    started = time.perf_counter()
    initial_order = args.order or automatic_order(args.eigenvalues, args.digits)
    adaptive = args.order == 0
    max_order = (
        initial_order
        if not adaptive
        else args.max_order
        or automatic_max_order(initial_order, args.eigenvalues, args.digits)
    )
    dps = args.dps or automatic_dps(max_order, args.digits)
    workers = min(args.workers, 2 * max_order + 1)
    order_step = max(2, math.ceil(args.eigenvalues / 3))
    comparison_order = max(
        args.eigenvalues, initial_order - max(2, initial_order // 6)
    )

    previous: list[mp.mpf] | None = None
    order = initial_order
    stable_digits = 0
    stability_reached = False
    total_computed = 0
    initially_reused = 0
    cache_source_dps = dps
    first_cache_pass = True
    selected: list[mp.mpf] = []
    diagnostics: dict[str, mp.mpf] = {}
    orders_tested: list[int] = []

    while True:
        theta, cache_report = theta_even_moments(
            2 * order,
            dps,
            workers,
            args.cache_dir,
            not args.no_cache,
        )
        if first_cache_pass:
            initially_reused = cache_report["reused"]
            first_cache_pass = False
        cache_source_dps = cache_report["cache_dps"]
        total_computed += cache_report["computed"]
        mp.mp.dps = dps
        phi = completed_even_coefficients(2 * order, theta)
        moments = logarithmic_moments(phi, 2 * order)

        if previous is None:
            comparison, _ = finite_height_spectrum(moments, comparison_order)
            previous = comparison[: args.eigenvalues]
            orders_tested.append(comparison_order)

        heights, diagnostics = finite_height_spectrum(
            moments, order, diagnostics=True
        )
        selected = heights[: args.eigenvalues]
        stable_digits = (
            stable_decimal_digits(previous, selected)
            if comparison_order < order
            else 0
        )
        orders_tested.append(order)
        stability_reached = stable_digits >= args.digits
        if not adaptive or stability_reached or order >= max_order:
            break
        previous = selected
        comparison_order = order
        order = min(max_order, order + order_step)

    elapsed = time.perf_counter() - started

    signed_values: list[mp.mpf] | None = None
    if args.signed:
        signed_values = sorted([-value for value in selected] + selected)

    return {
        "status": (
            "NUMERICAL_PREFIX_STABILITY_REACHED_NOT_A_PROOF"
            if stability_reached
            else "NUMERICAL_FINITE_COMPRESSION_NOT_A_PROOF"
        ),
        "script_version": SCRIPT_VERSION,
        "lean_snapshot": LEAN_SNAPSHOT,
        "formal_declarations_used": [
            "completedNativeOperatorCharacteristic",
            "IsLogDerivativeMomentSequence",
            "hankelGram",
            "shiftedHankel",
            "canonicalLDLInverseFactor",
            "finiteHeightOperator",
            "canonicalSignedFiniteHeightOperator",
        ],
        "configuration": {
            "requested_eigenvalues": args.eigenvalues,
            "printed_digits": args.digits,
            "matrix_order": order,
            "comparison_order": comparison_order,
            "maximum_order": max_order,
            "orders_tested": orders_tested,
            "internal_dps": dps,
            "workers": workers,
            "automatic_order": args.order == 0,
            "automatic_dps": args.dps == 0,
            "adaptive_refinement": adaptive,
        },
        "construction_firewall": {
            "root_finder": False,
            "height_table": False,
            "t_scan": False,
            "target_spectrum": False,
            "special_l_function_evaluator": False,
        },
        "formal_pipeline": (
            "completed even characteristic -> q*Phi=-Phi' moments -> "
            "Hankel G,K -> canonical LDL whitening -> J -> 1/sqrt(spec J)"
        ),
        "characteristic_backend": "completed theta/Mellin integral",
        "positive_eigenvalues": [_mp_text(value, args.digits) for value in selected],
        "signed_eigenvalues": (
            [_mp_text(value, args.digits) for value in signed_values]
            if signed_values is not None
            else None
        ),
        "numerical_diagnostics": {
            "prefix_stability_decimal_digits": stable_digits,
            "requested_stability_decimal_digits": args.digits,
            "requested_stability_reached": stability_reached,
            "whitening_error": mp.nstr(diagnostics["whitening_error"], 12),
            "jacobi_symmetry_error": mp.nstr(
                diagnostics["jacobi_symmetry_error"], 12
            ),
            "minimum_ldl_pivot": mp.nstr(
                diagnostics["minimum_ldl_pivot"], 12
            ),
            "theta_moments_reused_at_start": initially_reused,
            "theta_moments_computed_this_run": total_computed,
            "theta_moment_cache_dps": cache_source_dps,
            "elapsed_seconds": round(elapsed, 6),
        },
        "accuracy_note": (
            "Printed digits are working-precision output. Adaptive prefix stability "
            "compares consecutive finite orders; it is not an interval certificate "
            "or an infinite-limit proof."
        ),
    }


def main() -> int:
    args = build_parser().parse_args()
    report = run(args)
    if args.as_json:
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0

    config = report["configuration"]
    print(
        f"order={config['matrix_order']} comparison={config['comparison_order']} "
        f"dps={config['internal_dps']} workers={config['workers']}"
    )
    print("positive finite-height eigenvalues:")
    for index, value in enumerate(report["positive_eigenvalues"], 1):
        print(f"{index:4d}  {value}")
    if report["signed_eigenvalues"] is not None:
        print("signed sector:")
        for value in report["signed_eigenvalues"]:
            print(value)
    diagnostics = report["numerical_diagnostics"]
    print("diagnostics:")
    print("  orders tested           =", config["orders_tested"])
    print("  prefix stability digits =", diagnostics["prefix_stability_decimal_digits"])
    print("  requested stability     =", diagnostics["requested_stability_reached"])
    print("  whitening error         =", diagnostics["whitening_error"])
    print("  minimum LDL pivot       =", diagnostics["minimum_ldl_pivot"])
    print(
        "  theta moments cache     =",
        f"{diagnostics['theta_moments_reused_at_start']} reused at start,",
        f"{diagnostics['theta_moments_computed_this_run']} computed",
    )
    print("  theta cache precision   =", diagnostics["theta_moment_cache_dps"])
    print("  elapsed seconds         =", diagnostics["elapsed_seconds"])
    if config["adaptive_refinement"] and not diagnostics["requested_stability_reached"]:
        print(
            "warning: requested prefix stability was not reached before --max-order"
        )
    print(report["status"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
