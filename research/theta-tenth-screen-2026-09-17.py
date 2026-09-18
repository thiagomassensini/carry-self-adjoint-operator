#!/usr/bin/env python3
"""Exact-rational planning screen for the native tenth theta/Hankel gate.

This script is deliberately *not* a proof artifact.  It reuses the exact
rational enclosure formulas consumed by the Lean node certificates, but only
prints candidate boxes and interval diagnostics.  Its job is to select a
mesh/precision before emitting thousands of Lean declarations.

No floating-point arithmetic is used in the box computation.  The twenty
decimal pi interval is the one already certified in Mathlib by
`Real.pi_gt_d20` and `Real.pi_lt_d20`; the final formal certificate must still
replay every printed inequality in Lean.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
from math import ceil, comb, factorial, floor


PI_LO = Q(314159265358979323846, 10**20)
PI_HI = Q(314159265358979323847, 10**20)
GEOMETRIC_FACTOR = Q(12300, 12299)
# The sharp `p <= 10` exterior-tail lemma in
# `CompletedNativeThetaTenthSupport.lean` certifies this bound for the first
# mode.  The global factor is applied once when returning from the explicit
# `[0,1]` mode decomposition to the full theta tail.
TAIL_ERROR = Q(1, 100_000_000_000)
POWERS = (0, 2, 4, 6, 8, 10)
N10_SPECS = (
    (105, ((0, 2), (1, 1), (3, 1), (5, 1))),
    (-180, ((0, 2), (1, 1), (4, 2))),
    (-350, ((0, 2), (2, 2), (5, 1))),
    (2520, ((0, 2), (2, 1), (3, 1), (4, 1))),
    (-2646, ((0, 2), (3, 3))),
    (525, ((0, 1), (1, 2), (2, 1), (5, 1))),
    (-2205, ((0, 1), (1, 2), (3, 1), (4, 1))),
    (-9450, ((0, 1), (1, 1), (2, 2), (4, 1))),
    (26460, ((0, 1), (1, 1), (2, 1), (3, 2))),
    (-14700, ((0, 1), (2, 3), (3, 1))),
    (14175, ((1, 3), (2, 1), (4, 1))),
    (-35280, ((1, 3), (3, 2))),
    (22050, ((1, 2), (2, 2), (3, 1))),
)


def qfloor(x: Q) -> int:
    return x.numerator // x.denominator


def qceil(x: Q) -> int:
    return -((-x.numerator) // x.denominator)


def exp_lower(x: Q) -> Q:
    return sum((x / 32) ** i / factorial(i) for i in range(12)) ** 32


def exp_upper(x: Q) -> Q:
    return (
        sum((x / 32) ** i / factorial(i) for i in range(12))
        + (x / 32) ** 12 * Q(13, factorial(12) * 12)
    ) ** 32


def exp_lower128(x: Q) -> Q:
    return sum((x / 128) ** i / factorial(i) for i in range(12)) ** 128


def exp_upper128(x: Q) -> Q:
    return (
        sum((x / 128) ** i / factorial(i) for i in range(12))
        + (x / 128) ** 12 * Q(13, factorial(12) * 12)
    ) ** 128


def dec(x: Q, digits: int = 18) -> str:
    sign = "-" if x < 0 else ""
    x = abs(x)
    integer, remainder = divmod(x.numerator, x.denominator)
    out = []
    for _ in range(digits):
        remainder *= 10
        digit, remainder = divmod(remainder, x.denominator)
        out.append(str(digit))
    return f"{sign}{integer}.{' '.join(out).replace(' ', '')}"


def node_box(q: Q, scale: int, mode: int) -> tuple[Q, Q]:
    """The d20 analogue of the values fed to a mode-node theorem."""
    e_lo = Q(qfloor(exp_lower(2 * q) * scale), scale)
    e_hi = Q(qceil(exp_upper(2 * q) * scale), scale)
    arg_lo = mode * mode * PI_LO * e_lo - q / 2
    arg_hi = mode * mode * PI_HI * e_hi - q / 2
    outer_lower = exp_lower if mode == 1 else exp_lower128
    outer_upper = exp_upper if mode == 1 else exp_upper128
    outer_limit = 32 if mode == 1 else 128
    assert 0 <= arg_lo <= arg_hi <= outer_limit
    lo = Q(qfloor(2 / outer_upper(arg_hi) * scale), scale)
    hi = Q(qceil(2 / outer_lower(arg_lo) * scale), scale)
    assert 0 <= lo <= hi
    return lo, hi


def mode_boxes(cells: int, scale: int, mode: int) -> dict[int, tuple[Q, Q]]:
    nodes = {Q(j, cells) for j in range(cells + 1)}
    for p in POWERS:
        for j in range(cells):
            a, b = Q(j, cells), Q(j + 1, cells)
            mass = (b ** (p + 1) - a ** (p + 1)) / (p + 1)
            first = (b ** (p + 2) - a ** (p + 2)) / (p + 2)
            nodes.add(first / mass)
    node_bounds = {q: node_box(q, scale, mode) for q in nodes}

    boxes: dict[int, tuple[Q, Q]] = {}
    for p in POWERS:
        lower, upper = Q(), Q()
        for j in range(cells):
            a, b = Q(j, cells), Q(j + 1, cells)
            mass = (b ** (p + 1) - a ** (p + 1)) / (p + 1)
            first = (b ** (p + 2) - a ** (p + 2)) / (p + 2)
            mean = first / mass
            mean_lo, _ = node_bounds[mean]
            _, a_hi = node_bounds[a]
            _, b_hi = node_bounds[b]
            lower += mean_lo * mass
            upper += ((b * a_hi - a * b_hi) * mass + (b_hi - a_hi) * first) / (b - a)
        boxes[p] = lower, upper
    return boxes


def add(x: tuple[Q, Q], y: tuple[Q, Q]) -> tuple[Q, Q]:
    return x[0] + y[0], x[1] + y[1]


def sub(x: tuple[Q, Q], y: tuple[Q, Q]) -> tuple[Q, Q]:
    return x[0] - y[1], x[1] - y[0]


def mul(x: tuple[Q, Q], y: tuple[Q, Q]) -> tuple[Q, Q]:
    terms = (x[0] * y[0], x[0] * y[1], x[1] * y[0], x[1] * y[1])
    return min(terms), max(terms)


def power(x: tuple[Q, Q], n: int) -> tuple[Q, Q]:
    if n % 2 == 0 and x[0] <= 0 <= x[1]:
        return Q(), max(x[0] ** n, x[1] ** n)
    return min(x[0] ** n, x[1] ** n), max(x[0] ** n, x[1] ** n)


def scale_interval(c: int, x: tuple[Q, Q]) -> tuple[Q, Q]:
    return (c * x[0], c * x[1]) if c >= 0 else (c * x[1], c * x[0])


def product(c: int, factors: tuple[tuple[tuple[Q, Q], int], ...]) -> tuple[Q, Q]:
    out = (Q(c), Q(c))
    for x, n in factors:
        out = mul(out, power(x, n))
    return out


def numerator_interval(mu: list[tuple[Q, Q]]) -> tuple[Q, Q]:
    m = mu
    out = (Q(), Q())
    for coefficient, factors in N10_SPECS:
        out = add(out, product(coefficient,
            tuple((m[index], exponent) for index, exponent in factors)))
    return out


def centered_numerator_interval(mu: list[tuple[Q, Q]]) -> tuple[Q, Q, Q, Q]:
    """Bound N10 after expanding at the box centres.

    This keeps the common centre of every occurrence of a moment symbolic
    until the final absolute-error estimate.  It is still an independent
    box certificate, but it removes the artificial cancellation loss of
    evaluating each original signed monomial separately.
    """
    centres = [(lo + hi) / 2 for lo, hi in mu]
    radii = [(hi - lo) / 2 for lo, hi in mu]
    total: dict[tuple[int, ...], Q] = {}
    zero = (0, 0, 0, 0, 0, 0)
    for coefficient, factors in N10_SPECS:
        polynomial: dict[tuple[int, ...], Q] = {zero: Q(coefficient)}
        for index, exponent in factors:
            factor: dict[tuple[int, ...], Q] = {}
            for deviation_power in range(exponent + 1):
                key = tuple(
                    deviation_power if coordinate == index else 0
                    for coordinate in range(6))
                factor[key] = (Q(comb(exponent, deviation_power)) *
                               centres[index] ** (exponent - deviation_power))
            product_poly: dict[tuple[int, ...], Q] = {}
            for left_key, left_value in polynomial.items():
                for right_key, right_value in factor.items():
                    key = tuple(left_key[i] + right_key[i] for i in range(6))
                    product_poly[key] = (product_poly.get(key, Q()) +
                                         left_value * right_value)
            polynomial = product_poly
        for key, value in polynomial.items():
            total[key] = total.get(key, Q()) + value
    centre = total[zero]
    error = Q()
    for key, coefficient in total.items():
        if any(key):
            monomial_bound = Q(1)
            for radius, exponent in zip(radii, key):
                monomial_bound *= radius ** exponent
            error += abs(coefficient) * monomial_bound
    return centre - error, centre + error, centre, error


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=1024)
    parser.add_argument("--node-decimals", type=int, default=24)
    args = parser.parse_args()
    if args.cells <= 0:
        raise SystemExit("--cells must be positive")
    scale = 10 ** args.node_decimals
    first = mode_boxes(args.cells, scale, 1)
    second = mode_boxes(args.cells, scale, 2)
    # Retain modes 1 and 2 explicitly.  The old global factor is used only
    # for the remainder n >= 2, whose pointwise coefficient is
    # (1/12300)^2/(1-1/12300)=1/(12300*12299).
    remainder_factor = Q(1, 12300 * 12299)
    tail = {
        p: (
            first[p][0] + second[p][0],
            first[p][1] + second[p][1] + remainder_factor * first[p][1]
            + GEOMETRIC_FACTOR * TAIL_ERROR,
        )
        for p in POWERS
    }
    mu: list[tuple[Q, Q]] = [
        (Q(1, 2) - tail[0][1] / 4, Q(1, 2) - tail[0][0] / 4)
    ]
    for coefficient, prior, current in ((2, 0, 2), (12, 2, 4), (30, 4, 6),
                                        (56, 6, 8), (90, 8, 10)):
        mu.append((
            coefficient * tail[prior][0] - tail[current][1] / 4,
            coefficient * tail[prior][1] - tail[current][0] / 4,
        ))
    naive = numerator_interval(mu)
    centered = centered_numerator_interval(mu)

    print("SCREEN ONLY — not a Lean proof")
    print(f"cells={args.cells}; node-decimals={args.node_decimals}; pi=d20")
    print("first-mode integral boxes")
    for p in POWERS:
        lo, hi = first[p]
        print(f"  I{p}: [{dec(lo)}, {dec(hi)}], width={dec(hi - lo)}")
    print("second-mode integral boxes")
    for p in POWERS:
        lo, hi = second[p]
        print(f"  J{p}: [{dec(lo)}, {dec(hi)}], width={dec(hi - lo)}")
    print("theta-tail boxes")
    for p in POWERS:
        lo, hi = tail[p]
        print(f"  A{p}: [{dec(lo)}, {dec(hi)}], width={dec(hi - lo)}")
    print("xi cosine-moment boxes")
    for j, (lo, hi) in enumerate(mu):
        print(f"  mu{j}: [{dec(lo)}, {dec(hi)}], width={dec(hi - lo)}")
    print(f"N10 at interval centres: {dec(centered[2], 30)}")
    print(f"naive independent N10 interval: [{dec(naive[0], 30)}, {dec(naive[1], 30)}]")
    print(f"centred Taylor N10 interval: [{dec(centered[0], 30)}, {dec(centered[1], 30)}]")
    print(f"centred Taylor absolute error: {dec(centered[3], 30)}")
    print("A sign-indefinite naive interval is expected here; it diagnoses the need")
    print("for a dependency-preserving Bernstein/Taylor certificate, not a failure of N10.")


if __name__ == "__main__":
    main()
