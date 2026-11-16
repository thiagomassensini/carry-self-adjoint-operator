#!/usr/bin/env python3
"""Diagnostic Schur/Euler calculation from an existing C2 moment CSV.

This reads supplied moments only. It does not generate heights, moments, or
certified intervals. The odd Euler integral is evaluated from the source
Euler convolution recurrence, independently of the Schur-balance identity.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path

from mpmath import mp


def compute(dps: int, raw_moments: list[str]) -> dict[tuple[int, int], dict[str, mp.mpf]]:
    mp.dps = dps
    h = [mp.mpf(value) for value in raw_moments]
    result: dict[tuple[int, int], dict[str, mp.mpf]] = {}

    for s in (0, 1):
        for n in range(8):
            if n == 0:
                v = [mp.mpf(1)]
                pivot = h[s]
                condition = mp.mpf(1)
            else:
                old = mp.matrix([[h[i + j + s] for j in range(n)] for i in range(n)])
                coupling = mp.matrix([h[i + n + s] for i in range(n)])
                solved = mp.lu_solve(old, coupling)
                v = [-solved[i] for i in range(n)] + [mp.mpf(1)]
                pivot = h[2 * n + s] - sum(coupling[i] * solved[i] for i in range(n))
                condition = mp.norm(old, p=mp.inf) * mp.norm(old**-1, p=mp.inf)

            rho = sum(v[i] * h[i] for i in range(n + 1))

            def euler_moment(k: int) -> mp.mpf:
                convolution = sum(h[j] * h[k - 1 - j] for j in range(k))
                return (2 * k + 2) * h[k] - 2 * convolution

            integral_over_c0 = sum(
                v[i] * v[j] * euler_moment(i + j + s)
                for i in range(n + 1)
                for j in range(n + 1)
            )
            factor = 4 * n + 2 if s == 0 else 4 * n + 4
            square = mp.mpf(0) if s == 0 else 2 * rho**2
            residual = factor * pivot - integral_over_c0 - square
            scale = max(abs(factor * pivot), abs(integral_over_c0), abs(square), mp.mpf("1e-100"))
            q = -integral_over_c0 / (2 * rho**2) if s == 1 and rho else None
            result[s, n] = {
                "p": pivot,
                "rho": rho,
                "I_over_c0": integral_over_c0,
                "condition_inf": condition,
                "q": q,
                "relative_balance_residual": abs(residual) / scale,
            }
    return result


def relative_change(left: mp.mpf, right: mp.mpf) -> mp.mpf:
    return abs(right - left) / abs(right)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("csv", type=Path, help="existing CSV with columns k,h_k")
    parser.add_argument("--dps", nargs="+", type=int, default=[70, 90, 110, 120])
    args = parser.parse_args()
    if len(args.dps) < 2 or sorted(args.dps) != args.dps:
        parser.error("--dps must contain at least two increasing precision values")

    raw = list(csv.DictReader(args.csv.read_text(encoding="utf-8").splitlines()))
    if len(raw) < 16 or [int(row["k"]) for row in raw[:16]] != list(range(16)):
        parser.error("the CSV must provide rows k=0,...,15")
    raw_moments = [row["h_k"] for row in raw[:16]]
    runs = {dps: compute(dps, raw_moments) for dps in args.dps}

    stability = []
    for dps_left, dps_right in zip(args.dps, args.dps[1:]):
        changes = []
        left, right = runs[dps_left], runs[dps_right]
        for key in left:
            s, _n = key
            fields = ["p", "I_over_c0"] + (["rho", "q"] if s == 1 else [])
            changes.extend(relative_change(left[key][field], right[key][field]) for field in fields)
        stability.append(
            {
                "from_to_dps": f"{dps_left}->{dps_right}",
                "max_relative_change": mp.nstr(max(changes), 8),
            }
        )

    highest = runs[args.dps[-1]]
    table = []
    for n in range(8):
        row = {"n": n}
        for s in (0, 1):
            values = highest[s, n]
            row[f"p{s}"] = mp.nstr(values["p"], 14)
            row[f"I{s}_over_c0"] = mp.nstr(values["I_over_c0"], 14)
            row[f"condition{s}_inf"] = mp.nstr(values["condition_inf"], 8)
            row[f"relative_balance_residual{s}"] = mp.nstr(values["relative_balance_residual"], 8)
            if s == 1:
                row["rho1"] = mp.nstr(values["rho"], 14)
                row["q1"] = mp.nstr(values["q"], 14) if values["q"] is not None else None
        table.append(row)

    print(
        json.dumps(
            {
                "input": str(args.csv),
                "input_sha256": hashlib.sha256(args.csv.read_bytes()).hexdigest(),
                "dps": args.dps,
                "interpretation": "multiprecision diagnostic only; no interval certificate",
                "results": table,
                "precision_stability": stability,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
