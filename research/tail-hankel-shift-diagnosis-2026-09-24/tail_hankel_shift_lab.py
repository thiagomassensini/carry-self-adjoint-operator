#!/usr/bin/env python3
"""Reproducible diagnostic for the two shifts audited on 2026-09-24.

This is a falsification/shape laboratory, not a proof engine.

Part I evaluates the *literal* aligned-center `centerBracketTerm` formula
from NativeCarrySpectralWeyl.Camera.BracketSeries on cameras 2,...,7.  It
checks the finite-window form of

    T_(N+1) = T_N - a_N.

Part II uses a declared positive atomic Stieltjes model solely to test the
universal finite matrix algebra

    K = G S + boundary,  A = G^-1 K,
    A^T G = G A = K,
    G^(1/2) A G^(-1/2) = G^(-1/2) K G^(-1/2).

It deliberately does *not* claim that this synthetic measure is the native
moment sequence.  No candidate tail-to-moment map is fitted or inferred.
"""

from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp


mp.mp.dps = 80
CAMERAS = (2, 3, 4, 5, 6, 7)
CUTOFFS = (8, 16, 32, 64)
TIMES = (mp.mpf("0"), mp.mpf("1"), mp.mpf("14.134725141734693790"))
# This is a finite-window *identity* check, so 256 terms are enough: the two
# sides share the same terminal center and no numerical approximation of the
# infinite sum enters the reported residual.
TAIL_WINDOW = 256


def native_line(t: mp.mpf) -> mp.mpc:
    return mp.mpc(mp.mpf("0.5"), t)


def aligned_center(camera: int, index: int) -> int:
    return (4 if camera == 2 else camera) * (index + 1)


def dirichlet_value(s: mp.mpc, n: int) -> mp.mpc:
    return mp.power(n, -s)


def centered_bracket(s: mp.mpc, center: int, radius: int) -> mp.mpc:
    return (
        dirichlet_value(s, center - radius)
        - 2 * dirichlet_value(s, center)
        + dirichlet_value(s, center + radius)
    )


def center_bracket_term(camera: int, s: mp.mpc, index: int) -> mp.mpc:
    center = aligned_center(camera, index)
    if camera == 2:
        return centered_bracket(s, center, 1)
    return mp.fsum(centered_bracket(s, center, radius) for radius in range(1, camera // 2 + 1))


def tail_window(camera: int, t: mp.mpf, cutoff: int, terms: int) -> mp.mpc:
    s = native_line(t)
    return mp.fsum(center_bracket_term(camera, s, cutoff + m) for m in range(terms))


def norm_inf(matrix: mp.matrix) -> mp.mpf:
    return max((mp.fsum(abs(matrix[i, j]) for j in range(matrix.cols)) for i in range(matrix.rows)), default=mp.mpf("0"))


def atomic_moments(order: int) -> list[mp.mpf]:
    # Positive, distinct nodes: a controlled Stieltjes model for universal
    # finite-Hankel algebra only.  It is not native data.
    nodes = [mp.mpf(x) for x in ("0.08", "0.31", "0.73", "1.27", "1.91", "2.63", "3.47")]
    weights = [mp.mpf(x) for x in ("0.17", "0.11", "0.19", "0.13", "0.16", "0.09", "0.15")]
    return [mp.fsum(w * y**n for y, w in zip(nodes, weights)) for n in range(order + 1)]


def matrix_from_rows(rows: list[list[mp.mpf]]) -> mp.matrix:
    return mp.matrix(rows)


def hankel(moments: list[mp.mpf], n: int, shifted: bool = False) -> mp.matrix:
    offset = 1 if shifted else 0
    return matrix_from_rows([[moments[i + j + offset] for j in range(n)] for i in range(n)])


def raising_shift(n: int) -> mp.matrix:
    # S e_j = e_(j+1), j < n-1; S e_(n-1) = 0.
    result = mp.zeros(n)
    for j in range(n - 1):
        result[j + 1, j] = 1
    return result


def boundary_matrix(k: mp.matrix) -> mp.matrix:
    result = mp.zeros(k.rows)
    for i in range(k.rows):
        result[i, k.cols - 1] = k[i, k.cols - 1]
    return result


def diagonal(values: list[mp.mpf]) -> mp.matrix:
    result = mp.zeros(len(values))
    for i, value in enumerate(values):
        result[i, i] = value
    return result


def tail_checks() -> dict[str, object]:
    records = []
    for camera in CAMERAS:
        for t in TIMES:
            s = native_line(t)
            for cutoff in CUTOFFS:
                # Exact finite-window recurrence; its residual is only
                # arithmetic roundoff, not a tail truncation error.
                lead = center_bracket_term(camera, s, cutoff)
                tail_n = tail_window(camera, t, cutoff, TAIL_WINDOW)
                tail_succ = tail_window(camera, t, cutoff + 1, TAIL_WINDOW - 1)
                shift_residual = abs(tail_succ - (tail_n - lead))
                records.append(
                    {
                        "camera": camera,
                        "time": mp.nstr(t, 18),
                        "cutoff": cutoff,
                        "finite_window_shift_residual": mp.nstr(shift_residual, 8),
                    }
                )

    compensation = []
    for camera in CAMERAS:
        for t in TIMES:
            s = native_line(t)
            for left, right in zip(CUTOFFS, CUTOFFS[1:]):
                # Same terminal center for both tail windows makes this a
                # finite exact compensation identity.
                terminal = right + TAIL_WINDOW
                head_increment = mp.fsum(center_bracket_term(camera, s, n) for n in range(left, right))
                tail_difference = (
                    tail_window(camera, t, left, terminal - left)
                    - tail_window(camera, t, right, terminal - right)
                )
                compensation.append(
                    {
                        "camera": camera,
                        "time": mp.nstr(t, 18),
                        "cutoffs": [left, right],
                        "head_minus_tail_difference_residual": mp.nstr(abs(head_increment - tail_difference), 8),
                    }
                )
    return {"finite_window_shift": records, "finite_window_compensation": compensation}


def hankel_checks() -> dict[str, object]:
    results = []
    times_for_metric_flow = TIMES
    for n in (2, 3, 4):
        moments = atomic_moments(2 * n + 3)
        g = hankel(moments, n)
        k = hankel(moments, n, shifted=True)
        s = raising_shift(n)
        boundary = boundary_matrix(k)
        a = g**-1 * k
        c = mp.matrix([a[i, n - 1] for i in range(n)])
        rank_one = mp.zeros(n)
        for i in range(n):
            rank_one[i, n - 1] = c[i]

        eigenvalues, q = mp.eigsy(g)
        sqrt_g = q * diagonal([mp.sqrt(x) for x in eigenvalues]) * q.T
        invsqrt_g = q * diagonal([1 / mp.sqrt(x) for x in eigenvalues]) * q.T
        j = invsqrt_g * k * invsqrt_g
        whitened_conjugate = sqrt_g * a * invsqrt_g

        metric_flow = []
        for t in times_for_metric_flow:
            u = mp.expm(-mp.j * t * a)
            metric_flow.append(mp.nstr(norm_inf(u.conjugate().transpose() * g * u - g), 8))

        results.append(
            {
                "dimension": n,
                "min_eigenvalue_G": mp.nstr(min(eigenvalues), 12),
                "K_minus_GS_minus_boundary_norm_inf": mp.nstr(norm_inf(k - g * s - boundary), 8),
                "A_minus_S_minus_c_last_norm_inf": mp.nstr(norm_inf(a - s - rank_one), 8),
                "GA_minus_K_norm_inf": mp.nstr(norm_inf(g * a - k), 8),
                "ATG_minus_K_norm_inf": mp.nstr(norm_inf(a.T * g - k), 8),
                "J_minus_JT_norm_inf": mp.nstr(norm_inf(j - j.T), 8),
                "sqrtG_A_invSqrt_minus_J_norm_inf": mp.nstr(norm_inf(whitened_conjugate - j), 8),
                "metric_flow_residuals_at_t_0_1_first_height": metric_flow,
            }
        )
    return {"synthetic_stieltjes_hankel_algebra": results}


def nonlinear_obstruction() -> dict[str, str]:
    # R(F) = -F'/(2F) is scale-invariant.  A nonzero linear map cannot have
    # that property: this is the first obstruction to a linear tail -> moment
    # map after completion is converted to the normalized response.
    z = mp.mpc(0)
    response_f = -mp.mpf("0.5")  # F(z)=1+z, so -F'(0)/(2F(0))
    response_2f = response_f
    linearity_residual = abs(response_2f - 2 * response_f)
    return {
        "test_function": "F(z)=1+z at z=0",
        "R(F)": mp.nstr(response_f, 12),
        "R(2F)": mp.nstr(response_2f, 12),
        "R(2F)-2R(F)": mp.nstr(linearity_residual, 12),
        "interpretation": "nonzero: normalized response -F'/(2F) is not a linear transform of F",
    }


def main() -> None:
    report = {
        "precision_decimal_digits": mp.mp.dps,
        "literal_tail_formula": "centerBracketTerm of NativeCarrySpectralWeyl.Camera.BracketSeries",
        "tail_checks": tail_checks(),
        "hankel_checks": hankel_checks(),
        "linearity_obstruction": nonlinear_obstruction(),
        "scope": (
            "The tail tests use literal cameras 2..7. The Hankel matrix tests use an explicitly "
            "synthetic positive atomic Stieltjes model, so they certify universal finite algebra only."
        ),
    }
    output = Path(__file__).with_name("tail_hankel_shift_lab_report.json")
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {output}")
    print("max literal finite-window tail-shift residual:", max(
        mp.mpf(row["finite_window_shift_residual"])
        for row in report["tail_checks"]["finite_window_shift"]
    ))
    print("max synthetic K-GS-boundary residual:", max(
        mp.mpf(row["K_minus_GS_minus_boundary_norm_inf"])
        for row in report["hankel_checks"]["synthetic_stieltjes_hankel_algebra"]
    ))
    print("normalized-response linearity obstruction:", report["linearity_obstruction"]["R(2F)-2R(F)"])


if __name__ == "__main__":
    main()
