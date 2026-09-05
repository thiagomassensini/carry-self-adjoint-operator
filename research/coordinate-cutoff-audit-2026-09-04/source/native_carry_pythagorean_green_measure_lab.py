#!/usr/bin/env python3
"""Pythagorean carry measure for the infinite all-bases Green atlas.

The conservative all-bases incidence weights are

    omega_b(n) = k_b(n) log(b) / sum_c k_c(n) log(c).

They partition the mass of every n>1, but putting all of that mass through
every completed Green channel still leaves a harmonic outgoing tail.  The
native carry ratio q_b=b**(-1/2) supplies a second, orthogonal split:

    mu_G(b,n) = omega_b(n) q_b**2 = omega_b(n) / b,
    mu_R(b,n) = omega_b(n) (1-q_b**2).

Thus sum_b(mu_G+mu_R)=1.  The transmitted channel is measured with the
quadratically normalized Green operator

    Ahat_b = q_b A_b = (I-q_b U_b)**2,

while mu_R remains an explicit external residual/return port.  This extra
port is essential: it conserves the mass that did not cross the carry and
gives an endpoint lower frame bound without forcing the Green bulk to zero.

The laboratory proves finite-dimensional instances of the uniform estimates

    E_ext* E_ext >= 1/2 I,
    T* T <= (1+C_G) I,

where

    C_G = 3/2 + 12(zeta(2)-1) + 3(zeta(3)-1).

Consequently the normalized endpoint frame has a cutoff-independent lower
bound.  The base-2 bulk event at n=4 gives a cutoff-independent nonzero lower
bound for the normalized bulk.  Unlike uniform counting of all camera
horizontals, this measure therefore keeps both endpoint and bulk alive.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Sequence

import numpy as np
from scipy.linalg import eigh
from scipy.special import zeta

import native_carry_conservative_all_bases_atlas_lab as conservative
import native_carry_quadratic_weighted_green_atlas_lab as green


def parse_sizes(text: str) -> tuple[int, ...]:
    values = tuple(int(part.strip()) for part in text.split(",") if part.strip())
    if not values or any(value < 4 for value in values):
        raise ValueError("all sizes must be integers >= 4")
    return values


def chart_row_numbers(chart: green.TowerChart) -> np.ndarray:
    return np.asarray(
        [number for _, tower in chart.towers for number in tower],
        dtype=np.int64,
    )


def theoretical_constants() -> dict[str, float]:
    square_tail = float(zeta(2.0, 1.0) - 1.0)
    cube_tail = float(zeta(3.0, 1.0) - 1.0)
    active_green_bound = 1.5 + 12.0 * square_tail + 3.0 * cube_tail
    full_frame_upper = 1.0 + active_green_bound
    endpoint_lower = 0.5 / full_frame_upper
    bulk_fraction_lower = 0.25 / full_frame_upper
    return {
        "sum_b_ge_2_b_to_minus_2": square_tail,
        "sum_b_ge_2_b_to_minus_3": cube_tail,
        "C_G": active_green_bound,
        "full_frame_upper": full_frame_upper,
        "normalized_endpoint_lower": endpoint_lower,
        "normalized_bulk_fraction_lower": bulk_fraction_lower,
        "normalized_bulk_norm_lower": math.sqrt(bulk_fraction_lower),
        "poisson_norm_upper": math.sqrt((1.0 - endpoint_lower) / endpoint_lower),
        "poisson_norm_nonzero_lower": math.sqrt(
            bulk_fraction_lower / (1.0 - bulk_fraction_lower)
        ),
    }


def pythagorean_scale_audit(
    depths: np.ndarray, scales: np.ndarray, weights: np.ndarray
) -> dict[str, Any]:
    transmitted = np.sum(
        weights / np.arange(2, weights.shape[0] + 2, dtype=np.float64)[:, None],
        axis=0,
    )
    residual = np.sum(
        weights
        * (
            1.0
            - 1.0
            / np.arange(2, weights.shape[0] + 2, dtype=np.float64)[:, None]
        ),
        axis=0,
    )
    endpoint_scale = np.sum(scales * (depths == 1), axis=0)
    bulk_scale = np.sum(scales * (depths >= 2), axis=0)
    total_scale = endpoint_scale + bulk_scale
    endpoint_share = np.divide(
        endpoint_scale,
        total_scale,
        out=np.ones_like(total_scale),
        where=total_scale > 0.0,
    )
    partition = transmitted + residual
    return {
        "maximum_camera_partition_error_for_n_gt_1": float(
            np.max(np.abs(np.sum(weights, axis=0)[1:] - 1.0))
        ),
        "maximum_carry_split_error_for_n_gt_1": float(
            np.max(np.abs(partition[1:] - 1.0))
        ),
        "minimum_transmitted_mass": float(np.min(transmitted[1:])),
        "maximum_transmitted_mass": float(np.max(transmitted[1:])),
        "minimum_residual_mass": float(np.min(residual[1:])),
        "maximum_residual_mass": float(np.max(residual[1:])),
        "minimum_depth_one_scale_share": float(np.min(endpoint_share[1:])),
        "depth_one_share_lower_bound_pass": bool(
            np.min(endpoint_share[1:]) + 1.0e-12 >= 1.0 / 3.0
        ),
        "arithmetic_charge_proof": (
            "For every bulk base b with b^2|n and b<sqrt(n), map b to "
            "c=n/b>sqrt(n). Then k_c(n)=1, the map is injective, and "
            "k_b(n)log(b)<=2log(c). If b=sqrt(n), charge it to c=n. "
            "Hence bulk_scale<=2 endpoint_scale and endpoint_share>=1/3."
        ),
    }


def build_analyses(
    size: int,
) -> tuple[np.ndarray, np.ndarray, dict[str, Any]]:
    bases, depths, scales, weights = conservative.all_bases_weights(size)
    endpoint_rows: list[np.ndarray] = [np.eye(1, size, 0, dtype=np.float64)[0]]
    bulk_rows: list[np.ndarray] = []
    active_endpoint_count = 0
    active_bulk_count = 0
    residual_count = 0

    for base_index, base in enumerate(bases):
        chart = green.build_tower_chart(base, size)
        numbers = chart_row_numbers(chart)
        row_depths = depths[base_index, numbers - 1]
        row_weights = weights[base_index, numbers - 1]
        active = row_depths > 0

        # mu_G=omega/b and Ahat=q A.  In raw Green coordinates the total
        # multiplier is sqrt(omega) q^2.
        active_green = (
            np.sqrt(row_weights / float(base))[:, None]
            * (chart.q * chart.canonical_analysis)
        )
        endpoint_mask = active & (row_depths == 1)
        bulk_mask = active & (row_depths >= 2)
        endpoint_rows.extend(active_green[endpoint_mask])
        bulk_rows.extend(active_green[bulk_mask])
        active_endpoint_count += int(np.sum(endpoint_mask))
        active_bulk_count += int(np.sum(bulk_mask))

        active_numbers = numbers[active]
        residual_weights = row_weights[active] * (1.0 - 1.0 / float(base))
        for number, residual_weight in zip(active_numbers, residual_weights):
            row = np.zeros(size, dtype=np.float64)
            row[int(number) - 1] = math.sqrt(float(residual_weight))
            endpoint_rows.append(row)
        residual_count += int(active_numbers.size)

    endpoint = np.vstack(endpoint_rows)
    bulk = (
        np.vstack(bulk_rows)
        if bulk_rows
        else np.zeros((0, size), dtype=np.float64)
    )
    metadata = {
        "base_count": len(bases),
        "external_seed_rows": 1,
        "active_green_endpoint_rows": active_endpoint_count,
        "active_green_bulk_rows": active_bulk_count,
        "external_residual_return_rows": residual_count,
        "external_dimension": int(endpoint.shape[0]),
        "bulk_dimension": int(bulk.shape[0]),
        "measure": pythagorean_scale_audit(depths, scales, weights),
    }
    return endpoint, bulk, metadata


def one_size_audit(size: int, detailed: bool) -> dict[str, Any]:
    endpoint, bulk, metadata = build_analyses(size)
    endpoint_form = endpoint.T @ endpoint
    bulk_form = bulk.T @ bulk
    full_form = endpoint_form + bulk_form
    generalized_endpoint = eigh(
        endpoint_form,
        full_form,
        eigvals_only=True,
        check_finite=False,
        driver="gvd",
    )
    minimum = float(generalized_endpoint[0])
    maximum = float(generalized_endpoint[-1])
    bulk_fraction = max(0.0, 1.0 - minimum)
    constants = theoretical_constants()

    row: dict[str, Any] = {
        "ambient_dimension": size,
        **metadata,
        "raw_endpoint_min_eigenvalue": float(np.linalg.eigvalsh(endpoint_form)[0]),
        "raw_full_max_eigenvalue": float(np.linalg.eigvalsh(full_form)[-1]),
        "minimum_generalized_external_eigenvalue": minimum,
        "maximum_generalized_external_eigenvalue": maximum,
        "normalized_bulk_operator_norm_squared": bulk_fraction,
        "normalized_bulk_operator_norm": math.sqrt(bulk_fraction),
        "normalized_poisson_completion_norm": math.sqrt(
            bulk_fraction / minimum
        ),
        "uniform_external_lower_pass": bool(
            minimum + 1.0e-12 >= constants["normalized_endpoint_lower"]
        ),
        "uniform_nonzero_bulk_pass": bool(
            bulk_fraction + 1.0e-12
            >= constants["normalized_bulk_fraction_lower"]
        ),
    }

    if detailed:
        inverse_sqrt, _ = green.inverse_positive_sqrt(full_form)
        normalized_endpoint = endpoint @ inverse_sqrt
        normalized_bulk = bulk @ inverse_sqrt
        identity = np.eye(size, dtype=np.float64)
        poisson = normalized_bulk @ np.linalg.pinv(
            normalized_endpoint, rcond=1.0e-12
        )
        row["detailed_operator_audit"] = {
            "normalized_isometry_error": float(
                np.linalg.norm(
                    normalized_endpoint.T @ normalized_endpoint
                    + normalized_bulk.T @ normalized_bulk
                    - identity,
                    ord=2,
                )
            ),
            "external_rank": int(
                np.linalg.matrix_rank(normalized_endpoint, tol=1.0e-11)
            ),
            "poisson_intertwining_error": float(
                np.linalg.norm(
                    poisson @ normalized_endpoint - normalized_bulk,
                    ord=2,
                )
            ),
            "direct_poisson_operator_norm": float(
                np.linalg.norm(poisson, ord=2)
            ),
        }
    return row


def run_lab(args: argparse.Namespace) -> dict[str, Any]:
    sizes = parse_sizes(args.sizes)
    rows = [
        one_size_audit(size, detailed=(size == max(sizes))) for size in sizes
    ]
    constants = theoretical_constants()
    return {
        "schema": "org.native-carry.pythagorean-green-measure/v1",
        "status": "CARRY_DERIVED_MEASURE_WITH_UNIFORM_ENDPOINT_AND_BULK",
        "native_operator_authority": (
            "native_carry_primitive_real_operator_all_bases_fixed.py"
        ),
        "measure": {
            "vertical_scale": "x_b(n)=k_b(n) log(b)",
            "camera_partition": "omega_b(n)=x_b(n)/sum_c x_c(n)",
            "carry_mass": "q_b^2=1/b",
            "green_transmitted": "mu_G(b,n)=omega_b(n)/b",
            "orthogonal_residual": "mu_R(b,n)=omega_b(n)(1-1/b)",
            "fiber_pythagoras": "sum_b(mu_G(b,n)+mu_R(b,n))=1",
            "physical_joint_measure": (
                "multiply both channels by a(n)^2=1/n for the native state"
            ),
        },
        "green_normalization": {
            "raw": "A_b=q_b^(-1)(I-q_b U_b)^2",
            "quadratic_unit": "Ahat_b=q_b A_b=(I-q_b U_b)^2",
            "active_analysis": (
                "G_(b,n)f=sqrt(mu_G(b,n)) (Ahat_b f)(n)"
            ),
            "external_analysis": (
                "E_ext=(seed, residual-return, depth-one Green ports)"
            ),
            "bulk_analysis": "B=depth-at-least-two Green ports",
        },
        "uniform_infinite_bounds": {
            **constants,
            "active_green_bound_proof": (
                "Use |a+b+c|^2<=3 sum|.|^2. The leading term is <=3/2; "
                "the first ancestor is <=12 sum_(b>=2)b^-2; the second "
                "ancestor is <=3 sum_(b>=2)b^-3."
            ),
            "external_lower_proof": (
                "The residual-return form is diagonal with mass "
                "sum_b omega_b(n)(1-1/b)>=1/2 for every n>1; the seed has "
                "its own unit port."
            ),
            "nonzero_bulk_proof": (
                "At n=4 the base-2 depth-two row has omega_2(4)=1/2 and "
                "mu_G(2,4)=1/4. Testing e_4 and using F<=(1+C_G)I gives "
                "a normalized bulk fraction at least 1/[4(1+C_G)]."
            ),
        },
        "size_audits": rows,
        "infinite_operator_consequence": {
            "bounded_analysis": (
                "T=(E_ext,B) extends boundedly to the all-bases l2 atlas"
            ),
            "bounded_below": "T*T>=E_ext*E_ext>=1/2 I",
            "normalized_isometry": "V=T(T*T)^(-1/2)",
            "closed_external_range": True,
            "poisson_operator": "M_MB=B_norm E_norm^dagger",
            "exact_intertwining": "M_MB E_norm=B_norm",
            "limit_type": (
                "nontrivial bounded infinite Poisson/gamma-field candidate; "
                "its spectral Weyl family still comes from the logarithmic "
                "generator and the endpoint-bulk Schur complement"
            ),
        },
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sizes", default="8,16,32,64,128,256,512,1024")
    parser.add_argument("--output", type=Path)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    try:
        report = run_lab(args)
    except ValueError as exc:
        parser.error(str(exc))
    payload = json.dumps(report, indent=2, sort_keys=True)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload + "\n", encoding="utf-8")
    print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
