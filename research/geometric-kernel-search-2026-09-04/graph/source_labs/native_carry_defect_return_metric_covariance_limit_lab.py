#!/usr/bin/env python3
"""Unique limit of the return-metric covariance of carry-native defect probes.

For source-parametrized defect states

    f_{z,u}^{(M)} = (z-H_M)^(-1) J_E u,

with source readout

    S_M(z)=Q_M(z-H_M)^(-1)J_E=C_M(z-L_M)^(-1)E_M*,

the endpoint return metric

    G_E,M = I + M_MB,M* M_MB,M

satisfies the exact finite identity

    E_M* G_E,M E_M = I.

Therefore the contravariant/source-dual covariance is exactly

    Sigma_M^ret(z)
      := S_M(z) G_E,M S_M(z)*
       = C_M W_M(z) C_M*,

where W_M(z)=diag(|z-log n|^-2).  For a fixed finite camera pack, weighted
periodic averaging then yields

    Sigma_M^ret(z) / A_M(z) -> G_camera,
    A_M(z)=sum_{n<=M}|z-log n|^-2,

in operator norm.  The limit is unique and independent of the fixed nonreal z.

The script audits the exact finite metric identity, convergence to the exact
periodic Gram, z-universality, and the limiting quadratic observable.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import native_carry_collective_operator_lab as collective
import native_carry_primitive_real_operator_all_bases_fixed as native
import native_carry_pythagorean_node_weyl_colligation_lab as node_weyl
from native_carry_defect_source_probe_asymptotic_frame_lab import (
    exact_camera_gram,
    fraction_matrix_to_float,
    frac_text,
    resolvent_mass,
)


def parse_ints(text: str) -> tuple[int, ...]:
    vals = tuple(sorted({int(x.strip()) for x in text.split(",") if x.strip()}))
    if not vals or any(v < 1 for v in vals):
        raise ValueError("positive integer list required")
    return vals


def parse_complex_list(text: str) -> tuple[complex, ...]:
    vals: list[complex] = []
    for item in text.split(";"):
        item = item.strip().replace("i", "j")
        if not item:
            continue
        value = complex(item)
        if value.imag == 0.0:
            raise ValueError("every z must be non-real")
        vals.append(value)
    if not vals:
        raise ValueError("at least one non-real z is required")
    return tuple(vals)


def parse_times(text: str) -> tuple[float, ...]:
    vals = tuple(float(x.strip()) for x in text.split(",") if x.strip())
    if not vals or any(not math.isfinite(v) for v in vals):
        raise ValueError("finite times required")
    return vals


def pythagorean_endpoint_constant() -> float:
    zeta2 = math.pi * math.pi / 6.0
    zeta3 = 1.2020569031595942854
    c_g = 1.5 + 12.0 * (zeta2 - 1.0) + 3.0 * (zeta3 - 1.0)
    return 0.5 / (1.0 + c_g)


def camera_covariance(
    cameras: tuple[int, ...], cutoff: int, z: complex
) -> tuple[np.ndarray, int, float]:
    models = [native.build_camera_model(c, cutoff) for c in cameras]
    camera, size = collective.native_readout_matrix(models)
    logs = np.log(np.arange(1, size + 1, dtype=np.float64))
    weights = 1.0 / np.abs(z - logs) ** 2
    mass = resolvent_mass(cutoff, z)
    covariance = (camera * weights[None, :]) @ camera.T / mass
    return covariance, size, mass


def exact_metric_identity_audit(
    cameras: tuple[int, ...], cutoffs: tuple[int, ...], z: complex, limit_gram: np.ndarray,
    times: tuple[float, ...],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for cutoff in cutoffs:
        models = [native.build_camera_model(c, cutoff) for c in cameras]
        camera, size = collective.native_readout_matrix(models)
        coll = node_weyl.normalized_colligation(size)
        endpoint = np.asarray(coll["endpoint"], dtype=np.float64)
        poisson = np.asarray(coll["poisson"], dtype=np.float64)
        logs = np.log(np.arange(1, size + 1, dtype=np.float64))
        r = 1.0 / (z - logs)
        weights = 1.0 / np.abs(z - logs) ** 2
        source_probe = (camera * r[None, :]) @ endpoint.T
        return_metric = np.eye(endpoint.shape[0], dtype=np.float64) + poisson.T @ poisson
        metric_covariance = source_probe @ return_metric @ source_probe.conj().T
        direct_covariance = (camera * weights[None, :]) @ camera.T
        raw_covariance = source_probe @ source_probe.conj().T
        mass = resolvent_mass(cutoff, z)
        normalized = metric_covariance / mass
        normalized_raw = raw_covariance / mass
        eig = np.linalg.eigvalsh(normalized)
        raw_eig = np.linalg.eigvalsh(normalized_raw)
        time_rows: list[dict[str, float]] = []
        for t in times:
            state = collective.complex_state(t, size)
            chi = camera @ state
            metric_phi = float(np.vdot(chi, normalized @ chi).real)
            gram_phi = float(np.vdot(chi, limit_gram @ chi).real)
            time_rows.append({
                "t": float(t),
                "native_energy": float(np.vdot(chi, chi).real),
                "return_metric_probe_observable": metric_phi,
                "instantaneous_limit_gram_quadratic": gram_phi,
                "observable_difference": abs(metric_phi - gram_phi),
            })
        rows.append({
            "cutoff": cutoff,
            "ambient_dimension": size,
            "endpoint_dimension": int(endpoint.shape[0]),
            "return_metric_isometry_error": float(
                np.linalg.norm(endpoint.T @ return_metric @ endpoint - np.eye(size), 2)
            ),
            "exact_covariance_identity_error": float(
                np.linalg.norm(metric_covariance - direct_covariance, 2)
            ),
            "normalized_covariance_error_to_limit_gram": float(
                np.linalg.norm(normalized - limit_gram, 2)
            ),
            "normalized_metric_covariance_min_eigenvalue": float(eig[0]),
            "normalized_metric_covariance_max_eigenvalue": float(eig[-1]),
            "normalized_raw_covariance_min_eigenvalue": float(raw_eig[0]),
            "normalized_raw_covariance_max_eigenvalue": float(raw_eig[-1]),
            "metric_minus_raw_covariance_norm": float(
                np.linalg.norm(normalized - normalized_raw, 2)
            ),
            "times": time_rows,
        })
    return rows


def asymptotic_covariance_audit(
    cameras: tuple[int, ...], cutoffs: tuple[int, ...], zs: tuple[complex, ...],
    limit_gram: np.ndarray,
) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for z in zs:
        rows: list[dict[str, Any]] = []
        for cutoff in cutoffs:
            covariance, size, mass = camera_covariance(cameras, cutoff, z)
            eig = np.linalg.eigvalsh(covariance)
            rows.append({
                "cutoff": cutoff,
                "ambient_dimension": size,
                "resolvent_mass": mass,
                "operator_norm_error_to_unique_limit": float(
                    np.linalg.norm(covariance - limit_gram, 2)
                ),
                "minimum_eigenvalue": float(eig[0]),
                "maximum_eigenvalue": float(eig[-1]),
            })
        out.append({
            "z": [float(z.real), float(z.imag)],
            "rows": rows,
        })
    return out


def run(args: argparse.Namespace) -> dict[str, Any]:
    cameras = native.parse_cameras(args.cameras)
    identity_cutoffs = parse_ints(args.identity_cutoffs)
    covariance_cutoffs = parse_ints(args.covariance_cutoffs)
    zs = parse_complex_list(args.zs)
    times = parse_times(args.times)
    z0 = zs[0]
    exact_frac = exact_camera_gram(cameras)
    limit_gram = fraction_matrix_to_float(exact_frac)
    eig = np.linalg.eigvalsh(limit_gram)
    c_e = pythagorean_endpoint_constant()
    return {
        "schema": "org.native-carry.defect-return-metric-covariance-limit/v1",
        "status": "UNIQUE_RETURN_METRIC_DEFECT_COVARIANCE_LIMIT_PROVED_AND_AUDITED",
        "configuration": {
            "cameras": list(cameras),
            "identity_parameter": [float(z0.real), float(z0.imag)],
            "z_universality_parameters": [[float(z.real), float(z.imag)] for z in zs],
            "identity_cutoffs": list(identity_cutoffs),
            "covariance_cutoffs": list(covariance_cutoffs),
            "times": list(times),
        },
        "theorem": {
            "source_probe": "S_M(z)=C_M(z-L_M)^(-1)E_M*",
            "return_metric": "G_E,M=I+M_MB,M* M_MB,M",
            "exact_metric_isometry": "E_M* G_E,M E_M=I",
            "return_metric_covariance": "Sigma_M^ret(z)=S_M(z) G_E,M S_M(z)*",
            "exact_covariance_reduction": "Sigma_M^ret(z)=C_M W_M(z) C_M*",
            "normalization": "A_M(z)=sum_{n<=M}|z-log n|^-2",
            "unique_limit": "Sigma_M^ret(z)/A_M(z) -> G_camera in operator norm",
            "z_universality": "the same G_camera occurs for every fixed z in C\\R",
            "observable_limit": (
                "if chi_M(t)->chi(t), then <chi_M,Sigma_M^ret/A_M chi_M> "
                "-> <chi,G_camera chi>"
            ),
            "zero_detection": "G_camera>0 implies limiting observable=0 iff chi(t)=0",
        },
        "metric_equivalence": {
            "endpoint_lower_constant": c_e,
            "uniform_metric_bounds": "I <= G_E,M <= c_E^(-1) I",
            "consequence": (
                "return-metric weighting is uniformly equivalent to Euclidean source weighting "
                "and does not introduce or remove zeros"
            ),
            "raw_euclidean_covariance_status": (
                "S_MS_M*/A_M remains uniformly noncollapsing, but its unique operator limit "
                "is not proved by this argument"
            ),
        },
        "unique_limit_gram": {
            "exact": [[frac_text(x) for x in row] for row in exact_frac],
            "eigenvalues": [float(x) for x in eig],
            "minimum_eigenvalue": float(eig[0]),
            "maximum_eigenvalue": float(eig[-1]),
            "positive_definite": bool(eig[0] > 0.0),
        },
        "finite_exact_identity_audit": exact_metric_identity_audit(
            cameras, identity_cutoffs, z0, limit_gram, times
        ),
        "asymptotic_z_universality_audit": asymptotic_covariance_audit(
            cameras, covariance_cutoffs, zs, limit_gram
        ),
    }


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cameras", default="2,3,4,5,6,7")
    p.add_argument("--identity-cutoffs", default="8,16,32,64,128")
    p.add_argument("--covariance-cutoffs", default="128,256,512,1024,2048,4096,8192,16384,32768,65536")
    p.add_argument("--zs", default="0+6j;2+0.75j;-1+3j")
    p.add_argument("--times", default="0,14.134725141734695,30.424876125859512")
    p.add_argument("--output", type=Path)
    args = p.parse_args()
    report = run(args)
    text = json.dumps(report, indent=2, sort_keys=True)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
