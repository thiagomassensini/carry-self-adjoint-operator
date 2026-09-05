#!/usr/bin/env python3
"""Re-use Thiago's finite Jacobi/height lab with native theta moments.

The source lab is preserved unchanged. Its Cauchy/zeta path is not invoked.
This is a numerical audit of finite models, not an all-order positivity proof.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

import mpmath as mp


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(reference, dps):
    source = Path(__file__).parent / "source/native_carry_height_moment_jacobi_operator_lab.py"
    spec = importlib.util.spec_from_file_location("height_lab", source)
    lab = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(lab)
    mp.mp.dps = dps

    def forbidden(*args, **kwargs):
        raise RuntimeError("This audit uses only the supplied native moment reference")

    mp.zeta = forbidden
    mp.zetazero = forbidden
    raw = json.loads(reference.read_text())
    h = [mp.mpf(x) for x in raw["h"]]
    f = [mp.mpf(x) for x in raw["f"]]
    reconstructed = lab.log_derivative_moments(f, len(h))
    recurrence_defect = max(abs(a-b)/abs(b) for a, b in zip(reconstructed, h))
    rows = []
    for order in (4, 8, 12, 16):
        model = lab.jacobi_from_moments(h, order)
        J = model["jacobi"]
        heights, T = lab.height_spectrum(J)
        x0 = mp.zeros(order, 1)
        x0[0] = mp.sqrt(h[0])
        moment_defects = []
        state = x0.copy()
        for k in range(2*order + 1):
            calculated = (x0.T * state)[0]
            moment_defects.append(abs(calculated-h[k])/abs(h[k]))
            state = J*state

        # Assemble the real two-channel kernel in the actual height variable.
        eigs, U = mp.eigsy(J)
        sqrt_J = U * mp.diag([mp.sqrt(x) for x in eigs]) * U.T
        identity = mp.eye(order)

        def state_and_readout(t):
            even = (identity-t*t*J)**-1*x0
            odd = t*sqrt_J*even
            return even, odd, t*(x0.T*even)[0]

        x, z = mp.mpf("0.125"), mp.mpf("0.5")
        ex, ox, ax = state_and_readout(x)
        ez, oz, az = state_and_readout(z)
        kernel = (ex.T*ez + ox.T*oz)[0]
        divided_difference = (az-ax)/(z-x)
        a_prime_x = mp.diff(lambda t: state_and_readout(t)[2], x)
        diagonal_kernel = (ex.T*ex + ox.T*ox)[0]
        row = {
            "order": order,
            "G_positive": min(model["gram_eigenvalues"]) > 0,
            "K_positive": min(model["shifted_eigenvalues"]) > 0,
            "J_minimum_eigenvalue": eigs[0],
            "J_maximum_eigenvalue": eigs[-1],
            "first_three_height_eigenvalues": heights[:3],
            "T_inverse_square_eq_J_residual": mp.norm(T**-2-J),
            "native_moment_max_relative_defect_k_below_2N": max(moment_defects[:-1]),
            "next_moment_relative_defect_k_eq_2N": moment_defects[-1],
            "height_kernel_two_point_residual": abs(kernel-divided_difference),
            "height_kernel_diagonal_residual": abs(diagonal_kernel-a_prime_x),
            "boundary_closure": model["green_boundary_closure"],
            "defect_jets": model["defect_jet_realization"],
        }
        rows.append(row)
        print(f"order {order}: complete", flush=True)

    rotation_defects = []
    for n in (2, 3, 4, 7, 16, 81):
        for t in (mp.mpf(0), mp.mpf("0.125"), mp.mpf(2)):
            L = mp.log(n)
            psi = mp.power(n, -mp.mpf("0.5"))*mp.exp(-mp.j*t*L)
            real_pack = mp.power(n, -mp.mpf("0.5"))*mp.mpc(mp.cos(t*L), -mp.sin(t*L))
            dsigma = mp.diff(lambda sigma: mp.power(n, -sigma)*mp.exp(-mp.j*t*L), mp.mpf("0.5"))
            dt = mp.diff(lambda tau: mp.power(n, -mp.mpf("0.5"))*mp.exp(-mp.j*tau*L), t)
            rotation_defects.extend((abs(psi-real_pack), abs(dt-mp.j*dsigma), abs(abs(psi)**2-mp.mpf(1)/n)))

    return lab.mp_serializable({
        "status": "FINITE_COORDINATE_AND_BOUNDARY_AUDIT",
        "working_dps": dps,
        "source_lab_sha256": sha256(source),
        "reference_sha256": sha256(reference),
        "source_lab_original_path": "/home/thlinux/Downloads/hp/native_carry_height_moment_jacobi_operator_lab.py",
        "reference_method": raw["method"],
        "zeta_or_zeros_called": False,
        "native_recurrence_max_relative_defect": recurrence_defect,
        "real_complex_rotation_max_absolute_defect": max(rotation_defects),
        "dictionary": {
            "n": "material index; the phase generator is log(n)",
            "t": "height parameter, s=1/2+i*t",
            "v": "t^2, Taylor variable of -Phi'/Phi",
            "lambda": "positive Jacobi variable; inverse squared height under the spectral bridge",
            "J_N": "L_N^(-1) K_N L_N^(-T), constructed from h",
            "T_N": "J_N^(-1/2), finite real symmetric height operator",
            "N": "polynomial order, not number of geometric centers or raw material horizon",
        },
        "limits": [
            "No identification of J with the material generator log(n) is assumed or proved.",
            "The energy factor and boundary feedback in this lab are constructed from native h.",
            "Positivity and moment matching here concern only the tested finite orders.",
            "The inverse square root of a Jacobi compression is not asserted to be a compression of the infinite height operator.",
        ],
        "rows": rows,
    }, 75)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--dps", type=int, default=220)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = run(args.reference, args.dps)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
