#!/usr/bin/env python3
"""Finite, phase-sensitive replay from archived Jacobi and independent Phi jets.

No spectrum is an input. Phi is read from the independent archived completion
product calculation, not reconstructed by integrating the Jacobi readout.
The polynomial jet remains a finite proxy, with no native EM remainder bound.
"""
import argparse
import gzip
import hashlib
import importlib.util
import json
import platform
import subprocess
import sys
from pathlib import Path


def digest(path):
    out = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b''):
            out.update(block)
    return out.hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--momentos', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    root = args.momentos.resolve()
    source = root / 'native-jet-vm-20260930/native_jet_exploration'
    compare = source / 'campaign_20261012_resolvents/compare_resolvents.py'
    spec = importlib.util.spec_from_file_location('archived_resolvents', compare)
    engine = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(engine)
    mp = engine.mp
    engine.engine.install_firewall()
    mp.mp.dps = 180
    checkpoint = source / 'results/c11-n1536-spectrum-p20000/run.json'
    (dhat, ehat, mass), scale, provenance = engine.load_matrix(checkpoint)
    coefficients = root / 'native_jet_exploration/auditoria_corrected_vs_canonical/stage_B/coefficients.json'
    archive = json.loads(coefficients.read_text())
    c = [mp.mpf(a) for a in archive['normalized_completed_c']]
    assert len(c) == 257 and c[0] == 1
    assert mass > 0 and scale > 0
    d, e = [scale * a for a in dhat], [scale * a for a in ehat]
    v0 = mp.sqrt(mass)
    threshold = mp.mpf('1e-130')

    def inner(a, b):
        return mp.fsum(mp.conj(x) * y for x, y in zip(a, b))

    def norm(a):
        return mp.sqrt(mp.fsum(abs(x) ** 2 for x in a))

    def text(x):
        return mp.nstr(x, 170)

    def ct(x):
        return [text(mp.re(x)), text(mp.im(x))]

    def vector(a):
        return [ct(x) for x in a]

    def matrix_apply(x):
        n = len(x)
        return [d[i] * x[i] + (e[i - 1] * x[i - 1] if i else 0) +
                (e[i] * x[i + 1] if i + 1 < n else 0) for i in range(n)]

    def energy_factor(n):
        # J = L L^T with positive diagonal. B = L^T, not a fitted Gram.
        diag, off = [], []
        for i in range(n):
            pivot = d[i] - (off[i - 1] ** 2 if i else 0)
            assert pivot > 0
            diag.append(mp.sqrt(pivot))
            if i + 1 < n:
                off.append(e[i] / diag[i])
        return lambda x: [diag[i] * x[i] +
                          (off[i] * x[i + 1] if i + 1 < n else 0)
                          for i in range(n)]

    def solve(n, z):
        # Direct Schur solve for (I - z^2 J_N) X = sqrt(h0) e1.
        diag = [1 - z ** 2 * d[i] for i in range(n)]
        off = [-z ** 2 * e[i] for i in range(n - 1)]
        right = [v0] + [mp.mpc(0) for _ in range(n - 1)]
        for i in range(1, n):
            t = off[i - 1] / diag[i - 1]
            diag[i] -= t * off[i - 1]
            right[i] -= t * right[i - 1]
        x = [mp.mpc(0) for _ in range(n)]
        x[-1] = right[-1] / diag[-1]
        for i in range(n - 2, -1, -1):
            x[i] = (right[i] - off[i] * x[i + 1]) / diag[i]
        return x

    def phi(z, order):
        u = z ** 2
        p, dp = c[order], mp.mpc(0)
        for i in range(order - 1, -1, -1):
            dp, p = p + u * dp, c[i] + u * p
        return p, 2 * z * dp

    def relative_residual(a, b):
        return abs(a - b) / max(1, abs(a), abs(b))

    cases, summaries = [], []
    pairs = [('0.75', '0.2', '1.25', '0.3'),
             ('10', '0.2', '12', '0.3'),
             ('14', '0.02', '14.2', '0.03')]
    for n, m in [(8, 16), (16, 32), (32, 64)]:
        bapply = energy_factor(m)
        source_vector = [v0] + [mp.mpc(0) for _ in range(m - 1)]
        for zr, zi, wr, wi in pairs:
            z, w = mp.mpc(zr, zi), mp.mpc(wr, wi)
            x = solve(n, z) + [mp.mpc(0) for _ in range(m - n)]
            y = solve(m, w)
            jx, jy, bx, by = matrix_apply(x), matrix_apply(y), bapply(x), bapply(y)
            rz = [x[i] - z ** 2 * jx[i] - source_vector[i] for i in range(m)]
            rw = [y[i] - w ** 2 * jy[i] - source_vector[i] for i in range(m)]
            # The mixed-order vector residual must equal the unmodified boundary link.
            expected_rz = [mp.mpc(0) for _ in range(m)]
            expected_rz[n] = -z ** 2 * e[n - 1] * x[n - 1]
            qz, qw = inner(source_vector, x), inner(source_vector, y)
            denominator = w - mp.conj(z)
            gram = inner(x, y) + mp.conj(z) * w * inner(bx, by)
            vector_numerator = mp.conj(z) * inner(x, rw) - w * inner(rz, y)
            readout = (w * qw - mp.conj(z * qz)) / denominator
            fz, dz = phi(z, 256)
            fw, dw = phi(w, 256)
            ez, ew = dz + 2 * z * qz * fz, dw + 2 * w * qw * fw
            native_proxy = (-dw / fw + mp.conj(dz / fz)) / (2 * denominator)
            char_defect = (-ew / fw + mp.conj(ez / fz)) / (2 * denominator)
            vector_defect = vector_numerator / denominator
            vector_bound = (abs(z) * norm(x) * norm(rw) +
                            abs(w) * norm(rz) * norm(y)) / abs(denominator)
            char_bound = (abs(ew) / abs(fw) + abs(ez) / abs(fz)) / (2 * abs(denominator))
            error = max(relative_residual(readout - gram, vector_defect),
                        relative_residual(native_proxy - readout, char_defect),
                        relative_residual(native_proxy - gram, vector_defect + char_defect),
                        relative_residual(inner(x, jy), inner(bx, by)),
                        norm([a - b for a, b in zip(rz, expected_rz)]) / max(1, norm(rz)))
            assert error < threshold, error
            assert abs(native_proxy - gram) <= vector_bound + char_bound + threshold
            row = dict(N=n, M=m, z=ct(z), w=ct(w),
                       identity_relative_residual=text(error),
                       graph_residual_z_norm=text(norm(rz)), graph_residual_w_norm=text(norm(rw)),
                       characteristic_residual_z_norm=text(abs(ez)), characteristic_residual_w_norm=text(abs(ew)),
                       vector_defect_abs=text(abs(vector_defect)), characteristic_defect_abs=text(abs(char_defect)),
                       total_kernel_defect_abs=text(abs(native_proxy - gram)),
                       vector_bound=text(vector_bound), characteristic_bound=text(char_bound),
                       phi_128_256_gap_z=text(abs(phi(z, 128)[0] - fz)),
                       phi_128_256_gap_w=text(abs(phi(w, 128)[0] - fw)))
            summaries.append(row)
            cases.append(dict(**row, source=vector(source_vector), Xz=vector(x), Xw=vector(y),
                              JXz=vector(jx), JXw=vector(jy), BXz=vector(bx), BXw=vector(by),
                              graph_residual_z=vector(rz), graph_residual_w=vector(rw),
                              qz=ct(qz), qw=ct(qw), Phi_z=ct(fz), Phi_w=ct(fw),
                              Phi_derivative_z=ct(dz), Phi_derivative_w=ct(dw),
                              readout_kernel=ct(readout), parity_gram=ct(gram),
                              vector_defect=ct(vector_defect), characteristic_defect=ct(char_defect),
                              characteristic_proxy_kernel=ct(native_proxy)))
    args.out.mkdir(parents=True, exist_ok=True)
    states_file = args.out / 'states.json.gz'
    with gzip.open(states_file, 'wt') as out:
        json.dump(cases, out, ensure_ascii=False, indent=2)
        out.write('\n')
    result = dict(status='PASS', dps=180, threshold=str(threshold), cases=len(cases),
                  python=platform.python_version(),
                  momentos_head=subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip(),
                  checkpoint=provenance, independent_Phi_coefficients=dict(path=str(coefficients), sha256=digest(coefficients), degree_in_u=256),
                  source_hash=digest(Path(__file__)), states_sha256=digest(states_file),
                  inputs=['Jacobi diagonal', 'Jacobi offdiagonal', 'fixed physical scale', 'moments[0]',
                          'independent archived normalized_completed_c'],
                  scope='Finite numerical identities on saved decimal matrices and independent finite Phi polynomial. No native EM bound, infinite tail theorem, or physical Green Gram identification.',
                  zero_policy='Displayed zero means below working arithmetic resolution, not exact mathematical equality.',
                  summaries=summaries)
    (args.out / 'summary.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['status', 'dps', 'cases', 'states_sha256']}))
    for row in summaries:
        print(json.dumps({k: row[k] for k in ['N', 'M', 'z', 'w', 'graph_residual_z_norm', 'characteristic_residual_z_norm', 'total_kernel_defect_abs']}))


if __name__ == '__main__':
    main()
