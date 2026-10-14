# Original theta masses for the first odd source Schur remainder

These files accompany `docs/native-schur-theta-integral.md` and the three
`NativeSource*Theta*` production modules. The exact integral representation,
the negative odd leading coefficient at every order, the strict negative
mass at every odd order, and the first odd mass dominance are Lean theorems.
General all-order positive mass dominance remains open.

- `masses-512.json`: fresh positive-mass Arb quadrature, 512 bits, 12 modes.
- `masses-768.json`: repeat at 768 bits, 16 modes, with interval overlap checks.
- `first-odd-density.png`: floating-point illustration only.

Both certificates reuse the same published 1024-bit original theta
coefficient boxes in `research/native-kernel-series-2026-10-14/certificate-1024.json`.
The coefficient inputs are hash-checked against the existing source modules
and theta engine. The new computation is a source mass quadrature, not a
new moment integration. Negative mass uses the exact identity `M- = M+ - R`;
it is not obtained by discarding the infinite tail.

The script bounds omitted theta modes and the uncertain integration endpoint.
See the accompanying document and script comments for the estimates.
These are external Arb certificates, not kernel-checked numeric proofs.

Reproduce from the repository root on `llm`:

```bash
/home/thlinux/miniforge3/bin/python3 scripts/certify_first_odd_theta_masses.py \
  --bits 512 --modes 12 --output /tmp/theta-masses-512.json
/home/thlinux/miniforge3/bin/python3 scripts/certify_first_odd_theta_masses.py \
  --bits 768 --modes 16 --replication /tmp/theta-masses-512.json \
  --output /tmp/theta-masses-768.json
/home/thlinux/miniforge3/bin/python3 scripts/plot_first_odd_theta_density.py \
  --certificate /tmp/theta-masses-768.json --output /tmp/first-odd-density.png
lake build --wfail CarrySelfAdjointOperator.NativeSourceSchurThetaAudit \
  CarrySelfAdjointOperator CarrySelfAdjointOperator.Audit
```
