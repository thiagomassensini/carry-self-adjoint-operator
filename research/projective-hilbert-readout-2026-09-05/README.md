# Projective Hilbert kernel and completed native readout

This audit integrates 32 recovered theorems and checks 13 new theorems, including two conditional bridges to the native certificate. The raw Hilbert Gram and the scalar characteristic readout remain distinct constructions. The exact analytic tail is an explicit input term of the readout formula.

Reproduce from the repository root using the pinned Lean toolchain:

```bash
lake build --wfail CarrySelfAdjointOperator.C3ProjectiveHilbertReadoutKernel
bash scripts/audit.sh
```

Both commands passed; the full script completed all 14 Lake builds. `verification.json` records the dependency pins, theorem locations, transitive axioms and source hashes. The compressed logs preserve the complete command output. Original recovered sources remain in `../hp-notes-audit-2026-09-04/original-lean/`.

The native Gram identification is still open. Neither positivity of the raw kernel nor equality of the completed scalar readout supplies the symmetric observable, source and cyclic mass identity required by the conditional certificate theorem.

See [the mathematical map](../../docs/c3-projective-hilbert-readout-kernel.md).
