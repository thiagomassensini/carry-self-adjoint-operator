# Evidence for the HP notes audit — 2026-09-04

This archive accompanies [the map](../../docs/mapa-notas-hp-jets-retorno-atualizado.md).

- `original-lean/`: nine byte-preserved sources from `/home/thlinux/Downloads/hp`.
- `original-notes/`: the two notes explicitly requested by the user, byte-preserved.
- `hp-inventory.json`: filenames, hashes and Markdown headings for the 64 direct files. Swap files, historical compiled objects and archives were inventoried but not copied here.
- `local-lean-checks.json` and `logs/`: original-source compiler results against the project pins. All nine exit codes are zero. `FiniteEnrichedCameraState` has two unused-section-variable warnings.
- `snapshots.json`: repository main SHAs read during the audit. These are source snapshots, not newly adopted dependency pins.
- `provenance.json`: working base, consumed pins, original-file consistency and recovered module declarations.
- `check_note_formulas.py` and `note-formula-checks.json`: integer basis-action check for the printed commutator rank; separate elementary integration correction for the camera generator. These are not Lean theorems.
- `lean-audit.log`: full project audit after integrating the recovered bridge.

Only `CarrySelfAdjointOperator/C3ProjectiveCompletedJetBridge.lean` was integrated into the project library in this audit. Its eight theorem bodies are preserved. The historical trailing `#print axioms` commands were moved to `KernelConstructionAudit.lean`, which also covers the remaining recovered public theorems. Archiving another verified source does not mean that it is imported by the project root or present in an upstream package.

## Reproduce

From the repository root, using the toolchain in `lean-toolchain`:

```bash
lake build NativeCarrySpectralWeyl.Boundary.GreenCameraCoupling
lake env python3 research/hp-notes-audit-2026-09-04/recheck_original_lean.py
python3 research/hp-notes-audit-2026-09-04/check_note_formulas.py
bash scripts/audit.sh
```

The Lean recheck creates a fresh temporary output directory and reports its path. It never reads historical `.olean` files from Downloads. The formula script deterministically reproduces its JSON next to itself.

During the first compiler invocation, a missing `-R` source-root option prevented elaboration. After that invocation was corrected, `CanonicalNaimarkStateReadout` required building `GreenCameraCoupling`. Neither event was a proof failure. The archived final compiler results were produced after these environment issues were resolved.

The full project audit comprises 14 Lake build calls with `--wfail`. The archive stores the successful log. No GitHub CI result is claimed here.
