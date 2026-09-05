# Native moments through the projective valve — 2026-09-05

The [map](../../docs/ponte-valvula-momentos-nativos.md) explains the exact scalar bridge and its geometric scope.

`verification.json` records the commits cited by the user, their ancestry, the PR status read through GitHub, and the eight new theorem locations and audit results. `lean-audit.log.gz` preserves the complete local audit output as compressed UTF-8 text.

Reproduce from the repository root with the pinned Lean toolchain:

```bash
lake build --wfail CarrySelfAdjointOperator.NativeMomentProjectiveValveBridge
bash scripts/audit.sh
```

The bridge applies existing theorems to the actual native characteristic coefficients. Its statements do not assume moment positivity and do not assert a geometric Gram realization. No dependency pins changed and no GitHub CI monitoring was performed.
