# Camera return defect audit

The source moment formulas yield `I - variance = A* A`. Seven Lean theorems check the finite-family identity, its six-camera positivity specialization and the exact Gram image and squared length of the mixed residual ray. The original camera Gram and moments come from the pinned NativeCarrySpectralWeyl dependency.

Reproduce from the repository root:

```bash
lake build --wfail CarrySelfAdjointOperator.CameraReturnVarianceDefect
bash scripts/audit.sh
python3 research/camera-return-defect-2026-09-05/exact_camera_return_audit.py
```

The first two commands passed, including all 14 Lake stages in the full audit. The Python script uses SymPy for separate exact algebraic checks. Its rank-one and density calculations are symbolic evidence, distinct from the seven kernel-checked theorems. No target native moments or known zero locations are inputs.

The infinite-atlas limit and the identification with the native height Gram remain open. See the [mathematical map](../../docs/camera-return-defect-source-map.md).
