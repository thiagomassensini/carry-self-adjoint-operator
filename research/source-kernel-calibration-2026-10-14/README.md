# Source kernel calibration — 2026-10-14

Base: carry-self-adjoint-operator `8f791152e9c0f354b3aa399f0e0c3de5c24db1ec`.

The production modules and explicit audit are in `CarrySelfAdjointOperator/NativePrimeCarryKernelCalibration.lean`, `NativeSourceNormalizedKernelConnection.lean`, `NativeSourceCovariantBoundaryState.lean`, and `NativeSourceKernelCalibrationAudit.lean`.

The study is `docs/source-kernel-calibration-connection.md`. `verification.json` records the successful builds and the exact scope of the results. The native all-order source pairing and positivity remain open.

`BoundaryKernelProbe.lean` was compiled separately against the current standalone geometry-of-numbers checkout at `e1084b43533255b399b82dc307b536d7dfdca07f`. Run `lake env lean /absolute/path/to/BoundaryKernelProbe.lean` from that checkout. It uses newer geometry APIs than the consumed pin and is deliberately not imported into the root. No upstream source or dependency pin was modified.
