# Validação do estudo posicional e das fibras C2

Data: 2026-09-09. Base: `5b117ff4ca65247dbc5b26dc8636332cfb6f20ce`.

- Build focado: `lake build --wfail CarrySelfAdjointOperator.PositionalFiberShiftAudit`, sucesso (8714 jobs).
- Workflow completo: `bash scripts/audit.sh`, exit code 0.
- Audit estático: `static audit passed`.
- Final: `kernel audit passed`.
- Os 15 comandos `lake build --wfail` do workflow passaram.
- `git diff --check` passou.
- Todos os 22 teoremas novos estão registrados uma única vez e têm axiomas dentro do conjunto padrão.
- Dependency pins e toolchain preservados; não foi acrescentada hipótese espectral.

Log no servidor: `/tmp/positional-fiber-audit.Tfao6x/workflow.log`.

## Axiomas efetivamente impressos pelo workflow

| Teorema | Axiomas |
| --- | --- |
| `finiteDepthShift_sample_apply` | `propext,, Classical.choice,, Quot.sound` |
| `finiteDepthShift_sample_add_boundary` | `propext,, Classical.choice,, Quot.sound` |
| `finitePositionalObservable_shift` | `propext,, Classical.choice,, Quot.sound` |
| `finitePositionalObservable_difference_add_boundary` | `propext,, Classical.choice,, Quot.sound` |
| `positionalDepthCoordinates_eq_terminal` | `propext` |
| `positionalObservable_stable` | `propext,, Classical.choice,, Quot.sound` |
| `positionalObservable_difference_stable` | `propext,, Classical.choice,, Quot.sound` |
| `no_positionalObservable_eq_depth` | `propext,, Classical.choice,, Quot.sound` |
| `c2FiberPoint_plus_eq_nat` | `propext,, Classical.choice,, Quot.sound` |
| `c2FiberPoint_minus_eq_nat` | `propext,, Classical.choice,, Quot.sound` |
| `c2FiberPoint_succ` | `propext,, Classical.choice,, Quot.sound` |
| `c2FiberPoint_centered` | `propext,, Classical.choice,, Quot.sound` |
| `c2FiberPoint_centered_log` | `propext,, Classical.choice,, Quot.sound` |
| `c2FiberPoint_centered_log_increment` | `propext,, Classical.choice,, Quot.sound` |
| `c2FiberPoint_log_center_defect` | `propext,, Classical.choice,, Quot.sound` |
| `c2FiberPoint_log_increment_defect` | `propext,, Classical.choice,, Quot.sound` |
| `finiteC2FiberObservable_shift_add_boundary` | `propext,, Classical.choice,, Quot.sound` |
| `c2FiberPoint_right_log_defect_pos` | `propext,, Classical.choice,, Quot.sound` |
| `c2FiberPoint_right_log_increment_lt` | `propext,, Classical.choice,, Quot.sound` |
| `finiteC2FiberCenteredLog_eq_depthLog` | `propext,, Classical.choice,, Quot.sound` |
| `finiteC2FiberCenteredLog_commutator` | `propext,, Classical.choice,, Quot.sound` |
| `c2Fiber_centeredLog_amplitude_eq_green_and_seed` | `propext,, Classical.choice,, Quot.sound` |

## Identificação dos fontes verificados

- `CarrySelfAdjointOperator/FinitePositionalObservableShift.lean`: SHA-256 `b57184e8a418f0873ef181159e4eb80a2063fc73a1b18c18ec18e129416a67bf`.
- `CarrySelfAdjointOperator/C2FiberDepthLogTransport.lean`: SHA-256 `50f62cae94d5570d48e984a38b022c3a205ac5579c8dc7b354b844ef2ecb7439`.
- `CarrySelfAdjointOperator/PositionalFiberShiftAudit.lean`: SHA-256 `36e3d96a57de53a762472afaed83f00c2be1bdb253b610134c21813515936d60`.

Log SHA-256: `b99a58e70f7332a7f06b6b58e72947f94d0bf064dd6120033ac8f46a99382bb3`.
