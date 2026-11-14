# Checkpoint — C2 leg compensation through completed polarization

Date: 2026-11-14
Repository: `thiagomassensini/carry-self-adjoint-operator`
Branch: `codex/c2-legs-wronskian-2026-11-14`
Base: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532` (`origin/main`)

This work is isolated from the pre-existing dirty checkout at
`/home/thlinux/carry-self-adjoint-operator`. No root aggregator, dependency
manifest, or toolchain file was changed. No `AGENTS.md` applies in this
repository or worktree.

## D1 checkpoint — all-order leg identity

`CarrySelfAdjointOperator/C2LegJetCompensation.lean` proves the six-scalar
identity first and specializes it to the two independent C2 legs:

- `c2CenteredSixScalarBracket`
- `c2LegJetBracket_eq_central_add_compensation`
- controls `c2LegCompensation_zero_parameter`,
  `c2LegCentralPart_zero_order`, and
  `c2LegCompensation_zero_order_eq_bracket`
- `c2FiberAllOrderBracket_eq_legParts`
- `c2FiniteCamera_allOrderLogPowerReadout_eq_seed_add_legParts`

The finite readout keeps the original seed explicit. The compensation remains
the sum of the separate left- and right-leg increments; no infinite sum or
derivative exchange is used here.

## D2/D3 checkpoint — companion and crossed polarization

`CarrySelfAdjointOperator/C2LegCompletionPolarization.lean` keeps the finite
chart `V = 1 + Σ g_c`, its jet `J`, central part `d`, and leg correction `E`.
It proves the exponent derivative and the spectral-line derivative, then
identifies the chart with the repository's original finite C2 stencil and
finite characteristic. The original seed, centers, and cutoff are retained.

The abstract and finite results include:

- `c2FiniteChartJet_eq_central_add_legCorrection`
- `c2CompletedCompanion_eq_neg_deriv` (with local differentiability of `L`)
- `c2CompletedCompanion_sub_central_eq_legCorrection`
- `c2NormalizedResponse_sub_central_eq_legCorrection`
- `c2CentralNormalizedResponse_eq_logarithmic_split`
- `c2PolarizedWronskian_sub_central_eq_legCorrection`
- `c2PolarizedWronskian_normalized_legCorrection`
- finite source counterparts `c2FiniteChartHeightCompanion_sub_central_eq_legCorrection`,
  `c2FiniteChartHeightWronskian_sub_central_eq_legCorrection`, and
  `c2FiniteChartHeightWronskian_normalized_legCorrection`

The polarized correction contains both crossed terms,
`conj(V(z))*E(w) + conj(E(z))*V(w)`. Normalized statements require nonzero
source values; there is no division by a diagonal factor.

## D4 — finite physical adapter and exact open boundary

`CarrySelfAdjointOperator/C2LegCompletionFiniteAdapter.lean` proves that the
height-line chart is the original finite C2 characteristic and that the
dressing is the original completion divided by the C2 factor. It exports
`c2FiniteSourceGammaWronskian_split` and
`c2FiniteSourceGammaWronskian_split_with_legs`.

The latter states `WΓ − W = (WΓ − W₀) − (W − W₀)` and replaces the second
parenthesis with the proved two-leg formula. The first parenthesis remains an
explicit residual. The precise missing comparison for a future proof is, for
the same cutoff and nonreal heights:

```text
canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw =
  c2CentralPolarizedWronskian
    (fun x => c2FiniteChartHeightCharacteristic cutoff x)
    (fun x => c2FiniteChartHeightCentralCompanion cutoff x) z w
```

This comparison has not been proved, and no theorem equating `WΓ` and `W₀` is
claimed. The infinite-germ transport is also open: it needs local convergence
and justified derivative exchange for the finite C2 chart and the `J`, `d`,
and `E` sequences. The finite specialization does not assume those facts.

## Build and axiom audit

The following completed successfully (9555 Lake jobs):

```text
lake build CarrySelfAdjointOperator.C2LegJetCompensation \
  CarrySelfAdjointOperator.C2LegCompletionPolarization \
  CarrySelfAdjointOperator.C2LegCompletionFiniteAdapter \
  CarrySelfAdjointOperator.C2LegCompletionAudit
```

`C2LegCompletionAudit.lean` runs `#print axioms` on the exported results. The
reported dependencies are only Lean's standard `propext`, `Classical.choice`,
and `Quot.sound`; no project-specific axiom was introduced. A scan of the four
new Lean files found no `sorry`, `admit`, or `axiom` declarations.
