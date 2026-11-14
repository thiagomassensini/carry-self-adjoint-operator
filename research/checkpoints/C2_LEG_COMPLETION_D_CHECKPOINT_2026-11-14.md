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

## Integration checkpoint — relation to prompts A, B, and C

The four prompt results fit into one source-to-sign proof architecture, with
the remaining analytic estimate kept explicit:

- **B (common-pole cancellation)** fixes the exact cancellation and factor-2
  normalization before taking Taylor jets. Its identities are algebraic and
  do not establish a sign for the remaining source.
- **C (radial first correction)** identifies the finite first radial
  correction with a symmetric matrix of rank at most two and gives the exact
  seven-sample adapter. This is finite-order control; it does not assert
  convergence for arbitrary coefficients or control the quadratic remainder.
- **D (this checkpoint)** decomposes the finite C2 correction into its two
  leg increments and leaves the Gamma-versus-central comparison as an
  explicit residual. Infinite-germ transport remains open.
- **A (Hardy gate)** proves that an assumed eventual Gamma correction
  envelope yields nonnegative original boundary energy, and combines that
  energy sign with the Hardy nonrecurrence hypothesis to obtain strict
  positivity of both Hankel towers.

The precise bridge still missing is the envelope in
`HasNativeSourceGammaCorrectionEnvelope`: for each fixed order `n`, there
must be an `ε : ℕ → ℝ` tending to zero such that, eventually in the radial
index `k`,
`nativeSourceGammaCorrectionGap n k x ≤ ε k * ‖x‖^2` for every input `x`.
Prompts B, C, and D expose exact cancellation, finite radial structure, and
finite leg/Gamma residuals that may guide estimates for this gap, but none of
their theorems proves that envelope. Likewise, `InfinitePositiveRealNativeZeros`
remains an explicit hypothesis of A. Thus the combined result is a conditional
route to all-order strict Hankel positivity, not an unconditional positivity
claim; the two analytic inputs above remain open.

Other scope boundaries remain unchanged: B does not prove the removable
extension of `q = Q/(s-1)` at `s = 1`; C does not prove convergence or an
analytic remainder bound for arbitrary `β`; and D does not prove the stated
finite Gamma-to-central comparison or the local convergence and derivative
exchange needed for infinite-germ transport. The four prompts therefore
complete exact finite identities and a conditional positivity gate while
leaving these analytic bridges explicit.

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
