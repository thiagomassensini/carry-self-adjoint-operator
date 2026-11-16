# Luna E carrier checkpoint — E1/E2 and conditional E3/E4

Base: `c999ce41ccdec0ff194e7969bf1f7f329d374d3a`.

`CarrySelfAdjointOperator/C2LegCauchySynthesis.lean` now proves E1 and E2 in
an arbitrary complex Hilbert space. `c2CauchyCompanionSynthesis_eq_central_add_legs`
transports `Cᵢ = C₀,ᵢ + i Lᵢ Eᵢ` through the unchanged finite weights and
vectors. `c2CauchyDefect_eq_central_add_legs` gives the central-plus-leg signed
readout. The two pairing expansion theorems expose the full ordered double
sums, retaining every `(i,j)` cross.

`c2CarrierDefect_approximation_error_bound` proves the requested unsigned
two-vector tail estimate. It uses only the inner-product expansion,
`|Im z| ≤ ‖z‖`, and Cauchy–Schwarz; it assumes no sign, Gram/Hankel condition,
or inverse.

The original-source adapter in
`CarrySelfAdjointOperator/CompletedNativeC2LegEnvelopeTransport.lean` now
instantiates these results. Its finite value, central companion, two-leg
companion, and full finite companion use the same source weights
`nativeSourceChiralJetInput / completedNativePositiveHermiteBiehlerCoordinate`
and the same radial Cauchy feature vectors at each `canonicalCompletedC3RadialTiltPoint`.
No denominator is recomputed from the finite value chart.

The adapter proves the finite D companion splits after synthesis and, under
the existing strip and nonzero-coordinate conditions, identifies the
complete carrier defect with `nativeSourceGammaCorrectionGap`. E2 then gives
an explicit bound by `nativeSourceC2TailError`; the vector differences are
defined exactly, but no estimate that they tend to zero is proved.

`HasNativeSourceC2LegTailBounds` states the precise conditional E4 frontier:
at each fixed order, a cutoff `M(n,k)` may depend on `k`, while
`aₙ(k), bₙ(k) → 0`; the lower bound is on the SUM of central and leg readouts,
and the second bound controls the full tail budget. From these premises,
`nativeSourceC2LegTailBounds_imply_gammaCorrectionEnvelope` derives the A
envelope with `εₙ(k)=2aₙ(k)+bₙ(k)`. The final Hankel consumer still requires
`InfinitePositiveRealNativeZeros` explicitly. No cutoff/radial limits are
interchanged, and neither source estimate is proved by E1--E4.

Targeted `lake build --wfail` passed for the two proof modules and focused
axiom audit (9637 jobs, using the existing cache). Direct Lean compilation
with `-DwarningAsError=true` passed; every audited declaration depends only
on `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, or
new project axiom is present in the added Lean files.

Next: instantiate these identities with the original chiral Cauchy weights
and the finite D central/leg companions, export the exact Gamma-gap identity
and explicit tail, then state the conditional E4 bounds needed by A.
