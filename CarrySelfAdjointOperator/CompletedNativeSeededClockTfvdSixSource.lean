import CarrySelfAdjointOperator.CompletedNativeTfvdSixChannelJet
import CarrySelfAdjointOperator.C3DynamicCompletedGreenForm

/-!
# Native seeded-clock access to the six TFVD sources

The raw positive seeded-clock Gram is not the completed causal/chiral
readout.  This file makes the different, already present interface explicit:
each native seeded C3 block carries its incoming value and three ordinary
gradient legs, and one material-clock step carries the three log-jet legs.
Across a finite atlas of blocks these are exactly the coordinates of the
ordinary/log-jet prefix states which feed the lossless six-channel TFVD
analysis.
-/

open scoped ComplexConjugate InnerProductSpace BigOperators

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open C3TraceDynamics

noncomputable section

/-- The complete material block at native indices `3m+1, ..., 3m+4`.  It is
only a packaging of the existing native seed and of the four existing real
clock frequencies. -/
def nativeC3SeededClockMaterialBlock (m : ℕ) (s : ℂ) : SeededClockBlock where
  d := Real.log (3 * m + 1 : ℕ)
  a := Real.log (3 * m + 2 : ℕ)
  b := Real.log (3 * m + 3 : ℕ)
  c := Real.log (3 * m + 4 : ℕ)
  state := nativeBlockSeededData m s

/-- The enriched boundary observation supplied by one seeded clock block.
`ordinary` is retained before clocking, while `logJet` is retained after one
clock step.  Keeping both is essential: their raw positive Gram is not used
as the corrected readout. -/
structure SeededClockTfvdBoundaryObservation where
  incoming : ℂ
  ordinary : Fin 3 → ℂ
  logJet : Fin 3 → ℂ

/-- Read the ordinary and one-step log-jet legs directly from a complete
seeded-clock block. -/
def seededClockTfvdBoundaryObservation
    (block : SeededClockBlock) : SeededClockTfvdBoundaryObservation where
  incoming := block.state.1
  ordinary := block.state.2
  logJet := (seededClock block.d block.a block.b block.c block.state).2

/-- On the native block, the enriched observation is exactly the pre-existing
native seed, ordinary gradient block, and dynamic log-jet block. -/
theorem seededClockTfvdBoundaryObservation_native
    (m : ℕ) (s : ℂ) :
    seededClockTfvdBoundaryObservation (nativeC3SeededClockMaterialBlock m s) =
      { incoming := positiveDirichletValue s (3 * m)
        ordinary := nativeC3BlockGradient m s
        logJet := nativeC3BlockDynamicLogJet m s } := by
  rfl

/-- Every ordinary edge of the `3M` prefix is read from exactly one native
material block and one of its three retained ordinary legs. -/
theorem c2DirichletGradientPrefixCore_eq_seededClockTfvd_ordinary
    (M : ℕ) (m : Fin M) (r : Fin 3) (s : ℂ) :
    c2DirichletGradientPrefixCore s (3 * M)
        (3 * (m : ℕ) + (r : ℕ)) =
      (seededClockTfvdBoundaryObservation
        (nativeC3SeededClockMaterialBlock (m : ℕ) s)).ordinary r := by
  have hindex : 3 * (m : ℕ) + (r : ℕ) < 3 * M := by
    omega
  rw [c2DirichletGradientPrefixCore_apply, if_pos hindex]
  rw [seededClockTfvdBoundaryObservation_native]
  change positiveDirichletGradient s (3 * (m : ℕ) + (r : ℕ)) =
    nativeC3BlockGradient (m : ℕ) s r
  fin_cases r <;> rfl

/-- Every log-jet edge of the `3M` prefix is read from the same native
material block after one clock step. -/
theorem c2LogJetPrefixCore_eq_seededClockTfvd_logJet
    (M : ℕ) (m : Fin M) (r : Fin 3) (s : ℂ) :
    c2LogJetPrefixCore s (3 * M)
        (3 * (m : ℕ) + (r : ℕ)) =
      (seededClockTfvdBoundaryObservation
        (nativeC3SeededClockMaterialBlock (m : ℕ) s)).logJet r := by
  have hindex : 3 * (m : ℕ) + (r : ℕ) < 3 * M := by
    omega
  rw [c2LogJetPrefixCore_apply, if_pos hindex]
  rw [seededClockTfvdBoundaryObservation_native, nativeC3BlockDynamicLogJet_eq]
  fin_cases r <;> rfl

/-! ## Six analyzed sources obtained from the material boundary observation -/

/-- The ordinary finite TFVD analysis of the `M` native material blocks.  By
the coordinate theorem above, its input is precisely the concatenation of
their retained ordinary legs, completed by zero outside the atlas. -/
def nativeC3SeededClockOrdinaryTfvdAnalysis
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (s : ℂ) :
    NativeGpreFiniteTfvdAnalysisCarrier S :=
  nativeGpreFiniteTfvdAnalysis q S
    (canonicalCompletedC3DirichletGradientPrefixState s (3 * M))

/-- The log-jet finite TFVD analysis of the same `M` material blocks.  Its
input is the one-step clock output, again completed by zero off the atlas. -/
def nativeC3SeededClockLogJetTfvdAnalysis
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (s : ℂ) :
    NativeGpreFiniteTfvdAnalysisCarrier S :=
  nativeGpreFiniteTfvdAnalysis q S
    (canonicalCompletedC3LogJetPrefixState s (3 * M))

/-- The six lossless TFVD analyses read from the ordinary/log-jet material
observations at the direct, second, and reflected parameters. -/
def nativeC3SeededClockTfvdSixSourceAnalysis
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ) :
    CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S :=
  ((nativeC3SeededClockOrdinaryTfvdAnalysis M q S z,
      nativeC3SeededClockLogJetTfvdAnalysis M q S z),
    ((nativeC3SeededClockOrdinaryTfvdAnalysis M q S w,
        nativeC3SeededClockLogJetTfvdAnalysis M q S w),
      (nativeC3SeededClockOrdinaryTfvdAnalysis M q S (reflectedParameter z),
        nativeC3SeededClockLogJetTfvdAnalysis M q S (reflectedParameter z))))

/-- The material six-analysis datum is definitionally the analysis of the
canonical all-cutoff three-prefix source.  The preceding two coordinate
theorems are the substantive provenance statement behind this equality. -/
theorem nativeC3SeededClockTfvdSixSourceAnalysis_eq_canonical
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ) :
    nativeC3SeededClockTfvdSixSourceAnalysis M q S z w =
      canonicalC3AllCutoffMixedSourceTfvdAnalysis q S
        (canonicalC3AllCutoffMixedSourcePrefixState M z w) := by
  rfl

/-- The six material TFVD analyses reconstruct without loss to the canonical
three-prefix Hilbert source.  Hence all bracket/port cross terms remain
available after the material boundary observation. -/
theorem canonicalC3AllCutoffMixedSourceTfvdReconstruction_seededClockAnalysis
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3AllCutoffMixedSourceTfvdReconstruction q hqpos.le hq1 S
      (nativeC3SeededClockTfvdSixSourceAnalysis M q S z w) =
        canonicalC3AllCutoffMixedSourcePrefixState M z w := by
  rw [nativeC3SeededClockTfvdSixSourceAnalysis_eq_canonical]
  exact canonicalC3AllCutoffMixedSourceTfvdReconstruction_analysis
    q hqpos hq1 S (canonicalC3AllCutoffMixedSourcePrefixState M z w)

/-- The corrected radial Green boundary read directly from the six material
analyses.  It is a Green form of reconstructed direct and reflected ports;
it is not a raw material-clock Gram. -/
def nativeC3SeededClockTfvdSixSourceCorrectedBoundary
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) : ℂ :=
  canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary M
    (operatorHeightParameter z) (operatorHeightParameter w) q hq0 hq1 S
    (nativeC3SeededClockTfvdSixSourceAnalysis M q S
      (operatorHeightParameter z) (operatorHeightParameter w))

/-- The material corrected boundary is exactly the radial complex coordinate
of the finite completed ledger.  The height/global parameter distinction is
retained explicitly in the statement. -/
theorem nativeC3SeededClockTfvdSixSourceCorrectedBoundary_eq_ledgerRadial
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceCorrectedBoundary M z w q hqpos.le hq1 S =
      (canonicalCompletedC3AllCutoffKernelLedgerState M z w).radialComplexReadout := by
  unfold nativeC3SeededClockTfvdSixSourceCorrectedBoundary
  rw [nativeC3SeededClockTfvdSixSourceAnalysis_eq_canonical]
  exact canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary_canonicalPrefix_eq_ledgerRadial
    M z w q hqpos hq1 S

/-- The complete corrected causal/chiral scalar readout obtained from the
six material TFVD analyses.  It retains the reconstructed Green ports, all
three structural coordinates, tail completion, xi weight and chart. -/
def nativeC3SeededClockTfvdSixSourceFinalReadout
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) : ℂ :=
  canonicalC3AllCutoffMixedSourceTfvdFinalReadout M z w q hq0 hq1 S
    (nativeC3SeededClockTfvdSixSourceAnalysis M q S
      (operatorHeightParameter z) (operatorHeightParameter w))

/-- At the native material source, the complete enriched readout is exactly
the existing all-cutoff kernel-ledger final readout. -/
theorem nativeC3SeededClockTfvdSixSourceFinalReadout_eq_ledger
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceFinalReadout M z w q hqpos.le hq1 S =
      (canonicalCompletedC3AllCutoffKernelLedgerState M z w).finalReadout := by
  unfold nativeC3SeededClockTfvdSixSourceFinalReadout
  rw [nativeC3SeededClockTfvdSixSourceAnalysis_eq_canonical]
  exact canonicalC3AllCutoffMixedSourceTfvdFinalReadout_canonicalPrefix
    M z w q hqpos hq1 S

/-- Centered normalized response read from the native material six-source
observation.  This is deliberately distinct from `seededClockAtlasCoefficient`:
the latter is the raw positive four-node Gram and omits the enriched boundary
and provenance channels retained here. -/
def nativeC3SeededClockTfvdSixSourceNormalizedResponse
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (z : ℂ) : ℂ :=
  nativeC3SeededClockTfvdSixSourceFinalReadout (M + 1) z 0 q hq0 hq1 S /
    (mixedHermitianWeight canonicalC3ChartFactorHeight z 0 *
      ((2 : ℂ) * completedNativeOperatorCharacteristic z *
        (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0)))

/-- The material enriched normalized response is pointwise the six-analysis
response already known to encode the corrected chiral carrier. -/
theorem nativeC3SeededClockTfvdSixSourceNormalizedResponse_eq_sixAnalysis
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceNormalizedResponse M q hqpos.le hq1 S =
      canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q
        (show 0 ≤ q from hqpos.le) hq1 S := by
  funext z
  unfold nativeC3SeededClockTfvdSixSourceNormalizedResponse
    canonicalC3BracketTfvdSixAnalysisNormalizedResponse
  rw [nativeC3SeededClockTfvdSixSourceFinalReadout_eq_ledger
    (M + 1) z 0 q hqpos hq1 S]
  rw [← canonicalC3AllCutoffMixedSourceTfvdFinalReadout_canonicalPrefix
    (M + 1) z 0 q hqpos hq1 S]

/-- The corrected first-column coefficient read directly from the native
material enriched TFVD boundary observation. -/
def nativeC3SeededClockTfvdSixSourceJetCoefficient
    (M p : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) : ℂ :=
  iteratedDeriv (p + 1)
    (nativeC3SeededClockTfvdSixSourceNormalizedResponse M q hq0 hq1 S) 0 /
      (p + 1).factorial

/-- All corrected causal/chiral first-column coefficients are the central
jets of the material enriched six-source boundary observation, before any
moment crosswalk. -/
theorem canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_seededClockTfvdSixSourceJet
    (M p : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p =
      nativeC3SeededClockTfvdSixSourceJetCoefficient M p q hqpos.le hq1 S := by
  unfold nativeC3SeededClockTfvdSixSourceJetCoefficient
  rw [nativeC3SeededClockTfvdSixSourceNormalizedResponse_eq_sixAnalysis
    M q hqpos hq1 S]
  exact canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_sixAnalysisJet
    M p q hqpos hq1 S

/-- Low-order material calculation: the first enriched boundary jet is the
corrected first-column entry.  This is prior to identifying that entry with a
moment. -/
theorem nativeC3SeededClockTfvdSixSourceJet_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceJetCoefficient M 0 q hqpos.le hq1 S =
      canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M 0 := by
  exact (canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_seededClockTfvdSixSourceJet
    M 0 q hqpos hq1 S).symm

/-- Low-order material calculation: parity kills the second jet of the full
enriched material boundary observation. -/
theorem nativeC3SeededClockTfvdSixSourceJet_one_eq_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceJetCoefficient M 1 q hqpos.le hq1 S = 0 := by
  unfold nativeC3SeededClockTfvdSixSourceJetCoefficient
  rw [nativeC3SeededClockTfvdSixSourceNormalizedResponse_eq_sixAnalysis
    M q hqpos hq1 S]
  exact canonicalC3BracketTfvdSixAnalysisJet_one_eq_zero M q hqpos hq1 S

/-- Low-order material calculation: the third enriched boundary jet is the
corrected first-column entry at index two. -/
theorem nativeC3SeededClockTfvdSixSourceJet_two
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceJetCoefficient M 2 q hqpos.le hq1 S =
      canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M 2 := by
  exact (canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_seededClockTfvdSixSourceJet
    M 2 q hqpos hq1 S).symm

/-- Downstream crosswalk only: after the geometric material-jet identities,
the first jet is recognized as the zeroth completed log-derivative moment. -/
theorem nativeC3SeededClockTfvdSixSourceJet_zero_eq_canonicalMoment
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceJetCoefficient M 0 q hqpos.le hq1 S =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [nativeC3SeededClockTfvdSixSourceJet_zero M q hqpos hq1 S]
  simpa using canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_odd_eq_canonicalMoment M 0

/-- Downstream crosswalk only: after the geometric material-jet identities,
the third jet is recognized as the first completed log-derivative moment. -/
theorem nativeC3SeededClockTfvdSixSourceJet_two_eq_canonicalMoment
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceJetCoefficient M 2 q hqpos.le hq1 S =
      (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) := by
  rw [nativeC3SeededClockTfvdSixSourceJet_two M q hqpos hq1 S]
  simpa using canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_odd_eq_canonicalMoment M 1

end

end CarrySelfAdjointOperator
