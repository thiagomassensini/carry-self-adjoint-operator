import CarrySelfAdjointOperator.CompletedNativeHolomorphicGreenMomentGenealogy
import CarrySelfAdjointOperator.CompletedNativeIndependentReflectedCanonicalSection
import Mathlib.Tactic

/-!
# Physical-section crosswalk from holomorphic Green to the historical four-corner cell

The independent-reflected construction keeps the reflected coordinate
independent until the final physical section `v = conj u`.  This file records
the value-level comparison made at that section.  In particular, it does not
differentiate the anti-holomorphic physical section.

The first-leg phase dress is deliberately retained on both ports.  Its effect
on `greenForm` has two coefficients, rather than a spurious single scalar
factor, until the concrete diagonal-port data are inserted.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Finite
open FiniteNativeCarryOperator.Camera

noncomputable section
set_option autoImplicit false

/-! ## Phase dressing of the canonical independent-reflected ports -/

/-- The normalized canonical direct port is the phase dress of the
holomorphic port.  The direct spectral parameter is the fixed `w` parameter
`operatorHeightParameter 0`. -/
theorem canonicalC3IndependentReflectedPhysicalDirectGreenPort_eq_phaseDress_holomorphic
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    canonicalC3IndependentReflectedDirectGreenPort M q hq0 hq1 S u v =
      radialGreenDress (cpPhaseNormalizer 3 (operatorHeightParameter 0))
        (canonicalC3IndependentReflectedHolomorphicDirectGreenPort
          M q hq0 hq1 S u v) := by
  simpa [canonicalC3IndependentReflectedDirectGreenPort,
    canonicalC3IndependentReflectedHolomorphicDirectGreenPort] using
    (greenPort_eq_phaseNormalizerDress_holomorphicGreenPort (3 * M)
      (operatorHeightParameter 0)
      (canonicalC3IndependentReflectedSixSourceReconstruction
        M q hq0 hq1 S u v).wSource)

/-- The normalized canonical reflected port is the phase dress of the
holomorphic port at the independent reflected parameter. -/
theorem canonicalC3IndependentReflectedPhysicalReflectedGreenPort_eq_phaseDress_holomorphic
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    canonicalC3IndependentReflectedReflectedGreenPort M q hq0 hq1 S u v =
      radialGreenDress (cpPhaseNormalizer 3 (operatorHeightParameter v))
        (canonicalC3IndependentReflectedHolomorphicReflectedGreenPort
          M q hq0 hq1 S u v) := by
  simpa [canonicalC3IndependentReflectedReflectedGreenPort,
    canonicalC3IndependentReflectedHolomorphicReflectedGreenPort] using
    (greenPort_eq_phaseNormalizerDress_holomorphicGreenPort (3 * M)
      (operatorHeightParameter v)
      (canonicalC3IndependentReflectedSixSourceReconstruction
        M q hq0 hq1 S u v).reflectedZSource)

/-- Exact two-coefficient rule for dressing both first Green legs.
Because `greenForm` is conjugate-linear in its first argument, this is not in
general scalar multiplication of the original Green form. -/
theorem greenForm_phaseDress_eq_twoCoefficient
    {N : ℕ} (a b : ℂ)
    (direct reflected : FiniteC3GreenPortCarrier N) :
    greenForm (𝕜 := ℂ)
        (radialGreenDress a direct)
        (radialGreenDress b reflected) =
      b * inner ℂ direct.2 reflected.1 -
        (starRingEnd ℂ a) * inner ℂ direct.1 reflected.2 := by
  simp only [radialGreenDress, greenForm, inner_smul_left, inner_smul_right]

/-- Before restricting to the physical section, the normalized canonical
Green boundary is exactly the two-coefficient phase dressing of the
canonical holomorphic boundary ports. -/
theorem canonicalC3IndependentReflectedCorrectedGreenBoundary_eq_phaseDress_holomorphic
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    canonicalC3IndependentReflectedCorrectedGreenBoundary M q hq0 hq1 S u v =
      cpPhaseNormalizer 3 (operatorHeightParameter v) *
          inner ℂ
            (canonicalC3IndependentReflectedHolomorphicDirectGreenPort
              M q hq0 hq1 S u v).2
            (canonicalC3IndependentReflectedHolomorphicReflectedGreenPort
              M q hq0 hq1 S u v).1 -
        (starRingEnd ℂ (cpPhaseNormalizer 3 (operatorHeightParameter 0))) *
          inner ℂ
            (canonicalC3IndependentReflectedHolomorphicDirectGreenPort
              M q hq0 hq1 S u v).1
            (canonicalC3IndependentReflectedHolomorphicReflectedGreenPort
              M q hq0 hq1 S u v).2 := by
  unfold canonicalC3IndependentReflectedCorrectedGreenBoundary
  rw [canonicalC3IndependentReflectedPhysicalDirectGreenPort_eq_phaseDress_holomorphic,
    canonicalC3IndependentReflectedPhysicalReflectedGreenPort_eq_phaseDress_holomorphic,
    greenForm_phaseDress_eq_twoCoefficient]

/-! ## The physical section and the historical four-corner presentation -/

/-- The physical reflected coordinate has exactly the historical reflected
height parameter.  This is a value-level section identity, not a complex
differentiation statement. -/
theorem canonicalC3IndependentReflectedPhysicalReflectedParameter
    (u : ℂ) :
    operatorHeightParameter ((starRingEnd ℂ) u) =
      reflectedParameter (operatorHeightParameter u) := by
  exact (reflectedParameter_operatorHeightParameter_eq_operatorHeightParameter_conj u).symm

/-- The direct reconstructed port on the physical section is the historical
Genuine bracket port at the fixed `w` height. -/
theorem canonicalC3IndependentReflectedPhysicalDirectGreenPort_eq_historical
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) :
    canonicalC3IndependentReflectedDirectGreenPort M q hqpos.le hq1 S
      u ((starRingEnd ℂ) u) =
      finiteC3GenuineBracketGreenBoundaryPair (3 * M)
        (operatorHeightParameter 0) := by
  unfold canonicalC3IndependentReflectedDirectGreenPort
    canonicalC3IndependentReflectedSixSourceReconstruction
  rw [nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected_physicalSection,
    nativeC3SeededClockTfvdSixSourceAnalysis_eq_canonical]
  exact canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort_canonicalPrefix
    M (operatorHeightParameter u) (operatorHeightParameter 0) q hqpos hq1 S

/-- The reflected reconstructed port on the physical section is the
historical Genuine bracket port at the reflected height.  Its canonical-prefix
description is the ordinary plus log-jet recovery recorded below. -/
theorem canonicalC3IndependentReflectedPhysicalReflectedGreenPort_eq_historical
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) :
    canonicalC3IndependentReflectedReflectedGreenPort M q hqpos.le hq1 S
      u ((starRingEnd ℂ) u) =
      finiteC3GenuineBracketGreenBoundaryPair (3 * M)
        (reflectedParameter (operatorHeightParameter u)) := by
  unfold canonicalC3IndependentReflectedReflectedGreenPort
    canonicalC3IndependentReflectedSixSourceReconstruction
  rw [canonicalC3IndependentReflectedPhysicalReflectedParameter,
    nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected_physicalSection,
    nativeC3SeededClockTfvdSixSourceAnalysis_eq_canonical]
  exact canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort_canonicalPrefix
    M (operatorHeightParameter u) (operatorHeightParameter 0) q hqpos hq1 S

/-- On `v = conj u`, the physical independent-reflected Green boundary is
literally the historical four-corner Green component.  The exact historical
parameters are `z = operatorHeightParameter u`, `w = operatorHeightParameter
0`, and its finite prefix is `3 * M`. -/
theorem canonicalC3PhysicalDressedHolomorphicGreen_eq_historicalFourCorner
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) :
    canonicalC3IndependentReflectedCorrectedGreenBoundary M q hqpos.le hq1 S
      u ((starRingEnd ℂ) u) =
      canonicalCompletedNativeHistoricalFourCornerGreenComponent (3 * M)
        (operatorHeightParameter u) (operatorHeightParameter 0) := by
  rw [canonicalC3IndependentReflectedCorrectedGreenBoundary_physicalSection
      M q hqpos hq1 S u,
    nativeC3SeededClockTfvdSixSourceAnalysis_eq_canonical,
    canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary_canonicalPrefix
      M (operatorHeightParameter u) (operatorHeightParameter 0) q hqpos hq1 S,
    canonicalC3BracketTfvdMixedCorrectedBoundary_eq_greenReadout,
    canonicalC3BracketTfvdMixedGreenReadout_eq_bracketGreen]
  rw [show M * 3 = 3 * M from Nat.mul_comm M 3]
  rfl

/-- The same physical-section result, expanded into the exact historical
radial coefficient and ordinary/log-jet reconstructed prefix.  Thus the
`canonicalC3MixedRadialCoefficient` occurs after the physical section and
phase dressing, rather than as an unproved replacement for the holomorphic
collision coefficient. -/
theorem canonicalC3PhysicalDressedHolomorphicGreen_eq_mixedRadialCoefficient_mul_prefix
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) :
    canonicalC3IndependentReflectedCorrectedGreenBoundary M q hqpos.le hq1 S
      u ((starRingEnd ℂ) u) =
      canonicalC3MixedRadialCoefficient
          (operatorHeightParameter u) (operatorHeightParameter 0) *
        nativeGpreFourCornerPolarizedDirichletPrefix (3 * M)
          (operatorHeightParameter 0)
          (reflectedParameter (operatorHeightParameter u)) := by
  rw [canonicalC3PhysicalDressedHolomorphicGreen_eq_historicalFourCorner
    M q hqpos hq1 S u]
  exact canonicalCompletedNativeHistoricalFourCornerGreenComponent_eq
    (3 * M) (operatorHeightParameter u) (operatorHeightParameter 0)

/-- The historical reflected source in the preceding four-corner formula is
literally the ordinary plus log-jet reconstruction.  This isolates the source
crosswalk supplied by the physical six-source section without identifying it
with an independent source away from that section. -/
theorem canonicalC3PhysicalDressedHolomorphicGreen_eq_mixedRadialCoefficient_mul_logJetSource
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) :
    canonicalC3IndependentReflectedCorrectedGreenBoundary M q hqpos.le hq1 S
      u ((starRingEnd ℂ) u) =
      canonicalC3MixedRadialCoefficient
          (operatorHeightParameter u) (operatorHeightParameter 0) *
        ∑ n ∈ Finset.range (3 * M),
          (starRingEnd ℂ)
              (positiveDirichletGradient (operatorHeightParameter 0) n) *
            sameEdgeRecoveredReflectedGradient n
              (positiveDirichletGradient (operatorHeightParameter u) n)
              (positiveLogDirichletGradient (operatorHeightParameter u) n) := by
  rw [canonicalC3PhysicalDressedHolomorphicGreen_eq_historicalFourCorner
    M q hqpos hq1 S u,
    canonicalCompletedNativeHistoricalFourCornerGreenComponent_eq,
    canonicalCompletedNativeHistoricalFourCornerPrefix_eq_logJetReconstruction]

/-! ## Fixed-center completed ledger provenance -/

/-- At its fixed first leg, the explicit Green channel occurring in the
completed ledger is exactly the same historical four-corner component.  The
remaining provenance, off-diagonal, residual, tail, and archimedean channels
are not removed by this equality. -/
theorem canonicalCompletedFixedCenterLedger_greenChannel_eq_historicalFourCorner
    (M : ℕ) (w : ℂ) :
    canonicalC3MixedRadialCoefficient
        (operatorHeightParameter w) (operatorHeightParameter 0) *
      inner ℂ
        (canonicalCompletedC3DirichletGradientPrefixState
          (operatorHeightParameter 0) (3 * M))
        (canonicalCompletedC3DirichletGradientPrefixState
          (reflectedParameter (operatorHeightParameter w)) (3 * M)) =
      canonicalCompletedNativeHistoricalFourCornerGreenComponent (3 * M)
        (operatorHeightParameter w) (operatorHeightParameter 0) := by
  symm
  rw [canonicalCompletedNativeHistoricalFourCornerGreenComponent_eq,
    canonicalCompletedNativeHistoricalFourCornerPrefix_eq_inner]

/-- The fixed-center completed ledger with the Green component factored back
to its historical four-corner carrier.  The displayed quotient is intentional:
the Hermitian weights and the chart/denominator have not been silently
absorbed into the Green term. -/
theorem canonicalCompletedC3FixedCenterLedger_eq_fourCorner_add_corrections
    (M : ℕ) (w : ℂ) :
    canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M w =
      (mixedHermitianWeight nativeXiCompletionFactor w 0 *
          (canonicalCompletedNativeHistoricalFourCornerGreenComponent (3 * M)
              (operatorHeightParameter w) (operatorHeightParameter 0) +
            canonicalC3FiniteMixedHeightGreenProvenanceChannel M
              (operatorHeightParameter w) (operatorHeightParameter 0) +
            canonicalC3FiniteMixedHeightOffDiagonalChannel M
              (operatorHeightParameter w) (operatorHeightParameter 0) +
            canonicalC3FiniteMixedHeightReadoutResidualChannel M
              (operatorHeightParameter w) (operatorHeightParameter 0) +
            canonicalC3MixedHeightTailCompletionDefect M w 0) +
        canonicalCompletedC3ArchimedeanChartMixedChannel w 0) /
      (mixedHermitianWeight canonicalC3ChartFactorHeight w 0 *
        ((2 : ℂ) * conj (completedNativeOperatorCharacteristic 0) *
          completedNativeOperatorCharacteristic w)) := by
  unfold canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator
  rw [canonicalCompletedFixedCenterLedger_greenChannel_eq_historicalFourCorner]

/-- The fixed-center ledger written with its historical four-corner Green
channel visible.  This is a presentation of the existing completed scalar
ledger, not a new normalized response. -/
def canonicalCompletedC3FixedCenterFourCornerLedger
    (M : ℕ) (w : ℂ) : ℂ :=
  (mixedHermitianWeight nativeXiCompletionFactor w 0 *
      (canonicalCompletedNativeHistoricalFourCornerGreenComponent (3 * M)
          (operatorHeightParameter w) (operatorHeightParameter 0) +
        canonicalC3FiniteMixedHeightGreenProvenanceChannel M
          (operatorHeightParameter w) (operatorHeightParameter 0) +
        canonicalC3FiniteMixedHeightOffDiagonalChannel M
          (operatorHeightParameter w) (operatorHeightParameter 0) +
        canonicalC3FiniteMixedHeightReadoutResidualChannel M
          (operatorHeightParameter w) (operatorHeightParameter 0) +
        canonicalC3MixedHeightTailCompletionDefect M w 0) +
    canonicalCompletedC3ArchimedeanChartMixedChannel w 0) /
  (mixedHermitianWeight canonicalC3ChartFactorHeight w 0 *
    ((2 : ℂ) * conj (completedNativeOperatorCharacteristic 0) *
      completedNativeOperatorCharacteristic w))

/-- The four-corner ledger presentation is definitionally the explicit
right-hand side of the preceding channel decomposition. -/
theorem canonicalCompletedC3FixedCenterLedger_eq_fourCornerLedger
    (M : ℕ) (w : ℂ) :
    canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M w =
      canonicalCompletedC3FixedCenterFourCornerLedger M w := by
  exact canonicalCompletedC3FixedCenterLedger_eq_fourCorner_add_corrections M w

/-- The zeroth completed native logarithmic moment is the first variation of
the complete four-corner ledger presentation.  It retains the external
Hermitian weight, denominator, and all five non-Green channels; no claim is
made here that the four-corner term alone equals `h₀`. -/
theorem canonicalCompletedC3FixedCenterFourCornerLedgerFirstVariation_eq_h0
    (M : ℕ) :
    deriv (canonicalCompletedC3FixedCenterFourCornerLedger M) 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  have hfun : canonicalCompletedC3FixedCenterFourCornerLedger M =
      canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M := by
    funext w
    exact (canonicalCompletedC3FixedCenterLedger_eq_fourCornerLedger M w).symm
  rw [hfun]
  exact canonicalCompletedNativeFixedCenterLedgerFirstVariation_eq_h0 M

end

end CarrySelfAdjointOperator
