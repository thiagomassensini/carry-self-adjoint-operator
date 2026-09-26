import CarrySelfAdjointOperator.CompletedNativeIndependentReflectedRealAxisConvolution
import CarrySelfAdjointOperator.CompletedC3CentralLedgerChannelDerivative
import CarrySelfAdjointOperator.CompletedC3SymplecticCollisionVariationAudit
import Mathlib.Tactic

/-!
# Fixed-center ledger crosswalk for the real non-Green remainder

The independent-reflected remainder is first restricted to the real
diagonal.  There its direct role is the moving canonical `z` parameter, its
reflected role has the same parameter only because real conjugation is
trivial, and its `w` role remains fixed at the center.  This file identifies
that response-level remainder with the existing fixed-center channel ledger,
without placing the already extracted undressed Green boundary back into the
remainder.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section
set_option autoImplicit false

/-! ## Orientation and physical-section audit -/

/-- On the physical section, the independent-reflected non-Green response is
the pre-existing canonical non-Green response.  The first structural argument
is the fixed `w = 0` role, while the second is the reflected `z` parameter. -/
theorem canonicalC3IndependentReflectedNonGreenResponse_physicalSection
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) :
    canonicalC3IndependentReflectedNonGreenResponse M q hqpos.le hq1 S
        u ((starRingEnd ℂ) u) =
      canonicalC3CameraResolvedNonGreenResponse M q hqpos.le hq1 S u := by
  unfold canonicalC3IndependentReflectedNonGreenResponse
    canonicalC3CameraResolvedNonGreenResponse
  rw [nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected_physicalSection,
    ← reflectedParameter_operatorHeightParameter_eq_operatorHeightParameter_conj]

/-- On the real axis the physical-section crosswalk is an equality with the
literal `(t,t)` independent-reflected diagonal. -/
theorem canonicalC3IndependentReflectedNonGreenRealDiagonalResponse_eq_cameraResolved
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) :
    canonicalC3IndependentReflectedNonGreenRealDiagonalResponse M q hqpos.le hq1 S t =
      canonicalC3CameraResolvedNonGreenResponse M q hqpos.le hq1 S (t : ℂ) := by
  simpa [canonicalC3IndependentReflectedNonGreenRealDiagonalResponse] using
    (canonicalC3IndependentReflectedNonGreenResponse_physicalSection
      M q hqpos hq1 S (t : ℂ))

/-! ## Cutoff and normalization crosswalk -/

/-- The response-level non-Green diagonal at canonical cutoff `M` is the
fixed-center ledger at literal cutoff `M + 1`.  This is an equality of
normalized responses: both sides retain the xi weight, the common chart/F
denominator, and the archimedean channel in their original positions. -/
theorem canonicalC3CameraResolvedNonGreenResponse_ofReal_eq_fixedCenterLedger
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) :
    canonicalC3CameraResolvedNonGreenResponse M q hqpos.le hq1 S (t : ℂ) =
      canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator (M + 1) (t : ℂ) := by
  unfold canonicalC3CameraResolvedNonGreenResponse
  rw [nativeC3SeededClockTfvdSixSourceAnalysis_eq_canonical]
  dsimp only
  rw [
    canonicalC3AllCutoffMixedSourceTfvdStructuralReadout_canonicalPrefix
      (M + 1) (operatorHeightParameter (t : ℂ)) (operatorHeightParameter 0)
        q hqpos hq1 S]
  unfold canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator
  rw [canonicalC3MixedRadialCoefficient_operatorHeight_ofReal_zero,
    zero_mul, zero_add,
    canonicalC3MixedStructuralScalarReadout_state,
    canonicalC3FiniteMixedHeightStructuralDefect_eq_channelSum]
  unfold canonicalC3BracketTfvdSixAnalysisResponseDenominator
  ring

/-- Functional capstone: the new real non-Green remainder is precisely the
old fixed-center, channel-separated normalized ledger at cutoff `M + 1`.
The old ledger's `greenProvenance` coordinate is a structural provenance
channel, not the independent-reflected undressed Green boundary already
extracted into the convolution. -/
theorem canonicalC3IndependentReflectedNonGreenRealDiagonalResponse_eq_fixedCenterChannels
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) :
    canonicalC3IndependentReflectedNonGreenRealDiagonalResponse M q hqpos.le hq1 S t =
      canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator (M + 1) (t : ℂ) := by
  rw [canonicalC3IndependentReflectedNonGreenRealDiagonalResponse_eq_cameraResolved
    M q hqpos hq1 S t]
  exact canonicalC3CameraResolvedNonGreenResponse_ofReal_eq_fixedCenterLedger
    M q hqpos hq1 S t

/-! ## The old channel candidate, without reintroducing extracted Green -/

/-- The fixed-center real response carrying precisely the four structural/tail
channels and the separately retained archimedean operator branch.  Its
`greenProvenance` summand is retained because it belongs to the structural
readout; this definition contains no corrected or undressed Green boundary. -/
def canonicalCompletedC3FixedCenterNonGreenRealResponse (M : ℕ) (t : ℝ) : ℂ :=
  canonicalCompletedC3FixedCenterGreenProvenanceRealChannel M t +
    canonicalCompletedC3FixedCenterOffDiagonalRealChannel M t +
    canonicalCompletedC3FixedCenterReadoutResidualRealChannel M t +
    canonicalCompletedC3FixedCenterTailCompletionRealChannel M t +
    canonicalCompletedC3FixedCenterGlobalOperatorRealBranch t

/-- The new real non-Green remainder is functionally the fixed-center old
channel presentation, at the explicitly shifted cutoff `M + 1`. -/
theorem canonicalC3IndependentReflectedNonGreenRealDiagonalResponse_eq_fixedCenterNonGreenRealResponse
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) :
    canonicalC3IndependentReflectedNonGreenRealDiagonalResponse M q hqpos.le hq1 S t =
      canonicalCompletedC3FixedCenterNonGreenRealResponse (M + 1) t := by
  have htStrip : operatorHeightParameter (t : ℂ) ∈ genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter]
  calc
    canonicalC3IndependentReflectedNonGreenRealDiagonalResponse M q hqpos.le hq1 S t =
        canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator (M + 1) (t : ℂ) :=
      canonicalC3IndependentReflectedNonGreenRealDiagonalResponse_eq_fixedCenterChannels
        M q hqpos hq1 S t
    _ = canonicalCompletedC3FixedCenterRawWronskianBranch (t : ℂ) +
          canonicalCompletedC3FixedCenterArchimedeanBranch (t : ℂ) :=
      canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator_eq_raw_add_archimedean
        (M + 1) htStrip
    _ = canonicalCompletedC3FixedCenterGreenProvenanceRealChannel (M + 1) t +
          canonicalCompletedC3FixedCenterOffDiagonalRealChannel (M + 1) t +
          canonicalCompletedC3FixedCenterReadoutResidualRealChannel (M + 1) t +
          canonicalCompletedC3FixedCenterTailCompletionRealChannel (M + 1) t +
          canonicalCompletedC3FixedCenterGlobalOperatorRealBranch t := by
      rw [canonicalCompletedC3FixedCenterRawWronskianBranch_ofReal_eq_fourChannels,
        ← canonicalCompletedC3FixedCenterGlobalOperatorRealBranch_eq_archimedean]
    _ = canonicalCompletedC3FixedCenterNonGreenRealResponse (M + 1) t := rfl

/-- The channel candidate is the pre-existing total fixed-center symplectic
real branch.  This is an exact response equality, not an identification of
the provenance channel with the extracted Green carrier. -/
theorem canonicalCompletedC3FixedCenterNonGreenRealResponse_eq_totalSymplectic
    (M : ℕ) :
    canonicalCompletedC3FixedCenterNonGreenRealResponse M =
      canonicalCompletedC3FixedCenterTotalSymplecticRealBranch := by
  funext t
  unfold canonicalCompletedC3FixedCenterNonGreenRealResponse
    canonicalCompletedC3FixedCenterTotalSymplecticRealBranch
  rw [← canonicalCompletedC3FixedCenterRawWronskianBranch_ofReal_eq_fourChannels]

/-- The new non-Green remainder is therefore the old total fixed-center
symplectic real branch at cutoff `M + 1`. -/
theorem canonicalC3IndependentReflectedNonGreenRealDiagonalResponse_eq_totalSymplectic
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedNonGreenRealDiagonalResponse M q hqpos.le hq1 S =
      canonicalCompletedC3FixedCenterTotalSymplecticRealBranch := by
  funext t
  rw [canonicalC3IndependentReflectedNonGreenRealDiagonalResponse_eq_fixedCenterNonGreenRealResponse
    M q hqpos hq1 S t,
    canonicalCompletedC3FixedCenterNonGreenRealResponse_eq_totalSymplectic]

/-! ## The canonical remainder at index zero -/

/-- At canonical index zero the real remainder is literally the first real
derivative of the non-Green diagonal; its factorial denominator is one. -/
theorem canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder_zero_eq_deriv
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder M 0 q hq0 hq1 S =
      deriv
        (canonicalC3IndependentReflectedNonGreenRealDiagonalResponse M q hq0 hq1 S) 0 := by
  unfold canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder
    canonicalC3IndependentReflectedNonGreenRealJetCoefficient
    factorialNormalizedRealJetCoefficient
  simp [iteratedDeriv_one]

/-- The first real remainder derivative is the completed central ledger
variation.  Although its displayed finite-channel presentation uses cutoff
`M + 1`, the sewn total fixed-center branch is cutoff-independent. -/
theorem canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder_zero_eq_h0
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder M 0 q hqpos.le hq1 S =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder_zero_eq_deriv,
    canonicalC3IndependentReflectedNonGreenRealDiagonalResponse_eq_totalSymplectic
      M q hqpos hq1 S,
    deriv_canonicalCompletedC3FixedCenterTotalSymplecticRealBranch_zero]

/-- Channelwise first-order anatomy of the new remainder.  The four raw
channels are deliberately kept under one derivative: existing infrastructure
proves regularity and the derivative of their sum, without needing an
unjustified differentiability claim for every individual presentation. -/
theorem canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder_zero_eq_channelDerivative
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder M 0 q hqpos.le hq1 S =
      deriv
        (fun t : ℝ =>
          canonicalCompletedC3FixedCenterGreenProvenanceRealChannel (M + 1) t +
            canonicalCompletedC3FixedCenterOffDiagonalRealChannel (M + 1) t +
            canonicalCompletedC3FixedCenterReadoutResidualRealChannel (M + 1) t +
            canonicalCompletedC3FixedCenterTailCompletionRealChannel (M + 1) t) 0 +
        deriv canonicalCompletedC3FixedCenterGlobalOperatorRealBranch 0 := by
  rw [canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder_zero_eq_h0
      M q hqpos hq1 S,
    canonicalCompletedNativeLogDerivativeMoment_zero_eq_raw_plus_globalVariation,
    deriv_canonicalCompletedC3FixedCenterRawWronskianBranch_zero,
    ← deriv_canonicalCompletedC3FixedCenterFourRawRealChannels_zero (M + 1)]

/-- The archimedean term in the channel derivative is exactly the existing
xi-minus-chart replacement coefficient. -/
theorem canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder_zero_eq_rawChannels_add_chartReplacement
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder M 0 q hqpos.le hq1 S =
      deriv
        (fun t : ℝ =>
          canonicalCompletedC3FixedCenterGreenProvenanceRealChannel (M + 1) t +
            canonicalCompletedC3FixedCenterOffDiagonalRealChannel (M + 1) t +
            canonicalCompletedC3FixedCenterReadoutResidualRealChannel (M + 1) t +
            canonicalCompletedC3FixedCenterTailCompletionRealChannel (M + 1) t) 0 +
        canonicalCompletedC3ChartReplacementResponseTaylorCoefficient 1 := by
  rw [canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder_zero_eq_channelDerivative
      M q hqpos hq1 S,
    deriv_canonicalCompletedC3FixedCenterGlobalOperatorRealBranch_zero]

/-- The exact residual-square gate into which the new `Dreal_0` fits.  It is
an equivalence involving the dressed Gram and other retained quantities; it
does not assert that the remainder itself is a negative residual square. -/
theorem deriv_nonGreenRealCanonicalJetRemainder_zero_eq_dressedGram_re_iff_residualBalance
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder
        M 0 q hqpos.le hq1 S).re =
        (canonicalCompletedC3RealAxisPositiveKernel 0 0).re ↔
      (inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re -
        canonicalCompletedNativeLogDerivativeMoment 0 =
          -‖canonicalCompletedC3RealAxisResidualState 0‖ ^ 2 := by
  rw [canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder_zero_eq_h0
      M q hqpos hq1 S,
    ← deriv_canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator_zero (M + 1)]
  exact deriv_fixedCenterChannelSeparatedLedger_eq_dressedGram_re_iff_residualBalance (M + 1)

/-- The new real remainder derivative agrees with the complex derivative of
the old fixed-center channel ledger at the shifted cutoff.  This comparison
is valid only after the real-diagonal functional crosswalk above; it does not
differentiate the conjugate physical section termwise. -/
theorem canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder_zero_eq_fixedCenterLedgerDerivative
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder M 0 q hqpos.le hq1 S =
      deriv
        (canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator (M + 1)) 0 := by
  rw [canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder_zero_eq_h0
      M q hqpos hq1 S,
    ← deriv_canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator_zero (M + 1)]

/-! ## Canonical index zero with the channel remainder exposed -/

/-- The canonical zeroth coefficient is the two-term undressed Green
convolution plus the exact derivative of the four raw fixed-center channels
and the archimedean replacement branch. -/
theorem canonicalC3BracketTfvdSixAnalysisJetCoefficient_zero_eq_undressedGreen_add_channelDerivative
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisJetCoefficient M 0 q hqpos.le hq1 S =
      canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 1 *
          canonicalC3IndependentReflectedUndressedGreenJetCoefficient
            (M + 1) 0 q hqpos.le hq1 S 0 +
        canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 0 *
          canonicalC3IndependentReflectedUndressedGreenJetCoefficient
            (M + 1) 1 q hqpos.le hq1 S 0 +
        deriv
          (fun t : ℝ =>
            canonicalCompletedC3FixedCenterGreenProvenanceRealChannel (M + 1) t +
              canonicalCompletedC3FixedCenterOffDiagonalRealChannel (M + 1) t +
              canonicalCompletedC3FixedCenterReadoutResidualRealChannel (M + 1) t +
              canonicalCompletedC3FixedCenterTailCompletionRealChannel (M + 1) t) 0 +
          deriv canonicalCompletedC3FixedCenterGlobalOperatorRealBranch 0 := by
  rw [canonicalC3BracketTfvdSixAnalysisJetCoefficient_zero_eq_undressedGreen_convolution_add_realRemainder
      M q hqpos hq1 S,
    canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder_zero_eq_channelDerivative
      M q hqpos hq1 S]
  ring

/-- The same canonical zeroth coefficient with its two undressed Green jets
expanded over the fixed camera atlas.  The non-Green channels are intentionally
not camera-resolved in this investigation. -/
theorem canonicalC3BracketTfvdSixAnalysisJetCoefficient_zero_eq_cameraPairwise_undressedGreen_add_channelDerivative
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisJetCoefficient M 0 q hqpos.le hq1 S =
      canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 1 *
          (∑ directCamera ∈ canonicalFiniteCameraAtlas (M + 1),
            ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas (M + 1),
              canonicalC3CameraResolvedIndependentReflectedUndressedGreenJetCoefficient
                (M + 1) 0 q hqpos.le hq1 S 0 directCamera reflectedCamera) +
        canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 0 *
          (∑ directCamera ∈ canonicalFiniteCameraAtlas (M + 1),
            ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas (M + 1),
              canonicalC3CameraResolvedIndependentReflectedUndressedGreenJetCoefficient
                (M + 1) 1 q hqpos.le hq1 S 0 directCamera reflectedCamera) +
        deriv
          (fun t : ℝ =>
            canonicalCompletedC3FixedCenterGreenProvenanceRealChannel (M + 1) t +
              canonicalCompletedC3FixedCenterOffDiagonalRealChannel (M + 1) t +
              canonicalCompletedC3FixedCenterReadoutResidualRealChannel (M + 1) t +
              canonicalCompletedC3FixedCenterTailCompletionRealChannel (M + 1) t) 0 +
          deriv canonicalCompletedC3FixedCenterGlobalOperatorRealBranch 0 := by
  rw [canonicalC3BracketTfvdSixAnalysisJetCoefficient_zero_eq_undressedGreen_add_channelDerivative
    M q hqpos hq1 S,
    canonicalC3IndependentReflectedUndressedGreenJetCoefficient_eq_cameraPairwise_sum
      (M + 1) 0 q hqpos.le hq1 S 0,
    canonicalC3IndependentReflectedUndressedGreenJetCoefficient_eq_cameraPairwise_sum
      (M + 1) 1 q hqpos.le hq1 S 0]

/-- The corrected-chiral coefficient inherits the same zeroth-order channel
anatomy only after the six-analysis crosswalk has been established. -/
theorem canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_zero_eq_cameraPairwise_undressedGreen_add_channelDerivative
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M 0 =
      canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 1 *
          (∑ directCamera ∈ canonicalFiniteCameraAtlas (M + 1),
            ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas (M + 1),
              canonicalC3CameraResolvedIndependentReflectedUndressedGreenJetCoefficient
                (M + 1) 0 q hqpos.le hq1 S 0 directCamera reflectedCamera) +
        canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 0 *
          (∑ directCamera ∈ canonicalFiniteCameraAtlas (M + 1),
            ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas (M + 1),
              canonicalC3CameraResolvedIndependentReflectedUndressedGreenJetCoefficient
                (M + 1) 1 q hqpos.le hq1 S 0 directCamera reflectedCamera) +
        deriv
          (fun t : ℝ =>
            canonicalCompletedC3FixedCenterGreenProvenanceRealChannel (M + 1) t +
              canonicalCompletedC3FixedCenterOffDiagonalRealChannel (M + 1) t +
              canonicalCompletedC3FixedCenterReadoutResidualRealChannel (M + 1) t +
              canonicalCompletedC3FixedCenterTailCompletionRealChannel (M + 1) t) 0 +
          deriv canonicalCompletedC3FixedCenterGlobalOperatorRealBranch 0 := by
  rw [canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_sixAnalysisJet
    M 0 q hqpos hq1 S]
  exact canonicalC3BracketTfvdSixAnalysisJetCoefficient_zero_eq_cameraPairwise_undressedGreen_add_channelDerivative
    M q hqpos hq1 S

end

end CarrySelfAdjointOperator
