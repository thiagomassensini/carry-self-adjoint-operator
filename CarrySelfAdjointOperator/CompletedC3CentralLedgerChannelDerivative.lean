import CarrySelfAdjointOperator.CompletedC3CentralLedgerCollisionAudit
import CarrySelfAdjointOperator.CompletedC3AllOrderChartResponseCorrection
import Mathlib.Tactic

/-!
# Channel derivatives at the completed C3 central collision

The total central ledger derivative is already known to be `h₀`.  This file
separates that derivative into the two holomorphic blocks which exist before
the non-holomorphic finite Green channels are restricted to the real axis:

* the raw completed C3 Wronskian block;
* the archimedean `xi - chart` replacement block.

The radial finite Green channel is then restricted to the real height axis
and proved to vanish identically there.  Hence the raw central variation is
carried entirely by structural provenance/readout channels together with the
finite head--tail completion correction.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section

/-! ## The two normalized holomorphic blocks -/

/-- Common nonzero normalization used by the fixed-center completed ledger. -/
def canonicalCompletedC3FixedCenterLedgerNormalization (w : ℂ) : ℂ :=
  mixedHermitianWeight canonicalC3ChartFactorHeight w 0 *
    ((2 : ℂ) * conj (completedNativeOperatorCharacteristic 0) *
      completedNativeOperatorCharacteristic w)

/-- Raw C3 Wronskian contribution after the exact xi/chart/characteristic
normalization used by the completed ledger. -/
def canonicalCompletedC3FixedCenterRawWronskianBranch (w : ℂ) : ℂ :=
  mixedHermitianWeight nativeXiCompletionFactor w 0 *
      canonicalCompletedC3RawHeightMixedWronskian w 0 /
    canonicalCompletedC3FixedCenterLedgerNormalization w

/-- Independently retained archimedean/chart contribution with the same
normalization. -/
def canonicalCompletedC3FixedCenterArchimedeanBranch (w : ℂ) : ℂ :=
  canonicalCompletedC3ArchimedeanChartMixedChannel w 0 /
    canonicalCompletedC3FixedCenterLedgerNormalization w

/-- The explicit channel ledger is the sum of the raw C3 and archimedean
blocks.  This uses the exact finite head/structural/tail sewing and does not
differentiate or discard any subchannel. -/
theorem
    canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator_eq_raw_add_archimedean
    (M : ℕ) {w : ℂ}
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M w =
      canonicalCompletedC3FixedCenterRawWronskianBranch w +
        canonicalCompletedC3FixedCenterArchimedeanBranch w := by
  have hraw :=
    canonicalCompletedC3RawHeightMixedWronskian_eq_green_add_channels
      M hw zero_mem_completedNativeHeightDomain
  rw [greenForm_finiteC3GenuineBracket_twoParameter_eq_coefficient_mul_gram,
    c3RawGammaGram_eq_inner_completedPrefix,
    canonicalC3FiniteMixedHeightStructuralDefect_eq_channelSum] at hraw
  unfold canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator
    canonicalCompletedC3FixedCenterRawWronskianBranch
    canonicalCompletedC3FixedCenterArchimedeanBranch
    canonicalCompletedC3FixedCenterLedgerNormalization
  rw [hraw]
  ring

/-! ## Raw block as a normalized-response numerator -/

/-- Hermitian-polarized numerator of the raw completed C3 response with the
first leg fixed at the center. -/
def canonicalCompletedC3FixedCenterRawResponseNumerator (w : ℂ) : ℂ :=
  canonicalCompletedC3RawHeightNormalizedResponse w -
    conj (canonicalCompletedC3RawHeightNormalizedResponse 0)

/-- Pointwise cancellation of all nonzero product factors identifies the raw
Wronskian branch with the raw normalized-response numerator. -/
theorem canonicalCompletedC3FixedCenterRawWronskianBranch_eq_response
    {w : ℂ}
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hG : nativeHeightScalar w ≠ 0) :
    canonicalCompletedC3FixedCenterRawWronskianBranch w =
      canonicalCompletedC3FixedCenterRawResponseNumerator w := by
  have hzeroStrip : operatorHeightParameter (0 : ℂ) ∈ genuineCriticalStrip :=
    zero_mem_completedNativeHeightDomain
  have hchartW : canonicalC3ChartFactorHeight w ≠ 0 :=
    canonicalC3ChartFactorHeight_ne_zero hw
  have hchartZero : canonicalC3ChartFactorHeight 0 ≠ 0 :=
    canonicalC3ChartFactorHeight_ne_zero hzeroStrip
  have hxiW : nativeXiCompletionFactor w ≠ 0 :=
    nativeXiCompletionFactor_ne_zero hw
  have hxiZero : nativeXiCompletionFactor 0 ≠ 0 :=
    nativeXiCompletionFactor_ne_zero hzeroStrip
  have hGZero : nativeHeightScalar 0 ≠ 0 := nativeHeightScalar_zero_ne_zero
  have hG' :
      NativeCarrySpectralWeyl.Camera.nativeScalar
        (operatorHeightParameter w) ≠ 0 := by
    exact hG
  have hGZero' :
      NativeCarrySpectralWeyl.Camera.nativeScalar
        (operatorHeightParameter 0) ≠ 0 := by
    exact hGZero
  have hrawValueW :
      canonicalCompletedC3RawHeightValue w =
        canonicalC3ChartFactorHeight w * nativeHeightScalar w := by
    rw [canonicalCompletedC3RawHeightValue_eq_chart_mul_normalized hw,
      canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar
        hw]
  have hrawValueZero :
      canonicalCompletedC3RawHeightValue 0 =
        canonicalC3ChartFactorHeight 0 * nativeHeightScalar 0 := by
    rw [canonicalCompletedC3RawHeightValue_eq_chart_mul_normalized hzeroStrip,
      canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar
        hzeroStrip]
  have hrawW : canonicalCompletedC3RawHeightValue w ≠ 0 := by
    rw [hrawValueW]
    exact mul_ne_zero hchartW hG
  have hrawZero : canonicalCompletedC3RawHeightValue 0 ≠ 0 := by
    rw [hrawValueZero]
    exact mul_ne_zero hchartZero hGZero
  have hwronskian := completedGreenWronskian_eq_normalizedResponse_cross_mul
    canonicalCompletedC3RawHeightValue
    canonicalCompletedC3RawHeightCompanion w 0 hrawW hrawZero
  unfold canonicalCompletedC3FixedCenterRawWronskianBranch
    canonicalCompletedC3FixedCenterRawResponseNumerator
    canonicalCompletedC3FixedCenterLedgerNormalization
    canonicalCompletedC3RawHeightMixedWronskian
    canonicalCompletedC3RawHeightNormalizedResponse
    mixedHermitianWeight
  rw [hwronskian, hrawValueW, hrawValueZero]
  unfold completedNativeOperatorCharacteristic nativeHeightScalar
  simp only [map_mul]
  field_simp [hchartW, hchartZero, hxiW, hxiZero, hG', hGZero']

/-- The raw Wronskian branch agrees with the raw response numerator as a germ
at the Taylor center. -/
theorem canonicalCompletedC3FixedCenterRawWronskianBranch_eventuallyEq_response :
    canonicalCompletedC3FixedCenterRawWronskianBranch =ᶠ[nhds 0]
      canonicalCompletedC3FixedCenterRawResponseNumerator := by
  have hdomain :
      {w : ℂ | operatorHeightParameter w ∈ genuineCriticalStrip} ∈
        nhds 0 :=
    (hasDerivAt_operatorHeightParameter 0).continuousAt.preimage_mem_nhds
      (isOpen_genuineCriticalStrip.mem_nhds
        zero_mem_completedNativeHeightDomain)
  have hG : ∀ᶠ w : ℂ in nhds 0, nativeHeightScalar w ≠ 0 :=
    nativeHeightScalar_analyticAt_zero.continuousAt.eventually_ne
      nativeHeightScalar_zero_ne_zero
  filter_upwards [hdomain, hG] with w hw hG
  exact canonicalCompletedC3FixedCenterRawWronskianBranch_eq_response hw hG

/-- The derivative of the raw C3 ledger block is its first raw response
Taylor coefficient. -/
theorem deriv_canonicalCompletedC3FixedCenterRawWronskianBranch_zero :
    deriv canonicalCompletedC3FixedCenterRawWronskianBranch 0 =
      canonicalCompletedC3RawHeightResponseTaylorCoefficient 1 := by
  rw [canonicalCompletedC3FixedCenterRawWronskianBranch_eventuallyEq_response.deriv_eq]
  unfold canonicalCompletedC3FixedCenterRawResponseNumerator
    canonicalCompletedC3RawHeightResponseTaylorCoefficient
  rw [deriv_sub_const]
  simp [iteratedDeriv_one]

/-! ## The archimedean branch is exactly the chart replacement -/

/-- The archimedean branch is the complementary germ between the completed
and raw response numerators. -/
theorem canonicalCompletedC3FixedCenterArchimedeanBranch_eventuallyEq_replacement :
    canonicalCompletedC3FixedCenterArchimedeanBranch =ᶠ[nhds 0]
      (fun w : ℂ =>
        canonicalCompletedC3ChartReplacementNormalizedResponse w -
          conj (canonicalCompletedC3ChartReplacementNormalizedResponse 0)) := by
  have hledger :=
    canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_fixedCenter_eventuallyEq_response
      0
  have hchannels :
      (fun w : ℂ =>
        canonicalCompletedC3AllCutoffPolarizedLedgerNumerator 0 0 w) =ᶠ[nhds 0]
      (fun w : ℂ =>
        canonicalCompletedC3FixedCenterRawWronskianBranch w +
          canonicalCompletedC3FixedCenterArchimedeanBranch w) := by
    have hdomain :
        {w : ℂ | operatorHeightParameter w ∈ genuineCriticalStrip} ∈
          nhds 0 :=
      (hasDerivAt_operatorHeightParameter 0).continuousAt.preimage_mem_nhds
        (isOpen_genuineCriticalStrip.mem_nhds
          zero_mem_completedNativeHeightDomain)
    filter_upwards [hdomain] with w hw
    rw [← canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator_eq_ledger]
    exact
      canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator_eq_raw_add_archimedean
        0 hw
  have hcompleted :=
    completedNativeGreenNormalizedResponse_eventuallyEq_raw_add_chartReplacement
  have hraw :=
    canonicalCompletedC3FixedCenterRawWronskianBranch_eventuallyEq_response
  filter_upwards [hledger, hchannels, hcompleted, hraw] with w
      hledger hchannels hcompleted hraw
  unfold canonicalCompletedNativePolarizedResponseNumerator at hledger
  unfold canonicalCompletedC3FixedCenterRawResponseNumerator at hraw
  rw [hchannels, hraw] at hledger
  change
    canonicalCompletedC3RawHeightNormalizedResponse w -
          conj (canonicalCompletedC3RawHeightNormalizedResponse 0) +
        canonicalCompletedC3FixedCenterArchimedeanBranch w =
      completedGreenNormalizedResponse
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion w -
        conj (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion 0) at hledger
  simp only [Pi.add_apply] at hcompleted
  rw [hcompleted] at hledger
  have hcompletedZero :=
    completedNativeGreenNormalizedResponse_eventuallyEq_raw_add_chartReplacement.self_of_nhds
  simp only [Pi.add_apply] at hcompletedZero
  rw [hcompletedZero] at hledger
  simp only [map_add] at hledger
  linear_combination hledger

/-- The first variation of the archimedean ledger block is precisely the
first `xi - chart` replacement coefficient. -/
theorem deriv_canonicalCompletedC3FixedCenterArchimedeanBranch_zero :
    deriv canonicalCompletedC3FixedCenterArchimedeanBranch 0 =
      canonicalCompletedC3ChartReplacementResponseTaylorCoefficient 1 := by
  rw [canonicalCompletedC3FixedCenterArchimedeanBranch_eventuallyEq_replacement.deriv_eq]
  rw [deriv_sub_const]
  rw [canonicalCompletedC3ChartReplacementResponseTaylorCoefficient_eq_taylor]
  simp [iteratedDeriv_one]

/-- The two block derivatives recover the completed central moment with no
theta input. -/
theorem canonicalCompletedNativeLogDerivativeMoment_zero_eq_centralLedgerBlockDerivatives :
    (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) =
      deriv canonicalCompletedC3FixedCenterRawWronskianBranch 0 +
        deriv canonicalCompletedC3FixedCenterArchimedeanBranch 0 := by
  rw [deriv_canonicalCompletedC3FixedCenterRawWronskianBranch_zero,
    deriv_canonicalCompletedC3FixedCenterArchimedeanBranch_zero]
  exact canonicalCompletedNativeLogDerivativeMoment_zero_eq_raw_add_chartReplacement

/-! ## Radial channel on the real collision line -/

/-- The mixed radial coefficient vanishes identically when the moving
centered-height point is real and the other leg is fixed at zero. -/
@[simp] theorem canonicalC3MixedRadialCoefficient_operatorHeight_ofReal_zero
    (t : ℝ) :
    canonicalC3MixedRadialCoefficient
        (operatorHeightParameter (t : ℂ))
        (operatorHeightParameter 0) = 0 := by
  unfold canonicalC3MixedRadialCoefficient reflectedParameter
    criticalDisplacement operatorHeightParameter
  simp
  norm_num

/-- Therefore the entire finite radial Green contribution vanishes on the
real central-collision line, before any cutoff limit. -/
theorem canonicalCompletedC3FixedCenterFiniteRadialGreenChannel_ofReal_eq_zero
    (M : ℕ) (t : ℝ) :
    canonicalC3MixedRadialCoefficient
          (operatorHeightParameter (t : ℂ))
          (operatorHeightParameter 0) *
        inner ℂ
          (canonicalCompletedC3DirichletGradientPrefixState
            (operatorHeightParameter 0) (3 * M))
          (canonicalCompletedC3DirichletGradientPrefixState
            (reflectedParameter (operatorHeightParameter (t : ℂ))) (3 * M)) =
      0 := by
  rw [canonicalC3MixedRadialCoefficient_operatorHeight_ofReal_zero]
  simp

/-! ## The four surviving raw channels on the real axis -/

/-- Common multiplier of every raw C3 subchannel after completed ledger
normalization. -/
def canonicalCompletedC3FixedCenterRawChannelScale (w : ℂ) : ℂ :=
  mixedHermitianWeight nativeXiCompletionFactor w 0 /
    canonicalCompletedC3FixedCenterLedgerNormalization w

/-- Normalized Green-provenance channel on the real collision line. -/
def canonicalCompletedC3FixedCenterGreenProvenanceRealChannel
    (M : ℕ) (t : ℝ) : ℂ :=
  canonicalCompletedC3FixedCenterRawChannelScale (t : ℂ) *
    canonicalC3FiniteMixedHeightGreenProvenanceChannel M
      (operatorHeightParameter (t : ℂ)) (operatorHeightParameter 0)

/-- Normalized ordered off-diagonal channel on the real collision line. -/
def canonicalCompletedC3FixedCenterOffDiagonalRealChannel
    (M : ℕ) (t : ℝ) : ℂ :=
  canonicalCompletedC3FixedCenterRawChannelScale (t : ℂ) *
    canonicalC3FiniteMixedHeightOffDiagonalChannel M
      (operatorHeightParameter (t : ℂ)) (operatorHeightParameter 0)

/-- Normalized height-readout residual channel on the real collision line. -/
def canonicalCompletedC3FixedCenterReadoutResidualRealChannel
    (M : ℕ) (t : ℝ) : ℂ :=
  canonicalCompletedC3FixedCenterRawChannelScale (t : ℂ) *
    canonicalC3FiniteMixedHeightReadoutResidualChannel M
      (operatorHeightParameter (t : ℂ)) (operatorHeightParameter 0)

/-- Normalized finite head--tail completion channel on the real collision
line. -/
def canonicalCompletedC3FixedCenterTailCompletionRealChannel
    (M : ℕ) (t : ℝ) : ℂ :=
  canonicalCompletedC3FixedCenterRawChannelScale (t : ℂ) *
    canonicalC3MixedHeightTailCompletionDefect M (t : ℂ) 0

/-- The four nonradial channels reconstruct the raw Wronskian branch exactly
at every real height and every cutoff. -/
theorem canonicalCompletedC3FixedCenterRawWronskianBranch_ofReal_eq_fourChannels
    (M : ℕ) (t : ℝ) :
    canonicalCompletedC3FixedCenterRawWronskianBranch (t : ℂ) =
      canonicalCompletedC3FixedCenterGreenProvenanceRealChannel M t +
        canonicalCompletedC3FixedCenterOffDiagonalRealChannel M t +
        canonicalCompletedC3FixedCenterReadoutResidualRealChannel M t +
        canonicalCompletedC3FixedCenterTailCompletionRealChannel M t := by
  have htStrip :
      operatorHeightParameter (t : ℂ) ∈ genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter]
  have hraw :=
    canonicalCompletedC3RawHeightMixedWronskian_eq_green_add_channels
      M htStrip zero_mem_completedNativeHeightDomain
  rw [greenForm_finiteC3GenuineBracket_twoParameter_eq_coefficient_mul_gram,
    canonicalC3MixedRadialCoefficient_operatorHeight_ofReal_zero,
    zero_mul, zero_add,
    canonicalC3FiniteMixedHeightStructuralDefect_eq_channelSum] at hraw
  unfold canonicalCompletedC3FixedCenterRawWronskianBranch
  unfold
    canonicalCompletedC3FixedCenterGreenProvenanceRealChannel
    canonicalCompletedC3FixedCenterOffDiagonalRealChannel
    canonicalCompletedC3FixedCenterReadoutResidualRealChannel
    canonicalCompletedC3FixedCenterTailCompletionRealChannel
  unfold canonicalCompletedC3FixedCenterRawChannelScale
  rw [hraw]
  ring

/-- The raw branch is holomorphic at the center, even though its four finite
subchannels are naturally differentiated only after restriction to the real
height line. -/
theorem canonicalCompletedC3FixedCenterRawWronskianBranch_differentiableAt_zero :
    DifferentiableAt ℂ canonicalCompletedC3FixedCenterRawWronskianBranch 0 := by
  apply
    canonicalCompletedC3FixedCenterRawWronskianBranch_eventuallyEq_response.differentiableAt_iff.mpr
  unfold canonicalCompletedC3FixedCenterRawResponseNumerator
  have hraw : DifferentiableAt ℂ
      canonicalCompletedC3RawHeightNormalizedResponse 0 := by
    apply
      canonicalCompletedC3RawHeightNormalizedResponse_eventuallyEq_factors.differentiableAt_iff.mpr
    exact
      canonicalC3ChartFactorNormalizedResponse_analyticAt_zero.differentiableAt.add
        nativeHeightScalarNormalizedResponse_analyticAt_zero.differentiableAt
  exact hraw.sub (differentiableAt_const
    (c := conj (canonicalCompletedC3RawHeightNormalizedResponse 0)))

/-- Therefore the first real-axis variation of the four surviving raw
channels is exactly the first raw C3 response coefficient.  This theorem is
the precise finite-cutoff channel ledger to be split further. -/
theorem deriv_canonicalCompletedC3FixedCenterFourRawRealChannels_zero
    (M : ℕ) :
    deriv
        (fun t : ℝ =>
          canonicalCompletedC3FixedCenterGreenProvenanceRealChannel M t +
            canonicalCompletedC3FixedCenterOffDiagonalRealChannel M t +
            canonicalCompletedC3FixedCenterReadoutResidualRealChannel M t +
            canonicalCompletedC3FixedCenterTailCompletionRealChannel M t) 0 =
      canonicalCompletedC3RawHeightResponseTaylorCoefficient 1 := by
  rw [show
      (fun t : ℝ =>
        canonicalCompletedC3FixedCenterGreenProvenanceRealChannel M t +
          canonicalCompletedC3FixedCenterOffDiagonalRealChannel M t +
          canonicalCompletedC3FixedCenterReadoutResidualRealChannel M t +
          canonicalCompletedC3FixedCenterTailCompletionRealChannel M t) =
        (fun t : ℝ =>
          canonicalCompletedC3FixedCenterRawWronskianBranch (t : ℂ)) by
    funext t
    exact
      (canonicalCompletedC3FixedCenterRawWronskianBranch_ofReal_eq_fourChannels
        M t).symm]
  rw [deriv_comp_ofReal_eq
    canonicalCompletedC3FixedCenterRawWronskianBranch_differentiableAt_zero]
  simpa only [Complex.ofReal_zero] using
    deriv_canonicalCompletedC3FixedCenterRawWronskianBranch_zero

/-! ## Exact location of the residual-square balance -/

/-- The dressed central sewing is equivalent to one equality between the raw
TFVD-versus-raw-C3 mismatch and the archimedean replacement after subtracting
the retained residual square.  This separates completion curvature from the
finite structural/tail ledger without assigning either contribution by
definition. -/
theorem
    deriv_fixedCenterChannelSeparatedLedger_eq_dressedGram_re_iff_rawMismatch_eq_archimedean_sub_residual
    (M : ℕ) :
    (deriv
        (canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M) 0).re =
        (canonicalCompletedC3RealAxisPositiveKernel 0 0).re ↔
      (inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re -
          (canonicalCompletedC3RawHeightResponseTaylorCoefficient 1).re =
        (canonicalCompletedC3ChartReplacementResponseTaylorCoefficient 1).re -
          ‖canonicalCompletedC3RealAxisResidualState 0‖ ^ 2 := by
  rw [deriv_fixedCenterChannelSeparatedLedger_eq_dressedGram_re_iff_residualBalance]
  have hsplit := congrArg Complex.re
    canonicalCompletedNativeLogDerivativeMoment_zero_eq_raw_add_chartReplacement
  simp only [Complex.ofReal_re, Complex.add_re] at hsplit
  constructor <;> intro h <;> linarith

/-- The same balance with the archimedean replacement unfolded.  Thus the
term on the right is literally the xi-completion curvature minus the C3
chart curvature, followed by the retained residual-square correction. -/
theorem
    deriv_fixedCenterChannelSeparatedLedger_eq_dressedGram_re_iff_rawMismatch_eq_completionCurvature_sub_residual
    (M : ℕ) :
    (deriv
        (canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M) 0).re =
        (canonicalCompletedC3RealAxisPositiveKernel 0 0).re ↔
      (inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re -
          (canonicalCompletedC3RawHeightResponseTaylorCoefficient 1).re =
        (nativeXiCompletionResponseTaylorCoefficient 1 -
            canonicalC3ChartFactorResponseTaylorCoefficient 1).re -
          ‖canonicalCompletedC3RealAxisResidualState 0‖ ^ 2 := by
  simpa [canonicalCompletedC3ChartReplacementResponseTaylorCoefficient] using
    deriv_fixedCenterChannelSeparatedLedger_eq_dressedGram_re_iff_rawMismatch_eq_archimedean_sub_residual
      M

/-- Fully channel-read version of the same gate.  The first derivative on the
left is literally the sum of Green provenance, off-diagonal provenance,
height-readout residual, and head--tail completion.  The radial channel is
absent because it vanishes identically on the real collision line. -/
theorem
    deriv_fixedCenterChannelSeparatedLedger_eq_dressedGram_re_iff_fourRawChannelsMismatch
    (M : ℕ) :
    (deriv
        (canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M) 0).re =
        (canonicalCompletedC3RealAxisPositiveKernel 0 0).re ↔
      (inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re -
          (deriv
            (fun t : ℝ =>
              canonicalCompletedC3FixedCenterGreenProvenanceRealChannel M t +
                canonicalCompletedC3FixedCenterOffDiagonalRealChannel M t +
                canonicalCompletedC3FixedCenterReadoutResidualRealChannel M t +
                canonicalCompletedC3FixedCenterTailCompletionRealChannel M t)
            0).re =
        (deriv canonicalCompletedC3FixedCenterArchimedeanBranch 0).re -
          ‖canonicalCompletedC3RealAxisResidualState 0‖ ^ 2 := by
  rw [deriv_canonicalCompletedC3FixedCenterFourRawRealChannels_zero,
    deriv_canonicalCompletedC3FixedCenterArchimedeanBranch_zero]
  exact
    deriv_fixedCenterChannelSeparatedLedger_eq_dressedGram_re_iff_rawMismatch_eq_archimedean_sub_residual
      M

end

end CarrySelfAdjointOperator
