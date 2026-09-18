import CarrySelfAdjointOperator.CompletedNativeCorrectedCausalChiralGate
import CarrySelfAdjointOperator.CompletedNativeCorrectedChiralClockTower
import CarrySelfAdjointOperator.CompletedC3BracketTfvdGreenFactorization
import CarrySelfAdjointOperator.CompletedC3EnrichedSymplecticNoLeakBridge
import CarrySelfAdjointOperator.CompletedNativeTfvdWronskianMoments

/-!
# The corrected chiral first column from the actual TFVD six-channel jet

The existing all-cutoff kernel ledger is the concrete enriched boundary object
needed by the corrected chiral readout.  This file names its centered normalized
response and proves that its Taylor jet is the corrected coefficient before the
moment crosswalk is used.

The numerator retains all channels: the corrected Green port, three structural
coordinates (Green provenance, off-diagonal and readout residual), head--tail
completion and the archimedean chart.  Thus this is not a factorization through
the raw vertical trace alone.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open C3TraceDynamics
open Filter
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- The actual six-channel TFVD response.  Its numerator is the final readout
of the pre-existing lossless all-cutoff kernel ledger, so no residual channel is
discarded before normalization. -/
def canonicalC3BracketTfvdSixChannelNormalizedResponse
    (M : ℕ) (z : ℂ) : ℂ :=
  (canonicalCompletedC3AllCutoffKernelLedgerState (M + 1) z 0).finalReadout /
    (mixedHermitianWeight canonicalC3ChartFactorHeight z 0 *
      ((2 : ℂ) * completedNativeOperatorCharacteristic z *
        (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0)))

/-- At every regular point of the centered strip, the all-channel ledger
response is exactly the pre-existing completed TFVD response. -/
theorem canonicalC3BracketTfvdSixChannelNormalizedResponse_eq_response_of_nonzero
    (M : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hFz : completedNativeOperatorCharacteristic z ≠ 0) :
    canonicalC3BracketTfvdSixChannelNormalizedResponse M z =
      canonicalC3BracketTfvdNormalizedResponse M z := by
  have hzero : operatorHeightParameter 0 ∈ genuineCriticalStrip :=
    zero_mem_completedNativeHeightDomain
  have hchart :
      mixedHermitianWeight canonicalC3ChartFactorHeight z 0 ≠ 0 :=
    canonicalC3ChartMixedHermitianWeight_ne_zero hz hzero
  have hF0 : completedNativeOperatorCharacteristic 0 ≠ 0 :=
    completedNativeOperatorCharacteristic_zero_ne_zero
  have hden :
      (2 : ℂ) * completedNativeOperatorCharacteristic z *
          (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hFz)
      ((map_ne_zero (starRingEnd ℂ)).2 hF0)
  rw [canonicalC3BracketTfvdSixChannelNormalizedResponse,
    CanonicalCompletedC3AllCutoffKernelLedgerHilbert.finalReadout_eq_mixedChannels_finalReadout,
    canonicalCompletedC3AllCutoffKernelLedgerState_mixedChannels_eq,
    canonicalCompletedC3FiniteFNegFPrimeMixedChannels_finalReadout_eq_bracketTfvdWronskian
      (M + 1) hz hzero]
  unfold canonicalC3BracketTfvdNormalizedResponse
  field_simp [hchart, hden]

/-- The equality of six-channel and completed TFVD responses is a germ at the
center.  This is exactly the strength needed for every Taylor coefficient. -/
theorem canonicalC3BracketTfvdSixChannelNormalizedResponse_eventuallyEq_response
    (M : ℕ) :
    canonicalC3BracketTfvdSixChannelNormalizedResponse M =ᶠ[nhds 0]
      canonicalC3BracketTfvdNormalizedResponse M := by
  have hdomain : completedNativeHeightDomain ∈ nhds (0 : ℂ) :=
    isOpen_completedNativeHeightDomain.mem_nhds
      zero_mem_completedNativeHeightDomain
  have hnonzero : ∀ᶠ z in nhds (0 : ℂ),
      completedNativeOperatorCharacteristic z ≠ 0 :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero
  filter_upwards [hdomain, hnonzero] with z hz hFz
  exact canonicalC3BracketTfvdSixChannelNormalizedResponse_eq_response_of_nonzero M hz hFz

/-- All corrected causal/chiral coefficients are the central jet of the
actual TFVD ledger.  The statement is entirely pre-moment. -/
theorem canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_sixChannelJet
    (M p : ℕ) :
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p =
      iteratedDeriv (p + 1)
        (canonicalC3BracketTfvdSixChannelNormalizedResponse M) 0 /
          (p + 1).factorial := by
  calc
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p =
        canonicalC3BracketTfvdResponseTaylorCoefficient M (p + 1) := by
      rw [canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_response,
        canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient_eq_completed,
        ← canonicalC3BracketTfvdResponseTaylorCoefficient_eq_completed]
    _ = iteratedDeriv (p + 1)
          (canonicalC3BracketTfvdSixChannelNormalizedResponse M) 0 /
            (p + 1).factorial := by
      unfold canonicalC3BracketTfvdResponseTaylorCoefficient
      rw [← Filter.EventuallyEq.iteratedDeriv_eq (p + 1)
        (canonicalC3BracketTfvdSixChannelNormalizedResponse_eventuallyEq_response M)]

/-- First-column index zero is the first central jet of the six-channel
ledger; no moment has entered this equality. -/
theorem canonicalC3BracketTfvdSixChannelJet_zero
    (M : ℕ) :
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M 0 =
      iteratedDeriv 1 (canonicalC3BracketTfvdSixChannelNormalizedResponse M) 0 := by
  simpa using canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_sixChannelJet M 0

/-- The index-one first-column entry vanishes by the even parity of the
completed normalized response, transported through the six-channel germ. -/
theorem canonicalC3BracketTfvdSixChannelJet_one_eq_zero
    (M : ℕ) :
    iteratedDeriv 2 (canonicalC3BracketTfvdSixChannelNormalizedResponse M) 0 /
        (2 : ℕ).factorial = 0 := by
  calc
    iteratedDeriv 2 (canonicalC3BracketTfvdSixChannelNormalizedResponse M) 0 /
        (2 : ℕ).factorial =
        canonicalC3BracketTfvdResponseTaylorCoefficient M 2 := by
      unfold canonicalC3BracketTfvdResponseTaylorCoefficient
      rw [Filter.EventuallyEq.iteratedDeriv_eq 2
        (canonicalC3BracketTfvdSixChannelNormalizedResponse_eventuallyEq_response M)]
    _ = completedNativeGreenResponseTaylorCoefficient 2 :=
      canonicalC3BracketTfvdResponseTaylorCoefficient_eq_completed M 2
    _ = 0 := by
      simpa using completedNativeGreenResponseTaylorCoefficient_even_eq_zero 1

/-- First-column index two is the third central jet of the six-channel ledger;
again this equality precedes moment recognition. -/
theorem canonicalC3BracketTfvdSixChannelJet_two
    (M : ℕ) :
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M 2 =
      iteratedDeriv 3 (canonicalC3BracketTfvdSixChannelNormalizedResponse M) 0 /
        (3 : ℕ).factorial := by
  simpa using canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_sixChannelJet M 2

/-- Moment recognition for the zeroth entry is deliberately downstream of the
geometric jet theorem. -/
theorem canonicalC3BracketTfvdSixChannelJet_zero_eq_canonicalMoment
    (M : ℕ) :
    iteratedDeriv 1 (canonicalC3BracketTfvdSixChannelNormalizedResponse M) 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [← canonicalC3BracketTfvdSixChannelJet_zero]
  simpa using canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_odd_eq_canonicalMoment M 0

/-- Moment recognition for the second entry is likewise downstream of the
geometric jet theorem. -/
theorem canonicalC3BracketTfvdSixChannelJet_two_eq_canonicalMoment
    (M : ℕ) :
    iteratedDeriv 3 (canonicalC3BracketTfvdSixChannelNormalizedResponse M) 0 /
        (3 : ℕ).factorial =
      (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) := by
  rw [← canonicalC3BracketTfvdSixChannelJet_two]
  simpa using canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_odd_eq_canonicalMoment M 1

/-! ## The six vertical TFVD sources of the structural ledger -/

/-- Six lossless finite TFVD analyses: ordinary and log-jet vertical states at
`z`, at `w`, and at the reflected `z`.  This is the honest source domain for
the structural channels; a single pointwise raw trace would not retain it. -/
abbrev CanonicalC3AllCutoffMixedSourceTfvdAnalysisData
    (S : Finset NativeGpreBoundaryContext) :=
  (NativeGpreFiniteTfvdAnalysisCarrier S × NativeGpreFiniteTfvdAnalysisCarrier S) ×
    ((NativeGpreFiniteTfvdAnalysisCarrier S × NativeGpreFiniteTfvdAnalysisCarrier S) ×
      (NativeGpreFiniteTfvdAnalysisCarrier S × NativeGpreFiniteTfvdAnalysisCarrier S))

/-- Analyze all six vertical source states without combining value, log-jet,
direct, or reflected provenance. -/
def canonicalC3AllCutoffMixedSourceTfvdAnalysis
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (source : CanonicalC3AllCutoffMixedSourceHilbert) :
    CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S :=
  ((nativeGpreFiniteTfvdAnalysis q S source.zSource.1,
      nativeGpreFiniteTfvdAnalysis q S source.zSource.2),
    ((nativeGpreFiniteTfvdAnalysis q S source.wSource.1,
        nativeGpreFiniteTfvdAnalysis q S source.wSource.2),
      (nativeGpreFiniteTfvdAnalysis q S source.reflectedZSource.1,
        nativeGpreFiniteTfvdAnalysis q S source.reflectedZSource.2)))

/-- Reconstruct the three paired sources from their six TFVD analyses. -/
def canonicalC3AllCutoffMixedSourceTfvdReconstruction
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    CanonicalC3AllCutoffMixedSourceHilbert :=
  WithLp.toLp 2
    ((nativeGpreFiniteTfvdReconstruction q hq0 hq1 S data.1.1,
        nativeGpreFiniteTfvdReconstruction q hq0 hq1 S data.1.2),
      WithLp.toLp 2
        ((nativeGpreFiniteTfvdReconstruction q hq0 hq1 S data.2.1.1,
            nativeGpreFiniteTfvdReconstruction q hq0 hq1 S data.2.1.2),
          (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S data.2.2.1,
            nativeGpreFiniteTfvdReconstruction q hq0 hq1 S data.2.2.2)))

/-- The sixfold TFVD analysis is lossless on the complete mixed source. -/
theorem canonicalC3AllCutoffMixedSourceTfvdReconstruction_analysis
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (source : CanonicalC3AllCutoffMixedSourceHilbert) :
    canonicalC3AllCutoffMixedSourceTfvdReconstruction q hqpos.le hq1 S
      (canonicalC3AllCutoffMixedSourceTfvdAnalysis q S source) = source := by
  change
    WithLp.toLp 2
    ((nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
          (nativeGpreFiniteTfvdAnalysis q S source.zSource.1),
        nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
          (nativeGpreFiniteTfvdAnalysis q S source.zSource.2)),
      WithLp.toLp 2
        ((nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
            (nativeGpreFiniteTfvdAnalysis q S source.wSource.1),
          nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
            (nativeGpreFiniteTfvdAnalysis q S source.wSource.2)),
        (nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
            (nativeGpreFiniteTfvdAnalysis q S source.reflectedZSource.1),
          nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
            (nativeGpreFiniteTfvdAnalysis q S source.reflectedZSource.2)))) = source
  rw [nativeGpreFiniteTfvdReconstruction_analysis q hqpos hq1 S source.zSource.1,
    nativeGpreFiniteTfvdReconstruction_analysis q hqpos hq1 S source.zSource.2,
    nativeGpreFiniteTfvdReconstruction_analysis q hqpos hq1 S source.wSource.1,
    nativeGpreFiniteTfvdReconstruction_analysis q hqpos hq1 S source.wSource.2,
    nativeGpreFiniteTfvdReconstruction_analysis q hqpos hq1 S source.reflectedZSource.1,
    nativeGpreFiniteTfvdReconstruction_analysis q hqpos hq1 S source.reflectedZSource.2]
  rfl

/-- The structural triple as a functional of the six TFVD analyses.  Its
definition reconstructs first, precisely so all bracket/port cross terms and
provenance remain available to the pre-existing structural readout. -/
def canonicalC3AllCutoffMixedSourceTfvdStructuralReadout
    (M : ℕ) (directParameter reflectedParameter : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    CanonicalC3MixedStructuralChannelHilbert :=
  CanonicalC3AllCutoffMixedSourceHilbert.structuralReadout M
    directParameter reflectedParameter
    (canonicalC3AllCutoffMixedSourceTfvdReconstruction q hq0 hq1 S data)

/-- On analyzed data this is exactly the pre-existing source structural
readout, not an approximation or a new residual ansatz. -/
theorem canonicalC3AllCutoffMixedSourceTfvdStructuralReadout_analysis
    (M : ℕ) (directParameter reflectedParameter : ℂ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (source : CanonicalC3AllCutoffMixedSourceHilbert) :
    canonicalC3AllCutoffMixedSourceTfvdStructuralReadout M
        directParameter reflectedParameter q hqpos.le hq1 S
        (canonicalC3AllCutoffMixedSourceTfvdAnalysis q S source) =
      CanonicalC3AllCutoffMixedSourceHilbert.structuralReadout M
        directParameter reflectedParameter source := by
  unfold canonicalC3AllCutoffMixedSourceTfvdStructuralReadout
  rw [canonicalC3AllCutoffMixedSourceTfvdReconstruction_analysis q hqpos hq1 S source]

/-- For the canonical three-prefix source, the structural triple recovered
from six TFVD analyses is the ledger's exact provenance/off-diagonal/residual
coordinate. -/
theorem canonicalC3AllCutoffMixedSourceTfvdStructuralReadout_canonicalPrefix
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3AllCutoffMixedSourceTfvdStructuralReadout M
        w (reflectedParameter z) q hqpos.le hq1 S
        (canonicalC3AllCutoffMixedSourceTfvdAnalysis q S
          (canonicalC3AllCutoffMixedSourcePrefixState M z w)) =
      canonicalC3FiniteMixedHeightStructuralChannelState M z w := by
  rw [canonicalC3AllCutoffMixedSourceTfvdStructuralReadout_analysis
      M w (reflectedParameter z) q hqpos hq1 S
        (canonicalC3AllCutoffMixedSourcePrefixState M z w),
    canonicalC3AllCutoffMixedSourcePrefixState_structuralReadout_eq]

/-- The first recovered structural coordinate is exactly the Green-provenance
channel of the finite kernel ledger. -/
theorem canonicalC3AllCutoffMixedSourceTfvd_greenProvenance_canonicalPrefix
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (canonicalC3AllCutoffMixedSourceTfvdStructuralReadout M
        w (reflectedParameter z) q hqpos.le hq1 S
        (canonicalC3AllCutoffMixedSourceTfvdAnalysis q S
          (canonicalC3AllCutoffMixedSourcePrefixState M z w))).fst =
      canonicalC3FiniteMixedHeightGreenProvenanceChannel M z w := by
  rw [canonicalC3AllCutoffMixedSourceTfvdStructuralReadout_canonicalPrefix
    M z w q hqpos hq1 S]
  rfl

/-- The second recovered structural coordinate is exactly the retained
off-diagonal cross channel. -/
theorem canonicalC3AllCutoffMixedSourceTfvd_offDiagonal_canonicalPrefix
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (canonicalC3AllCutoffMixedSourceTfvdStructuralReadout M
        w (reflectedParameter z) q hqpos.le hq1 S
        (canonicalC3AllCutoffMixedSourceTfvdAnalysis q S
          (canonicalC3AllCutoffMixedSourcePrefixState M z w))).snd.fst =
      canonicalC3FiniteMixedHeightOffDiagonalChannel M z w := by
  rw [canonicalC3AllCutoffMixedSourceTfvdStructuralReadout_canonicalPrefix
    M z w q hqpos hq1 S]
  rfl

/-- The third recovered structural coordinate is exactly the retained local
readout residual. -/
theorem canonicalC3AllCutoffMixedSourceTfvd_readoutResidual_canonicalPrefix
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (canonicalC3AllCutoffMixedSourceTfvdStructuralReadout M
        w (reflectedParameter z) q hqpos.le hq1 S
        (canonicalC3AllCutoffMixedSourceTfvdAnalysis q S
          (canonicalC3AllCutoffMixedSourcePrefixState M z w))).snd.snd =
      canonicalC3FiniteMixedHeightReadoutResidualChannel M z w := by
  rw [canonicalC3AllCutoffMixedSourceTfvdStructuralReadout_canonicalPrefix
    M z w q hqpos hq1 S]
  rfl

/-- The direct Green port is a functional of the same six lossless TFVD
analyses: reconstruct the `w` source and take its existing Green port. -/
def canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort
    (M : ℕ) (_z w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    FiniteC3GreenPortCarrier (3 * M) :=
  CanonicalC3AllCutoffMixedSourceHilbert.greenPort (3 * M) w
    (canonicalC3AllCutoffMixedSourceTfvdReconstruction q hq0 hq1 S data).wSource

/-- The reflected Green port is recovered from the reflected `z` source in
the same six-analysis carrier. -/
def canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort
    (M : ℕ) (z _w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    FiniteC3GreenPortCarrier (3 * M) :=
  CanonicalC3AllCutoffMixedSourceHilbert.greenPort (3 * M)
    (reflectedParameter z)
    (canonicalC3AllCutoffMixedSourceTfvdReconstruction q hq0 hq1 S data).reflectedZSource

/-- On the canonical source, the direct recovered port is the established
Genuine bracket Green boundary pair. -/
theorem canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort_canonicalPrefix
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort M z w q hqpos.le hq1 S
        (canonicalC3AllCutoffMixedSourceTfvdAnalysis q S
          (canonicalC3AllCutoffMixedSourcePrefixState M z w)) =
      finiteC3GenuineBracketGreenBoundaryPair (3 * M) w := by
  unfold canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort
  rw [canonicalC3AllCutoffMixedSourceTfvdReconstruction_analysis q hqpos hq1 S
      (canonicalC3AllCutoffMixedSourcePrefixState M z w),
    canonicalC3AllCutoffMixedSourcePrefixState_wSource,
    canonicalC3AllCutoffGreenPort_prefix_eq]

/-- On the canonical source, the reflected recovered port is the established
Genuine bracket Green boundary pair at the reflected parameter. -/
theorem canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort_canonicalPrefix
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort M z w q hqpos.le hq1 S
        (canonicalC3AllCutoffMixedSourceTfvdAnalysis q S
          (canonicalC3AllCutoffMixedSourcePrefixState M z w)) =
      finiteC3GenuineBracketGreenBoundaryPair (3 * M) (reflectedParameter z) := by
  unfold canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort
  rw [canonicalC3AllCutoffMixedSourceTfvdReconstruction_analysis q hqpos hq1 S
      (canonicalC3AllCutoffMixedSourcePrefixState M z w),
    canonicalC3AllCutoffMixedSourcePrefixState_reflectedZSource,
    canonicalC3AllCutoffGreenPort_prefix_eq]

/-- The corrected causal boundary pairing itself is a Green functional of
the recovered direct and reflected TFVD ports. -/
def canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) : ℂ :=
  greenForm (𝕜 := ℂ)
    (canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort M z w q hq0 hq1 S data)
    (canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort M z w q hq0 hq1 S data)

/-- Exact radial seam: on canonical analyzed data, the Green form of the two
recovered ports is the pre-existing corrected TFVD boundary.  The three
structural channels above remain separate; this theorem does not absorb them. -/
theorem canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary_canonicalPrefix
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary M z w q hqpos.le hq1 S
        (canonicalC3AllCutoffMixedSourceTfvdAnalysis q S
          (canonicalC3AllCutoffMixedSourcePrefixState M z w)) =
      canonicalC3BracketTfvdMixedCorrectedBoundary M z w := by
  unfold canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary
  rw [canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort_canonicalPrefix
      M z w q hqpos hq1 S,
    canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort_canonicalPrefix
      M z w q hqpos hq1 S]
  calc
    greenForm (𝕜 := ℂ)
        (finiteC3GenuineBracketGreenBoundaryPair (3 * M) w)
        (finiteC3GenuineBracketGreenBoundaryPair
          (3 * M) (reflectedParameter z)) =
        canonicalC3BracketTfvdMixedGreenReadout M z w := by
      rw [Nat.mul_comm 3 M]
      exact (canonicalC3BracketTfvdMixedGreenReadout_eq_bracketGreen M z w).symm
    _ = canonicalC3BracketTfvdMixedCorrectedBoundary M z w :=
      (canonicalC3BracketTfvdMixedCorrectedBoundary_eq_greenReadout M z w).symm

/-- The recovered corrected boundary at the height parameters is exactly the
radial complex coordinate of the canonical all-cutoff ledger at `(z,w)`. -/
theorem canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary_canonicalPrefix_eq_ledgerRadial
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary M
        (operatorHeightParameter z) (operatorHeightParameter w) q hqpos.le hq1 S
        (canonicalC3AllCutoffMixedSourceTfvdAnalysis q S
          (canonicalC3AllCutoffMixedSourcePrefixState M
            (operatorHeightParameter z) (operatorHeightParameter w))) =
      (canonicalCompletedC3AllCutoffKernelLedgerState M z w).radialComplexReadout := by
  rw [canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary_canonicalPrefix
      M (operatorHeightParameter z) (operatorHeightParameter w) q hqpos hq1 S,
    canonicalC3BracketTfvdMixedCorrectedBoundary_eq_greenReadout,
    canonicalC3BracketTfvdMixedGreenReadout_eq_bracketGreen]
  symm
  rw [canonicalCompletedC3AllCutoffKernelLedgerState_radial_eq_greenForm,
    Nat.mul_comm M 3]

/-- The full completed causal/chiral readout as a functional of six enriched
TFVD analyses plus the retained scalar completion coordinates.  The input
data supplies the lossless ordinary/log-jet source; `z,w` retain the global
tail, xi-weight, and archimedean chart provenance. -/
def canonicalC3AllCutoffMixedSourceTfvdFinalReadout
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) : ℂ :=
  let structural := canonicalC3AllCutoffMixedSourceTfvdStructuralReadout M
    (operatorHeightParameter w) (reflectedParameter (operatorHeightParameter z))
    q hq0 hq1 S data
  mixedHermitianWeight nativeXiCompletionFactor z w *
      (canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary M
          (operatorHeightParameter z) (operatorHeightParameter w)
          q hq0 hq1 S data +
        canonicalC3MixedStructuralScalarReadout structural +
        canonicalC3MixedHeightTailCompletionDefect M z w) +
    canonicalCompletedC3ArchimedeanChartMixedChannel z w

/-- At canonical data, the six-analysis functional is exactly the final
readout of the pre-existing all-cutoff kernel ledger.  This is the complete
ports-to-corrected-carrier seam: radial port, all cross/provenance channels,
tail, xi weight, and chart are still explicit. -/
theorem canonicalC3AllCutoffMixedSourceTfvdFinalReadout_canonicalPrefix
    (M : ℕ) (z w : ℂ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3AllCutoffMixedSourceTfvdFinalReadout M z w q hqpos.le hq1 S
        (canonicalC3AllCutoffMixedSourceTfvdAnalysis q S
          (canonicalC3AllCutoffMixedSourcePrefixState M
            (operatorHeightParameter z) (operatorHeightParameter w))) =
      (canonicalCompletedC3AllCutoffKernelLedgerState M z w).finalReadout := by
  unfold canonicalC3AllCutoffMixedSourceTfvdFinalReadout
  rw [canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary_canonicalPrefix_eq_ledgerRadial
      M z w q hqpos hq1 S,
    canonicalC3AllCutoffMixedSourceTfvdStructuralReadout_canonicalPrefix
      M (operatorHeightParameter z) (operatorHeightParameter w) q hqpos hq1 S,
    CanonicalCompletedC3AllCutoffKernelLedgerHilbert.finalReadout,
    CanonicalCompletedC3AllCutoffKernelLedgerHilbert.rawReadout,
    canonicalCompletedC3AllCutoffKernelLedgerState_structural,
    canonicalCompletedC3AllCutoffKernelLedgerState_tail,
    canonicalCompletedC3AllCutoffKernelLedgerState_xiWeight,
    canonicalCompletedC3AllCutoffKernelLedgerState_archimedeanChart]

/-! ## First column as the jet of the six-analysis TFVD functional -/

/-- Centered normalized response obtained directly from the six analyzed
TFVD sources.  Its numerator is the complete corrected carrier reconstructed
by `canonicalC3AllCutoffMixedSourceTfvdFinalReadout`, not the raw trace. -/
def canonicalC3BracketTfvdSixAnalysisNormalizedResponse
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (z : ℂ) : ℂ :=
  canonicalC3AllCutoffMixedSourceTfvdFinalReadout (M + 1) z 0 q hq0 hq1 S
      (canonicalC3AllCutoffMixedSourceTfvdAnalysis q S
        (canonicalC3AllCutoffMixedSourcePrefixState (M + 1)
          (operatorHeightParameter z) (operatorHeightParameter 0))) /
    (mixedHermitianWeight canonicalC3ChartFactorHeight z 0 *
      ((2 : ℂ) * completedNativeOperatorCharacteristic z *
        (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0)))

/-- The six-analysis normalized response is pointwise the pre-existing
six-channel response.  Thus its equality is stronger than the central germ
needed below, and is obtained entirely from TFVD reconstruction. -/
theorem canonicalC3BracketTfvdSixAnalysisNormalizedResponse_eq_sixChannel
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hqpos.le hq1 S =
      canonicalC3BracketTfvdSixChannelNormalizedResponse M := by
  funext z
  unfold canonicalC3BracketTfvdSixAnalysisNormalizedResponse
    canonicalC3BracketTfvdSixChannelNormalizedResponse
  rw [canonicalC3AllCutoffMixedSourceTfvdFinalReadout_canonicalPrefix
    (M + 1) z 0 q hqpos hq1 S]

/-- The sought all-order port/boundary functional: take the central jet only
after the six TFVD analyses have been reassembled into the corrected carrier.
It is therefore a functional of bracket, ports, and their retained
provenance—not a definition using the log-derivative moments. -/
def canonicalC3BracketTfvdSixAnalysisJetCoefficient
    (M p : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) : ℂ :=
  iteratedDeriv (p + 1)
    (canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hq0 hq1 S) 0 /
      (p + 1).factorial

/-- All corrected causal/chiral first-column coefficients are read from the
six-analysis TFVD functional.  This is the all-order `PORTS -> CORRECTED
CHIRAL FIRST COLUMN` identity, before invoking the moment crosswalk. -/
theorem canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_sixAnalysisJet
    (M p : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p =
      canonicalC3BracketTfvdSixAnalysisJetCoefficient M p q hqpos.le hq1 S := by
  unfold canonicalC3BracketTfvdSixAnalysisJetCoefficient
  rw [canonicalC3BracketTfvdSixAnalysisNormalizedResponse_eq_sixChannel
    M q hqpos hq1 S]
  exact canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_sixChannelJet M p

/-- Low-order geometric calculation, index zero: the first jet of the
six-analysis carrier is the corrected coefficient. -/
theorem canonicalC3BracketTfvdSixAnalysisJet_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisJetCoefficient M 0 q hqpos.le hq1 S =
      canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M 0 := by
  exact (canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_sixAnalysisJet
    M 0 q hqpos hq1 S).symm

/-- Low-order geometric calculation, index one: parity kills the second jet
of the full six-analysis corrected carrier. -/
theorem canonicalC3BracketTfvdSixAnalysisJet_one_eq_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisJetCoefficient M 1 q hqpos.le hq1 S = 0 := by
  unfold canonicalC3BracketTfvdSixAnalysisJetCoefficient
  rw [canonicalC3BracketTfvdSixAnalysisNormalizedResponse_eq_sixChannel
    M q hqpos hq1 S]
  exact canonicalC3BracketTfvdSixChannelJet_one_eq_zero M

/-- Low-order geometric calculation, index two: the third jet of the
six-analysis carrier is the corrected coefficient. -/
theorem canonicalC3BracketTfvdSixAnalysisJet_two
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisJetCoefficient M 2 q hqpos.le hq1 S =
      canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M 2 := by
  exact (canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_sixAnalysisJet
    M 2 q hqpos hq1 S).symm

/-- Moment recognition for index zero is strictly downstream of the
geometric six-analysis identity. -/
theorem canonicalC3BracketTfvdSixAnalysisJet_zero_eq_canonicalMoment
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisJetCoefficient M 0 q hqpos.le hq1 S =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [canonicalC3BracketTfvdSixAnalysisJet_zero M q hqpos hq1 S]
  simpa using canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_odd_eq_canonicalMoment M 0

/-- Moment recognition for index two is likewise downstream of the full
port-plus-cross-channel geometric calculation. -/
theorem canonicalC3BracketTfvdSixAnalysisJet_two_eq_canonicalMoment
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisJetCoefficient M 2 q hqpos.le hq1 S =
      (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) := by
  rw [canonicalC3BracketTfvdSixAnalysisJet_two M q hqpos hq1 S]
  simpa using canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_odd_eq_canonicalMoment M 1

/-! ## Exact remaining material-clock interface -/

/-- A seeded clock atlas has corrected boundary transport as soon as its first
column is read by the six-analysis TFVD jet.  This theorem isolates the sole
remaining material identification; the right-hand side is geometric and
pre-moment. -/
theorem seededClockAtlas_hasCorrectedNativeChiralBoundaryTransport_of_sixAnalysisJet
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (hfirstColumn : ∀ p : ℕ,
      seededClockAtlasCoefficient block p 0 =
        canonicalC3BracketTfvdSixAnalysisJetCoefficient M p q hqpos.le hq1 S) :
    HasCorrectedNativeChiralBoundaryTransport M
      (seededClockAtlasCoefficient block) := by
  intro p
  exact (hfirstColumn p).trans
    (canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_sixAnalysisJet
      M p q hqpos hq1 S).symm

/-- Via the already-proved corrected-clock equivalence, a material
first-column identification with the six-analysis jet immediately gives the
original same-edge Green-to-clock boundary transport. -/
theorem seededClockAtlas_sameEdgeTransport_of_sixAnalysisJet
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (hfirstColumn : ∀ p : ℕ,
      seededClockAtlasCoefficient block p 0 =
        canonicalC3BracketTfvdSixAnalysisJetCoefficient M p q hqpos.le hq1 S) :
    HasSameEdgeGreenToClockBoundaryTransport M block := by
  exact seededClockAtlas_sameEdgeTransport_of_hasCorrectedNativeChiralBoundaryTransport
    M block
    (seededClockAtlas_hasCorrectedNativeChiralBoundaryTransport_of_sixAnalysisJet
      M block q hqpos hq1 S hfirstColumn)

end

end CarrySelfAdjointOperator
