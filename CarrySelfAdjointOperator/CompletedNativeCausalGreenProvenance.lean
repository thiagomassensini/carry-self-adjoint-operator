import CarrySelfAdjointOperator.CompletedNativeProjectionEnergyIntertwining
import CarrySelfAdjointOperator.CompletedC3DirichletGradientBracketSource
import CarrySelfAdjointOperator.CompletedC3CausalGreenGramSewing
import CarrySelfAdjointOperator.CompletedNativeTfvdGreenMomentGramBridge
import CarrySelfAdjointOperator.CompletedNativeHilbertTraceGlueWronskian
import CarrySelfAdjointOperator.CompletedNativeReturnMetricReadoutCrosswalk
import CarrySelfAdjointOperator.CompletedNativeCentralCarryAtlasEnergy
import CarrySelfAdjointOperator.CompletedNativePolarizedSameEdgeGreenGramBridge
import CarrySelfAdjointOperator.CompletedC3FullWronskianPolarization
import CarrySelfAdjointOperator.BR2CausalGreenResponseTransport
import CarrySelfAdjointOperator.ProjectiveValveCarryEnergyFrontier
import Mathlib.Tactic

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Camera
open FiniteNativeCarryOperator.Camera
open Filter

noncomputable section

/-!
This file records the causal Green provenance chain before moments, Hankel
matrices, or Jacobi coordinates are introduced.

The key object is the native causal response together with its boundary
return. The exact reconstruction identity says that their sum is the
original completed gradient state. The pair-to-sum readout therefore gives
the same polarized energy, while the source equation identifies the causal
response with the native incidence source. None of these statements uses a
moment kernel or a spectral factorization.
-/

theorem canonicalCompletedC3CausalGreenBoundarySum_state
    {base : ℕ} (hbase : IsSupported base)
    {s : ℂ} (hs : 0 < s.re) :
    canonicalCompletedC3CausalGreenBoundarySum
        (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
          hbase s hs) =
      canonicalCompletedC3DirichletGradientState s hs := by
  rw [canonicalCompletedC3CausalGreenBoundarySum_apply]
  exact canonicalCompletedC3DirichletGradientCausalGreenBoundaryState_sum
    hbase s hs

theorem canonicalCompletedC3CausalGreenBoundarySum_inner_eq_nativeState_inner
    {base : ℕ} (hbase : IsSupported base)
    {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) :
    inner ℂ
        (canonicalCompletedC3CausalGreenBoundarySum
          (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
            hbase s hs))
        (canonicalCompletedC3CausalGreenBoundarySum
          (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
            hbase t ht)) =
      inner ℂ
        (canonicalCompletedC3DirichletGradientState s hs)
        (canonicalCompletedC3DirichletGradientState t ht) := by
  rw [canonicalCompletedC3CausalGreenBoundarySum_state hbase hs,
    canonicalCompletedC3CausalGreenBoundarySum_state hbase ht]

theorem canonicalCompletedC3CausalGreenBoundarySum_adjointSquare_eq_nativeState_inner
    {base : ℕ} (hbase : IsSupported base)
    {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) :
    inner ℂ
        (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
          hbase s hs)
        ((canonicalCompletedC3CausalGreenBoundarySum.adjoint)
          (canonicalCompletedC3CausalGreenBoundarySum
            (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
              hbase t ht))) =
      inner ℂ
        (canonicalCompletedC3DirichletGradientState s hs)
        (canonicalCompletedC3DirichletGradientState t ht) := by
  calc
    inner ℂ
          (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
            hbase s hs)
          ((canonicalCompletedC3CausalGreenBoundarySum.adjoint)
            (canonicalCompletedC3CausalGreenBoundarySum
              (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
                hbase t ht))) =
        inner ℂ
          (canonicalCompletedC3CausalGreenBoundarySum
            (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
              hbase s hs))
          (canonicalCompletedC3CausalGreenBoundarySum
            (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
              hbase t ht)) := by
      symm
      exact canonicalCompletedC3CausalGreenBoundarySum_inner_eq_adjointSquare
        (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
          hbase s hs)
        (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
          hbase t ht)
    _ = inner ℂ
          (canonicalCompletedC3DirichletGradientState s hs)
          (canonicalCompletedC3DirichletGradientState t ht) :=
      canonicalCompletedC3CausalGreenBoundarySum_inner_eq_nativeState_inner
        hbase hs ht

theorem canonicalCompletedC3CausalGreenBoundary_native_source_response
    {base : ℕ} (hbase : IsSupported base)
    {s : ℂ} (hs : 0 < s.re) :
    carryWeightedVerticalCenteredBracket
        (canonicalBR2CarryAmplitudeRatio base)
        (canonicalCompletedC3DirichletGradientCausalGreenState
          base s hs) =
      canonicalCompletedC3DirichletGradientBracketSourceState
        base s hs := by
  exact canonicalCompletedC3DirichletGradientBracket_causalGreen_eq_source
    hbase s hs

theorem canonicalCompletedC3GradientCompatiblePoissonGraphKernel_eq_nativeState_inner
    {r s : ℂ} (hr : 0 < r.re) (hs : 0 < s.re) :
    canonicalCompletedC3GradientCompatiblePoissonGraphKernel r s hr hs =
      inner ℂ
        (canonicalCompletedC3DirichletGradientState r hr)
        (canonicalCompletedC3DirichletGradientState s hs) := by
  rw [canonicalCompletedC3GradientCompatiblePoissonGraphKernel_eq_rawGammaGram]
  rfl

theorem canonicalCompletedC3CausalGreenProjectionBridge
    {base : ℕ} (hbase : IsSupported base)
    {r s : ℂ} (hr : 0 < r.re) (hs : 0 < s.re) :
    (canonicalCompletedC3GradientCompatiblePoissonGraphKernel r s hr hs =
      inner ℂ
        (canonicalCompletedC3DirichletGradientState r hr)
        (canonicalCompletedC3DirichletGradientState s hs)) ∧
    (canonicalCompletedC3GradientCompatiblePoissonGraphKernel r s hr hs =
      inner ℂ
        (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
          hbase r hr)
        ((canonicalCompletedC3CausalGreenBoundarySum.adjoint)
          (canonicalCompletedC3CausalGreenBoundarySum
            (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
              hbase s hs)))) := by
  refine ⟨canonicalCompletedC3GradientCompatiblePoissonGraphKernel_eq_nativeState_inner
      hr hs, ?_⟩
  exact canonicalCompletedC3GradientCompatiblePoissonGraphKernel_eq_causalAdjointSquare
    hbase r s hr hs

theorem canonicalCompletedNativeCarryGreenIncidenceCrosswalk
    {base radius : ℕ} (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    (canonicalBR2CarryAmplitudeRatio base =
      CarryGeometry.carryAmplitude base 1) ∧
    (Nonempty (BR2BracketIncidenceJetTransport base radius
      (canonicalBR2CameraBracketCausalGreenResponseParityJet base radius))) ∧
    (∀ index : ℕ,
      carryWeightedVerticalCenteredBracket
          (canonicalBR2CarryAmplitudeRatio base)
          (canonicalBR2CameraBracketCausalGreenResponse base radius index) =
        br2CameraBracketVerticalState base radius index) ∧
    (∀ x y : CarryVerticalL2,
      inner ℂ x y =
        inner ℂ
            (carryVerticalL2WeightedGreen
              (canonicalBR2CarryAmplitudeRatio base)
              (carryWeightedVerticalCenteredBracket
                (canonicalBR2CarryAmplitudeRatio base) x))
            (carryVerticalL2WeightedGreen
              (canonicalBR2CarryAmplitudeRatio base)
              (carryWeightedVerticalCenteredBracket
                (canonicalBR2CarryAmplitudeRatio base) y)) +
        inner ℂ
            (carryVerticalL2WeightedGreen
              (canonicalBR2CarryAmplitudeRatio base)
              (carryWeightedVerticalCenteredBracket
                (canonicalBR2CarryAmplitudeRatio base) x))
            (carryWeightedVerticalReturn
              (canonicalBR2CarryAmplitudeRatio base)
              (canonicalBR2CarryAmplitudeRatio_pos hbase).le
              (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
              (carryWeightedVerticalTrace
                (canonicalBR2CarryAmplitudeRatio base) y)) +
        inner ℂ
            (carryWeightedVerticalReturn
              (canonicalBR2CarryAmplitudeRatio base)
              (canonicalBR2CarryAmplitudeRatio_pos hbase).le
              (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
              (carryWeightedVerticalTrace
                (canonicalBR2CarryAmplitudeRatio base) x))
            (carryVerticalL2WeightedGreen
              (canonicalBR2CarryAmplitudeRatio base)
              (carryWeightedVerticalCenteredBracket
                (canonicalBR2CarryAmplitudeRatio base) y)) +
        inner ℂ
            (carryWeightedVerticalReturn
              (canonicalBR2CarryAmplitudeRatio base)
              (canonicalBR2CarryAmplitudeRatio_pos hbase).le
              (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
              (carryWeightedVerticalTrace
                (canonicalBR2CarryAmplitudeRatio base) x))
            (carryWeightedVerticalReturn
              (canonicalBR2CarryAmplitudeRatio base)
              (canonicalBR2CarryAmplitudeRatio_pos hbase).le
              (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
              (carryWeightedVerticalTrace
                (canonicalBR2CarryAmplitudeRatio base) y))) := by
  refine ⟨canonicalBR2CarryAmplitudeRatio_eq_carryAmplitude base,
    ⟨canonicalBR2CameraBracketCausalGreenResponseIncidenceJetTransport
      hbase hradius⟩, ?_, ?_⟩
  · intro index
    exact canonicalBR2WeightedVerticalCenteredBracket_causalGreenResponse
      hbase hradius index
  · intro x y
    exact canonicalCarryTfvd_inner_eq_fourChannel hbase x y

theorem canonicalCompletedNativeCarryGreen_tfvd_reconstruction
    {base radius : ℕ} (hbase : IsSupported base)
    (_hradius : radius ∈ radiusSet base)
    (S : Finset NativeGpreBoundaryContext) (index : ℕ) :
    nativeGpreFiniteTfvdReconstruction
        (canonicalBR2CarryAmplitudeRatio base)
        (canonicalBR2CarryAmplitudeRatio_pos hbase).le
        (canonicalBR2CarryAmplitudeRatio_lt_one hbase) S
        (nativeGpreFiniteTfvdAnalysis
          (canonicalBR2CarryAmplitudeRatio base) S
          (canonicalBR2CameraBracketCausalGreenResponse
            base radius index)) =
      canonicalBR2CameraBracketCausalGreenResponse base radius index := by
  simpa [canonicalBR2CameraBracketCausalGreenResponse] using
    (nativeGpreFiniteTfvdReconstruction_analysis_br2CausalGreenResponse
      (canonicalBR2CarryAmplitudeRatio base)
      (canonicalBR2CarryAmplitudeRatio_pos hbase)
      (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
      S base radius index)

theorem canonicalCompletedNativeTfvdGreenPort_nativeLine_eq_packagedNativeSlope
    (time : ℝ) :
    canonicalCompletedTfvdGreenPortState (nativeLine time) =
      finitePackagedNativeSlopeGreenPort 3 time := by
  calc
    canonicalCompletedTfvdGreenPortState (nativeLine time) =
        finiteC3GenuineBracketGreenBoundaryPair 3 (nativeLine time) := by
      exact congrFun cameraFreeTfvdGreenPort_vector_intertwiner
        (nativeLine time)
    _ = finitePackagedNativeSlopeGreenPort 3 time :=
      finiteC3GenuineBracketGreenBoundaryPair_nativeLine_eq_nativeSlopePort
        3 time

/-! ## Native four-corner carrier before scalar moments -/

/-- The complete native four-corner cell is the pre-Hankel object behind the
causal Green readout.  The three equalities keep its provenance visible:
the Genuine Green form, its literal Hilbert inner product, and the exact
ordinary/log-jet reconstruction on the reflected leg.  No moment sequence,
Hankel matrix, or Jacobi operator is used here. -/
theorem canonicalCompletedNativeCarryGreenFourCornerProvenance
    (M : ℕ) (z w : ℂ) :
    (greenForm (𝕜 := ℂ)
        (finiteC3GenuineBracketGreenBoundaryPair M w)
        (finiteC3GenuineBracketGreenBoundaryPair M (reflectedParameter z)) =
      canonicalC3MixedRadialCoefficient z w *
        nativeGpreFourCornerPolarizedDirichletPrefix
          M w (reflectedParameter z)) ∧
    (nativeGpreFourCornerPolarizedDirichletPrefix
        M w (reflectedParameter z) =
      inner ℂ
        (canonicalCompletedC3DirichletGradientPrefixState w M)
        (canonicalCompletedC3DirichletGradientPrefixState
          (reflectedParameter z) M)) ∧
    (nativeGpreFourCornerPolarizedDirichletPrefix
        M w (reflectedParameter z) =
      ∑ n ∈ Finset.range M,
        (starRingEnd ℂ) (positiveDirichletGradient w n) *
          sameEdgeRecoveredReflectedGradient n
            (positiveDirichletGradient z n)
            (positiveLogDirichletGradient z n)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      greenForm_finiteC3GenuineBracket_twoParameter_eq_coefficient_mul_nativeFourCorner
        M z w
  · exact nativeGpreFourCornerPolarizedDirichletPrefix_eq_inner
      M w (reflectedParameter z)
  · exact nativeGpreFourCornerPolarizedDirichletPrefix_reflected_eq_logJetReconstruction
      M w z

/-- The remaining scalar sewing gate is exactly the vanishing of the explicit
finite total defect after the native four-corner carrier has been exposed.
This is the precise handoff from the causal/pre-Hankel construction to the
completed Wronskian, not a replacement of that construction by a Gram ansatz.
-/
theorem canonicalCompletedNativeCarryGreenWronskian_sewing_iff_totalDefect_zero
    {z w : ℂ} (hz : 0 < z.re) (hzUpper : z.re < 1) (hw : 0 < w.re) :
    canonicalCompletedC3RawMixedWronskian z w =
        canonicalC3MixedRadialCoefficient z w *
          canonicalCompletedC3RawGammaGram
            w (reflectedParameter z) hw
            (by simpa [reflectedParameter] using sub_pos.mpr hzUpper) ↔
      Tendsto
        (fun M : ℕ => canonicalC3FiniteMixedTotalDefect M z w)
        atTop (nhds 0) := by
  simpa [canonicalCompletedC3MixedRadialGreenKernel] using
    (canonicalC3FiniteMixedTotalDefect_tendsto_zero_iff
      hz hzUpper hw).symm

/-! ## The stronger scalar identity above the Gram layer -/

/-- The signed chiral Wronskian response reads the native moments directly.
This is the causal scalar identity produced by the completed Green operator;
no Gram matrix or Jacobi coordinate appears in its statement. -/
theorem canonicalCompletedNativeCarryGreenChiralResponse_oddCoefficient_eq_moment
    (M n : ℕ) :
    canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
        M (2 * n + 1) =
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  exact canonicalCompletedC3FullWronskianChiralResponse_odd_eq_canonicalMoment
    M n

/-- The same Wronskian identity before specializing to a parity diagonal:
the coefficient of order `p + q + 1` is the polarized native moment. -/
theorem canonicalCompletedNativeCarryGreenChiralResponse_succCoefficient_eq_polarizedMoment
    (M p q : ℕ) :
    canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
        M (p + q + 1) =
      polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q := by
  exact canonicalCompletedC3FullWronskianChiralResponse_succ_eq_polarizedMoment
    M p q

theorem canonicalCompletedNativeCausalGreenProvenance
    {base : ℕ} (hbase : IsSupported base)
    {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) :
    (carryWeightedVerticalCenteredBracket
        (canonicalBR2CarryAmplitudeRatio base)
        (canonicalCompletedC3DirichletGradientCausalGreenState
          base s hs) =
      canonicalCompletedC3DirichletGradientBracketSourceState base s hs) ∧
    (canonicalCompletedC3CausalGreenBoundarySum
        (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
          hbase s hs) =
      canonicalCompletedC3DirichletGradientState s hs) ∧
    (inner ℂ
        (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
          hbase s hs)
        ((canonicalCompletedC3CausalGreenBoundarySum.adjoint)
          (canonicalCompletedC3CausalGreenBoundarySum
            (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
              hbase t ht))) =
      inner ℂ
        (canonicalCompletedC3DirichletGradientState s hs)
        (canonicalCompletedC3DirichletGradientState t ht)) ∧
    (IsSelfAdjoint canonicalNativeGreenFrameReturnMetric) ∧
    (canonicalNativeGreenFrameReturnMetric.IsPositive) := by
  refine ⟨canonicalCompletedC3CausalGreenBoundary_native_source_response
      hbase hs, ?_, ?_, ?_, ?_⟩
  · exact canonicalCompletedC3CausalGreenBoundarySum_state hbase hs
  · exact canonicalCompletedC3CausalGreenBoundarySum_adjointSquare_eq_nativeState_inner
      hbase hs ht
  · exact canonicalNativeGreenFrameReturnMetric_isSelfAdjoint
  · exact canonicalNativeGreenFrameReturnMetric_isPositive

end
end CarrySelfAdjointOperator
