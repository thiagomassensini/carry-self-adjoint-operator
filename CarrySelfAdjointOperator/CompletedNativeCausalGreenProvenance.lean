import CarrySelfAdjointOperator.CompletedNativeProjectionEnergyIntertwining
import CarrySelfAdjointOperator.CompletedC3DirichletGradientBracketSource
import CarrySelfAdjointOperator.CompletedC3CausalGreenGramSewing
import CarrySelfAdjointOperator.CompletedNativeTfvdGreenMomentGramBridge
import CarrySelfAdjointOperator.CompletedNativeHilbertTraceGlueWronskian
import CarrySelfAdjointOperator.CompletedNativeReturnMetricReadoutCrosswalk
import CarrySelfAdjointOperator.CompletedNativeCentralCarryAtlasEnergy
import CarrySelfAdjointOperator.BR2CausalGreenResponseTransport
import Mathlib.Tactic

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
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
