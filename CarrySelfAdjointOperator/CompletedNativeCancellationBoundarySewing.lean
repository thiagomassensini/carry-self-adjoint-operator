import CarrySelfAdjointOperator.CompletedC3GreenInverseSewingProbe
import CarrySelfAdjointOperator.CompletedC3CausalGreenGramSewing
import CarrySelfAdjointOperator.CompletedC3BoundaryRelationSewingBridge
import CarrySelfAdjointOperator.CompletedC3SameStructuredBoundaryState
import CPFormal.Analytic.CpNativeGpreHilbertGluedGreenDefect
import Mathlib.Tactic

/-!
# Completed native cancellation boundary sewing

The finite C3 cancellation is a source/response/return identity.  This file
keeps those three pieces in a fixed carrier and transports the response plus
return to the completed ordinary TFVD state.  It also exposes the canonical
Hilbert boundary pencil whose provenance coordinates cancel inside the Green
form.

The scalar Psi,F trace is retained as a separate projection of the same
packaged completed state.  Its comparison with the Gamma boundary form is
recorded as the existing raw sewing defect.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- Finite source, causal Green response, boundary return, and reconstructed
prefix.  No moment or Jacobi data occur in this carrier. -/
structure CanonicalCompletedC3FiniteCancellationData
    (base cutoff : ℕ) (s : ℂ) where
  source : CarryVerticalL2
  greenResponse : CarryVerticalL2
  boundaryReturn : CarryVerticalL2
  prefixState : CarryVerticalL2
  source_eq_canonical :
    source = canonicalCompletedC3DirichletGradientBracketSource base cutoff s
  greenResponse_eq_weightedGreen :
    greenResponse =
      carryVerticalL2WeightedGreen
        (canonicalBR2CarryAmplitudeRatio base) source
  reconstruction : greenResponse + boundaryReturn = prefixState

/-- Canonical finite cancellation data assembled from the existing maps. -/
def canonicalCompletedC3FiniteCancellationData
    {base cutoff : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) (s : ℂ) :
    CanonicalCompletedC3FiniteCancellationData base cutoff s where
  source := canonicalCompletedC3DirichletGradientBracketSource base cutoff s
  greenResponse :=
    canonicalCompletedC3DirichletGradientBracketGreenResponse base cutoff s
  boundaryReturn :=
    canonicalCompletedC3DirichletGradientPrefixBoundaryReturn hbase cutoff s
  prefixState :=
    canonicalCompletedC3DirichletGradientPrefixState s
      (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
  source_eq_canonical := rfl
  greenResponse_eq_weightedGreen := rfl
  reconstruction := by
    simpa [canonicalCompletedC3DirichletGradientPrefixBoundaryReturn] using
      (canonicalCompletedC3DirichletGradient_cancellationGreen_add_boundary_eq_prefix
        (base := base) (cutoff := cutoff) hbase s)

@[simp] theorem canonicalCompletedC3FiniteCancellationData_source
    {base cutoff : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) (s : ℂ) :
    (canonicalCompletedC3FiniteCancellationData (cutoff := cutoff) hbase s).source =
      canonicalCompletedC3DirichletGradientBracketSource base cutoff s := rfl

@[simp] theorem canonicalCompletedC3FiniteCancellationData_greenResponse
    {base cutoff : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) (s : ℂ) :
    (canonicalCompletedC3FiniteCancellationData (cutoff := cutoff) hbase s).greenResponse =
      canonicalCompletedC3DirichletGradientBracketGreenResponse base cutoff s := rfl

@[simp] theorem canonicalCompletedC3FiniteCancellationData_boundaryReturn
    {base cutoff : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) (s : ℂ) :
    (canonicalCompletedC3FiniteCancellationData (cutoff := cutoff) hbase s).boundaryReturn =
      canonicalCompletedC3DirichletGradientPrefixBoundaryReturn hbase cutoff s := rfl

@[simp] theorem canonicalCompletedC3FiniteCancellationData_prefix
    {base cutoff : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) (s : ℂ) :
    (canonicalCompletedC3FiniteCancellationData (cutoff := cutoff) hbase s).prefixState =
      canonicalCompletedC3DirichletGradientPrefixState s
        (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1) := rfl

theorem canonicalCompletedC3FiniteCancellationData_reconstruction
    {base cutoff : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) (s : ℂ) :
    (canonicalCompletedC3FiniteCancellationData (cutoff := cutoff) hbase s).greenResponse +
        (canonicalCompletedC3FiniteCancellationData (cutoff := cutoff) hbase s).boundaryReturn =
      (canonicalCompletedC3FiniteCancellationData (cutoff := cutoff) hbase s).prefixState :=
  (canonicalCompletedC3FiniteCancellationData (cutoff := cutoff) hbase s).reconstruction

theorem canonicalCompletedC3FiniteCancellationData_source_is_bracket
    {base cutoff : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) (s : ℂ) :
    (canonicalCompletedC3FiniteCancellationData (cutoff := cutoff) hbase s).source =
      carryWeightedVerticalCenteredBracket
        (canonicalBR2CarryAmplitudeRatio base)
        (canonicalCompletedC3DirichletGradientPrefixState s
          (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)) := rfl

theorem canonicalCompletedC3FiniteCancellationData_greenResponse_is_response
    {base cutoff : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) (s : ℂ) :
    (canonicalCompletedC3FiniteCancellationData (cutoff := cutoff) hbase s).greenResponse =
      carryVerticalL2WeightedGreen
        (canonicalBR2CarryAmplitudeRatio base)
        (canonicalCompletedC3FiniteCancellationData (cutoff := cutoff) hbase s).source :=
  (canonicalCompletedC3FiniteCancellationData (cutoff := cutoff) hbase s).greenResponse_eq_weightedGreen

/-- Semantic alias for the existing response/return product. -/
abbrev CanonicalCompletedC3CancellationBoundaryCarrier :=
  CanonicalCompletedC3CausalGreenBoundaryCarrier

def canonicalCompletedC3CancellationBoundaryState
    {base : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (s : ℂ) (hs : 0 < s.re) :
    CanonicalCompletedC3CancellationBoundaryCarrier :=
  canonicalCompletedC3DirichletGradientCausalGreenBoundaryState hbase s hs

def canonicalCompletedC3CancellationBoundaryReconstruction :
    CanonicalCompletedC3CancellationBoundaryCarrier →L[ℂ] CarryVerticalL2 :=
  canonicalCompletedC3CausalGreenBoundarySum

@[simp] theorem canonicalCompletedC3CancellationBoundaryReconstruction_apply
    (state : CanonicalCompletedC3CancellationBoundaryCarrier) :
    canonicalCompletedC3CancellationBoundaryReconstruction state =
      state.fst + state.snd :=
  canonicalCompletedC3CausalGreenBoundarySum_apply state

theorem canonicalCompletedC3CancellationBoundaryState_reconstructs
    {base : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (s : ℂ) (hs : 0 < s.re) :
    canonicalCompletedC3CancellationBoundaryReconstruction
        (canonicalCompletedC3CancellationBoundaryState hbase s hs) =
      canonicalCompletedC3DirichletGradientState s hs := by
  change
    (canonicalCompletedC3CancellationBoundaryState hbase s hs).fst +
        (canonicalCompletedC3CancellationBoundaryState hbase s hs).snd = _
  exact canonicalCompletedC3DirichletGradientCausalGreenBoundaryState_sum
    hbase s hs

def canonicalCompletedC3FiniteCancellationBoundaryState
    {base : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (s : ℂ) :
    CanonicalCompletedC3CancellationBoundaryCarrier :=
  canonicalCompletedC3DirichletGradientCausalGreenBoundaryPrefixState
    hbase cutoff s

@[simp] theorem canonicalCompletedC3FiniteCancellationBoundaryState_fst
    {base : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (s : ℂ) :
    (canonicalCompletedC3FiniteCancellationBoundaryState hbase cutoff s).fst =
      canonicalCompletedC3DirichletGradientBracketGreenResponse base cutoff s := rfl

@[simp] theorem canonicalCompletedC3FiniteCancellationBoundaryState_snd
    {base : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (s : ℂ) :
    (canonicalCompletedC3FiniteCancellationBoundaryState hbase cutoff s).snd =
      canonicalCompletedC3DirichletGradientPrefixBoundaryReturn hbase cutoff s := rfl

theorem canonicalCompletedC3FiniteCancellationBoundaryState_reconstructs
    {base cutoff : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) (s : ℂ) :
    canonicalCompletedC3CancellationBoundaryReconstruction
        (canonicalCompletedC3FiniteCancellationBoundaryState hbase cutoff s) =
      canonicalCompletedC3DirichletGradientPrefixState s
        (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1) := by
  change
    (canonicalCompletedC3FiniteCancellationBoundaryState hbase cutoff s).fst +
        (canonicalCompletedC3FiniteCancellationBoundaryState hbase cutoff s).snd = _
  rw [canonicalCompletedC3FiniteCancellationBoundaryState_fst,
    canonicalCompletedC3FiniteCancellationBoundaryState_snd]
  simpa [canonicalCompletedC3DirichletGradientPrefixBoundaryReturn] using
      (canonicalCompletedC3DirichletGradient_cancellationGreen_add_boundary_eq_prefix
        (base := base) (cutoff := cutoff) hbase s)

theorem canonicalCompletedC3CancellationBoundaryState_is_finite_limit
    {base : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3FiniteCancellationBoundaryState hbase cutoff s)
      Filter.atTop
      (nhds (canonicalCompletedC3CancellationBoundaryState hbase s hs)) :=
  canonicalCompletedC3DirichletGradientCausalGreenBoundaryPrefixState_tendsto
    hbase hs

/-- CPFormal glued boundary, retaining the provenance coordinates. -/
abbrev CanonicalCompletedC3CancellationNativeBoundaryCarrier
    (S : Finset NativeGpreBoundaryContext) :=
  CPFormal.Analytic.Cp.NativeGpreHilbertGluedBoundary S

/-- CPFormal native glued boundary pencil pulled back along reconstruction. -/
def canonicalCompletedC3CancellationNativeBoundaryPencil
    {base : ℕ}
    (_hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (S : Finset NativeGpreBoundaryContext) :
    LinearBoundaryPencil CanonicalCompletedC3CancellationBoundaryCarrier
      (CanonicalCompletedC3CancellationNativeBoundaryCarrier S) where
  valueTrace :=
    (CPFormal.Analytic.Cp.nativeGpreHilbertGluedBoundaryPencil
      (canonicalBR2CarryAmplitudeRatio base) S).valueTrace.comp
      canonicalCompletedC3CancellationBoundaryReconstruction.toLinearMap
  fluxTrace :=
    (CPFormal.Analytic.Cp.nativeGpreHilbertGluedBoundaryPencil
      (canonicalBR2CarryAmplitudeRatio base) S).fluxTrace.comp
      canonicalCompletedC3CancellationBoundaryReconstruction.toLinearMap

@[simp] theorem canonicalCompletedC3CancellationNativeBoundaryPencil_valueTrace
    {base : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (S : Finset NativeGpreBoundaryContext)
    (state : CanonicalCompletedC3CancellationBoundaryCarrier) :
    (canonicalCompletedC3CancellationNativeBoundaryPencil hbase S).valueTrace state =
      (CPFormal.Analytic.Cp.nativeGpreHilbertGluedBoundaryPencil
        (canonicalBR2CarryAmplitudeRatio base) S).valueTrace
        (canonicalCompletedC3CancellationBoundaryReconstruction state) := rfl

@[simp] theorem canonicalCompletedC3CancellationNativeBoundaryPencil_fluxTrace
    {base : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (S : Finset NativeGpreBoundaryContext)
    (state : CanonicalCompletedC3CancellationBoundaryCarrier) :
    (canonicalCompletedC3CancellationNativeBoundaryPencil hbase S).fluxTrace state =
      (CPFormal.Analytic.Cp.nativeGpreHilbertGluedBoundaryPencil
        (canonicalBR2CarryAmplitudeRatio base) S).fluxTrace
        (canonicalCompletedC3CancellationBoundaryReconstruction state) := rfl

theorem canonicalCompletedC3CancellationNativeBoundaryPencil_greenDefect_eq_verticalWronskian
    {base : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (S : Finset NativeGpreBoundaryContext)
    (x y : CanonicalCompletedC3CancellationBoundaryCarrier) :
    inner ℂ
        ((canonicalCompletedC3CancellationNativeBoundaryPencil hbase S).fluxTrace y)
        ((canonicalCompletedC3CancellationNativeBoundaryPencil hbase S).valueTrace x) -
      inner ℂ
        ((canonicalCompletedC3CancellationNativeBoundaryPencil hbase S).valueTrace y)
        ((canonicalCompletedC3CancellationNativeBoundaryPencil hbase S).fluxTrace x) =
      carryWeightedVerticalBoundaryWronskian
        (canonicalBR2CarryAmplitudeRatio base)
        (canonicalCompletedC3CancellationBoundaryReconstruction x)
        (canonicalCompletedC3CancellationBoundaryReconstruction y) := by
  exact CPFormal.Analytic.Cp.nativeGpreHilbertGluedGreenDefect_eq_verticalWronskian
    (canonicalBR2CarryAmplitudeRatio base) S
    (canonicalCompletedC3CancellationBoundaryReconstruction x)
    (canonicalCompletedC3CancellationBoundaryReconstruction y)

theorem canonicalCompletedC3CancellationNativeBoundaryPencil_state_greenDefect
    {base : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (S : Finset NativeGpreBoundaryContext)
    (s t : ℂ) (hs : 0 < s.re) (ht : 0 < t.re) :
    inner ℂ
        ((canonicalCompletedC3CancellationNativeBoundaryPencil hbase S).fluxTrace
          (canonicalCompletedC3CancellationBoundaryState hbase t ht))
        ((canonicalCompletedC3CancellationNativeBoundaryPencil hbase S).valueTrace
          (canonicalCompletedC3CancellationBoundaryState hbase s hs)) -
      inner ℂ
        ((canonicalCompletedC3CancellationNativeBoundaryPencil hbase S).valueTrace
          (canonicalCompletedC3CancellationBoundaryState hbase t ht))
        ((canonicalCompletedC3CancellationNativeBoundaryPencil hbase S).fluxTrace
          (canonicalCompletedC3CancellationBoundaryState hbase s hs)) =
      carryWeightedVerticalBoundaryWronskian
        (canonicalBR2CarryAmplitudeRatio base)
        (canonicalCompletedC3DirichletGradientState s hs)
        (canonicalCompletedC3DirichletGradientState t ht) := by
  rw [canonicalCompletedC3CancellationNativeBoundaryPencil_greenDefect_eq_verticalWronskian,
    canonicalCompletedC3CancellationBoundaryState_reconstructs,
    canonicalCompletedC3CancellationBoundaryState_reconstructs]

/-- Augmented carrier retaining native cancellation channels and scalar trace. -/
abbrev CanonicalCompletedC3CancellationTraceCarrier :=
  CanonicalCompletedC3CancellationBoundaryCarrier × (ℂ × ℂ)

def canonicalCompletedC3CancellationTraceState
    {base : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hz : 0 < (operatorHeightParameter z).re) :
    CanonicalCompletedC3CancellationTraceCarrier :=
  (canonicalCompletedC3CancellationBoundaryState hbase
      (operatorHeightParameter z) hz,
    canonicalCompletedC3ScalarBoundaryPair z)

def canonicalCompletedC3CancellationTraceMap :
    CanonicalCompletedC3CancellationTraceCarrier →L[ℂ] (ℂ × ℂ) :=
  ContinuousLinearMap.snd ℂ CanonicalCompletedC3CancellationBoundaryCarrier
    (ℂ × ℂ)

@[simp] theorem canonicalCompletedC3CancellationTraceMap_apply
    (state : CanonicalCompletedC3CancellationTraceCarrier) :
    canonicalCompletedC3CancellationTraceMap state = state.2 := rfl

theorem canonicalCompletedC3CancellationTraceState_trace_eq_scalarPair
    {base : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hz : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3CancellationTraceMap
        (canonicalCompletedC3CancellationTraceState hbase z hz) =
      canonicalCompletedC3ScalarBoundaryPair z := rfl

theorem canonicalCompletedC3CancellationTraceState_trace_eq_F_negFprime
    {base : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    {z : ℂ} (hz : 0 < (operatorHeightParameter z).re)
    (_hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3CancellationTraceMap
        (canonicalCompletedC3CancellationTraceState hbase z hz) =
      (-deriv completedNativeOperatorCharacteristic z,
        completedNativeOperatorCharacteristic z) := by
  change canonicalCompletedC3ScalarBoundaryPair z = _
  simp [canonicalCompletedC3ScalarBoundaryPair,
    completedNativeOperatorBoundaryCompanion_eq_neg_deriv]

theorem canonicalCompletedC3CancellationTraceGlue_difference_eq_rawDefect
    {base : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzPos : 0 < (operatorHeightParameter z).re)
    (hwPos : 0 < (operatorHeightParameter w).re)
    (_hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (_hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (_S : Finset NativeGpreBoundaryContext) :
    greenForm (𝕜 := ℂ)
        (canonicalCompletedC3GammaBoundaryState z hz)
        (canonicalCompletedC3GammaBoundaryState w hw) -
      greenForm (𝕜 := ℂ)
        (canonicalCompletedC3CancellationTraceMap
          (canonicalCompletedC3CancellationTraceState hbase z hzPos))
        (canonicalCompletedC3CancellationTraceMap
          (canonicalCompletedC3CancellationTraceState hbase w hwPos)) =
      canonicalCompletedC3RawGammaWronskianDefect z w hz hw := by
  rw [canonicalCompletedC3CancellationTraceState_trace_eq_scalarPair,
    canonicalCompletedC3CancellationTraceState_trace_eq_scalarPair,
    canonicalCompletedC3RawGammaWronskianDefect_eq_boundaryGreenForm_sub]

theorem canonicalCompletedC3CancellationTraceGlue_iff_rawDefect_zero
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (_hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (_hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    greenForm (𝕜 := ℂ)
        (canonicalCompletedC3GammaBoundaryState z hz)
        (canonicalCompletedC3GammaBoundaryState w hw) =
      greenForm (𝕜 := ℂ)
        (canonicalCompletedC3ScalarBoundaryPair z)
        (canonicalCompletedC3ScalarBoundaryPair w) ↔
      canonicalCompletedC3RawGammaWronskianDefect z w hz hw = 0 := by
  rw [canonicalCompletedC3RawGammaWronskianDefect_eq_boundaryGreenForm_sub]
  constructor
  · intro h
    exact sub_eq_zero.mpr h
  · intro h
    exact sub_eq_zero.mp h

end

end CarrySelfAdjointOperator
