import CarrySelfAdjointOperator.FiniteEnrichedCameraNaimarkEscapeIntertwining
import CarrySelfAdjointOperator.CompletedNativeAmbientRadialIntertwiningNoGo
import Mathlib.Tactic

/-!
# Camera vertical/horizontal energy crosswalk: exact frontier

The literal normalized ambient Gram is closed as a no-go.  This module does
not reopen that route or introduce another ambient Gram.  It audits the
different proposed explanation: whether the positive central ambient excess
is the energy of the horizontal sector removed by the *historical finite
camera orthogonalization*.

The carriers below must not be conflated.

| object | carrier | established structure |
|---|---|---|
| `cameraLogVerticalContribution`, `cameraLogHorizontalContribution` | `CameraLogSpace = ℕ →₀ ℝ` | algebraic direct sum only |
| finite historical projection | finite state family of `CarryVerticalL2` | orthogonal projection / Parseval |
| normalized ambient response | `CarryGammaComplexNaimark` | positive ambient Gram |

In particular, `IsCompl` in the first row is not used as an orthogonality
statement.  The actual finite orthogonality is supplied only by
`finiteCanonicalCameraProjection` and
`finiteCanonicalCameraBlindProjection`, under positive definiteness of the
finite row Gram.

The existing pin supplies no concrete isometric map from the finite
state-valued family to `CarryGammaComplexNaimark` which sends a selected
finite state to `canonicalCompletedC3NormalizedAmbientResponseState 0` and
intertwines the historical projection with a completed ambient projection.
`NaimarkProjectorIntertwiningSeam` records the more general missing
readout/synthesis squares.  Accordingly, the embedding structure introduced
here is a *test interface*, not an existence assertion and not a new
realization.  Conditional identities below isolate the sole residual that a
future geometric bridge must discharge.
-/

open scoped BigOperators InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Carry.Cp
open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk

noncomputable section

/-! ## The all-other-cameras horizontal formula -/

/-- The scalar synthesis of the algebraic horizontal contribution of a prime
camera is exactly the logarithm of the product of the other prime-camera
voices.  This is an all-order finite-support statement; it says nothing about
the finite historical blind projection. -/
theorem cameraLogHorizontalContribution_synthesis_eq_log_cameraHorizontal
    {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    cameraLogContributionSynthesis (cameraLogHorizontalContribution n p) =
      Real.log (cameraHorizontal n p) := by
  rw [cameraLogHorizontalContribution_synthesis_sub,
    primeDepthLogLedger_eq_log hn]
  have hsplit := CPFormal.Carry.Cp.log_camera_split hn hp
  linarith

/-- The horizontal output has the requested explicit other-camera formula:
after removing prime camera `p`, only factorization voices in the erased
finite support remain.  This is a scalar synthesis formula in
`CameraLogSpace`, not a Hilbert Gram identity. -/
theorem cameraLogHorizontalContribution_synthesis_eq_sum_otherCameraVerticals
    {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    cameraLogContributionSynthesis (cameraLogHorizontalContribution n p) =
      ∑ q ∈ (n.factorization.support).erase p,
        (n.factorization q : ℝ) * Real.log q := by
  rw [cameraLogHorizontalContribution_synthesis_eq_log_cameraHorizontal hn hp,
    CPFormal.Carry.Cp.log_cameraHorizontal_eq_sum_erase]

/-! ## The actual finite historical orthogonal splitting -/

/-- State-side visible output of the historical finite camera projector.
This is `V R X`, not the camera-indexed readout `R X`; keeping this state-side
form is necessary before it can even be compared with an ambient state. -/
noncomputable def finiteCanonicalCameraHilbertVisibleState
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (X : FiniteHilbertFamily state CarryVerticalL2) :
    FiniteHilbertFamily state CarryVerticalL2 :=
  finiteHilbertMatrixSynthesis (finiteCanonicalCameraProjection C) X

/-- State-side blind output of the same historical finite camera projector.
It is the literal complement `B = I - V R` in the finite standard Hilbert
metric. -/
noncomputable def finiteCanonicalCameraHilbertBlindState
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (X : FiniteHilbertFamily state CarryVerticalL2) :
    FiniteHilbertFamily state CarryVerticalL2 :=
  finiteHilbertMatrixSynthesis (finiteCanonicalCameraBlindProjection C) X

/-- The state-side visible output is the synthesis of the historical
whitened readout. -/
theorem finiteCanonicalCameraHilbertVisibleState_eq_synthesis_readout
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (X : FiniteHilbertFamily state CarryVerticalL2) :
    finiteCanonicalCameraHilbertVisibleState C X =
      finiteCanonicalCameraHilbertSynthesis C
        (finiteCanonicalCameraHilbertReadout C X) := by
  exact finiteCanonicalCameraProjection_hilbert_action C X

/-- Polarized Parseval identity in the actual finite state-side metric.  This
is the historical orthogonal decomposition; no `IsCompl` theorem from the
camera-log atlas is used. -/
theorem finiteCanonicalCameraHilbertVisibleBlind_inner_add
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef)
    (X Y : FiniteHilbertFamily state CarryVerticalL2) :
    inner ℂ (finiteCanonicalCameraHilbertVisibleState C X)
        (finiteCanonicalCameraHilbertVisibleState C Y) +
      inner ℂ (finiteCanonicalCameraHilbertBlindState C X)
        (finiteCanonicalCameraHilbertBlindState C Y) =
      inner ℂ X Y := by
  rw [finiteCanonicalCameraHilbertVisibleState_eq_synthesis_readout,
    finiteCanonicalCameraHilbertVisibleState_eq_synthesis_readout,
    finiteCanonicalCameraHilbertSynthesis_isometry C hG]
  exact finiteCanonicalEnrichedCameraHilbert_parseval C hG X Y

/-- Diagonal Pythagoras for the historical finite projection in its actual
Hilbert metric. -/
theorem finiteCanonicalCameraHilbertVisibleBlind_norm_sq_add
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef)
    (X : FiniteHilbertFamily state CarryVerticalL2) :
    ‖finiteCanonicalCameraHilbertVisibleState C X‖ ^ 2 +
      ‖finiteCanonicalCameraHilbertBlindState C X‖ ^ 2 = ‖X‖ ^ 2 := by
  have h := finiteCanonicalCameraHilbertVisibleBlind_inner_add C hG X X
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-! ## The only honest central-energy test -/

/-- Data required to *test* the proposed identification at the center.

There is deliberately no constructor for a canonical instance.  A future
construction must provide this concrete isometry from the finite historical
state carrier to the actual normalized ambient carrier and prove that it maps
the selected finite state to the actual ambient response.  It still must also
instantiate the readout/synthesis squares of
`NaimarkProjectorIntertwiningSeam` before visible/blind can be called an
ambient vertical/horizontal split. -/
structure CanonicalCompletedNativeCameraAmbientEnergyEmbedding
    {state : Type*} [Fintype state] [DecidableEq state]
    (X0 : FiniteHilbertFamily state CarryVerticalL2) where
  toLinearIsometry :
    FiniteHilbertFamily state CarryVerticalL2 →ₗᵢ[ℂ] CarryGammaComplexNaimark
  map_central :
    toLinearIsometry X0 =
      canonicalCompletedC3NormalizedAmbientResponseState 0
        (by norm_num [operatorHeightParameter])

/-- The test residual for the proposed visible/vertical equality
`‖V₀‖² = h₀`.  It is defined only after a supplied concrete ambient embedding;
no abstract factorization or target PSD statement is used. -/
def canonicalCompletedNativeCameraVisibleEnergyResidual
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (X0 : FiniteHilbertFamily state CarryVerticalL2)
    (E : CanonicalCompletedNativeCameraAmbientEnergyEmbedding X0) : ℝ :=
  ‖E.toLinearIsometry (finiteCanonicalCameraHilbertVisibleState C X0)‖ ^ 2 -
    canonicalCompletedNativeLogDerivativeMoment 0

/-- The test residual for the proposed blind/horizontal equality
`‖H₀‖² = δ_A`, where `δ_A` is the already established literal ambient central
excess.  This does not assert that the blind output is the atlas horizontal
output; it records exactly what a bridge would have to prove. -/
def canonicalCompletedNativeCameraHorizontalEnergyResidual
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (X0 : FiniteHilbertFamily state CarryVerticalL2)
    (E : CanonicalCompletedNativeCameraAmbientEnergyEmbedding X0) : ℝ :=
  ‖E.toLinearIsometry (finiteCanonicalCameraHilbertBlindState C X0)‖ ^ 2 -
    canonicalCompletedC3NormalizedAmbientCentralExcess

/-- Once an actual isometric central embedding is supplied, the historic
visible/blind split transports to a Pythagorean split of the *same* normalized
ambient state.  This theorem is conditional precisely because the required
embedding is not available in the current API. -/
theorem canonicalCompletedNativeCameraAmbientEmbedding_pythagoras
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef)
    (X0 : FiniteHilbertFamily state CarryVerticalL2)
    (E : CanonicalCompletedNativeCameraAmbientEnergyEmbedding X0) :
    ‖E.toLinearIsometry (finiteCanonicalCameraHilbertVisibleState C X0)‖ ^ 2 +
      ‖E.toLinearIsometry (finiteCanonicalCameraHilbertBlindState C X0)‖ ^ 2 =
        ‖canonicalCompletedC3NormalizedAmbientResponseState 0
          (by norm_num [operatorHeightParameter])‖ ^ 2 := by
  calc
    ‖E.toLinearIsometry (finiteCanonicalCameraHilbertVisibleState C X0)‖ ^ 2 +
        ‖E.toLinearIsometry (finiteCanonicalCameraHilbertBlindState C X0)‖ ^ 2 =
        ‖finiteCanonicalCameraHilbertVisibleState C X0‖ ^ 2 +
          ‖finiteCanonicalCameraHilbertBlindState C X0‖ ^ 2 := by
            rw [E.toLinearIsometry.norm_map, E.toLinearIsometry.norm_map]
    _ = ‖X0‖ ^ 2 :=
      finiteCanonicalCameraHilbertVisibleBlind_norm_sq_add C hG X0
    _ = ‖E.toLinearIsometry X0‖ ^ 2 := by
      rw [E.toLinearIsometry.norm_map]
    _ = ‖canonicalCompletedC3NormalizedAmbientResponseState 0
          (by norm_num [operatorHeightParameter])‖ ^ 2 := by
      rw [E.map_central]

/-- The visible and horizontal central residuals are negatives of one
another.  Hence the proposed equality `‖V₀‖² = h₀` is equivalent to
`‖H₀‖² = δ_A`; their common test is one scalar residual, not two fitted
normalizations. -/
theorem canonicalCompletedNativeCameraHorizontalEnergyResidual_eq_neg_visible
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef)
    (X0 : FiniteHilbertFamily state CarryVerticalL2)
    (E : CanonicalCompletedNativeCameraAmbientEnergyEmbedding X0) :
    canonicalCompletedNativeCameraHorizontalEnergyResidual C X0 E =
      - canonicalCompletedNativeCameraVisibleEnergyResidual C X0 E := by
  have hsplit := canonicalCompletedNativeCameraAmbientEmbedding_pythagoras
    C hG X0 E
  unfold canonicalCompletedNativeCameraHorizontalEnergyResidual
    canonicalCompletedNativeCameraVisibleEnergyResidual
    canonicalCompletedC3NormalizedAmbientCentralExcess
  linarith

/-- Exact equivalence of the two central energy tests, conditional on a
concrete isometric embedding of the finite historical state. -/
theorem canonicalCompletedNativeCameraHorizontalEnergyResidual_eq_zero_iff
    {camera state : Type*}
    [Fintype camera] [Fintype state]
    [DecidableEq camera] [DecidableEq state]
    (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef)
    (X0 : FiniteHilbertFamily state CarryVerticalL2)
    (E : CanonicalCompletedNativeCameraAmbientEnergyEmbedding X0) :
    canonicalCompletedNativeCameraHorizontalEnergyResidual C X0 E = 0 ↔
      canonicalCompletedNativeCameraVisibleEnergyResidual C X0 E = 0 := by
  rw [canonicalCompletedNativeCameraHorizontalEnergyResidual_eq_neg_visible
    C hG X0 E]
  constructor <;> intro h <;> linarith

end

end CarrySelfAdjointOperator
