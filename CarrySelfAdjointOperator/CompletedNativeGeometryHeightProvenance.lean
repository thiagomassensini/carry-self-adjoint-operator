import CarrySelfAdjointOperator.ExactCutoffCameraGram
import CarrySelfAdjointOperator.FiniteCameraLogarithmicMomentCrosswalk
import CarrySelfAdjointOperator.CompletedNativeCameraUniversality
import CarrySelfAdjointOperator.CanonicalCompletedNativeStieltjesOperator
import CarrySelfAdjointOperator.CompletedNativeTfvdGreenMomentGramBridge
import Mathlib.Tactic

open scoped BigOperators
open Filter

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite

noncomputable section

/-!
# Provenance ledger for the native geometric height operator

This file records the direction of the construction which is easy to lose in
an archaeological search.  The finite native camera rows produce a literal
Gram matrix first.  After the common completed characteristic is exposed, the
same native construction produces its logarithmic moments, the two Hankel
forms, the canonical Jacobi section, and finally the inverse-square-root
height operator.

There are two different Gram objects in this ledger:

* `literalFiniteCameraGram` is the finite row Gram of the native camera
  stencils;
* `hankelGram` and `shiftedHankel` are the scalar moment Grams of the common
  completed characteristic.

The equality between those two levels is not silently asserted here.  The
Green/Taylor coefficient identity remains an explicit residual gate in
`CompletedNativeTfvdGreenMomentGramBridge`.  Thus this module proves the
native provenance of the operator while preserving the exact remaining seam.
-/

/-! ## Native geometry and the literal Gram -/

/-- The six-camera literal Gram has the exact periodic-core plus boundary
residue decomposition at every cutoff. -/
theorem nativeGeometry_sixCamera_literalGram_eq_periodic_add_residue
    (cutoff : ℕ) (i j : Fin 6) :
    NativeCarryC3Crosswalk.literalFiniteCameraGram cutoff
        (sixCamera i) (sixCamera j) =
      (cutoff : ℝ) *
          NativeCarrySpectralWeyl.Finite.periodicGramMatrix 420 sixCamera i j +
        NativeCarryC3Crosswalk.exactCutoffCameraGramResidue 420 cutoff
          (sixCamera i) (sixCamera j) := by
  apply NativeCarryC3Crosswalk.literalFiniteCameraGram_eq_periodicGram_add_residue
  · intro k
    fin_cases k <;> norm_num [sixCamera]

/- The normalized literal Gram converges to the same six-camera periodic Gram
as the native cutoff grows. -/
theorem nativeGeometry_sixCamera_literalGram_tendsto :
    Tendsto (fun cutoff : ℕ ↦
      fun i j ↦ (cutoff : ℝ)⁻¹ *
        NativeCarryC3Crosswalk.literalFiniteCameraGram cutoff
          (sixCamera i) (sixCamera j))
      atTop (nhds NativeCarrySpectralWeyl.Finite.sixCameraGram) :=
  NativeCarryC3Crosswalk.tendsto_normalizedLiteralSixCameraGram

/-! ## Native camera, common characteristic, and moments -/

/-- Removing the native camera factor exposes the common completed
characteristic; no target spectrum is involved in this step. -/
theorem nativeGeometry_normalizedCamera_eq_commonCharacteristic
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) :
    normalizedCompletedNativeCameraCharacteristic camera cutoff =
      fun time : ℝ ↦ completedNativeOperatorCharacteristic (time : ℂ) :=
  normalizedCompletedNativeCameraCharacteristic_eq hcamera cutoff

/-- The logarithmic moment sequence read from any supported native camera is
the canonical completed-native sequence. -/
theorem nativeGeometry_cameraMoments_eq_canonical
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) :
    completedNativeCameraLogDerivativeMoment camera cutoff =
      canonicalCompletedNativeLogDerivativeMoment :=
  completedNativeCameraLogDerivativeMoment_eq_canonical hcamera cutoff

/-- Both scalar Gram towers obtained after the native camera readout agree
with the canonical completed-native Hankel pair. -/
theorem nativeGeometry_cameraHankelPair_eq_canonical
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff N : ℕ) :
    hankelGram (completedNativeCameraLogDerivativeMoment camera cutoff) N =
        hankelGram canonicalCompletedNativeLogDerivativeMoment N ∧
      shiftedHankel (completedNativeCameraLogDerivativeMoment camera cutoff) N =
        shiftedHankel canonicalCompletedNativeLogDerivativeMoment N := by
  constructor <;>
    rw [nativeGeometry_cameraMoments_eq_canonical hcamera cutoff]

/-! ## Hankel, Jacobi, and height -/

/-- Under the existing all-order Stieltjes positivity gate, the Jacobi section
read from the native camera moments is exactly the canonical native Jacobi
section.  The existential Gram proof is intentional: positivity is a
certificate, not a numerically fitted matrix. -/
theorem nativeGeometry_cameraJacobiSection_eq_canonical
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff N : ℕ)
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    ∃ hgram :
        (hankelGram (completedNativeCameraLogDerivativeMoment camera cutoff) N).PosDef,
      canonicalFiniteJacobiSection
          (completedNativeCameraLogDerivativeMoment camera cutoff) N hgram =
        canonicalCompletedNativeStieltjesFiniteJacobiTower hpos N := by
  let hgramCanonical :=
    canonicalCompletedNativeStieltjes_hankelGram_posDef hpos N
  have hgramCamera :
      (hankelGram (completedNativeCameraLogDerivativeMoment camera cutoff) N).PosDef := by
    rw [nativeGeometry_cameraMoments_eq_canonical hcamera cutoff]
    exact hgramCanonical
  refine ⟨hgramCamera, ?_⟩
  exact canonicalFiniteJacobiSection_eq_of_completedNativeLogDerivativeMoments
    (completedNativeCameraLogDerivativeMoment_isMomentSequence hcamera cutoff)
    canonicalCompletedNativeLogDerivativeMoment_isMomentSequence
    N hgramCamera hgramCanonical

/-- The finite native height operator is the exact `J_N^(-1/2)` functional
calculus of the Jacobi section generated by the canonical moment carrier. -/
def nativeGeometryFiniteHeightOperator
    (hpos : CanonicalCompletedNativeStieltjesPositivity) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  canonicalFiniteHeightOperator
    (greenWronskianMomentKernel_odd_shiftedMomentGram
      (canonicalCompletedNativeStieltjesJet_momentKernel hpos))
    N
    (canonicalCompletedNativeStieltjes_hankelGram_posDef hpos N)
    (greenJetOdd_prefix_linearIndependent
      (canonicalCompletedNativeStieltjesJet_odd_linearIndependent hpos) N)

/-- The native geometric height section is symmetric by construction. -/
theorem nativeGeometryFiniteHeightOperator_isSymm
    (hpos : CanonicalCompletedNativeStieltjesPositivity) (N : ℕ) :
    (nativeGeometryFiniteHeightOperator hpos N).IsSymm := by
  unfold nativeGeometryFiniteHeightOperator
  exact canonicalFiniteHeightOperator_isSymm
    (greenWronskianMomentKernel_odd_shiftedMomentGram
      (canonicalCompletedNativeStieltjesJet_momentKernel hpos))
    N
    (canonicalCompletedNativeStieltjes_hankelGram_posDef hpos N)
    (greenJetOdd_prefix_linearIndependent
      (canonicalCompletedNativeStieltjesJet_odd_linearIndependent hpos) N)

/- The compact theorem below is intentionally stated as a finite provenance
chain. It does not claim that the all-order positivity gate or the concrete
Green/Taylor Gram identification has already been proved. -/
theorem nativeGeometry_to_finiteHeight_chain
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff N : ℕ)
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    normalizedCompletedNativeCameraCharacteristic camera cutoff =
        (fun time : ℝ ↦ completedNativeOperatorCharacteristic (time : ℂ)) ∧
      completedNativeCameraLogDerivativeMoment camera cutoff =
        canonicalCompletedNativeLogDerivativeMoment ∧
      (∃ hgram :
          (hankelGram (completedNativeCameraLogDerivativeMoment camera cutoff) N).PosDef,
        canonicalFiniteJacobiSection
            (completedNativeCameraLogDerivativeMoment camera cutoff) N hgram =
          canonicalCompletedNativeStieltjesFiniteJacobiTower hpos N) ∧
      (nativeGeometryFiniteHeightOperator hpos N).IsSymm := by
  refine ⟨nativeGeometry_normalizedCamera_eq_commonCharacteristic hcamera cutoff,
    nativeGeometry_cameraMoments_eq_canonical hcamera cutoff,
    nativeGeometry_cameraJacobiSection_eq_canonical hcamera cutoff N hpos,
    nativeGeometryFiniteHeightOperator_isSymm hpos N⟩

/-! ## The remaining Green/Taylor seam -/

/-- The missing Green-to-Hankel identification is an exact, named defect
condition, not evidence that the native operator had no geometric origin. -/
theorem nativeGeometry_greenMomentGate_iff_defect_zero
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (moments : ℕ → ℝ)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState) :
    HasCanonicalCompletedNativeGreenMomentJets xiState moments ↔
      ∀ i j,
        canonicalCompletedNativeGreenMomentGramDefect xiState moments i j = 0 :=
  hasCanonicalCompletedNativeGreenMomentJets_iff_defect_zero_of_factors
    xiState moments hxi hnative

/-- If the explicit native forward-difference Gram residual vanishes, the
factor-level Green identities close the moment-jet gate.  This is the exact
conditional bridge still required before identifying the literal camera Gram
with the scalar Green/Taylor Hankel Gram. -/
theorem nativeGeometry_greenForwardDifferenceResidual_zero_closes_momentGate
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi] [CompleteSpace Hxi]
    (xiState : ℂ → Hxi)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hkernel :
      HasCompletedNativeRealAxisNormalizedGreenKernel
        (completedNativeC3ProductLedgerState xiState))
    (hresidual : ∀ i j,
      canonicalCompletedNativeGreenForwardDifferenceGramResidual
        xiState hkernel i j = 0) :
    HasCanonicalCompletedNativeGreenMomentJets xiState
      canonicalCompletedNativeLogDerivativeMoment :=
  hasCanonicalCompletedNativeGreenMomentJets_of_forwardDifferenceResidual_zero
    xiState hxi hnative hkernel hresidual

end

end CarrySelfAdjointOperator
