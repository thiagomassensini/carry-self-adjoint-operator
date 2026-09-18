import CarrySelfAdjointOperator.NativeScalarGenuineIdentification
import CarrySelfAdjointOperator.CompletedNativeGeometryHeightProvenance

/-!
# Native-camera/Genuine instantiation of the all-order downstream chain

This module changes only the source instantiation.  The all-order derivative,
triangular, parity, finite-prefix, limit, Hankel/Jacobi, and operator
machinery remains upstream and is consumed through the existing provenance
bridges.
-/

namespace CarrySelfAdjointOperator

noncomputable section

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

theorem nativeCameraGenuineAllOrderInstantiation
    {camera cutoff N : ℕ}
    (hcamera : 2 ≤ camera)
    (hpos : CanonicalCompletedNativeStieltjesPositivity)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {greenJet : (ℕ ⊕ ℕ) → E}
    (hgreen :
      IsGreenWronskianMomentKernelGramRepresentation
        canonicalCompletedNativeLogDerivativeMoment greenJet)
    (hodd : LinearIndependent ℝ
      (fun n : ℕ ↦ greenJet (Sum.inr n))) :
    (∀ s : ℂ, nativeScalar s = genuineContinuation s) ∧
      completedNativeCameraLogDerivativeMoment camera cutoff =
        canonicalCompletedNativeLogDerivativeMoment ∧
      (hankelGram
          (completedNativeCameraLogDerivativeMoment camera cutoff) N =
          hankelGram canonicalCompletedNativeLogDerivativeMoment N ∧
        shiftedHankel
          (completedNativeCameraLogDerivativeMoment camera cutoff) N =
          shiftedHankel canonicalCompletedNativeLogDerivativeMoment N) ∧
      (∃ hgram :
          (hankelGram
            (completedNativeCameraLogDerivativeMoment camera cutoff) N).PosDef,
        canonicalFiniteJacobiSection
            (completedNativeCameraLogDerivativeMoment camera cutoff) N hgram =
          canonicalCompletedNativeStieltjesFiniteJacobiTower hpos N) ∧
      nativeGeometryFiniteHeightOperator hpos N =
        canonicalFiniteHeightOperator
          (greenWronskianMomentKernel_odd_shiftedMomentGram hgreen)
          N
          (canonicalCompletedNativeStieltjes_hankelGram_posDef hpos N)
          (greenJetOdd_prefix_linearIndependent hodd N) := by
  refine ⟨?_, nativeGeometry_cameraMoments_eq_canonical hcamera cutoff,
    nativeGeometry_cameraHankelPair_eq_canonical hcamera cutoff N,
    nativeGeometry_cameraJacobiSection_eq_canonical hcamera cutoff N hpos,
    nativeGeometryFiniteHeightOperator_eq_of_greenMomentKernel
      hgreen hpos N hodd⟩
  intro s
  exact nativeScalar_eq_genuineContinuation_unconditional s

end

end CarrySelfAdjointOperator
