import CarrySelfAdjointOperator.NativeGammaC9Analytic
import CarrySelfAdjointOperator.NativeGammaCanonicalSource
import CarrySelfAdjointOperator.CompletedC3BoundaryRelationSewingBridge

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped InnerProductSpace
open CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false

theorem nativeCanonicalGammaPair_original (z : ℂ) (hz : z.im ≠ 0) :
    (nativeCanonicalGammaSource z, nativeCanonicalGammaCauchyTrace z hz) =
      canonicalCompletedC3GammaBoundaryState z hz := rfl

theorem nativeC9WitnessPoint_height :
    operatorHeightParameter nativeC9WitnessPoint = (3/8 : ℂ) + 4*Complex.I := by
  apply Complex.ext <;> norm_num [operatorHeightParameter, nativeC9WitnessPoint]

theorem nativeC9WitnessPoint_strip :
    operatorHeightParameter nativeC9WitnessPoint ∈ genuineCriticalStrip := by
  rw [nativeC9WitnessPoint_height]
  constructor <;> norm_num

theorem nativeCanonicalGammaCoefficients_cameraSix_ne_zero (z : ℂ)
    (hs : 0 < (operatorHeightParameter z).re) :
    nativeCanonicalGammaCoefficients z 4 ≠ 0 := by
  rw [nativeCanonicalGammaCoefficients_cameraSix]
  exact positiveDirichletGradient_one_ne_zero _ hs

theorem nativeC9CanonicalGammaCauchyReadout (z : ℂ) (hz : z.im ≠ 0) :
    inner ℂ nativeC9Exterior (nativeCanonicalGammaCauchyTrace z hz) =
      nativeC9Beta z * positiveDirichletGradient (operatorHeightParameter z) 1 := by
  unfold nativeCanonicalGammaCauchyTrace
  rw [nativeCanonicalGammaSource_eq_synthesis, nativeC9CauchyReadout_selectsCameraSix,
    nativeCanonicalGammaCoefficients_cameraSix]

theorem canonicalGammaCauchyTrace_C9_nonzero :
    inner ℂ nativeC9Exterior (nativeCanonicalGammaCauchyTrace nativeC9WitnessPoint
      nativeC9WitnessPoint_admissible.1) ≠ 0 := by
  rw [nativeC9CanonicalGammaCauchyReadout]
  exact mul_ne_zero nativeC9Beta_witness_ne_zero
    (positiveDirichletGradient_one_ne_zero _ nativeC9WitnessPoint_strip.1)

/-- The original canonical source, not an artificial single-camera input. -/
theorem canonicalGammaCauchyTrace_hasExterior :
    nativeSixCameraExterior (nativeCanonicalGammaCauchyTrace nativeC9WitnessPoint
      nativeC9WitnessPoint_admissible.1) ≠ 0 := by
  intro he
  apply canonicalGammaCauchyTrace_C9_nonzero
  rw [nativeSixCameraProjection_roundtrip
    (nativeCanonicalGammaCauchyTrace nativeC9WitnessPoint nativeC9WitnessPoint_admissible.1), he,
    add_zero, nativeC9Exterior_orthogonal]

theorem canonicalGammaCauchyTrace_not_in_sixCameras :
    nativeCanonicalGammaCauchyTrace nativeC9WitnessPoint nativeC9WitnessPoint_admissible.1 ∉
      LinearMap.range nativeSixCameraSynthesis := by
  rintro ⟨c, hc⟩
  apply canonicalGammaCauchyTrace_hasExterior
  rw [← hc, nativeSixCameraExterior_synthesis]

theorem originalCanonicalGammaCauchyTrace_hasExterior :
    nativeSixCameraExterior (canonicalCompletedC3GammaBoundaryState nativeC9WitnessPoint
      nativeC9WitnessPoint_admissible.1).2 ≠ 0 :=
  canonicalGammaCauchyTrace_hasExterior

end
end CarrySelfAdjointOperator.GammaMaterialSewing
