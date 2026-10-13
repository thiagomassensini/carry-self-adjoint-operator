import CarrySelfAdjointOperator.NativeGammaMixedSource
import CarrySelfAdjointOperator.NativeGammaCanonicalExteriorWitness

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false

theorem nativeC9Exterior_readout_exterior (u : CarryGammaComplexCamera) :
    inner ℂ nativeC9Exterior u = inner ℂ nativeC9Exterior (nativeSixCameraExterior u) := by
  conv_lhs => rw [nativeSixCameraProjection_roundtrip u]
  rw [inner_add_right, nativeC9Exterior_orthogonal, zero_add]

theorem nativeC9CauchyReadout_mixedDuality (z : ℂ) (hz : z.im ≠ 0) (c : Fin 6 → ℂ) :
    inner ℂ nativeC9Exterior (nativeComplexCauchy z hz (nativeSixCameraSynthesis c)) =
      (3 * nativeC9Beta z / 278) * inner ℂ nativeMixedVector (nativeSixCameraSynthesis c) := by
  rw [nativeC9CauchyReadout_selectsCameraSix, nativeMixedVector_inner_synthesis]
  ring

theorem nativeC9CauchyReadout_complement_zero (z : ℂ) (hz : z.im ≠ 0) (c : Fin 6 → ℂ) :
    inner ℂ nativeC9Exterior (nativeComplexCauchy z hz
      (nativeSixCameraSynthesis (nativeMixedComplement c))) = 0 := by
  rw [nativeC9CauchyReadout_selectsCameraSix, nativeMixedComplement_cameraSix, mul_zero]

theorem nativeC9CauchyReadout_mixed_eq_full (z : ℂ) (hz : z.im ≠ 0) (c : Fin 6 → ℂ) :
    inner ℂ nativeC9Exterior (nativeComplexCauchy z hz
        (nativeSixCameraSynthesis (nativeMixedCoefficients c))) =
      inner ℂ nativeC9Exterior (nativeComplexCauchy z hz (nativeSixCameraSynthesis c)) := by
  rw [nativeC9CauchyReadout_selectsCameraSix, nativeC9CauchyReadout_selectsCameraSix,
    nativeMixedCoefficients_cameraSix]

theorem nativeC9Exterior_energy_bound (u : CarryGammaComplexCamera) :
    ‖inner ℂ nativeC9Exterior u‖ ^ 2 ≤
      (9012/139 : ℝ) * ‖nativeSixCameraExterior u‖ ^ 2 := by
  rw [nativeC9Exterior_readout_exterior]
  have h := norm_inner_le_norm (𝕜 := ℂ) nativeC9Exterior (nativeSixCameraExterior u)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  simpa only [mul_pow, nativeC9Exterior_norm_squared] using hsq

theorem nativeC9CauchyExterior_energy_bound (z : ℂ) (hz : z.im ≠ 0) (c : Fin 6 → ℂ) :
    ‖nativeC9Beta z‖ ^ 2 * ‖c 4‖ ^ 2 ≤ (9012/139 : ℝ) *
      ‖nativeSixCameraExterior (nativeComplexCauchy z hz (nativeSixCameraSynthesis c))‖ ^ 2 := by
  have h := nativeC9Exterior_energy_bound (nativeComplexCauchy z hz (nativeSixCameraSynthesis c))
  rwa [nativeC9CauchyReadout_selectsCameraSix, norm_mul, mul_pow] at h

theorem nativeC9CauchyExterior_energy_bound_divided (z : ℂ) (hz : z.im ≠ 0) (c : Fin 6 → ℂ) :
    ‖nativeC9Beta z‖ ^ 2 * ‖c 4‖ ^ 2 / (9012/139 : ℝ) ≤
      ‖nativeSixCameraExterior (nativeComplexCauchy z hz (nativeSixCameraSynthesis c))‖ ^ 2 := by
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 9012/139)).mpr
    (by simpa [mul_comm] using nativeC9CauchyExterior_energy_bound z hz c)

theorem nativeCanonicalGammaCauchyExterior_energy_lower_bound (z : ℂ) (hz : z.im ≠ 0) :
    ‖nativeC9Beta z‖ ^ 2 *
        ‖CPFormal.Analytic.Cp.positiveDirichletGradient (operatorHeightParameter z) 1‖ ^ 2 ≤
      (9012/139 : ℝ) * ‖nativeSixCameraExterior (nativeCanonicalGammaCauchyTrace z hz)‖ ^ 2 := by
  have h := nativeC9CauchyExterior_energy_bound z hz (nativeCanonicalGammaCoefficients z)
  rwa [nativeCanonicalGammaCoefficients_cameraSix, ← nativeCanonicalGammaSource_eq_synthesis] at h

theorem nativeCanonicalGammaCauchyExterior_energy_witness :
    0 < ‖nativeC9Beta nativeC9WitnessPoint‖ ^ 2 *
        ‖CPFormal.Analytic.Cp.positiveDirichletGradient (operatorHeightParameter nativeC9WitnessPoint) 1‖ ^ 2 ∧
    ‖nativeC9Beta nativeC9WitnessPoint‖ ^ 2 *
        ‖CPFormal.Analytic.Cp.positiveDirichletGradient (operatorHeightParameter nativeC9WitnessPoint) 1‖ ^ 2 ≤
      (9012/139 : ℝ) * ‖nativeSixCameraExterior (nativeCanonicalGammaCauchyTrace
        nativeC9WitnessPoint nativeC9WitnessPoint_admissible.1)‖ ^ 2 := by
  refine ⟨mul_pos (pow_pos (norm_pos_iff.mpr nativeC9Beta_witness_ne_zero) 2)
    (pow_pos (norm_pos_iff.mpr (positiveDirichletGradient_one_ne_zero _
      nativeC9WitnessPoint_strip.1)) 2), nativeCanonicalGammaCauchyExterior_energy_lower_bound _ _⟩

end
end CarrySelfAdjointOperator.GammaMaterialSewing
