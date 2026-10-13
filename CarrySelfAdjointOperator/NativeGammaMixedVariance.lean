import CarrySelfAdjointOperator.NativeGammaMixedResponse
import CarrySelfAdjointOperator.NativeGammaThreeSectorResolvent
import CarrySelfAdjointOperator.NativeGammaC9EnergyBound

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false

def nativeMixedResolventVariance (z : ℂ) : ℝ :=
  -(nativeMixedCauchyResponse z).im / z.im - ‖nativeMixedCauchyResponse z‖ ^ 2

theorem nativeMixedGamma_ward (z : ℂ) (hz : z.im ≠ 0) :
    z.im * ‖carryGammaComplexState z hz nativeMixedUnitVector‖ ^ 2 =
      -(nativeMixedCauchyResponse z).im := by
  have h := nativeMixedGammaKernel_greenIdentity z z hz hz
  unfold nativeMixedGammaKernel at h
  rw [inner_self_eq_norm_sq_to_K] at h
  have hi := congrArg Complex.im h
  simp [Complex.mul_im] at hi
  rw [← Complex.ofReal_pow, Complex.ofReal_re] at hi
  nlinarith

theorem nativeMixedCauchy_norm_ledger (z : ℂ) (hz : z.im ≠ 0) :
    ‖nativeComplexCauchy z hz nativeMixedUnitVector‖ ^ 2 =
      ‖nativeMixedCauchyResponse z‖ ^ 2 +
        ‖nativeSixCameraExterior (nativeComplexCauchy z hz nativeMixedUnitVector)‖ ^ 2 := by
  have h := nativeSixCameraProjection_metricLedger
    (nativeComplexCauchy z hz nativeMixedUnitVector) (nativeComplexCauchy z hz nativeMixedUnitVector)
  rw [← nativeSixCameraSynthesis_inner] at h
  change inner ℂ _ _ = inner ℂ (nativeSixCameraProjection _) (nativeSixCameraProjection _) + _ at h
  rw [nativeMixedCauchy_unit_compression] at h
  have hn : ‖nativeMixedUnitVector‖ = 1 := by
    nlinarith [nativeMixedUnitVector_norm_sq, norm_nonneg nativeMixedUnitVector]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), h, map_add,
    inner_self_eq_norm_sq, inner_self_eq_norm_sq]
  simp [norm_smul, hn]

theorem nativeMixedResolventVariance_exact (z : ℂ) (hz : z.im ≠ 0) :
    nativeMixedResolventVariance z =
      ‖nativeSixCameraExterior (nativeComplexCauchy z hz nativeMixedUnitVector)‖ ^ 2 +
      ‖nativeGammaGlobalEscape z hz nativeMixedUnitVector‖ ^ 2 := by
  have hward : -(nativeMixedCauchyResponse z).im / z.im =
      ‖carryGammaComplexState z hz nativeMixedUnitVector‖ ^ 2 := by
    apply (div_eq_iff hz).mpr
    linear_combination -nativeMixedGamma_ward z hz
  have hfull : ‖carryGammaComplexState z hz nativeMixedUnitVector‖ ^ 2 =
      ‖nativeComplexCauchy z hz nativeMixedUnitVector‖ ^ 2 +
        ‖nativeGammaGlobalEscape z hz nativeMixedUnitVector‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), nativeGammaResolvent_fullGram,
      map_add, inner_self_eq_norm_sq, inner_self_eq_norm_sq]
  unfold nativeMixedResolventVariance
  rw [hward, hfull, nativeMixedCauchy_norm_ledger]
  ring

theorem nativeMixedResolventVariance_nonnegative (z : ℂ) (hz : z.im ≠ 0) :
    0 ≤ nativeMixedResolventVariance z := by
  rw [nativeMixedResolventVariance_exact z hz]
  positivity

theorem nativeMixedCauchy_C9_readout (z : ℂ) (hz : z.im ≠ 0) :
    inner ℂ nativeC9Exterior (nativeComplexCauchy z hz nativeMixedUnitVector) =
      (Real.sqrt 278 : ℂ)⁻¹ * (nativeC9Beta z * 3) := by
  rw [nativeMixedUnitVector, map_smul, inner_smul_right]
  have h := nativeC9CauchyReadout_selectsCameraSix z hz nativeMixedRay
  change inner ℂ nativeC9Exterior (nativeComplexCauchy z hz nativeMixedVector) = nativeC9Beta z * 3 at h
  rw [h]

theorem nativeMixedCauchy_C9_energy_lower_bound (z : ℂ) (hz : z.im ≠ 0) :
    9 * ‖nativeC9Beta z‖ ^ 2 / (278 * (9012/139 : ℝ)) ≤
      ‖nativeSixCameraExterior (nativeComplexCauchy z hz nativeMixedUnitVector)‖ ^ 2 := by
  have h := nativeC9Exterior_energy_bound (nativeComplexCauchy z hz nativeMixedUnitVector)
  rw [nativeMixedCauchy_C9_readout] at h
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 278)
  simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_ofNat, mul_pow, inv_pow, hs] at h
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 278 * (9012/139))).mpr
  nlinarith

theorem nativeMixedResolventVariance_C9_lower_bound (z : ℂ) (hz : z.im ≠ 0) :
    9 * ‖nativeC9Beta z‖ ^ 2 / (278 * (9012/139 : ℝ)) ≤ nativeMixedResolventVariance z := by
  apply (nativeMixedCauchy_C9_energy_lower_bound z hz).trans
  rw [nativeMixedResolventVariance_exact z hz]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem nativeMixedResolventVariance_witness_positive :
    0 < nativeMixedResolventVariance nativeC9WitnessPoint := by
  have hp : 0 < 9 * ‖nativeC9Beta nativeC9WitnessPoint‖ ^ 2 / (278 * (9012/139 : ℝ)) := by
    exact div_pos (mul_pos (by norm_num)
      (pow_pos (norm_pos_iff.mpr nativeC9Beta_witness_ne_zero) 2)) (by norm_num)
  exact hp.trans_le (nativeMixedResolventVariance_C9_lower_bound _ nativeC9WitnessPoint_admissible.1)

end
end CarrySelfAdjointOperator.GammaMaterialSewing
