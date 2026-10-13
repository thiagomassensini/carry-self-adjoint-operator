import CarrySelfAdjointOperator.NativeGammaMixedProfiles
import CarrySelfAdjointOperator.NativeGammaComplexLinearState

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators InnerProductSpace ComplexConjugate Matrix
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

def nativeMixedCauchyResponse (z : ℂ) : ℂ :=
  (-9 * nativeCauchyIntervalIntegral 3 z - 8 * nativeCauchyIntervalIntegral 4 z +
    33 * nativeCauchyIntervalIntegral 6 z) / 139

theorem nativeMixedCauchy_camera_readout (z : ℂ) (hz : z.im ≠ 0) (i : Fin 6) :
    inner ℂ (nativeComplexCameraVector (atlasSixCameraIndex i))
        (nativeComplexCauchy z hz nativeMixedVector) =
      if i = 4 then (278/3 : ℂ) * nativeMixedCauchyResponse z else 0 := by
  simp only [nativeMixedVector, nativeSixCameraSynthesis, LinearMap.coe_mk,
    AddHom.coe_mk, map_sum, map_smul, inner_sum, inner_smul_right,
    nativeComplexCamera_Cauchy_integral, nativeSixPeriodicMean_eq_original]
  fin_cases i <;> simp only [Fin.ext_iff] <;>
    norm_num [nativeMixedRay, nativeSixPeriodicMean, atlasSixCameraIndex, sixCamera,
      cameraSlope, cameraLabel, nativeMixedCauchyResponse, Fin.sum_univ_succ] <;> ring

theorem nativeMixedCauchy_responseCoordinates (z : ℂ) (hz : z.im ≠ 0) :
    nativeSixCameraCoordinates (nativeComplexCauchy z hz nativeMixedVector) =
      nativeMixedCauchyResponse z • nativeMixedRay := by
  have he : nativeSixCameraAnalysis (nativeComplexCauchy z hz nativeMixedVector) =
      nativeSixCameraGram *ᵥ (nativeMixedCauchyResponse z • nativeMixedRay) := by
    ext i
    change inner ℂ (nativeComplexCameraVector (atlasSixCameraIndex i)) _ = _
    rw [nativeMixedCauchy_camera_readout]
    fin_cases i <;>
      simp [nativeSixCameraGram, sixCameraGram, sixCameraGramRat, Matrix.mulVec,
        dotProduct, nativeMixedRay, Fin.sum_univ_succ] <;> ring
  change nativeSixCameraGram⁻¹ *ᵥ nativeSixCameraAnalysis _ = _
  rw [he, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ nativeSixCameraGram_isUnit,
    Matrix.one_mulVec]

theorem nativeMixedCauchy_compression (z : ℂ) (hz : z.im ≠ 0) :
    nativeSixCameraProjection (nativeComplexCauchy z hz nativeMixedVector) =
      nativeMixedCauchyResponse z • nativeMixedVector := by
  change nativeSixCameraSynthesis (nativeSixCameraCoordinates _) = _
  rw [nativeMixedCauchy_responseCoordinates, map_smul]
  rfl

theorem nativeMixedCauchy_unit_compression (z : ℂ) (hz : z.im ≠ 0) :
    nativeSixCameraProjection (nativeComplexCauchy z hz nativeMixedUnitVector) =
      nativeMixedCauchyResponse z • nativeMixedUnitVector := by
  rw [nativeMixedUnitVector, map_smul, map_smul, nativeMixedCauchy_compression]
  simp only [smul_smul, mul_comm]

theorem nativeMixedUnitVector_exterior_orthogonal (u : CarryGammaComplexCamera) :
    inner ℂ nativeMixedUnitVector (nativeSixCameraExterior u) = 0 := by
  rw [nativeMixedUnitVector, inner_smul_left]
  exact mul_eq_zero_of_right _ (nativeSixCameraExterior_orthogonal nativeMixedRay u)

theorem nativeMixedCauchy_unit_readout (z : ℂ) (hz : z.im ≠ 0) :
    inner ℂ nativeMixedUnitVector (nativeComplexCauchy z hz nativeMixedUnitVector) =
      nativeMixedCauchyResponse z := by
  have h := nativeSixCameraProjection_roundtrip (nativeComplexCauchy z hz nativeMixedUnitVector)
  have hn : ‖nativeMixedUnitVector‖ = 1 := by
    nlinarith [nativeMixedUnitVector_norm_sq, norm_nonneg nativeMixedUnitVector]
  change _ = nativeSixCameraProjection _ + _ at h
  rw [h, inner_add_right, nativeMixedCauchy_unit_compression,
    inner_smul_right, nativeMixedUnitVector_exterior_orthogonal, add_zero,
    inner_self_eq_norm_sq_to_K, hn]
  simp

def nativeMixedGammaKernel (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  inner ℂ (carryGammaComplexState z hz nativeMixedUnitVector)
    (carryGammaComplexState w hw nativeMixedUnitVector)

theorem nativeMixedGammaKernel_greenIdentity (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    (w - conj z) * nativeMixedGammaKernel z w hz hw =
      conj (nativeMixedCauchyResponse z) - nativeMixedCauchyResponse w := by
  have h := carryGammaComplex_twoParameter_greenIdentity z w hz hw
    nativeMixedUnitVector nativeMixedUnitVector
  rw [← nativeComplexCauchy_apply, ← nativeComplexCauchy_apply] at h
  have he : inner ℂ (nativeComplexCauchy z hz nativeMixedUnitVector) nativeMixedUnitVector =
      conj (nativeMixedCauchyResponse z) := by
    rw [← inner_conj_symm]
    rw [nativeMixedCauchy_unit_readout]
  rw [he, nativeMixedCauchy_unit_readout] at h
  unfold nativeMixedGammaKernel
  linear_combination -h

end
end CarrySelfAdjointOperator.GammaMaterialSewing
