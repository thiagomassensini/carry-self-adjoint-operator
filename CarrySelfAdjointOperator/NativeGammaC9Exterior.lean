import CarrySelfAdjointOperator.NativeGammaCauchyIntegral
import CarrySelfAdjointOperator.NativeGammaSixCameraProjection

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators InnerProductSpace ComplexConjugate Matrix
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

def nativeCameraNine : CameraIndex := ⟨9, by norm_num⟩

def nativeC9ProjectedCoefficients : Fin 6 → ℂ :=
  ![-54/139,112/139,18/139,0,27/139,0]

def nativeC9Exterior : CarryGammaComplexCamera :=
  nativeComplexCameraVector nativeCameraNine - nativeSixCameraSynthesis nativeC9ProjectedCoefficients

theorem nativeC9Exterior_literal :
    nativeC9Exterior = nativeComplexCameraVector nativeCameraNine +
      (54/139 : ℂ) • nativeComplexCameraVector (atlasSixCameraIndex 0) -
      (112/139 : ℂ) • nativeComplexCameraVector (atlasSixCameraIndex 1) -
      (18/139 : ℂ) • nativeComplexCameraVector (atlasSixCameraIndex 2) -
      (27/139 : ℂ) • nativeComplexCameraVector (atlasSixCameraIndex 4) := by
  simp only [nativeC9Exterior, nativeSixCameraSynthesis, LinearMap.coe_mk, AddHom.coe_mk]
  norm_num [nativeC9ProjectedCoefficients, Fin.sum_univ_succ, atlasSixCameraIndex, sixCamera]
  module

theorem nativeC9_camera_analysis :
    nativeSixCameraAnalysis (nativeComplexCameraVector nativeCameraNine) = ![0,6,0,0,12,0] := by
  ext i
  change inner ℂ (nativeComplexCameraVector (atlasSixCameraIndex i))
    (nativeComplexCameraVector nativeCameraNine) = _
  rw [nativeComplexCameraVector_inner]
  fin_cases i <;> norm_num [nativeCameraNine, atlasSixCameraIndex, sixCamera, gramKernel,
    periodicMeanKernel, periodicProductMean, periodicProductSum, pairPeriod, cameraLabel,
    cameraSlope, profile, c2Profile, oddProfile, evenProfile, dvdIndicator, Finset.sum_range_succ]

theorem nativeC9_projected_solve :
    nativeSixCameraGram *ᵥ nativeC9ProjectedCoefficients = ![0,6,0,0,12,0] := by
  ext i
  fin_cases i <;> norm_num [nativeSixCameraGram, sixCameraGram, sixCameraGramRat,
    nativeC9ProjectedCoefficients, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem nativeC9Coordinates_exact :
    nativeSixCameraCoordinates (nativeComplexCameraVector nativeCameraNine) =
      nativeC9ProjectedCoefficients := by
  change nativeSixCameraGram⁻¹ *ᵥ nativeSixCameraAnalysis _ = _
  rw [nativeC9_camera_analysis, ← nativeC9_projected_solve, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ nativeSixCameraGram_isUnit, Matrix.one_mulVec]

theorem nativeC9Exterior_eq_Q :
    nativeC9Exterior = nativeSixCameraExterior (nativeComplexCameraVector nativeCameraNine) := by
  change _ - _ = _ - nativeSixCameraSynthesis (nativeSixCameraCoordinates _)
  rw [nativeC9Coordinates_exact]
  rfl

theorem nativeC9Exterior_orthogonal (c : Fin 6 → ℂ) :
    inner ℂ nativeC9Exterior (nativeSixCameraSynthesis c) = 0 := by
  rw [nativeC9Exterior_eq_Q, ← inner_conj_symm, nativeSixCameraExterior_orthogonal, map_zero]

theorem nativeC9Exterior_norm_squared : ‖nativeC9Exterior‖^2 = (9012/139 : ℝ) := by
  have he : inner ℂ nativeC9Exterior nativeC9Exterior = (9012/139 : ℂ) := by
    have hx : inner ℂ nativeC9Exterior nativeC9Exterior =
        inner ℂ nativeC9Exterior (nativeComplexCameraVector nativeCameraNine) := by
      calc
        _ = inner ℂ nativeC9Exterior (nativeComplexCameraVector nativeCameraNine -
          nativeSixCameraSynthesis nativeC9ProjectedCoefficients) := rfl
        _ = _ := by rw [inner_sub_right, nativeC9Exterior_orthogonal, sub_zero]
    rw [hx]
    rw [nativeC9Exterior, inner_sub_left, nativeComplexCameraVector_inner,
      nativeSixCameraSynthesis_inner_any, nativeC9_camera_analysis]
    norm_num [nativeCameraNine, nativeC9ProjectedCoefficients, dotProduct, Fin.sum_univ_succ,
      gramKernel, periodicMeanKernel, periodicProductMean, periodicProductSum, pairPeriod,
      cameraLabel, cameraSlope, profile, oddProfile, dvdIndicator, Finset.sum_range_succ,
      map_div, map_ofNat]
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), he]
  norm_num

def nativeC9Beta (z : ℂ) : ℂ :=
  (-224*nativeCauchyIntervalIntegral 3 z + 48*nativeCauchyIntervalIntegral 4 z +
    80*nativeCauchyIntervalIntegral 6 z)/139

theorem nativeC9CauchyReadout_column (z : ℂ) (hz : z.im ≠ 0) (j : Fin 6) :
    inner ℂ nativeC9Exterior
      (nativeComplexCauchy z hz (nativeComplexCameraVector (atlasSixCameraIndex j))) =
        if j = 4 then nativeC9Beta z else 0 := by
  rw [nativeC9Exterior, inner_sub_left]
  simp only [nativeSixCameraSynthesis, LinearMap.coe_mk, AddHom.coe_mk, sum_inner,
    inner_smul_left, nativeComplexCamera_Cauchy_integral]
  fin_cases j <;> simp only [Fin.ext_iff] <;>
    norm_num [nativeC9ProjectedCoefficients, nativeCameraNine, atlasSixCameraIndex,
      nativeC9Beta, sixCamera, periodicMeanKernel, pairPeriod, periodicProductMean,
      periodicProductSum, cameraLabel, cameraSlope, profile, c2Profile, oddProfile,
      evenProfile, dvdIndicator, Finset.sum_range_succ, Fin.sum_univ_succ,
      Fin.mk.injEq, map_div, map_neg, map_ofNat] <;> ring

/-- Label 6 is index 4; the other five original source columns cancel. -/
theorem nativeC9CauchyReadout_selectsCameraSix (z : ℂ) (hz : z.im ≠ 0) (c : Fin 6 → ℂ) :
    inner ℂ nativeC9Exterior (nativeComplexCauchy z hz (nativeSixCameraSynthesis c)) =
      nativeC9Beta z * c 4 := by
  change inner ℂ nativeC9Exterior
    (nativeComplexCauchy z hz (∑ j, c j • nativeComplexCameraVector (atlasSixCameraIndex j))) = _
  rw [map_sum, inner_sum]
  simp only [map_smul, inner_smul_right, nativeC9CauchyReadout_column]
  simp
  ring

end
end CarrySelfAdjointOperator.GammaMaterialSewing
