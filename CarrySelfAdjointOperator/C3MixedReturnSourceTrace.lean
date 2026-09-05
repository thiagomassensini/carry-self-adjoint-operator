import CarrySelfAdjointOperator.MixedReturnNativeReadout
import CarrySelfAdjointOperator.CompletedC3GreenInverseSewingProbe
import CarrySelfAdjointOperator.CompletedC3CompressedLogarithmicOperator

/-!
# The mixed return readout of the existing C3 source

The actual source packs Green-port coefficients into CameraHilbert. These
are not the six camera resultants. We calculate its normalized return
projection in the intrinsic Gram metric, without replacing the source,
Gamma field, native moments, or operator.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- The existing return ray, embedded with the same six camera labels as the
faithful C3 source. -/
def sixCameraReturnFinsupp : CameraFinsupp :=
  (∑ i : Fin 3, Finsupp.single (firstC3CameraIndex i)
    (sixCameraMixedReturnRay ⟨i.val, by omega⟩)) +
  ∑ i : Fin 3, Finsupp.single (secondC3CameraIndex i)
    (sixCameraMixedReturnRay ⟨i.val + 3, by omega⟩)

def sixCameraReturnVector : CameraHilbert :=
  cameraEmbedding sixCameraReturnFinsupp

/-- Unit direction for the intrinsic Gram norm, corresponding to
`G^(1/2) v / sqrt 278` in whitened Euclidean coordinates. -/
def sixCameraReturnUnitVector : CameraHilbert :=
  (Real.sqrt 278)⁻¹ • sixCameraReturnVector

/-- Both realified channels are read by the same intrinsic return direction. -/
def sixCameraReturnReadout (source : RealifiedCameraComplexification) : ℂ :=
  (inner ℝ sixCameraReturnUnitVector source.fst : ℂ) +
    Complex.I * (inner ℝ sixCameraReturnUnitVector source.snd : ℂ)

set_option maxHeartbeats 800000 in
 theorem inner_sixCameraReturnVector_first (i : Fin 3) :
    inner ℝ sixCameraReturnVector (cameraVector (firstC3CameraIndex i)) = 0 := by
  unfold sixCameraReturnVector sixCameraReturnFinsupp cameraVector
  rw [map_add, map_sum, map_sum, inner_add_left]
  simp only [sum_inner]
  fin_cases i <;>
    norm_num [cameraEmbedding_inner, gramForm_single_single,
      sixCameraMixedReturnRay, Fin.sum_univ_succ,
      gramKernel, periodicMeanKernel, periodicProductMean,
      periodicProductSum, pairPeriod, firstC3CameraIndex,
      secondC3CameraIndex, cameraLabel, cameraSlope,
      profile, c2Profile, oddProfile, evenProfile, dvdIndicator,
      Finset.sum_range_succ]

set_option maxHeartbeats 800000 in
 theorem inner_sixCameraReturnVector_second (i : Fin 3) :
    inner ℝ sixCameraReturnVector (cameraVector (secondC3CameraIndex i)) =
      if i = 1 then 278 / 3 else 0 := by
  unfold sixCameraReturnVector sixCameraReturnFinsupp cameraVector
  rw [map_add, map_sum, map_sum, inner_add_left]
  simp only [sum_inner]
  fin_cases i <;>
    norm_num [cameraEmbedding_inner, gramForm_single_single,
      sixCameraMixedReturnRay, Fin.sum_univ_succ,
      gramKernel, periodicMeanKernel, periodicProductMean,
      periodicProductSum, pairPeriod, firstC3CameraIndex,
      secondC3CameraIndex, cameraLabel, cameraSlope,
      profile, c2Profile, oddProfile, evenProfile, dvdIndicator,
      Finset.sum_range_succ]

/-- Gram evaluation of the actual C3 coefficient packing. -/
theorem inner_sixCameraReturnVector_sourceMap_fst
    (x : FiniteC3GreenPortCarrier 3) :
    inner ℝ sixCameraReturnVector (canonicalC3SixCameraSourceMap x).fst =
      (278 / 3) * (x.2 1).re := by
  unfold canonicalC3SixCameraSourceMap
  rw [WithLp.toLp_fst]
  unfold canonicalC3RealCameraFinsupp
  rw [map_add, map_sum, map_sum, inner_add_right]
  simp only [inner_sum]
  have hsingle (i : CameraIndex) (a : ℝ) :
      cameraEmbedding (Finsupp.single i a) = a • cameraVector i := by
    rw [cameraVector, ← map_smul]
    congr 1
    simp
  simp_rw [hsingle, real_inner_smul_right]
  simp [inner_sixCameraReturnVector_first, inner_sixCameraReturnVector_second]
  ring

theorem inner_sixCameraReturnVector_sourceMap_snd
    (x : FiniteC3GreenPortCarrier 3) :
    inner ℝ sixCameraReturnVector (canonicalC3SixCameraSourceMap x).snd =
      (278 / 3) * (x.2 1).im := by
  unfold canonicalC3SixCameraSourceMap
  rw [WithLp.toLp_snd]
  unfold canonicalC3ImagCameraFinsupp
  rw [map_add, map_sum, map_sum, inner_add_right]
  simp only [inner_sum]
  have hsingle (i : CameraIndex) (a : ℝ) :
      cameraEmbedding (Finsupp.single i a) = a • cameraVector i := by
    rw [cameraVector, ← map_smul]
    congr 1
    simp
  simp_rw [hsingle, real_inner_smul_right]
  simp [inner_sixCameraReturnVector_first, inner_sixCameraReturnVector_second]
  ring

/-- The source projection selects the horizontal middle Green coordinate;
it does not synthesize the resultants of cameras 2, 3, 4 and 6. -/
theorem sixCameraReturnReadout_sourceMap (x : FiniteC3GreenPortCarrier 3) :
    sixCameraReturnReadout (canonicalC3SixCameraSourceMap x) =
      ((Real.sqrt 278 / 3 : ℝ) : ℂ) * x.2 1 := by
  have hnorm : (Real.sqrt 278)⁻¹ * (278 / 3) = Real.sqrt 278 / 3 := by
    have hs : Real.sqrt 278 ≠ 0 := by positivity
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 278)
    field_simp
    nlinarith
  unfold sixCameraReturnReadout sixCameraReturnUnitVector
  rw [real_inner_smul_left, real_inner_smul_left,
    inner_sixCameraReturnVector_sourceMap_fst, inner_sixCameraReturnVector_sourceMap_snd]
  simp only [← mul_assoc, hnorm]
  apply Complex.ext <;> simp

/-- Exact readout of the canonical completed C3 source. -/
theorem sixCameraReturnReadout_canonicalSource (z : ℂ) :
    sixCameraReturnReadout (canonicalCompletedC3SixCameraSource z) =
      ((Real.sqrt 278 / 3 : ℝ) : ℂ) *
        positiveDirichletGradient (operatorHeightParameter z) 1 := by
  rw [canonicalCompletedC3SixCameraSource, sixCameraReturnReadout_sourceMap,
    canonicalCompletedOperatorC3State_eq_greenBoundaryPair,
    finiteC3GenuineBracketGreenBoundaryPair_snd_apply]
  norm_num


/-- The intrinsic Hilbert norm agrees with the source Gram normalization. -/
theorem sixCameraReturnVector_norm_sq : ‖sixCameraReturnVector‖ ^ 2 = 278 := by
  rw [← real_inner_self_eq_norm_sq]
  nth_rw 2 [sixCameraReturnVector]
  unfold sixCameraReturnFinsupp
  rw [map_add, map_sum, map_sum, inner_add_right]
  simp only [inner_sum]
  have hsingle (i : CameraIndex) (a : ℝ) :
      cameraEmbedding (Finsupp.single i a) = a • cameraVector i := by
    rw [cameraVector, ← map_smul]
    congr 1
    simp
  simp_rw [hsingle, real_inner_smul_right]
  norm_num [inner_sixCameraReturnVector_first, inner_sixCameraReturnVector_second,
    sixCameraMixedReturnRay, Fin.sum_univ_succ]

/-- No arbitrary calibration is used in the return projection. -/
theorem sixCameraReturnUnitVector_norm_sq : ‖sixCameraReturnUnitVector‖ ^ 2 = 1 := by
  unfold sixCameraReturnUnitVector
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 278), sixCameraReturnVector_norm_sq]
  norm_num

/-- Explicit arithmetic coordinate selected by the actual source projection. -/
theorem sixCameraReturnReadout_canonicalSource_eq_powers (z : ℂ) :
    sixCameraReturnReadout (canonicalCompletedC3SixCameraSource z) =
      ((Real.sqrt 278 / 3 : ℝ) : ℂ) *
        ((3 : ℂ) ^ (-operatorHeightParameter z) -
          (2 : ℂ) ^ (-operatorHeightParameter z)) := by
  rw [sixCameraReturnReadout_canonicalSource]
  norm_num [positiveDirichletGradient, natDirichletTerm, dirichletTerm]

end
end CarrySelfAdjointOperator
