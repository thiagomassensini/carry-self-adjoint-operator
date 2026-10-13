import CarrySelfAdjointOperator.NativeGammaSixCameraProjection
import CarrySelfAdjointOperator.CompletedC3CompressedLogarithmicOperator

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators InnerProductSpace
open NativeCarrySpectralWeyl.Infinite NativeCarryC3Crosswalk CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false

def nativeC3PackedCoefficients (x : FiniteC3GreenPortCarrier 3) : Fin 6 → ℂ :=
  ![x.1 0,x.1 1,x.1 2,x.2 0,x.2 1,x.2 2]

theorem cameraEmbedding_single_eq_smul (b : CameraIndex) (t : ℝ) :
    cameraEmbedding (Finsupp.single b t) = t • cameraVector b := by
  unfold cameraVector
  rw [← map_smul]
  congr 1
  simp

theorem nativeSixCameraSynthesis_pack (x : FiniteC3GreenPortCarrier 3) :
    nativeSixCameraSynthesis (nativeC3PackedCoefficients x) = canonicalC3SixCameraSourceMap x := by
  apply RealHilbertComplexification.ext
  · change RealHilbertComplexification.re (nativeSixCameraSynthesis _) =
      cameraEmbedding (canonicalC3RealCameraFinsupp x)
    rw [canonicalC3RealCameraFinsupp, map_add, map_sum, map_sum]
    simp only [cameraEmbedding_single_eq_smul]
    simp [nativeSixCameraSynthesis, nativeC3PackedCoefficients, nativeComplexCameraVector,
      Fin.sum_univ_succ,
      firstC3CameraIndex, secondC3CameraIndex, atlasSixCameraIndex,
      NativeCarrySpectralWeyl.Finite.sixCamera, add_assoc]
  · change RealHilbertComplexification.im (nativeSixCameraSynthesis _) =
      cameraEmbedding (canonicalC3ImagCameraFinsupp x)
    rw [canonicalC3ImagCameraFinsupp, map_add, map_sum, map_sum]
    simp only [cameraEmbedding_single_eq_smul]
    simp [nativeSixCameraSynthesis, nativeC3PackedCoefficients, nativeComplexCameraVector,
      Fin.sum_univ_succ,
      firstC3CameraIndex, secondC3CameraIndex, atlasSixCameraIndex,
      NativeCarrySpectralWeyl.Finite.sixCamera, add_assoc]

def nativeCanonicalGammaCoefficients (z : ℂ) : Fin 6 → ℂ :=
  nativeC3PackedCoefficients (canonicalCompletedOperatorC3State z)

def nativeCanonicalGammaSource (z : ℂ) : CarryGammaComplexCamera :=
  canonicalCompletedC3SixCameraSource z

def nativeCanonicalGammaCauchyTrace (z : ℂ) (hz : z.im ≠ 0) : CarryGammaComplexCamera :=
  nativeComplexCauchy z hz (nativeCanonicalGammaSource z)

theorem nativeCanonicalGammaSource_eq_synthesis (z : ℂ) :
    nativeCanonicalGammaSource z = nativeSixCameraSynthesis (nativeCanonicalGammaCoefficients z) :=
  (nativeSixCameraSynthesis_pack _).symm

theorem nativeCanonicalGammaSource_noExterior (z : ℂ) :
    nativeSixCameraExterior (nativeCanonicalGammaSource z) = 0 := by
  rw [nativeCanonicalGammaSource_eq_synthesis, nativeSixCameraExterior_synthesis]

theorem nativeCanonicalGammaSource_coordinates (z : ℂ) :
    nativeSixCameraCoordinates (nativeCanonicalGammaSource z) = nativeCanonicalGammaCoefficients z := by
  rw [nativeCanonicalGammaSource_eq_synthesis, nativeSixCameraCoordinates_synthesis]

theorem nativeCanonicalGammaCoefficients_cameraSix (z : ℂ) :
    nativeCanonicalGammaCoefficients z 4 = positiveDirichletGradient (operatorHeightParameter z) 1 := by
  unfold nativeCanonicalGammaCoefficients
  rw [canonicalCompletedOperatorC3State_eq_greenBoundaryPair]
  simp [nativeC3PackedCoefficients]

theorem positiveDirichletGradient_one_ne_zero (s : ℂ) (hs : 0 < s.re) :
    positiveDirichletGradient s 1 ≠ 0 := by
  have hn (n : ℕ) (hn : 0 < n) : ‖natDirichletTerm s n‖ = (n : ℝ)^(-s.re) := by
    unfold natDirichletTerm dirichletTerm
    simpa only [Int.cast_natCast, Complex.ofReal_natCast, Complex.neg_re] using
      Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn : (0 : ℝ) < n) (-s)
  have hnorm : ‖natDirichletTerm s 3‖ < ‖natDirichletTerm s 2‖ := by
    rw [hn 3 (by norm_num), hn 2 (by norm_num)]
    exact Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num) (by linarith)
  intro he
  have heq : natDirichletTerm s 3 = natDirichletTerm s 2 := by
    simpa only [positiveDirichletGradient, Nat.reduceAdd, sub_eq_zero] using he
  rw [heq] at hnorm
  exact (lt_irrefl _ hnorm)

end
end CarrySelfAdjointOperator.GammaMaterialSewing
