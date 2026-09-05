import CarrySelfAdjointOperator.C3MixedReturnTraceObstruction
import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration

/-!
# A camera-domain test of the existing full Gamma energy

The logarithmic multiplier and its Gamma field are unchanged. A single
camera test in the maximal domain controls the full two-quadrature Gamma
state through its exact defect equation. This is not the raw C3 norm.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace RealInnerProductSpace
open Set MeasureTheory Filter Topology

set_option autoImplicit false

namespace CarrySelfAdjointOperator
open CPFormal.Analytic.Cp NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Boundary
noncomputable section

/-- The already constructed Naimark camera vector, in its proved domain. -/
def cameraLogDomainVector (camera : CameraIndex) : logarithmicMultiplication.domain :=
  ⟨naimarkCameraVector camera,
    naimarkCameraVector_mem_logarithmicMultiplicationDomain camera⟩

/-- The diagonal second camera moment is literally the squared norm of the
existing logarithmic multiplier applied to the existing Naimark vector. -/
theorem norm_logarithmic_camera_sq (camera : CameraIndex) :
    ‖logarithmicMultiplication (cameraLogDomainVector camera)‖ ^ 2 =
      gramKernel camera camera *
        (1 + Real.log (cameraSlope (cameraLabel camera)) ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hpoint :
      (fun x => inner ℝ
        (logarithmicMultiplication (cameraLogDomainVector camera) x)
        (logarithmicMultiplication (cameraLogDomainVector camera) x)) =ᵐ[positiveLebesgueMeasure]
      (cameraInterval camera).indicator
        (fun x => (1 + Real.log x) ^ 2 * periodicMeanKernel camera camera) := by
    filter_upwards [logarithmicMultiplication_coeFn (cameraLogDomainVector camera),
      naimarkCameraVector_coeFn camera] with x hY hV
    rw [hY]
    change inner ℝ (logarithmicCoordinate x • naimarkCameraVector camera x)
      (logarithmicCoordinate x • naimarkCameraVector camera x) = _
    rw [hV]
    by_cases hx : x ∈ cameraInterval camera
    · simp only [Set.indicator_of_mem hx, real_inner_smul_left,
        real_inner_smul_right, inner_kolmogorovVector, logarithmicCoordinate]
      ring
    · simp [Set.indicator_of_notMem hx]
  rw [integral_congr_ae hpoint, integral_indicator (cameraInterval_measurable camera),
    positiveLebesgueMeasure, Measure.restrict_restrict (cameraInterval_measurable camera),
    inter_eq_left.mpr (cameraInterval_subset_positive camera), integral_mul_const]
  have hs : (0 : ℝ) < cameraSlope (cameraLabel camera) := by
    exact_mod_cast cameraSlope_pos camera
  rw [cameraInterval, ← intervalIntegral.integral_of_le hs.le,
    integral_centeredLogSq_zero hs]
  unfold gramKernel
  simp only [min_self]
  ring

/-- A fixed source pairing is controlled by the full Gamma norm. Both
quadratures and the logarithmic-domain term are retained. -/
theorem carryGammaSource_camera_test_bound
    (z : ℂ) (hz : z.im ≠ 0) (u : RealifiedCameraComplexification)
    (v : logarithmicMultiplication.domain) :
    |inner ℝ (v : NaimarkSpace) (naimarkIsometry u.fst)| ≤
      (|z.re| * ‖(v : NaimarkSpace)‖ + |z.im| * ‖(v : NaimarkSpace)‖ +
        ‖logarithmicMultiplication v‖) * ‖carryGammaComplexState z hz u‖ := by
  let f := carryGammaSource z hz u
  have h := congrArg WithLp.fst (carryGammaSource_defect_equation z hz u)
  simp only [realifiedNaimarkScalar_fst, WithLp.add_fst,
    realifiedLogarithmicMultiplication_fst, realifiedNaimarkPort_fst] at h
  have heq :
      inner ℝ (v : NaimarkSpace) (naimarkIsometry u.fst) =
        z.re * inner ℝ (v : NaimarkSpace) f.fst -
        z.im * inner ℝ (v : NaimarkSpace) f.snd -
        inner ℝ (logarithmicMultiplication v) f.fst := by
    have he := congrArg (fun t : NaimarkSpace => inner ℝ (v : NaimarkSpace) t) h
    have hsym := logarithmicMultiplication_isFormalAdjoint v
      (carryGammaIntoDomain z hz u).1
    simp only [carryGammaIntoDomain_fst_coe] at hsym
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right] at he
    change z.re * inner ℝ (v : NaimarkSpace) f.fst -
      z.im * inner ℝ (v : NaimarkSpace) f.snd =
      inner ℝ (v : NaimarkSpace) (logarithmicMultiplication (carryGammaIntoDomain z hz u).1) +
      inner ℝ (v : NaimarkSpace) (naimarkIsometry u.fst) at he
    rw [← hsym] at he
    linarith
  have hf : ‖f.fst‖ ≤ ‖carryGammaComplexState z hz u‖ := by
    exact WithLp.norm_fst_le NaimarkSpace f
  have hg : ‖f.snd‖ ≤ ‖carryGammaComplexState z hz u‖ := by
    exact WithLp.norm_snd_le NaimarkSpace f
  rw [heq]
  calc
    _ ≤ |z.re * inner ℝ (v : NaimarkSpace) f.fst| +
        |z.im * inner ℝ (v : NaimarkSpace) f.snd| +
        |inner ℝ (logarithmicMultiplication v) f.fst| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (|z.re| * ‖(v : NaimarkSpace)‖ + |z.im| * ‖(v : NaimarkSpace)‖ +
        ‖logarithmicMultiplication v‖) * ‖carryGammaComplexState z hz u‖ := by
      rw [abs_mul, abs_mul]
      have h1 := abs_real_inner_le_norm (v : NaimarkSpace) f.fst
      have h2 := abs_real_inner_le_norm (v : NaimarkSpace) f.snd
      have h3 := abs_real_inner_le_norm (logarithmicMultiplication v) f.fst
      have h1p := h1.trans (mul_le_mul_of_nonneg_left hf (norm_nonneg _))
      have h2p := h2.trans (mul_le_mul_of_nonneg_left hg (norm_nonneg _))
      have h3p := h3.trans (mul_le_mul_of_nonneg_left hf (norm_nonneg _))
      nlinarith [mul_le_mul_of_nonneg_left h1p (abs_nonneg z.re),
        mul_le_mul_of_nonneg_left h2p (abs_nonneg z.im)]

set_option maxHeartbeats 800000 in
theorem inner_cameraFive_firstC3 (i : Fin 3) :
    inner ℝ (cameraVector (secondC3CameraIndex 0))
      (cameraVector (firstC3CameraIndex i)) = 0 := by
  unfold cameraVector
  rw [cameraEmbedding_inner, gramForm_single_single]
  fin_cases i <;> norm_num [gramKernel, periodicMeanKernel, periodicProductMean,
    periodicProductSum, pairPeriod, firstC3CameraIndex, secondC3CameraIndex,
    cameraLabel, cameraSlope, profile, c2Profile, oddProfile, evenProfile,
    dvdIndicator, Finset.sum_range_succ]

set_option maxHeartbeats 800000 in
theorem inner_cameraFive_secondC3 (i : Fin 3) :
    inner ℝ (cameraVector (secondC3CameraIndex 0))
      (cameraVector (secondC3CameraIndex i)) = if i = 0 then 20 else 0 := by
  unfold cameraVector
  rw [cameraEmbedding_inner, gramForm_single_single]
  fin_cases i <;> norm_num [gramKernel, periodicMeanKernel, periodicProductMean,
    periodicProductSum, pairPeriod, secondC3CameraIndex, cameraLabel, cameraSlope,
    profile, c2Profile, oddProfile, evenProfile, dvdIndicator, Finset.sum_range_succ]

theorem cameraFive_gram_diagonal :
    gramKernel (secondC3CameraIndex 0) (secondC3CameraIndex 0) = 20 := by
  have h := inner_cameraFive_secondC3 0
  unfold cameraVector at h
  rw [cameraEmbedding_inner, gramForm_single_single] at h
  norm_num at h
  exact h

theorem norm_naimark_cameraFive_le_five :
    ‖naimarkCameraVector (secondC3CameraIndex 0)‖ ≤ 5 := by
  have h := norm_naimarkCameraVector_sq (secondC3CameraIndex 0)
  rw [cameraFive_gram_diagonal] at h
  nlinarith [norm_nonneg (naimarkCameraVector (secondC3CameraIndex 0))]

theorem norm_logarithmic_cameraFive_le_ten :
    ‖logarithmicMultiplication (cameraLogDomainVector (secondC3CameraIndex 0))‖ ≤ 10 := by
  have h := norm_logarithmic_camera_sq (secondC3CameraIndex 0)
  rw [cameraFive_gram_diagonal] at h
  have hslope : cameraSlope (cameraLabel (secondC3CameraIndex 0)) = 5 := by decide
  rw [hslope] at h
  norm_num only [Nat.cast_ofNat] at h
  have hlog0 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hexp : (5 : ℝ) < Real.exp 2 := by
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 4
    norm_num [Finset.sum_range_succ] at he
    linarith
  have hlog2 : Real.log 5 < 2 := (Real.log_lt_iff_lt_exp (by norm_num)).2 hexp
  have hlogSq : Real.log 5 ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg (show 0 ≤ 2 - Real.log 5 by linarith)
      (show 0 ≤ 2 + Real.log 5 by linarith)]
  nlinarith [hlogSq,
    norm_nonneg (logarithmicMultiplication (cameraLogDomainVector (secondC3CameraIndex 0)))]

/-- The test reads a coordinate of the full existing source, with all
remaining coordinates still present in the Gamma vector being bounded. -/
theorem canonicalC3CameraFive_source_test (z : ℂ) :
    inner ℝ (naimarkCameraVector (secondC3CameraIndex 0))
      (naimarkIsometry (canonicalCompletedC3SixCameraSource z).fst) =
      20 * (positiveDirichletGradient (operatorHeightParameter z) 0).re := by
  rw [← naimarkIsometry_cameraVector, naimarkIsometry.inner_map_map]
  unfold canonicalCompletedC3SixCameraSource canonicalC3SixCameraSourceMap
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
  simp only [inner_cameraFive_firstC3, inner_cameraFive_secondC3, mul_zero,
    Finset.sum_const_zero, zero_add]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [canonicalCompletedOperatorC3State_eq_greenBoundaryPair,
    finiteC3GenuineBracketGreenBoundaryPair_snd_apply]
  norm_num
  ring

/-- A quantitative lower bound for the complete Gamma state follows from
one actual camera-domain test. It includes any cancellation among the
mixed component and its complement. -/
theorem canonicalC3Gamma_energy_gt_sixteenth_of_cameraFive
    (z : ℂ) (hz : z.im ≠ 0) (hre : |z.re| ≤ 1) (him : |z.im| ≤ 1)
    (hcoord : (1 / 4 : ℝ) <
      |(positiveDirichletGradient (operatorHeightParameter z) 0).re|) :
    (1 / 16 : ℝ) < ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 := by
  have h := carryGammaSource_camera_test_bound z hz
    (canonicalCompletedC3SixCameraSource z)
    (cameraLogDomainVector (secondC3CameraIndex 0))
  change |inner ℝ (naimarkCameraVector (secondC3CameraIndex 0))
    (naimarkIsometry (canonicalCompletedC3SixCameraSource z).fst)| ≤ _ at h
  rw [canonicalC3CameraFive_source_test, abs_mul] at h
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 20)] at h
  have hv := norm_naimark_cameraFive_le_five
  have hY := norm_logarithmic_cameraFive_le_ten
  have hcoef : |z.re| * ‖naimarkCameraVector (secondC3CameraIndex 0)‖ +
      |z.im| * ‖naimarkCameraVector (secondC3CameraIndex 0)‖ +
      ‖logarithmicMultiplication (cameraLogDomainVector (secondC3CameraIndex 0))‖ ≤ 20 := by
    have h1 := mul_le_mul_of_nonneg_right hre
      (norm_nonneg (naimarkCameraVector (secondC3CameraIndex 0)))
    have h2 := mul_le_mul_of_nonneg_right him
      (norm_nonneg (naimarkCameraVector (secondC3CameraIndex 0)))
    nlinarith
  have htotal := h.trans (mul_le_mul_of_nonneg_right hcoef
    (norm_nonneg (carryGammaComplexState z hz (canonicalCompletedC3SixCameraSource z))))
  change 20 * |(positiveDirichletGradient (operatorHeightParameter z) 0).re| ≤
    20 * ‖canonicalCompletedC3PolarizedGammaState z hz‖ at htotal
  nlinarith [norm_nonneg (canonicalCompletedC3PolarizedGammaState z hz)]

end
end CarrySelfAdjointOperator
