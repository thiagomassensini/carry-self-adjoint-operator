import CarrySelfAdjointOperator.CanonicalC3HeightClosureAudit
import CarrySelfAdjointOperator.C3GammaCameraMomentBound
import CarrySelfAdjointOperator.CompletedNativeCausalCellChiralLedger

/-!
# Local trace comparison for the existing canonical Gamma

The camera-domain estimate is compared to the already identified native
response at the Taylor center. No scalar or spectral data are replaced.
-/

open scoped ComplexConjugate InnerProductSpace
open Filter Topology Set

set_option autoImplicit false

namespace CarrySelfAdjointOperator
open CPFormal.Analytic.Cp NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Boundary
noncomputable section

theorem completedNativeGreenResponse_eventually_odd :
    (fun z => completedGreenNormalizedResponse
      completedNativeOperatorCharacteristic completedNativeOperatorBoundaryCompanion (-z)) =ᶠ[𝓝 0]
    (fun z => -completedGreenNormalizedResponse
      completedNativeOperatorCharacteristic completedNativeOperatorBoundaryCompanion z) := by
  have hd := completedNativeOperatorCharacteristic_eventually_even.deriv
  filter_upwards [completedNativeOperatorCharacteristic_eventually_even, hd] with z hz hdz
  rw [deriv_comp_neg] at hdz
  have hderiv : deriv completedNativeOperatorCharacteristic (-z) =
      -deriv completedNativeOperatorCharacteristic z := by linear_combination -hdz
  unfold completedGreenNormalizedResponse
  rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv,
    completedNativeOperatorBoundaryCompanion_eq_neg_deriv, hz, hderiv]
  ring

/-- On the imaginary approach to the Taylor center, native polarization
is exactly the ordinary removable slope from zero. -/
theorem completedNativePolarizedDslope_imaginaryAxis_eventuallyEq_slope :
    (fun t : ℝ => canonicalCompletedNativePolarizedDslopeKernel
      (Complex.I * (t : ℂ)) (Complex.I * (t : ℂ))) =ᶠ[𝓝 0]
    (fun t : ℝ => dslope
      (completedGreenNormalizedResponse completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion) 0 (Complex.I * (t : ℂ))) := by
  have ht : ContinuousAt (fun t : ℝ => Complex.I * (t : ℂ)) 0 := by fun_prop
  have htz : Tendsto (fun t : ℝ => Complex.I * (t : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using ht.tendsto
  have ho := completedNativeGreenResponse_eventually_odd.comp_tendsto htz
  filter_upwards [ho] with t hodd
  simp only [Function.comp_apply] at hodd
  by_cases ht0 : t = 0
  · subst t
    simp [canonicalCompletedNativePolarizedDslopeKernel]
  have hz : Complex.I * (t : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht0)
  have hneg : Complex.I * (t : ℂ) ≠ -(Complex.I * (t : ℂ)) := by
    intro h
    apply hz
    linear_combination h / 2
  have hc : conj (Complex.I * (t : ℂ)) = -(Complex.I * (t : ℂ)) := by simp
  rw [canonicalCompletedNativePolarizedDslopeKernel, hc,
    dslope_of_ne _ hneg, dslope_of_ne _ hz]
  simp only [slope, smul_eq_mul, vsub_eq_sub]
  rw [hodd, completedNativeGreenNormalizedResponse_zero]
  simp only [sub_neg_eq_add, sub_zero]
  field_simp [hz]

/-- The target diagonal tends to the already proved native zeroth moment. -/
theorem completedNativePolarizedDslope_imaginaryAxis_tendsto :
    Tendsto (fun t : ℝ => canonicalCompletedNativePolarizedDslopeKernel
      (Complex.I * (t : ℂ)) (Complex.I * (t : ℂ))) (𝓝 0)
      (𝓝 (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) := by
  have hc := continuousAt_dslope_same.mpr
    completedNativeGreenNormalizedResponse_hasDerivAt_h0.differentiableAt
  have ht : ContinuousAt (fun t : ℝ => Complex.I * (t : ℂ)) 0 := by fun_prop
  have htz : Tendsto (fun t : ℝ => Complex.I * (t : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using ht.tendsto
  have hlim := hc.tendsto.comp htz
  simp only [dslope_same,
    completedNativeGreenNormalizedResponse_hasDerivAt_h0.deriv] at hlim
  exact hlim.congr' completedNativePolarizedDslope_imaginaryAxis_eventuallyEq_slope.symm

/-- A coarse bound from the already formalized native theta-tail ledger. -/
theorem completedNativeCharacteristic_zero_norm_le_half :
    ‖completedNativeOperatorCharacteristic 0‖ ≤ (1/2 : ℝ) := by
  have hF := XiThetaCosine.completedNative_eq_xiCosineKernel 0
  change completedNativeOperatorCharacteristic 0 =
    (completedNativeXiCosineTransformReal 0 : ℂ) at hF
  rw [completedNativeXiCosineTransformReal_zero] at hF
  rw [hF, Complex.norm_real, Real.norm_eq_abs,
    completedNativeXiCosineMoment_zero_eq_thetaTailMoments]
  have ht0 := completedNativeThetaTailMoment_nonneg 0
  have ht1 := completedNativeThetaTailMoment_zero_le_calibration
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- The previously proved central gradient bound supplies the camera test
strictly; no coefficient is fitted to the native moment. -/
theorem canonicalC3CameraFive_central_coordinate_gt_quarter :
    (1/4 : ℝ) <
      |(positiveDirichletGradient (operatorHeightParameter 0) 0).re| := by
  have hcoord :
      positiveDirichletGradient (operatorHeightParameter 0) 0 =
        canonicalCentralCompletedDirichletGradientState 0 := by
    change positiveDirichletGradient (operatorHeightParameter 0) 0 =
      natDirichletTerm (1/2 : ℂ) 2 - natDirichletTerm (1/2 : ℂ) 1
    norm_num [operatorHeightParameter, positiveDirichletGradient]
  have him : (positiveDirichletGradient (operatorHeightParameter 0) 0).im = 0 := by
    change (natDirichletTerm (operatorHeightParameter 0) 2 -
      natDirichletTerm (operatorHeightParameter 0) 1).im = 0
    norm_num only [operatorHeightParameter, mul_zero, add_zero]
    rw [natDirichletTerm_half_eq_realRpow, natDirichletTerm_half_eq_realRpow]
    simp
  have hs := canonicalCentralCompletedGradient_firstCoordinate_sq_gt_sixteenth
  rw [← hcoord, Complex.sq_norm, Complex.normSq_apply, him] at hs
  nlinarith [sq_abs ((positiveDirichletGradient (operatorHeightParameter 0) 0).re),
    abs_nonneg ((positiveDirichletGradient (operatorHeightParameter 0) 0).re)]

theorem continuousAt_canonicalC3CameraFive_coordinate :
    ContinuousAt (fun z : ℂ =>
      |(positiveDirichletGradient (operatorHeightParameter z) 0).re|) 0 := by
  simp only [positiveDirichletGradient, natDirichletTerm, dirichletTerm,
    operatorHeightParameter]
  norm_num
  fun_prop

/-- Exact diagonal normalization of the existing Gamma Gram. -/
theorem canonicalC3NormalizedGamma_diagonal_re_eq_energy
    (z : ℂ) (hz : z.im ≠ 0) :
    (canonicalCompletedC3NormalizedPolarizedGammaKernel z z hz hz).re =
      ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 /
        (2 * ‖completedNativeOperatorCharacteristic z‖ ^ 2) := by
  rw [canonicalCompletedC3NormalizedPolarizedGammaKernel,
    canonicalCompletedC3PolarizedGammaKernel_diagonal_eq_norm_sq,
    canonicalCompletedC3GammaCharacteristicWeight_self_eq_normSq,
    ← Complex.sq_norm]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]

theorem canonicalC3NormalizedGamma_diagonal_gt_sixteenth
    (z : ℂ) (hz : z.im ≠ 0)
    (henergy : (1/16 : ℝ) < ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2)
    (hF : completedNativeOperatorCharacteristic z ≠ 0)
    (hFbound : ‖completedNativeOperatorCharacteristic z‖ < (2/3 : ℝ)) :
    (1/16 : ℝ) <
      (canonicalCompletedC3NormalizedPolarizedGammaKernel z z hz hz).re := by
  rw [canonicalC3NormalizedGamma_diagonal_re_eq_energy]
  have hnorm : 0 < ‖completedNativeOperatorCharacteristic z‖ :=
    norm_pos_iff.mpr hF
  have hsq : ‖completedNativeOperatorCharacteristic z‖ ^ 2 ≤ (4/9 : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ 2/3 - ‖completedNativeOperatorCharacteristic z‖ by linarith)
      (show 0 ≤ 2/3 + ‖completedNativeOperatorCharacteristic z‖ by linarith)]
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-- This lower bound concerns the same normalized Gamma kernel as the named
sewing, uniformly at all nearby off-axis points. -/
theorem canonicalC3NormalizedGamma_diagonal_eventually_gt_sixteenth :
    ∀ᶠ z : ℂ in 𝓝 0, ∀ hz : z.im ≠ 0,
      (1/16 : ℝ) <
        (canonicalCompletedC3NormalizedPolarizedGammaKernel z z hz hz).re := by
  have hc := continuousAt_canonicalC3CameraFive_coordinate.tendsto.eventually
    (eventually_gt_nhds canonicalC3CameraFive_central_coordinate_gt_quarter)
  have hFc := completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt
  have hFne := hFc.eventually_ne completedNativeOperatorCharacteristic_zero_ne_zero
  have hFbound := hFc.norm.tendsto.eventually
    (eventually_lt_nhds (show ‖completedNativeOperatorCharacteristic 0‖ < (2/3 : ℝ) by
      linarith [completedNativeCharacteristic_zero_norm_le_half]))
  filter_upwards [hc, hFne, hFbound, Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)]
    with z hcoord hF hbound hball
  intro hz
  have hnorm : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hball
  apply canonicalC3NormalizedGamma_diagonal_gt_sixteenth z hz
    (canonicalC3Gamma_energy_gt_sixteenth_of_cameraFive z hz
      ((Complex.abs_re_le_norm z).trans hnorm.le)
      ((Complex.abs_im_le_norm z).trans hnorm.le) hcoord) hF hbound

/-- The scalar native target lies strictly below the same ruler on a
sufficiently small imaginary approach to the Taylor center. -/
theorem completedNativePolarizedDslope_imaginaryAxis_eventually_lt_sixteenth :
    ∀ᶠ t : ℝ in 𝓝 0,
      (canonicalCompletedNativePolarizedDslopeKernel
        (Complex.I * (t : ℂ)) (Complex.I * (t : ℂ))).re < (1/16 : ℝ) := by
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp
    completedNativePolarizedDslope_imaginaryAxis_tendsto
  simp only [Complex.ofReal_re] at hreal
  exact hreal.eventually
    (eventually_lt_nhds canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth)

/-- The entire existing normalized Gamma kernel differs from the native
kernel near the center. All source channels and cross terms are included. -/
theorem canonicalC3NormalizedGamma_ne_native_near_imaginary_center :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ hz : (Complex.I * (t : ℂ)).im ≠ 0,
      canonicalCompletedC3NormalizedPolarizedGammaKernel
        (Complex.I * (t : ℂ)) (Complex.I * (t : ℂ)) hz hz ≠
      canonicalCompletedNativePolarizedDslopeKernel
        (Complex.I * (t : ℂ)) (Complex.I * (t : ℂ)) := by
  have ht : Tendsto (fun t : ℝ => Complex.I * (t : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using (show ContinuousAt (fun t : ℝ => Complex.I * (t : ℂ)) 0 by fun_prop).tendsto
  have hg := ht.eventually canonicalC3NormalizedGamma_diagonal_eventually_gt_sixteenth
  filter_upwards [hg, completedNativePolarizedDslope_imaginaryAxis_eventually_lt_sixteenth]
    with t hgamma hnative
  intro hz heq
  have hr := congrArg Complex.re heq
  have hb := hgamma hz
  linarith

/-- Division-free consequence at the exact named raw sewing endpoint. -/
theorem canonicalC3RawGammaWronskianDefect_ne_zero_near_imaginary_center :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ hz : (Complex.I * (t : ℂ)).im ≠ 0,
      canonicalCompletedC3RawGammaWronskianDefect
        (Complex.I * (t : ℂ)) (Complex.I * (t : ℂ)) hz hz ≠ 0 := by
  have ht : Tendsto (fun t : ℝ => Complex.I * (t : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using (show ContinuousAt (fun t : ℝ => Complex.I * (t : ℂ)) 0 by fun_prop).tendsto
  have hstrip := ht.eventually (isOpen_completedNativeHeightDomain.mem_nhds
    zero_mem_completedNativeHeightDomain)
  have hF := ht.eventually
    (completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero)
  filter_upwards [canonicalC3NormalizedGamma_ne_native_near_imaginary_center, hstrip, hF]
    with t hne hs hFne
  intro hz hzero
  have hsep : Complex.I * (t : ℂ) ≠ conj (Complex.I * (t : ℂ)) := by
    intro heq
    apply hz
    have h := congrArg Complex.im heq
    simp only [Complex.conj_im] at h
    linarith
  apply hne hz
  apply (canonicalCompletedC3NormalizedPolarizedGammaKernel_eq_dslope_iff_rawWronskian
    0 _ _ hz hz hs hs hFne hFne hsep).mpr
  exact sub_eq_zero.mp hzero

/-- Therefore no Green-right-inverse trace realization exists at these
nearby diagonal pairs. The right-inverse vectors themselves are unchanged. -/
theorem canonicalC3GreenInverseTraceRealization_empty_near_imaginary_center :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ hz : (Complex.I * (t : ℂ)).im ≠ 0,
      IsEmpty (CanonicalCompletedC3GreenInverseTraceRealization
        (Complex.I * (t : ℂ)) (Complex.I * (t : ℂ)) hz hz) := by
  filter_upwards [canonicalC3RawGammaWronskianDefect_ne_zero_near_imaginary_center] with t ht
  intro hz
  exact ⟨fun realization => ht hz realization.rawGammaWronskianDefect_eq_zero⟩


/-- Actual off-axis counterexamples occur arbitrarily close to the center,
with a nonzero native characteristic and inside the Genuine strip. -/
theorem canonicalC3RawDefect_counterexamples_arbitrarily_close
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧ t < 1/2 ∧
      operatorHeightParameter (Complex.I * (t : ℂ)) ∈ genuineCriticalStrip ∧
      completedNativeOperatorCharacteristic (Complex.I * (t : ℂ)) ≠ 0 ∧
      ∀ hz : (Complex.I * (t : ℂ)).im ≠ 0,
        canonicalCompletedC3RawGammaWronskianDefect
          (Complex.I * (t : ℂ)) (Complex.I * (t : ℂ)) hz hz ≠ 0 := by
  have ht : Tendsto (fun t : ℝ => Complex.I * (t : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using (show ContinuousAt (fun t : ℝ => Complex.I * (t : ℂ)) 0 by fun_prop).tendsto
  have hF := ht.eventually
    (completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero)
  have hgood : ∀ᶠ t : ℝ in 𝓝[>] 0,
      0 < t ∧ t < ε ∧ t < 1/2 ∧
      operatorHeightParameter (Complex.I * (t : ℂ)) ∈ genuineCriticalStrip ∧
      completedNativeOperatorCharacteristic (Complex.I * (t : ℂ)) ≠ 0 ∧
      ∀ hz : (Complex.I * (t : ℂ)).im ≠ 0,
        canonicalCompletedC3RawGammaWronskianDefect
          (Complex.I * (t : ℂ)) (Complex.I * (t : ℂ)) hz hz ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2)).filter_mono nhdsWithin_le_nhds,
      hF.filter_mono nhdsWithin_le_nhds,
      canonicalC3RawGammaWronskianDefect_ne_zero_near_imaginary_center.filter_mono
        nhdsWithin_le_nhds] with t hpos heps hhalf hFne hraw
    change 0 < t at hpos
    have hs : operatorHeightParameter (Complex.I * (t : ℂ)) ∈ genuineCriticalStrip := by
      change 0 < (operatorHeightParameter (Complex.I * (t : ℂ))).re ∧
        (operatorHeightParameter (Complex.I * (t : ℂ))).re < 1
      constructor <;> norm_num [operatorHeightParameter] <;> linarith
    exact ⟨hpos, heps, hhalf, hs, hFne, hraw⟩
  exact hgood.exists

/-- The already named canonical Gamma/Cauchy scalarization is false for
this source and this logarithmic Gamma field. No zero-set assumption enters. -/
theorem not_canonicalCompletedC3GammaCauchyScalarization_cameraFive :
    ¬ CanonicalCompletedC3GammaCauchyScalarization := by
  intro hscalar
  obtain ⟨t, ht, _, _, _, _, hraw⟩ :=
    canonicalC3RawDefect_counterexamples_arbitrarily_close 1 (by norm_num)
  let z := Complex.I * (t : ℂ)
  have hz : z.im ≠ 0 := by simpa [z] using ne_of_gt ht
  have henergy :=
    (canonicalCompletedNativeGammaCauchyScalarization_iff_energy
      canonicalCompletedC3SixCameraSource).mp hscalar z hz
  unfold completedGammaEnergy at henergy
  rw [totalCarryGammaState_of_im_ne_zero _ hz] at henergy
  change completedGreenWronskian completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion z z =
    (z - conj z) * (‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 : ℝ) at henergy
  apply hraw hz
  unfold canonicalCompletedC3RawGammaWronskianDefect
  rw [canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel,
    canonicalCompletedC3PolarizedGammaKernel_diagonal_eq_norm_sq]
  rw [← Complex.ofReal_pow]
  exact sub_eq_zero.mpr henergy.symm

end
end CarrySelfAdjointOperator
