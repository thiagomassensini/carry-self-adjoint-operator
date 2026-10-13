import CarrySelfAdjointOperator.NativeGammaCameraComplexLinear
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped ENNReal MeasureTheory InnerProductSpace
open Set MeasureTheory NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

def nativeCauchyKernel (z : ℂ) (x : ℝ) : ℂ :=
  (z - (logarithmicCoordinate x : ℂ))⁻¹

theorem nativeCauchyKernel_real (z : ℂ) (x : ℝ) :
    (nativeCauchyKernel z x).re = logarithmicResolventRealCoefficient z x := by
  simp [nativeCauchyKernel, Complex.inv_re, Complex.normSq_apply,
    logarithmicResolventRealCoefficient, logarithmicResolventDenominator, pow_two]

theorem nativeCauchyKernel_imag (z : ℂ) (x : ℝ) :
    (nativeCauchyKernel z x).im = logarithmicResolventImaginaryCoefficient z x := by
  simp [nativeCauchyKernel, Complex.inv_im, Complex.normSq_apply,
    logarithmicResolventImaginaryCoefficient, logarithmicResolventDenominator, pow_two]

theorem nativeCauchyKernel_literal (z : ℂ) (x : ℝ) :
    nativeCauchyKernel z x = (z-1-(Real.log x : ℂ))⁻¹ := by
  unfold nativeCauchyKernel logarithmicCoordinate
  push_cast
  congr 1
  ring

theorem nativeCauchyKernel_measurable (z : ℂ) : Measurable (nativeCauchyKernel z) := by
  exact (measurable_const.sub (Complex.measurable_ofReal.comp measurable_logarithmicCoordinate)).inv

theorem nativeCauchyKernel_bound (z : ℂ) (hz : z.im ≠ 0) (x : ℝ) :
    ‖nativeCauchyKernel z x‖ ≤ |z.im|⁻¹ := by
  have him : |z.im| ≤ ‖z-(logarithmicCoordinate x : ℂ)‖ := by
    simpa using Complex.abs_im_le_norm (z-(logarithmicCoordinate x : ℂ))
  rw [nativeCauchyKernel, norm_inv]
  exact (inv_le_inv₀ (lt_of_lt_of_le (abs_pos.mpr hz) him) (abs_pos.mpr hz)).mpr him

theorem nativeCauchyKernel_integrableOn (z : ℂ) (hz : z.im ≠ 0) (a b : ℝ) :
    IntegrableOn (nativeCauchyKernel z) (Ioc a b) volume :=
  Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
    (nativeCauchyKernel_measurable z).aestronglyMeasurable
    (ae_of_all _ (nativeCauchyKernel_bound z hz))

def nativeCauchyIntervalIntegral (l : ℝ) (z : ℂ) : ℂ :=
  ∫ x in Ioc 0 l, nativeCauchyKernel z x

theorem nativeCauchyIntervalIntegral_endpoint_zero (l : ℝ) (z : ℂ) :
    (∫ x in Icc 0 l, nativeCauchyKernel z x) = nativeCauchyIntervalIntegral l z :=
  integral_Icc_eq_integral_Ioc

theorem boundedMultiplier_camera_inner (m : BoundedRealNaimarkMultiplier) (b c : CameraIndex) :
    inner ℝ (naimarkCameraVector b) (boundedRealNaimarkMultiplier m (naimarkCameraVector c)) =
      periodicMeanKernel b c *
        ∫ x in cameraInterval b ∩ cameraInterval c, m.coefficient x ∂positiveLebesgueMeasure := by
  rw [L2.inner_def]
  have he : (fun x => inner ℝ (naimarkCameraVector b x)
      ((boundedRealNaimarkMultiplier m (naimarkCameraVector c)) x)) =ᵐ[positiveLebesgueMeasure]
      (cameraInterval b ∩ cameraInterval c).indicator
        (fun x => m.coefficient x * periodicMeanKernel b c) := by
    filter_upwards [naimarkCameraVector_coeFn b, naimarkCameraVector_coeFn c,
      boundedRealNaimarkMultiplier_coeFn m (naimarkCameraVector c)] with x hb hc hm
    rw [hm, boundedRealNaimarkMultiplierFunction, hb, hc]
    by_cases hxb : x ∈ cameraInterval b <;> by_cases hxc : x ∈ cameraInterval c <;>
      simp [hxb, hxc, real_inner_smul_right, inner_kolmogorovVector]
  rw [integral_congr_ae he, integral_indicator
    ((cameraInterval_measurable b).inter (cameraInterval_measurable c)), integral_mul_const]
  ring

theorem cameraOverlap_integral (b c : CameraIndex) (f : ℝ → ℝ) :
    (∫ x in cameraInterval b ∩ cameraInterval c, f x ∂positiveLebesgueMeasure) =
      ∫ x in Ioc 0 ((min (cameraSlope (cameraLabel b)) (cameraSlope (cameraLabel c)) : ℕ) : ℝ), f x := by
  have hs : cameraInterval b ∩ cameraInterval c =
      Ioc 0 ((min (cameraSlope (cameraLabel b)) (cameraSlope (cameraLabel c)) : ℕ) : ℝ) := by
    simp [cameraInterval, Ioc_inter_Ioc]
  rw [hs]
  unfold positiveLebesgueMeasure
  rw [Measure.restrict_restrict measurableSet_Ioc]
  rw [inter_eq_left.mpr (by intro x hx; exact hx.1)]

theorem nativeComplexCamera_Cauchy_integral (z : ℂ) (hz : z.im ≠ 0) (b c : CameraIndex) :
    inner ℂ (nativeComplexCameraVector b) (nativeComplexCauchy z hz (nativeComplexCameraVector c)) =
      (periodicMeanKernel b c : ℂ) *
        nativeCauchyIntervalIntegral (min (cameraSlope (cameraLabel b)) (cameraSlope (cameraLabel c))) z := by
  have hcre : RealHilbertComplexification.re (nativeComplexCauchy z hz (nativeComplexCameraVector c)) =
      allBasesCauchyRealPart z hz (cameraVector c) := by
    rw [nativeComplexCauchy_apply]
    change RealHilbertComplexification.re (nativeComplexCameraBlock (allBasesCauchyRealPart z hz)
      (allBasesCauchyImaginaryPart z hz) (nativeComplexCameraVector c)) = _
    rw [nativeComplexCameraBlock_re]
    simp only [nativeComplexCameraVector, RealHilbertComplexification.re_mk,
      RealHilbertComplexification.im_mk, map_zero, sub_zero]
  have hcim : RealHilbertComplexification.im (nativeComplexCauchy z hz (nativeComplexCameraVector c)) =
      allBasesCauchyImaginaryPart z hz (cameraVector c) := by
    rw [nativeComplexCauchy_apply]
    change RealHilbertComplexification.im (nativeComplexCameraBlock (allBasesCauchyRealPart z hz)
      (allBasesCauchyImaginaryPart z hz) (nativeComplexCameraVector c)) = _
    rw [nativeComplexCameraBlock_im]
    simp only [nativeComplexCameraVector, RealHilbertComplexification.re_mk,
      RealHilbertComplexification.im_mk, map_zero, add_zero]
  have hr : inner ℝ (cameraVector b) (allBasesCauchyRealPart z hz (cameraVector c)) =
      periodicMeanKernel b c * ∫ x in Ioc 0
        ((min (cameraSlope (cameraLabel b)) (cameraSlope (cameraLabel c)) : ℕ) : ℝ),
          logarithmicResolventRealCoefficient z x := by
    rw [inner_allBasesCauchyRealPart, naimarkIsometry_cameraVector, naimarkIsometry_cameraVector]
    rw [logarithmicResolventRealOperator, boundedMultiplier_camera_inner, cameraOverlap_integral]
    rfl
  have hi : inner ℝ (cameraVector b) (allBasesCauchyImaginaryPart z hz (cameraVector c)) =
      periodicMeanKernel b c * ∫ x in Ioc 0
        ((min (cameraSlope (cameraLabel b)) (cameraSlope (cameraLabel c)) : ℕ) : ℝ),
          logarithmicResolventImaginaryCoefficient z x := by
    rw [inner_allBasesCauchyImaginaryPart, naimarkIsometry_cameraVector, naimarkIsometry_cameraVector]
    rw [logarithmicResolventImaginaryOperator, boundedMultiplier_camera_inner, cameraOverlap_integral]
    rfl
  have hint := nativeCauchyKernel_integrableOn z hz 0
    ((min (cameraSlope (cameraLabel b)) (cameraSlope (cameraLabel c)) : ℕ) : ℝ)
  apply Complex.ext
  · change (RealHilbertComplexification.complexInner _ _).re = _
    simp only [RealHilbertComplexification.complexInner_re]
    rw [hcre, hcim]
    simp only [nativeComplexCameraVector, RealHilbertComplexification.re_mk,
      RealHilbertComplexification.im_mk, inner_zero_left, add_zero, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hr]
    congr 1
    unfold nativeCauchyIntervalIntegral
    rw [← Nat.cast_min]
    simpa only [RCLike.re_to_complex, nativeCauchyKernel_real] using
      (integral_re (𝕜 := ℂ) hint)
  · change (RealHilbertComplexification.complexInner _ _).im = _
    simp only [RealHilbertComplexification.complexInner_im]
    rw [hcre, hcim]
    simp only [nativeComplexCameraVector, RealHilbertComplexification.re_mk,
      RealHilbertComplexification.im_mk, inner_zero_left, sub_zero, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [hi]
    congr 1
    unfold nativeCauchyIntervalIntegral
    rw [← Nat.cast_min]
    simpa only [RCLike.im_to_complex, nativeCauchyKernel_imag] using
      (integral_im (𝕜 := ℂ) hint)

end
end CarrySelfAdjointOperator.GammaMaterialSewing
