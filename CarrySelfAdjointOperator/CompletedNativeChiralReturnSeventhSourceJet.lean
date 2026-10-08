import CarrySelfAdjointOperator.CompletedNativeChiralReturnBoundaryCancellation
import CarrySelfAdjointOperator.CompletedNativeEighthBernsteinCertificate
import Mathlib.Analysis.Analytic.Order

/-!
# Seventh source derivative from the raw theta integral certificate

Only raw cosine integrals, their certified theta bounds, and the local
identity (-F'/F) F = -F' are used. No canonical logarithmic moment or
positivity certificate is a premise. This is a finite source-jet sign,
not all-order return contractivity.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- Connected eighth-order raw source numerator, before moment identification. -/
def nativeSourceSeventhNumerator (a b c d e : ℝ) : ℝ :=
  630 * b ^ 4 - 420 * a * b ^ 2 * c + 35 * a ^ 2 * c ^ 2 +
    28 * a ^ 2 * b * d - a ^ 3 * e

/-- Exact polynomial sewing of the independent raw-source certificate.
The sixth connected source term is retained as a square. -/
theorem nativeSourceSeventhNumerator_certificate_identity (a b c d e : ℝ) :
    10 * (3 * b ^ 2 - a * c) * nativeSourceSeventhNumerator a b c d e -
      21 * (30 * b ^ 3 - 15 * a * b * c + a ^ 2 * d) ^ 2 =
      a ^ 2 * xiEighthMomentNumerator a b c d e := by
  unfold nativeSourceSeventhNumerator xiEighthMomentNumerator
  ring

/-- The five raw integrals lie in the existing refined theta certificate box. -/
theorem nativeSourceCosineIntegral_refined_box :
    (7767507 / 15625000 : ℝ) ≤ completedNativeXiCosineMoment 0 ∧
    completedNativeXiCosineMoment 0 ≤ (19884837 / 40000000 : ℝ) ∧
    (574269 / 25000000 : ℝ) ≤ completedNativeXiCosineMoment 1 ∧
    completedNativeXiCosineMoment 1 ≤ (22974587 / 1000000000 : ℝ) ∧
    (2962661 / 1000000000 : ℝ) ≤ completedNativeXiCosineMoment 2 ∧
    completedNativeXiCosineMoment 2 ≤ (740861 / 250000000 : ℝ) ∧
    (299619 / 500000000 : ℝ) ≤ completedNativeXiCosineMoment 3 ∧
    completedNativeXiCosineMoment 3 ≤ (600193 / 1000000000 : ℝ) ∧
    (10059 / 62500000 : ℝ) ≤ completedNativeXiCosineMoment 4 ∧
    completedNativeXiCosineMoment 4 ≤ (161051 / 1000000000 : ℝ) := by
  have h0l := completedNativeThetaTailMoment_finite_lower 0
  have h0u := completedNativeThetaTailMoment_finite_upper_refined 0 (by norm_num)
  have h2l := completedNativeThetaTailMoment_finite_lower 2
  have h2u := completedNativeThetaTailMoment_finite_upper_refined 2 (by norm_num)
  have h4l := completedNativeThetaTailMoment_finite_lower 4
  have h4u := completedNativeThetaTailMoment_finite_upper_refined 4 (by norm_num)
  have h6l := completedNativeThetaTailMoment_finite_lower 6
  have h6u := completedNativeThetaTailMoment_finite_upper_refined 6 (by norm_num)
  have h8l := completedNativeThetaTailMoment_finite_lower 8
  have h8u := completedNativeThetaTailMoment_finite_upper_refined 8 (by norm_num)
  have hfour : completedNativeXiCosineMoment 4 =
      56 * completedNativeThetaTailMoment 6 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 8 := by
    convert completedNativeXiCosineMoment_succ_eq_thetaTailMoments 3 using 1
    norm_num
  rw [completedNativeXiCosineMoment_zero_eq_thetaTailMoments,
    completedNativeXiCosineMoment_one_eq_thetaTailMoments,
    completedNativeXiCosineMoment_two_eq_thetaTailMoments,
    completedNativeXiCosineMoment_three_eq_thetaTailMoments, hfour]
  constructor <;> try constructor
  all_goals repeat' constructor
  all_goals linarith [thetaFirstMode_refined_integral_lower_0,
    thetaFirstMode_refined_integral_upper_0, thetaFirstMode_refined_integral_lower_2,
    thetaFirstMode_refined_integral_upper_2, thetaFirstMode_refined_integral_lower_4,
    thetaFirstMode_refined_integral_upper_4, thetaFirstMode_refined_integral_lower_6,
    thetaFirstMode_refined_integral_upper_6, thetaFirstMode_refined_integral_lower_8,
    thetaFirstMode_refined_integral_upper_8]

/-- Strict source sign obtained from the refined integral certificate;
no Hankel or logarithmic-moment positivity theorem supplies it. -/
theorem nativeSourceSeventhNumerator_pos :
    0 < nativeSourceSeventhNumerator
      (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
      (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
      (completedNativeXiCosineMoment 4) := by
  obtain ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1, he0, he1⟩ :=
    nativeSourceCosineIntegral_refined_box
  have hp := xiEighthMoment_numerator_lower_bound_of_refined_box _ _ _ _ _
    ha0 ha1 hb0 hb1 hc0 hc1 hd0 hd1 he0 he1
  have hp' : 0 < xiEighthMomentNumerator
      (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
      (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
      (completedNativeXiCosineMoment 4) := lt_of_lt_of_le (by norm_num) hp
  have ha := completedNativeXiCosineMoment_pos 0
  have hA : 0 < 3 * completedNativeXiCosineMoment 1 ^ 2 -
      completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 2 := by
    linarith [completedNativeXiCosineMoment_strict_kurtosis]
  have hid := nativeSourceSeventhNumerator_certificate_identity
    (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
    (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
    (completedNativeXiCosineMoment 4)
  have hrhs := mul_pos (sq_pos_of_pos ha) hp'
  have hprod : 0 < 10 * (3 * completedNativeXiCosineMoment 1 ^ 2 -
      completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 2) *
      nativeSourceSeventhNumerator
        (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) := by
    nlinarith [sq_nonneg (30 * completedNativeXiCosineMoment 1 ^ 3 -
      15 * completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 1 *
        completedNativeXiCosineMoment 2 + completedNativeXiCosineMoment 0 ^ 2 *
        completedNativeXiCosineMoment 3)]
  exact (mul_pos_iff_of_pos_left (mul_pos (by norm_num) hA)).mp hprod

/-- Local regularity of the actual native logarithmic source. -/
theorem nativeSourceLogSlope_analyticAt :
    AnalyticAt ℂ completedNativeOperatorLogDerivative 0 := by
  have hf := completedNativeOperatorCharacteristic_analyticAt zero_mem_completedNativeHeightDomain
  unfold completedNativeOperatorLogDerivative
  exact hf.deriv.neg.div hf completedNativeOperatorCharacteristic_zero_ne_zero

/-- Division-free Leibniz recurrence of raw source derivatives at the center. -/
theorem nativeSourceLogSlope_derivative_recurrence (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) *
      iteratedDeriv j completedNativeOperatorLogDerivative 0 *
      iteratedDeriv (n - j) completedNativeOperatorCharacteristic 0) =
        -iteratedDeriv (n + 1) completedNativeOperatorCharacteristic 0 := by
  have hf := completedNativeOperatorCharacteristic_analyticAt zero_mem_completedNativeHeightDomain
  have heq : (fun z => completedNativeOperatorLogDerivative z *
      completedNativeOperatorCharacteristic z) =ᶠ[nhds 0]
      (fun z => -deriv completedNativeOperatorCharacteristic z) := by
    filter_upwards [hf.continuousAt.eventually_ne completedNativeOperatorCharacteristic_zero_ne_zero]
      with z hz
    simp [completedNativeOperatorLogDerivative, hz]
  calc
    _ = iteratedDeriv n (fun z => completedNativeOperatorLogDerivative z *
          completedNativeOperatorCharacteristic z) 0 :=
      (iteratedDeriv_fun_mul nativeSourceLogSlope_analyticAt.contDiffAt hf.contDiffAt).symm
    _ = iteratedDeriv n (fun z => -deriv completedNativeOperatorCharacteristic z) 0 :=
      heq.iteratedDeriv_eq n
    _ = _ := by rw [iteratedDeriv_fun_neg, iteratedDeriv_succ']

/-- All derivatives through order seven of the actual -F'/F source, obtained
from the division-free product identity and the raw even characteristic jets. -/
theorem nativeSourceLogSlope_center_jets :
    let a := (completedNativeXiCosineMoment 0 : ℂ)
    let b := (completedNativeXiCosineMoment 1 : ℂ)
    let c := (completedNativeXiCosineMoment 2 : ℂ)
    let d := (completedNativeXiCosineMoment 3 : ℂ)
    let e := (completedNativeXiCosineMoment 4 : ℂ)
    iteratedDeriv 0 completedNativeOperatorLogDerivative 0 = 0 ∧
    iteratedDeriv 1 completedNativeOperatorLogDerivative 0 = b / a ∧
    iteratedDeriv 2 completedNativeOperatorLogDerivative 0 = 0 ∧
    iteratedDeriv 3 completedNativeOperatorLogDerivative 0 = (3 * b^2 - a*c) / a^2 ∧
    iteratedDeriv 4 completedNativeOperatorLogDerivative 0 = 0 ∧
    iteratedDeriv 5 completedNativeOperatorLogDerivative 0 =
      (30*b^3 - 15*a*b*c + a^2*d) / a^3 ∧
    iteratedDeriv 6 completedNativeOperatorLogDerivative 0 = 0 ∧
    iteratedDeriv 7 completedNativeOperatorLogDerivative 0 =
      (630*b^4 - 420*a*b^2*c + 35*a^2*c^2 + 28*a^2*b*d - a^3*e) / a^4 := by
  let a : ℂ := completedNativeXiCosineMoment 0
  let b : ℂ := completedNativeXiCosineMoment 1
  let c : ℂ := completedNativeXiCosineMoment 2
  let d : ℂ := completedNativeXiCosineMoment 3
  let e : ℂ := completedNativeXiCosineMoment 4
  change _ = 0 ∧ _ = b/a ∧ _ = 0 ∧ _ = (3*b^2-a*c)/a^2 ∧ _ = 0 ∧
    _ = (30*b^3-15*a*b*c+a^2*d)/a^3 ∧ _ = 0 ∧
    _ = (630*b^4-420*a*b^2*c+35*a^2*c^2+28*a^2*b*d-a^3*e)/a^4
  have ha : a ≠ 0 := by
    change (completedNativeXiCosineMoment 0 : ℂ) ≠ 0
    exact_mod_cast (completedNativeXiCosineMoment_pos 0).ne'
  have hf0 : completedNativeOperatorCharacteristic 0 = a := by
    have h := XiThetaCosine.completedNative_eq_xiCosineKernel 0
    have he : completedNativeOperatorCharacteristic 0 =
      (completedNativeXiCosineTransformReal 0 : ℂ) := by
      simpa [completedNativeXiCosineTransformReal] using h
    rw [he, completedNativeXiCosineTransformReal_zero]
  have hf1 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 0
  have hf2 : iteratedDeriv 2 completedNativeOperatorCharacteristic 0 = -b := by
    simpa only [Complex.ofReal_neg] using iteratedDeriv_two_completedNativeOperatorCharacteristic_zero
  have hf3 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 1
  have hf4 : iteratedDeriv 4 completedNativeOperatorCharacteristic 0 = c :=
    iteratedDeriv_four_completedNativeOperatorCharacteristic_zero
  have hf5 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 2
  have hf6 : iteratedDeriv 6 completedNativeOperatorCharacteristic 0 = -d := by
    simpa only [Complex.ofReal_neg] using iteratedDeriv_six_completedNativeOperatorCharacteristic_zero
  have hf7 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 3
  have hf8 : iteratedDeriv 8 completedNativeOperatorCharacteristic 0 = e :=
    iteratedDeriv_eight_completedNativeOperatorCharacteristic_zero
  have h0 := nativeSourceLogSlope_derivative_recurrence 0
  have h1 := nativeSourceLogSlope_derivative_recurrence 1
  have h2 := nativeSourceLogSlope_derivative_recurrence 2
  have h3 := nativeSourceLogSlope_derivative_recurrence 3
  have h4 := nativeSourceLogSlope_derivative_recurrence 4
  have h5 := nativeSourceLogSlope_derivative_recurrence 5
  have h6 := nativeSourceLogSlope_derivative_recurrence 6
  have h7 := nativeSourceLogSlope_derivative_recurrence 7
  norm_num [Finset.sum_range_succ, Nat.choose, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8]
    at h0 h1 h2 h3 h4 h5 h6 h7
  have hq0 : completedNativeOperatorLogDerivative 0 = 0 := h0.resolve_right ha
  have hq1 : deriv completedNativeOperatorLogDerivative 0 = b/a := by
    apply (eq_div_iff ha).mpr
    linear_combination h1
  have hq2 : iteratedDeriv 2 completedNativeOperatorLogDerivative 0 = 0 := by
    rw [hq0] at h2
    simpa using (mul_eq_zero.mp (by simpa using h2)).resolve_right ha
  have hq3 : iteratedDeriv 3 completedNativeOperatorLogDerivative 0 = (3*b^2-a*c)/a^2 := by
    rw [hq1] at h3
    field_simp [ha] at h3 ⊢
    linear_combination h3
  have hq4 : iteratedDeriv 4 completedNativeOperatorLogDerivative 0 = 0 := by
    rw [hq0, hq2] at h4
    simpa using (mul_eq_zero.mp (by simpa using h4)).resolve_right ha
  have hq5 : iteratedDeriv 5 completedNativeOperatorLogDerivative 0 =
      (30*b^3-15*a*b*c+a^2*d)/a^3 := by
    rw [hq1, hq3] at h5
    field_simp [ha] at h5 ⊢
    linear_combination h5
  have hq6 : iteratedDeriv 6 completedNativeOperatorLogDerivative 0 = 0 := by
    rw [hq0, hq2, hq4] at h6
    simpa using (mul_eq_zero.mp (by simpa using h6)).resolve_right ha
  have hq7 : iteratedDeriv 7 completedNativeOperatorLogDerivative 0 =
      (630*b^4-420*a*b^2*c+35*a^2*c^2+28*a^2*b*d-a^3*e)/a^4 := by
    rw [hq1, hq3, hq5] at h7
    field_simp [ha] at h7 ⊢
    linear_combination h7
  exact ⟨by simpa using hq0, by simpa using hq1, hq2, hq3, hq4, hq5, hq6, hq7⟩

/-- The seventh source derivative is a strictly positive REAL number,
proved from upstream integrals before any canonical moment identification. -/
theorem nativeSourceLogSlope_seventh_derivative_eq_positive_integralRatio :
    iteratedDeriv 7 completedNativeOperatorLogDerivative 0 =
      (nativeSourceSeventhNumerator
        (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) / completedNativeXiCosineMoment 0 ^ 4 : ℝ) := by
  have h := nativeSourceLogSlope_center_jets
  dsimp only at h
  rw [h.2.2.2.2.2.2.2]
  unfold nativeSourceSeventhNumerator
  push_cast
  rfl

theorem nativeSourceLogSlope_seventh_derivative_re_pos :
    0 < (iteratedDeriv 7 completedNativeOperatorLogDerivative 0).re := by
  rw [nativeSourceLogSlope_seventh_derivative_eq_positive_integralRatio, Complex.ofReal_re]
  exact div_pos nativeSourceSeventhNumerator_pos (pow_pos (completedNativeXiCosineMoment_pos 0) 4)

end
end CarrySelfAdjointOperator
