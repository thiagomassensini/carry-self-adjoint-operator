import CarrySelfAdjointOperator.CompletedNativeThetaFiniteMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeRadialThreePointDeterminant

/-!
# Strict positivity of the second native Hankel determinant

The five integral bounds are proved from the first theta mode, convex weighted
quadrature, and the full geometric mode/tail majorants. No external numerical
result is an input to these theorems.
-/

open Real Set Filter MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false

theorem completedNativeThetaTailMoment_zero_certified_bounds :
    (115153/10000000:ℝ) ≤ completedNativeThetaTailMoment 0 ∧
      completedNativeThetaTailMoment 0 ≤ (11521/1000000:ℝ) := by
  have hl := completedNativeThetaTailMoment_finite_lower 0
  have hu := completedNativeThetaTailMoment_finite_upper 0 (by norm_num)
  constructor
  · linarith [thetaFirstMode_integral_lower_0]
  · linarith [thetaFirstMode_integral_upper_0]

theorem completedNativeThetaTailMoment_two_certified_bounds :
    (24726/100000000:ℝ) ≤ completedNativeThetaTailMoment 2 ∧
      completedNativeThetaTailMoment 2 ≤ (24748/100000000:ℝ) := by
  have hl := completedNativeThetaTailMoment_finite_lower 2
  have hu := completedNativeThetaTailMoment_finite_upper 2 (by norm_num)
  constructor
  · linarith [thetaFirstMode_integral_lower_2]
  · linarith [thetaFirstMode_integral_upper_2]

theorem completedNativeThetaTailMoment_four_certified_bounds :
    (199929/10000000000:ℝ) ≤ completedNativeThetaTailMoment 4 ∧
      completedNativeThetaTailMoment 4 ≤ (20029/1000000000:ℝ) := by
  have hl := completedNativeThetaTailMoment_finite_lower 4
  have hu := completedNativeThetaTailMoment_finite_upper 4 (by norm_num)
  constructor
  · linarith [thetaFirstMode_integral_lower_4]
  · linarith [thetaFirstMode_integral_upper_4]

theorem completedNativeThetaTailMoment_six_certified_upper :
    completedNativeThetaTailMoment 6 ≤ (2891/1000000000:ℝ) := by
  have hu := completedNativeThetaTailMoment_finite_upper 6 (by norm_num)
  linarith [thetaFirstMode_integral_upper_6]

theorem completedNativeXiCosineMoment_zero_ge_497_div_1000 :
    (497/1000:ℝ) ≤ completedNativeXiCosineMoment 0 := by
  rw [completedNativeXiCosineMoment_zero_eq_thetaTailMoments]
  linarith [completedNativeThetaTailMoment_zero_certified_bounds.2]

theorem completedNativeXiCosineMoment_one_ge_287_div_12500 :
    (287/12500:ℝ) ≤ completedNativeXiCosineMoment 1 := by
  rw [completedNativeXiCosineMoment_one_eq_thetaTailMoments]
  linarith [completedNativeThetaTailMoment_zero_certified_bounds.1,
    completedNativeThetaTailMoment_two_certified_bounds.2]

theorem completedNativeXiCosineMoment_two_ge_37_div_12500 :
    (37/12500:ℝ) ≤ completedNativeXiCosineMoment 2 := by
  rw [completedNativeXiCosineMoment_two_eq_thetaTailMoments]
  linarith [completedNativeThetaTailMoment_two_certified_bounds.1,
    completedNativeThetaTailMoment_four_certified_bounds.2]

theorem completedNativeXiCosineMoment_two_le_593_div_200000 :
    completedNativeXiCosineMoment 2 ≤ (593/200000:ℝ) := by
  rw [completedNativeXiCosineMoment_two_eq_thetaTailMoments]
  linarith [completedNativeThetaTailMoment_two_certified_bounds.2,
    completedNativeThetaTailMoment_four_certified_bounds.1]

theorem completedNativeXiCosineMoment_three_ge_299_div_500000 :
    (299/500000:ℝ) ≤ completedNativeXiCosineMoment 3 := by
  rw [completedNativeXiCosineMoment_three_eq_thetaTailMoments]
  linarith [completedNativeThetaTailMoment_four_certified_bounds.1,
    completedNativeThetaTailMoment_six_certified_upper]

/-- The previous five-bound interface is now filled by native integral proofs. -/
theorem canonicalCompletedNativeHankel_two_det_pos :
    0 < (hankelGram canonicalCompletedNativeLogDerivativeMoment 2).det :=
  canonicalCompletedNativeHankel_two_det_pos_of_xiMoment_bounds
    completedNativeXiCosineMoment_zero_ge_497_div_1000
    completedNativeXiCosineMoment_one_ge_287_div_12500
    completedNativeXiCosineMoment_two_ge_37_div_12500
    completedNativeXiCosineMoment_two_le_593_div_200000
    completedNativeXiCosineMoment_three_ge_299_div_500000

/-- The rational box gives a quantitative margin, without matching the
external interval calculation's many decimal digits. -/
theorem canonicalCompletedNativeHankel_two_det_gt_546_div_trillion :
    (546/1000000000000:ℝ) <
      (hankelGram canonicalCompletedNativeLogDerivativeMoment 2).det := by
  rw [canonicalCompletedNativeHankel_two_det_eq_xiCosineMoments]
  have hm := completedNativeXiCosineMoment_pos 0
  apply (lt_div_iff₀ (mul_pos (by norm_num) (pow_pos hm 3))).2
  have hn := xiSixthMoment_numerator_lower_bound_of_box _ _ _ _
    completedNativeXiCosineMoment_zero_ge_497_div_1000
    completedNativeXiCosineMoment_zero_lt_249_div_500.le
    completedNativeXiCosineMoment_one_ge_287_div_12500
    completedNativeXiCosineMoment_two_ge_37_div_12500
    completedNativeXiCosineMoment_two_le_593_div_200000
    completedNativeXiCosineMoment_three_ge_299_div_500000
  have hd : completedNativeXiCosineMoment 0 ^ 3 ≤ (249/500:ℝ)^3 :=
    pow_le_pow_left₀ hm.le completedNativeXiCosineMoment_zero_lt_249_div_500.le 3
  linarith

theorem canonicalCompletedNativeSecondSchurComplement_pos :
    0 < canonicalCompletedNativeLogDerivativeMoment 2 -
      canonicalCompletedNativeLogDerivativeMoment 1 ^ 2 /
        canonicalCompletedNativeLogDerivativeMoment 0 :=
  canonicalCompletedNativeHankel_two_det_pos_iff_schur.mp
    canonicalCompletedNativeHankel_two_det_pos

/-- The determinant corollary uses the already proved remainder-controlled
three-point limit. No new kernel or operator is constructed. -/
theorem canonicalCompletedNativeRadialThreePointDeterminant_eventually_re_pos :
    ∀ᶠ k : ℕ in atTop,
      0 < (canonicalCompletedNativeRadialDslopeSampleMatrix k 3).det.re :=
  canonicalCompletedNativeRadialThreePointDeterminant_eventually_re_pos_of_delta
    canonicalCompletedNativeHankel_two_det_pos

end
end CarrySelfAdjointOperator
