import CarrySelfAdjointOperator.CompletedNativeEighthBernsteinCertificate
import CarrySelfAdjointOperator.CompletedNativeSixthOrderThetaPositivity
import Mathlib.Tactic

/-!
# Eighth-order theta certificate for the first shifted native Hankel minor

This file only uses the existing canonical logarithmic moments.  It derives
the first shifted two-by-two determinant from the completed theta cosine
moments and proves its strict sign by the rational refined-tail certificate.
-/

namespace CarrySelfAdjointOperator

noncomputable section
set_option autoImplicit false

/-- The fourth logarithmic coefficient follows from the existing recurrence. -/
theorem canonicalCompletedNativeLogDerivativeMoment_three_eq_eighthOrderRatio :
    canonicalCompletedNativeLogDerivativeMoment 3 =
      (-4 * completedNativeRealEvenCharacteristicCoefficient 0 ^ 3 *
          completedNativeRealEvenCharacteristicCoefficient 4 +
        4 * completedNativeRealEvenCharacteristicCoefficient 0 ^ 2 *
          completedNativeRealEvenCharacteristicCoefficient 1 *
          completedNativeRealEvenCharacteristicCoefficient 3 +
        2 * completedNativeRealEvenCharacteristicCoefficient 0 ^ 2 *
          completedNativeRealEvenCharacteristicCoefficient 2 ^ 2 -
        4 * completedNativeRealEvenCharacteristicCoefficient 0 *
          completedNativeRealEvenCharacteristicCoefficient 1 ^ 2 *
          completedNativeRealEvenCharacteristicCoefficient 2 +
        completedNativeRealEvenCharacteristicCoefficient 1 ^ 4) /
        completedNativeRealEvenCharacteristicCoefficient 0 ^ 4 := by
  have hr := canonicalCompletedNativeLogDerivativeMoment_real_recurrence 3
  norm_num [Finset.sum_range_succ] at hr
  rw [canonicalCompletedNativeLogDerivativeMoment_zero_eq_secondOrderRatio,
    canonicalCompletedNativeLogDerivativeMoment_one_eq_fourthOrderDiscriminant,
    canonicalCompletedNativeLogDerivativeMoment_two_eq_sixthOrderRatio] at hr
  have hc := completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero
  field_simp [hc] at hr ⊢
  linear_combination hr

/-- The first shifted two-by-two determinant is `h₁h₃-h₂²`. -/
theorem canonicalCompletedNativeShiftedHankel_two_det_eq :
    (shiftedHankel canonicalCompletedNativeLogDerivativeMoment 2).det =
      canonicalCompletedNativeLogDerivativeMoment 1 *
        canonicalCompletedNativeLogDerivativeMoment 3 -
      canonicalCompletedNativeLogDerivativeMoment 2 ^ 2 := by
  rw [Matrix.det_fin_two]
  norm_num [shiftedHankel, pow_two]

/-- Exact scalar reduction in the real even characteristic coefficients. -/
theorem canonicalCompletedNativeShiftedHankel_two_det_eq_eighthOrderRatio :
    (shiftedHankel canonicalCompletedNativeLogDerivativeMoment 2).det =
      (8 * completedNativeRealEvenCharacteristicCoefficient 0 ^ 2 *
          completedNativeRealEvenCharacteristicCoefficient 2 *
          completedNativeRealEvenCharacteristicCoefficient 4 -
        9 * completedNativeRealEvenCharacteristicCoefficient 0 ^ 2 *
          completedNativeRealEvenCharacteristicCoefficient 3 ^ 2 -
        4 * completedNativeRealEvenCharacteristicCoefficient 0 *
          completedNativeRealEvenCharacteristicCoefficient 1 ^ 2 *
          completedNativeRealEvenCharacteristicCoefficient 4 +
        10 * completedNativeRealEvenCharacteristicCoefficient 0 *
          completedNativeRealEvenCharacteristicCoefficient 1 *
          completedNativeRealEvenCharacteristicCoefficient 2 *
          completedNativeRealEvenCharacteristicCoefficient 3 -
        4 * completedNativeRealEvenCharacteristicCoefficient 0 *
          completedNativeRealEvenCharacteristicCoefficient 2 ^ 3 -
        2 * completedNativeRealEvenCharacteristicCoefficient 1 ^ 3 *
          completedNativeRealEvenCharacteristicCoefficient 3 +
        completedNativeRealEvenCharacteristicCoefficient 1 ^ 2 *
          completedNativeRealEvenCharacteristicCoefficient 2 ^ 2) /
        completedNativeRealEvenCharacteristicCoefficient 0 ^ 4 := by
  rw [canonicalCompletedNativeShiftedHankel_two_det_eq,
    canonicalCompletedNativeLogDerivativeMoment_one_eq_fourthOrderDiscriminant,
    canonicalCompletedNativeLogDerivativeMoment_two_eq_sixthOrderRatio,
    canonicalCompletedNativeLogDerivativeMoment_three_eq_eighthOrderRatio]
  field_simp [completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero]
  ring

/-- Exact cosine-moment normalization of the shifted determinant. -/
theorem canonicalCompletedNativeShiftedHankel_two_det_eq_xiCosineMoments :
    (shiftedHankel canonicalCompletedNativeLogDerivativeMoment 2).det =
      xiEighthMomentNumerator
        (completedNativeXiCosineMoment 0)
        (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2)
        (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) /
        (1209600 * completedNativeXiCosineMoment 0 ^ 4) := by
  rw [canonicalCompletedNativeShiftedHankel_two_det_eq_eighthOrderRatio,
    completedNativeRealEvenCharacteristicCoefficient_zero_eq_xiCosineMoment,
    completedNativeRealEvenCharacteristicCoefficient_one_eq_xiCosineMoment,
    completedNativeRealEvenCharacteristicCoefficient_two_eq_xiCosineMoment,
    completedNativeRealEvenCharacteristicCoefficient_three_eq_xiCosineMoment,
    completedNativeRealEvenCharacteristicCoefficient_four_eq_xiCosineMoment]
  unfold xiEighthMomentNumerator
  ring

/-- The eighth cosine moment retains both neighboring theta-tail orders. -/
theorem completedNativeXiCosineMoment_four_eq_thetaTailMoments :
    completedNativeXiCosineMoment 4 =
      56 * completedNativeThetaTailMoment 6 -
        (1 / 4 : ℝ) * completedNativeThetaTailMoment 8 := by
  convert completedNativeXiCosineMoment_succ_eq_thetaTailMoments 3 using 1
  norm_num

theorem canonicalCompletedNativeShiftedHankel_two_det_pos :
    0 < (shiftedHankel canonicalCompletedNativeLogDerivativeMoment 2).det := by
  have A0lo := completedNativeThetaTailMoment_finite_lower 0
  have A0hi := completedNativeThetaTailMoment_finite_upper_refined 0 (by norm_num)
  have A2lo := completedNativeThetaTailMoment_finite_lower 2
  have A2hi := completedNativeThetaTailMoment_finite_upper_refined 2 (by norm_num)
  have A4lo := completedNativeThetaTailMoment_finite_lower 4
  have A4hi := completedNativeThetaTailMoment_finite_upper_refined 4 (by norm_num)
  have A6lo := completedNativeThetaTailMoment_finite_lower 6
  have A6hi := completedNativeThetaTailMoment_finite_upper_refined 6 (by norm_num)
  have A8lo := completedNativeThetaTailMoment_finite_lower 8
  have A8hi := completedNativeThetaTailMoment_finite_upper_refined 8 (by norm_num)
  have hnum := xiEighthMoment_numerator_lower_bound_of_refined_box
    (1 / 2 - completedNativeThetaTailMoment 0 / 4)
    (2 * completedNativeThetaTailMoment 0 - completedNativeThetaTailMoment 2 / 4)
    (12 * completedNativeThetaTailMoment 2 - completedNativeThetaTailMoment 4 / 4)
    (30 * completedNativeThetaTailMoment 4 - completedNativeThetaTailMoment 6 / 4)
    (56 * completedNativeThetaTailMoment 6 - completedNativeThetaTailMoment 8 / 4)
    (by linarith [thetaFirstMode_refined_integral_upper_0])
    (by linarith [thetaFirstMode_refined_integral_lower_0])
    (by linarith [thetaFirstMode_refined_integral_lower_0,
      thetaFirstMode_refined_integral_upper_2])
    (by linarith [thetaFirstMode_refined_integral_upper_0,
      thetaFirstMode_refined_integral_lower_2])
    (by linarith [thetaFirstMode_refined_integral_lower_2,
      thetaFirstMode_refined_integral_upper_4])
    (by linarith [thetaFirstMode_refined_integral_upper_2,
      thetaFirstMode_refined_integral_lower_4])
    (by linarith [thetaFirstMode_refined_integral_lower_4,
      thetaFirstMode_refined_integral_upper_6])
    (by linarith [thetaFirstMode_refined_integral_upper_4,
      thetaFirstMode_refined_integral_lower_6])
    (by linarith [thetaFirstMode_refined_integral_lower_6,
      thetaFirstMode_refined_integral_upper_8])
    (by linarith [thetaFirstMode_refined_integral_upper_6,
      thetaFirstMode_refined_integral_lower_8])
  have hzero : 0 < 1 / 2 - completedNativeThetaTailMoment 0 / 4 := by
    calc
      0 < completedNativeXiCosineMoment 0 := completedNativeXiCosineMoment_pos 0
      _ = 1 / 2 - completedNativeThetaTailMoment 0 / 4 := by
        rw [completedNativeXiCosineMoment_zero_eq_thetaTailMoments]
        ring
  have hden : 0 < 1209600 * (1 / 2 - completedNativeThetaTailMoment 0 / 4) ^ 4 := by
    positivity
  rw [canonicalCompletedNativeShiftedHankel_two_det_eq_xiCosineMoments,
    completedNativeXiCosineMoment_zero_eq_thetaTailMoments,
    completedNativeXiCosineMoment_one_eq_thetaTailMoments,
    completedNativeXiCosineMoment_two_eq_thetaTailMoments,
    completedNativeXiCosineMoment_three_eq_thetaTailMoments,
    completedNativeXiCosineMoment_four_eq_thetaTailMoments]
  have hnumpos : 0 < xiEighthMomentNumerator
      (1 / 2 - completedNativeThetaTailMoment 0 / 4)
      (2 * completedNativeThetaTailMoment 0 - completedNativeThetaTailMoment 2 / 4)
      (12 * completedNativeThetaTailMoment 2 - completedNativeThetaTailMoment 4 / 4)
      (30 * completedNativeThetaTailMoment 4 - completedNativeThetaTailMoment 6 / 4)
      (56 * completedNativeThetaTailMoment 6 - completedNativeThetaTailMoment 8 / 4) :=
    lt_of_lt_of_le (by norm_num) hnum
  have hnumpos' : 0 < xiEighthMomentNumerator
      (1 / 2 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 0)
      (2 * completedNativeThetaTailMoment 0 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 2)
      (12 * completedNativeThetaTailMoment 2 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 4)
      (30 * completedNativeThetaTailMoment 4 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 6)
      (56 * completedNativeThetaTailMoment 6 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 8) := by
    have heq : xiEighthMomentNumerator
        (1 / 2 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 0)
        (2 * completedNativeThetaTailMoment 0 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 2)
        (12 * completedNativeThetaTailMoment 2 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 4)
        (30 * completedNativeThetaTailMoment 4 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 6)
        (56 * completedNativeThetaTailMoment 6 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 8) =
      xiEighthMomentNumerator
        (1 / 2 - completedNativeThetaTailMoment 0 / 4)
        (2 * completedNativeThetaTailMoment 0 - completedNativeThetaTailMoment 2 / 4)
        (12 * completedNativeThetaTailMoment 2 - completedNativeThetaTailMoment 4 / 4)
        (30 * completedNativeThetaTailMoment 4 - completedNativeThetaTailMoment 6 / 4)
        (56 * completedNativeThetaTailMoment 6 - completedNativeThetaTailMoment 8 / 4) := by
      unfold xiEighthMomentNumerator
      ring
    rw [heq]
    exact hnumpos
  have hden' : 0 < 1209600 *
      (1 / 2 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 0) ^ 4 := by
    have heq : 1209600 * (1 / 2 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 0) ^ 4 =
        1209600 * (1 / 2 - completedNativeThetaTailMoment 0 / 4) ^ 4 := by
      ring
    rw [heq]
    exact hden
  exact div_pos hnumpos' hden'

end

end CarrySelfAdjointOperator
