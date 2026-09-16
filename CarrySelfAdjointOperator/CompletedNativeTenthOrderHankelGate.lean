import CarrySelfAdjointOperator.CompletedNativeShiftedHankelEighthGate
import Mathlib.Tactic

/-!
# Tenth-order algebraic reduction for the third native Hankel minor

This module contains only the native logarithmic-moment recurrence and finite
matrix algebra.  In particular, it neither asserts a sign for the third
Hankel determinant nor introduces a new positive carrier.  A later analytic
certificate may bound the displayed numerator through an already-proved
downstream theta/cosine identity, but the characteristic and the moments here
remain the canonical native ones.
-/

namespace CarrySelfAdjointOperator

noncomputable section

set_option autoImplicit false

/-- Tenth-order logarithmic coefficient from the native real recurrence. -/
theorem canonicalCompletedNativeLogDerivativeMoment_four_eq_tenthOrderRatio :
    canonicalCompletedNativeLogDerivativeMoment 4 =
      (-completedNativeRealEvenCharacteristicCoefficient 1 ^ 5 +
        5 * completedNativeRealEvenCharacteristicCoefficient 0 *
          completedNativeRealEvenCharacteristicCoefficient 1 ^ 3 *
          completedNativeRealEvenCharacteristicCoefficient 2 -
        5 * completedNativeRealEvenCharacteristicCoefficient 0 ^ 2 *
          completedNativeRealEvenCharacteristicCoefficient 1 *
          completedNativeRealEvenCharacteristicCoefficient 2 ^ 2 -
        5 * completedNativeRealEvenCharacteristicCoefficient 0 ^ 2 *
          completedNativeRealEvenCharacteristicCoefficient 1 ^ 2 *
          completedNativeRealEvenCharacteristicCoefficient 3 +
        5 * completedNativeRealEvenCharacteristicCoefficient 0 ^ 3 *
          completedNativeRealEvenCharacteristicCoefficient 2 *
          completedNativeRealEvenCharacteristicCoefficient 3 +
        5 * completedNativeRealEvenCharacteristicCoefficient 0 ^ 3 *
          completedNativeRealEvenCharacteristicCoefficient 1 *
          completedNativeRealEvenCharacteristicCoefficient 4 -
        5 * completedNativeRealEvenCharacteristicCoefficient 0 ^ 4 *
          completedNativeRealEvenCharacteristicCoefficient 5) /
        completedNativeRealEvenCharacteristicCoefficient 0 ^ 5 := by
  have hr := canonicalCompletedNativeLogDerivativeMoment_real_recurrence 4
  norm_num [Finset.sum_range_succ] at hr
  rw [canonicalCompletedNativeLogDerivativeMoment_zero_eq_secondOrderRatio,
    canonicalCompletedNativeLogDerivativeMoment_one_eq_fourthOrderDiscriminant,
    canonicalCompletedNativeLogDerivativeMoment_two_eq_sixthOrderRatio,
    canonicalCompletedNativeLogDerivativeMoment_three_eq_eighthOrderRatio] at hr
  have hc := completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero
  field_simp [hc] at hr ⊢
  linear_combination hr

/-- The third native Hankel determinant in its moment variables. -/
theorem canonicalCompletedNativeHankel_three_det_eq :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment 3).det =
      canonicalCompletedNativeLogDerivativeMoment 0 *
          canonicalCompletedNativeLogDerivativeMoment 2 *
          canonicalCompletedNativeLogDerivativeMoment 4 +
        2 * canonicalCompletedNativeLogDerivativeMoment 1 *
          canonicalCompletedNativeLogDerivativeMoment 2 *
          canonicalCompletedNativeLogDerivativeMoment 3 -
        canonicalCompletedNativeLogDerivativeMoment 0 *
          canonicalCompletedNativeLogDerivativeMoment 3 ^ 2 -
        canonicalCompletedNativeLogDerivativeMoment 1 ^ 2 *
          canonicalCompletedNativeLogDerivativeMoment 4 -
        canonicalCompletedNativeLogDerivativeMoment 2 ^ 3 := by
  rw [Matrix.det_fin_three]
  norm_num [hankelGram, pow_two]
  ring

/-- The single native scalar whose sign is exactly the sign of the third
Hankel minor, because the central coefficient is already nonzero. -/
def canonicalCompletedNativeHankelThreeNumerator (a b c d e f : ℝ) : ℝ :=
  -15 * a ^ 2 * b * d * f +
    16 * a ^ 2 * b * e ^ 2 +
    20 * a ^ 2 * c ^ 2 * f -
    48 * a ^ 2 * c * d * e +
    27 * a ^ 2 * d ^ 3 -
    5 * a * b ^ 2 * c * f +
    7 * a * b ^ 2 * d * e +
    12 * a * b * c ^ 2 * e -
    18 * a * b * c * d ^ 2 +
    4 * a * c ^ 3 * d -
    3 * b ^ 3 * c * e +
    4 * b ^ 3 * d ^ 2 -
    b ^ 2 * c ^ 2 * d

/-- Exact tenth-order reduction of the third native Hankel determinant. -/
theorem canonicalCompletedNativeHankel_three_det_eq_tenthOrderRatio :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment 3).det =
      canonicalCompletedNativeHankelThreeNumerator
        (completedNativeRealEvenCharacteristicCoefficient 0)
        (completedNativeRealEvenCharacteristicCoefficient 1)
        (completedNativeRealEvenCharacteristicCoefficient 2)
        (completedNativeRealEvenCharacteristicCoefficient 3)
        (completedNativeRealEvenCharacteristicCoefficient 4)
        (completedNativeRealEvenCharacteristicCoefficient 5) /
        completedNativeRealEvenCharacteristicCoefficient 0 ^ 5 := by
  rw [canonicalCompletedNativeHankel_three_det_eq,
    canonicalCompletedNativeLogDerivativeMoment_zero_eq_secondOrderRatio,
    canonicalCompletedNativeLogDerivativeMoment_one_eq_fourthOrderDiscriminant,
    canonicalCompletedNativeLogDerivativeMoment_two_eq_sixthOrderRatio,
    canonicalCompletedNativeLogDerivativeMoment_three_eq_eighthOrderRatio,
    canonicalCompletedNativeLogDerivativeMoment_four_eq_tenthOrderRatio]
  unfold canonicalCompletedNativeHankelThreeNumerator
  field_simp [completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero]
  ring

end

end CarrySelfAdjointOperator
