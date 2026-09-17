import CarrySelfAdjointOperator.CompletedNativeTenthOrderThetaBridge
import Mathlib.Tactic

/-!
# Tenth-order cosine-moment form of the third native Hankel minor

This is a finite algebraic transport of the canonical native determinant to
the downstream cosine moments.  It contains no sign claim: the remaining
analytic gate is precisely the sign of the displayed integer polynomial on a
certified theta-tail box.
-/

namespace CarrySelfAdjointOperator

noncomputable section

set_option autoImplicit false

/-- Integer numerator obtained from the third native Hankel minor after the
canonical cosine-moment normalizations through order ten. -/
def canonicalCompletedNativeHankelThreeXiTenthMomentNumerator
    (m0 m1 m2 m3 m4 m5 : ℝ) : ℝ :=
  105 * m0 ^ 2 * m1 * m3 * m5 -
    180 * m0 ^ 2 * m1 * m4 ^ 2 -
    350 * m0 ^ 2 * m2 ^ 2 * m5 +
    2520 * m0 ^ 2 * m2 * m3 * m4 -
    2646 * m0 ^ 2 * m3 ^ 3 +
    525 * m0 * m1 ^ 2 * m2 * m5 -
    2205 * m0 * m1 ^ 2 * m3 * m4 -
    9450 * m0 * m1 * m2 ^ 2 * m4 +
    26460 * m0 * m1 * m2 * m3 ^ 2 -
    14700 * m0 * m2 ^ 3 * m3 +
    14175 * m1 ^ 3 * m2 * m4 -
    35280 * m1 ^ 3 * m3 ^ 2 +
    22050 * m1 ^ 2 * m2 ^ 2 * m3

/-- Exact tenth-order cosine-moment form of the third native Hankel
determinant. -/
theorem canonicalCompletedNativeHankel_three_det_eq_xiTenthMomentRatio :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment 3).det =
      canonicalCompletedNativeHankelThreeXiTenthMomentNumerator
          (completedNativeXiCosineMoment 0)
          (completedNativeXiCosineMoment 1)
          (completedNativeXiCosineMoment 2)
          (completedNativeXiCosineMoment 3)
          (completedNativeXiCosineMoment 4)
          (completedNativeXiCosineMoment 5) /
        (36578304000 * completedNativeXiCosineMoment 0 ^ 5) := by
  rw [canonicalCompletedNativeHankel_three_det_eq_tenthOrderRatio,
    completedNativeRealEvenCharacteristicCoefficient_zero_eq_xiCosineMoment,
    completedNativeRealEvenCharacteristicCoefficient_one_eq_xiCosineMoment,
    completedNativeRealEvenCharacteristicCoefficient_two_eq_xiCosineMoment,
    completedNativeRealEvenCharacteristicCoefficient_three_eq_xiCosineMoment,
    completedNativeRealEvenCharacteristicCoefficient_four_eq_xiCosineMoment,
    completedNativeRealEvenCharacteristicCoefficient_five_eq_xiCosineMoment]
  unfold canonicalCompletedNativeHankelThreeNumerator
    canonicalCompletedNativeHankelThreeXiTenthMomentNumerator
  ring

end

end CarrySelfAdjointOperator
