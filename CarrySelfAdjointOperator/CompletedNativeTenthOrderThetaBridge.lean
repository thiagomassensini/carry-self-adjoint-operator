import CarrySelfAdjointOperator.CompletedNativeTenthOrderHankelGate
import CarrySelfAdjointOperator.CompletedNativeXiThetaMoments
import Mathlib.Tactic

/-!
# Tenth-order downstream theta bridge

The native characteristic and its logarithmic moments remain the primary
objects. This module records only the already-derived analytic certificate
which writes their tenth Taylor coefficient through the concrete theta tail.
No positivity claim for the third Hankel minor is made here.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- The tenth cosine moment retains the adjacent eighth and tenth theta-tail
orders. -/
theorem completedNativeXiCosineMoment_five_eq_thetaTailMoments :
    completedNativeXiCosineMoment 5 =
      90 * completedNativeThetaTailMoment 8 -
        (1 / 4 : ℝ) * completedNativeThetaTailMoment 10 := by
  convert completedNativeXiCosineMoment_succ_eq_thetaTailMoments 4 using 1
  norm_num

/-- The native tenth Taylor coefficient, expressed downstream through its
concrete theta-tail certificate. -/
theorem completedNativeRealEvenCharacteristicCoefficient_five_eq_thetaTailMoments :
    completedNativeRealEvenCharacteristicCoefficient 5 =
      -(90 * completedNativeThetaTailMoment 8 -
          (1 / 4 : ℝ) * completedNativeThetaTailMoment 10) / 3628800 := by
  rw [completedNativeRealEvenCharacteristicCoefficient_five_eq_xiCosineMoment,
    completedNativeXiCosineMoment_five_eq_thetaTailMoments]

end

end CarrySelfAdjointOperator
