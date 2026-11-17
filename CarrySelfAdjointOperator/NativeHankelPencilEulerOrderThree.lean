import CarrySelfAdjointOperator.NativeAllOrderFiniteDiscriminantBridge
import CarrySelfAdjointOperator.NativeAllOrderCharacteristicCeiling
import CarrySelfAdjointOperator.NativeHankelPencilEulerMassRecurrenceAudit

/-! Order-three Euler source gate. The central fourth Hankel determinant is
certified directly by the original order-14 source face; the shifted gate is
reduced to its exact characteristic ceiling and is not asserted. -/
namespace CarrySelfAdjointOperator

open Matrix
open scoped BigOperators

noncomputable section
set_option autoImplicit false

local notation "m" => canonicalCompletedNativeLogDerivativeMoment
local notation "c₀" => completedNativeRealEvenCharacteristicCoefficient 0

/-- The source certificate for the central 4×4 determinant, together with
the already positive 3×3 prefix, proves the next central Schur remainder.
No 4×4 `PosDef` hypothesis is used. -/
theorem nativeSourceEuler_even_remainder_three_pos :
    0 < nativeSourceSchurRemainder 0 3 := by
  rw [nativeSourceSchurRemainder_eq]
  have hc₀ : 0 < c₀ := lt_of_lt_of_le
    (by norm_num : (0 : ℝ) < 1/3)
    completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  have hprev : 0 < nativeSourcePrefixDet 0 3 :=
    nativeSourceEuler_even_three_prefixDet_pos
  have hnext : 0 < nativeSourcePrefixDet 0 4 := by
    unfold nativeSourcePrefixDet
    exact nativeSourceCentral_hankelDet_four_pos
  have hA : IsUnit (sourceMomentMatrix m 0 3) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    exact (ne_of_gt hprev)
  have hratio : nativeSourcePrefixDet 0 4 =
      nativeSourcePrefixDet 0 3 * sourceMomentSchur m 0 3 := by
    calc
      nativeSourcePrefixDet 0 4 = nativeSourcePrefixDet 0 (3+1) := by norm_num
      _ = nativeSourceBorderedScalar 0 3 :=
        nativeSourcePrefixDet_succ_eq_borderedScalar 0 3
      _ = nativeSourcePrefixDet 0 3 * sourceMomentSchur m 0 3 :=
        nativeSourceBorderedScalar_eq 0 3 hA
  rw [hratio] at hnext
  exact mul_pos hc₀ ((mul_pos_iff_of_pos_left hprev).mp hnext)

/-- The order-three central Euler mass gate follows from the independent
order-14 source certificate, with the full positive/negative masses retained. -/
theorem nativeSchurEuler_even_orderThree_mass_gate :
    nativeThetaNegativeMass (nativeSchurEulerPolynomial 0 3) <
      nativeThetaPositiveMass (nativeSchurEulerPolynomial 0 3) := by
  exact (nativeSchurEuler_even_pos_iff_mass_balance 3
    nativeSourceEuler_even_prefix_three_isUnit).mp
      nativeSourceEuler_even_remainder_three_pos

/-- In the shifted tower the order-three gate is exactly the generic
characteristic ceiling for `c₈`. The theorem records the reduction only. -/
theorem nativeSchurEuler_odd_orderThree_mass_gate_iff_characteristic_ceiling :
    nativeThetaNegativeMass (nativeSchurEulerPolynomial 1 3) <
      2*c₀*(nativeSchurCriticalReadout 1 3)^2 +
        nativeThetaPositiveMass (nativeSchurEulerPolynomial 1 3) ↔
      completedNativeRealEvenCharacteristicCoefficient 8 <
        nativeSourceCharacteristicCeiling 1 3 := by
  rw [← nativeSchurEuler_odd_pos_iff_mass_balance 3
      nativeSourceEuler_odd_prefix_three_isUnit]
  rw [nativeSourceSchurRemainder_eq]
  have hc₀ : 0 < c₀ := lt_of_lt_of_le
    (by norm_num : (0 : ℝ) < 1/3)
    completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  rw [mul_pos_iff_of_pos_left hc₀,
    nativeSourceShiftedSchur_pos_iff_characteristic_ceiling]

end
end CarrySelfAdjointOperator
