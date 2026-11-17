import CarrySelfAdjointOperator.NativeSourceAllOrderSchur

/-! Exact all-order coefficient ceiling for the next native Schur pivot.
The characteristic and moment sequence are the original completed-source
objects imported from the CSA; this module only rearranges their established
logarithmic derivative recurrence. -/
namespace CarrySelfAdjointOperator

open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false

local notation "m" => canonicalCompletedNativeLogDerivativeMoment
local notation "c₀" => completedNativeRealEvenCharacteristicCoefficient 0

/-- The next characteristic coefficient's ceiling, computed from the old
moments, old characteristic coefficients, and the Schur coupling correction.
The denominator is the positive integer `2*n+s+1`. -/
def nativeSourceCharacteristicCeiling (s n : ℕ) : ℝ :=
  -((∑ k ∈ Finset.range (2*n+s), m k *
        completedNativeRealEvenCharacteristicCoefficient (2*n+s-k)) +
      c₀ * (sourceMomentCoupling m s n ⬝ᵥ
        ((sourceMomentMatrix m s n)⁻¹ *ᵥ sourceMomentCoupling m s n))) /
    ((2*n+s+1 : ℕ) : ℝ)

/-- The Schur remainder is exactly the positive index factor times the gap
between the old-data ceiling and the next characteristic coefficient. -/
theorem nativeSourceSchurRemainder_eq_characteristic_gap (s n : ℕ) :
    nativeSourceSchurRemainder s n =
      ((2*n+s+1 : ℕ) : ℝ) *
        (nativeSourceCharacteristicCeiling s n -
          completedNativeRealEvenCharacteristicCoefficient (2*n+s+1)) := by
  have hrec := canonicalCompletedNativeLogDerivativeMoment_real_recurrence (2*n+s)
  have hq : (0 : ℝ) < ((2*n+s+1 : ℕ) : ℝ) := by positivity
  unfold nativeSourceSchurRemainder nativeSourceCharacteristicCeiling
  field_simp [ne_of_gt hq]
  nlinarith [hrec]

/-- The characteristic recurrence isolates the Schur expression without a
positivity assumption. When the prefix is a unit, this is the usual Schur
complement; the identity itself remains algebraically valid for Lean's total
matrix inverse at singular prefixes as well. -/
theorem nativeSource_schur_eq_characteristic_recurrence
    (s n : ℕ) :
    c₀ * sourceMomentSchur m s n =
      -((2*n+s+1 : ℕ) : ℝ) *
          completedNativeRealEvenCharacteristicCoefficient (2*n+s+1) -
        (∑ k ∈ Finset.range (2*n+s), m k *
          completedNativeRealEvenCharacteristicCoefficient (2*n+s-k)) -
        c₀ * (sourceMomentCoupling m s n ⬝ᵥ
          ((sourceMomentMatrix m s n)⁻¹ *ᵥ sourceMomentCoupling m s n)) := by
  rw [← nativeSourceSchurRemainder_eq s n,
    nativeSourceSchurRemainder_eq_characteristic_gap]
  unfold nativeSourceCharacteristicCeiling
  have hq : (↑(2*n+s+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hq]
  ring

/-- For every prefix order and shift, positivity of the actual Schur pivot is
equivalent to a strict upper bound on the next completed-characteristic
coefficient. No `PosDef` hypothesis is used. -/
theorem nativeSource_schur_pos_iff_characteristic_ceiling
    (s n : ℕ) :
    0 < sourceMomentSchur m s n ↔
      completedNativeRealEvenCharacteristicCoefficient (2*n+s+1) <
        nativeSourceCharacteristicCeiling s n := by
  have hc₀ : 0 < c₀ := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/3)
      completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  have hq : (0 : ℝ) < ((2*n+s+1 : ℕ) : ℝ) := by positivity
  have hrel := nativeSourceSchurRemainder_eq s n
  have hgap := nativeSourceSchurRemainder_eq_characteristic_gap s n
  constructor
  · intro hs
    have hr : 0 < nativeSourceSchurRemainder s n := by
      rw [hrel]
      exact mul_pos hc₀ hs
    rw [hgap] at hr
    have : 0 < nativeSourceCharacteristicCeiling s n -
        completedNativeRealEvenCharacteristicCoefficient (2*n+s+1) :=
      (mul_pos_iff_of_pos_left hq).mp hr
    exact (sub_pos.mp this)
  · intro hc
    have hg : 0 < nativeSourceCharacteristicCeiling s n -
        completedNativeRealEvenCharacteristicCoefficient (2*n+s+1) :=
      sub_pos.mpr hc
    have hr : 0 < nativeSourceSchurRemainder s n := by
      rw [hgap]
      exact mul_pos hq hg
    rw [hrel] at hr
    exact (mul_pos_iff_of_pos_left hc₀).mp hr

/-- Central tower indexing: dimension `n+1` is controlled by coefficient
`c_(2*n+1)`. -/
theorem nativeSourceCentralSchur_pos_iff_characteristic_ceiling
    (n : ℕ) :
    0 < sourceMomentSchur m 0 n ↔
      completedNativeRealEvenCharacteristicCoefficient (2*n+1) <
        nativeSourceCharacteristicCeiling 0 n := by
  simpa using nativeSource_schur_pos_iff_characteristic_ceiling 0 n

/-- Shifted tower indexing: dimension `n+1` is controlled by coefficient
`c_(2*n+2)`. -/
theorem nativeSourceShiftedSchur_pos_iff_characteristic_ceiling
    (n : ℕ) :
    0 < sourceMomentSchur m 1 n ↔
      completedNativeRealEvenCharacteristicCoefficient (2*n+2) <
        nativeSourceCharacteristicCeiling 1 n := by
  simpa using nativeSource_schur_pos_iff_characteristic_ceiling 1 n

end
end CarrySelfAdjointOperator
