import CarrySelfAdjointOperator.NativeHankelPencilEulerOrderTwo
import CarrySelfAdjointOperator.CompletedNativeChiralReturnFourteenthSourceIntegral
import CarrySelfAdjointOperator.CompletedNativeChiralReturnEightBoundaryFace

/-! Finite source-boundary discriminants as the next canonical Hankel
determinants. The identities are algebraic consequences of the already
identified original boundary coefficients; the shifted fourth-order sign is
left at its explicit characteristic ceiling. -/
namespace CarrySelfAdjointOperator

open Matrix
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "m" => canonicalCompletedNativeLogDerivativeMoment

private theorem nativeSourceBoundaryCoefficient_eq_twice_moment (j : ℕ) :
    nativeSourceOddBoundaryCoefficient j = 2*m j := by
  rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical]

/-- The order-14 central source discriminant is sixteen times the canonical
4×4 central Hankel determinant. -/
theorem nativeSourceSevenEvenDiscriminant_eq_sixteen_hankelDet :
    nativeSourceSevenEvenDiscriminant =
      16*(sourceMomentMatrix m 0 4).det := by
  rw [nativeSourceSevenEvenDiscriminant,
    nativeSourceFiveEvenDiscriminant_eq_eight_hankelDet]
  unfold nativeSourceSevenEvenCoupling0 nativeSourceSevenEvenCoupling1
    nativeSourceSevenEvenCoupling2
  simp_rw [nativeSourceBoundaryCoefficient_eq_twice_moment]
  conv_rhs => rw [Matrix.det_succ_row_zero]
  simp [sourceMomentMatrix, Fin.succAbove, Matrix.det_fin_three, Fin.sum_univ_succ,
    pow_two]
  ring_nf

/-- The order-16 shifted source discriminant is sixteen times the canonical
4×4 shifted Hankel determinant. -/
theorem nativeSourceEightOddDiscriminant_eq_sixteen_shifted_hankelDet :
    nativeSourceEightOddDiscriminant =
      16*(sourceMomentMatrix m 1 4).det := by
  rw [nativeSourceEightOddDiscriminant,
    nativeSourceSixOddDiscriminant_eq_eight_shifted_hankelDet]
  unfold nativeSourceEightOddCoupling0 nativeSourceEightOddCoupling1
    nativeSourceEightOddCoupling2
  simp_rw [nativeSourceBoundaryCoefficient_eq_twice_moment]
  conv_rhs => rw [Matrix.det_succ_row_zero]
  simp [sourceMomentMatrix, Fin.succAbove, Matrix.det_fin_three, Fin.sum_univ_succ,
    pow_two]
  ring_nf

/-- The existing source certificate therefore proves the central 4×4
determinant positive. -/
theorem nativeSourceCentral_hankelDet_four_pos :
    0 < (sourceMomentMatrix m 0 4).det := by
  have h := nativeSourceSevenEvenDiscriminant_pos
  rw [nativeSourceSevenEvenDiscriminant_eq_sixteen_hankelDet] at h
  nlinarith

/-- For the shifted 4×4 determinant, the source's existing coefficient
ceiling is an exact condition; this theorem does not assert that the bound
holds. -/
theorem nativeSourceShifted_hankelDet_four_pos_iff_characteristic_ceiling :
    0 < (sourceMomentMatrix m 1 4).det ↔
      completedNativeRealEvenCharacteristicCoefficient 8 <
        nativeSourceEightCharacteristicCeiling := by
  have hdet := nativeSourceEightOddDiscriminant_eq_sixteen_shifted_hankelDet
  have hgate := nativeSourceEightOddDiscriminant_pos_iff_characteristic_ceiling
  constructor
  · intro h
    apply hgate.mp
    rw [hdet]
    exact mul_pos (by norm_num) h
  · intro h
    have hp := hgate.mpr h
    rw [hdet] at hp
    nlinarith

end
end CarrySelfAdjointOperator
