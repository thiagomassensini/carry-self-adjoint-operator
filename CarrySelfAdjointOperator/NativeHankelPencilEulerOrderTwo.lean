import CarrySelfAdjointOperator.NativeHankelPencilConditionalPositivity
import CarrySelfAdjointOperator.NativeHankelPencilCofactor
import CarrySelfAdjointOperator.NativeCompletedSourceFourthPositiveChannel
import CarrySelfAdjointOperator.CompletedNativeChiralReturnTenthSourceIntegral
import CarrySelfAdjointOperator.CompletedNativeChiralReturnTwelfthSourceIntegral

/-! The two Euler balances at `n = 2`, fed by source-first determinant
certificates. The old 2×2 prefixes are used only for invertibility. The
positive 3×3 determinant signs below come from the independent source boundary
integrals; no `PosDef` hypothesis on a 3×3 Hankel matrix is used. -/
namespace CarrySelfAdjointOperator

open Matrix
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

local notation "m" => canonicalCompletedNativeLogDerivativeMoment
local notation "c₀" => completedNativeRealEvenCharacteristicCoefficient 0

private theorem sourceMomentMatrix_zero_two_det :
    (sourceMomentMatrix m 0 2).det = m 0*m 2-m 1^2 := by
  rw [Matrix.det_fin_two]
  simp [sourceMomentMatrix, pow_two]

private theorem sourceMomentMatrix_one_two_det :
    (sourceMomentMatrix m 1 2).det = m 1*m 3-m 2^2 := by
  rw [Matrix.det_fin_two]
  simp [sourceMomentMatrix, pow_two]

/-- The source-first fourth-order discriminants certify only the old
2×2 prefixes needed by the Euler identities. -/
theorem nativeSourceEuler_even_prefix_two_isUnit :
    IsUnit (sourceMomentMatrix m 0 2) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [sourceMomentMatrix_zero_two_det]
  exact (ne_of_gt SourcePositiveReduction.nativeMoment_first_discriminant_pos)

theorem nativeSourceEuler_odd_prefix_two_isUnit :
    IsUnit (sourceMomentMatrix m 1 2) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [sourceMomentMatrix_one_two_det]
  exact (ne_of_gt SourcePositiveReduction.nativeMoment_shifted_discriminant_pos)

/-- The even source boundary discriminant is eight times the canonical
3×3 Hankel determinant. This is a finite algebraic identification only. -/
theorem nativeSourceFiveEvenDiscriminant_eq_eight_hankelDet :
    nativeSourceFiveEvenDiscriminant =
      8*(sourceMomentMatrix m 0 3).det := by
  have hcoeff (j : ℕ) : nativeSourceOddBoundaryCoefficient j = 2*m j := by
    rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
      primeDepthGeometricMoment_eq_canonical]
  unfold nativeSourceFiveEvenDiscriminant
  rw [hcoeff 0, hcoeff 1, hcoeff 2, hcoeff 3, hcoeff 4]
  rw [Matrix.det_fin_three]
  simp [sourceMomentMatrix, pow_two]
  ring

/-- The odd source boundary discriminant is eight times the shifted 3×3
Hankel determinant. -/
theorem nativeSourceSixOddDiscriminant_eq_eight_shifted_hankelDet :
    nativeSourceSixOddDiscriminant =
      8*(sourceMomentMatrix m 1 3).det := by
  have hcoeff (j : ℕ) : nativeSourceOddBoundaryCoefficient j = 2*m j := by
    rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
      primeDepthGeometricMoment_eq_canonical]
  unfold nativeSourceSixOddDiscriminant
  rw [hcoeff 1, hcoeff 2, hcoeff 3, hcoeff 4, hcoeff 5]
  rw [Matrix.det_fin_three]
  simp [sourceMomentMatrix, pow_two]
  ring

theorem nativeSourceEuler_even_three_prefixDet_pos :
    0 < nativeSourcePrefixDet 0 3 := by
  have h := nativeSourceFiveEvenDiscriminant_pos
  rw [nativeSourceFiveEvenDiscriminant_eq_eight_hankelDet] at h
  unfold nativeSourcePrefixDet
  nlinarith

theorem nativeSourceEuler_odd_three_prefixDet_pos :
    0 < nativeSourcePrefixDet 1 3 := by
  have h := nativeSourceSixOddDiscriminant_pos
  rw [nativeSourceSixOddDiscriminant_eq_eight_shifted_hankelDet] at h
  unfold nativeSourcePrefixDet
  nlinarith

private theorem nativeSourceEuler_schur_even_two_pos :
    0 < sourceMomentSchur m 0 2 := by
  have hprev : 0 < nativeSourcePrefixDet 0 2 := by
    rw [nativeSourcePrefixDet, sourceMomentMatrix_zero_two_det]
    exact SourcePositiveReduction.nativeMoment_first_discriminant_pos
  have hnext := nativeSourceEuler_even_three_prefixDet_pos
  have hratio : nativeSourcePrefixDet 0 3 =
      nativeSourcePrefixDet 0 2*sourceMomentSchur m 0 2 := by
    calc
      nativeSourcePrefixDet 0 3 = nativeSourcePrefixDet 0 (2+1) := by norm_num
      _ = nativeSourceBorderedScalar 0 2 := nativeSourcePrefixDet_succ_eq_borderedScalar 0 2
      _ = nativeSourcePrefixDet 0 2*sourceMomentSchur m 0 2 :=
        nativeSourceBorderedScalar_eq 0 2 nativeSourceEuler_even_prefix_two_isUnit
  rw [hratio] at hnext
  exact (mul_pos_iff_of_pos_left hprev).mp hnext

private theorem nativeSourceEuler_schur_odd_two_pos :
    0 < sourceMomentSchur m 1 2 := by
  have hprev : 0 < nativeSourcePrefixDet 1 2 := by
    rw [nativeSourcePrefixDet, sourceMomentMatrix_one_two_det]
    exact SourcePositiveReduction.nativeMoment_shifted_discriminant_pos
  have hnext := nativeSourceEuler_odd_three_prefixDet_pos
  have hratio : nativeSourcePrefixDet 1 3 =
      nativeSourcePrefixDet 1 2*sourceMomentSchur m 1 2 := by
    calc
      nativeSourcePrefixDet 1 3 = nativeSourcePrefixDet 1 (2+1) := by norm_num
      _ = nativeSourceBorderedScalar 1 2 := nativeSourcePrefixDet_succ_eq_borderedScalar 1 2
      _ = nativeSourcePrefixDet 1 2*sourceMomentSchur m 1 2 :=
        nativeSourceBorderedScalar_eq 1 2 nativeSourceEuler_odd_prefix_two_isUnit
  rw [hratio] at hnext
  exact (mul_pos_iff_of_pos_left hprev).mp hnext

private theorem nativeSourceEuler_even_remainder_two_pos :
    0 < nativeSourceSchurRemainder 0 2 := by
  rw [nativeSourceSchurRemainder_eq]
  have hc₀ : 0 < c₀ := lt_of_lt_of_le
    (by norm_num : (0 : ℝ) < 1/3)
    completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  exact mul_pos hc₀ nativeSourceEuler_schur_even_two_pos

private theorem nativeSourceEuler_odd_remainder_two_pos :
    0 < nativeSourceSchurRemainder 1 2 := by
  rw [nativeSourceSchurRemainder_eq]
  have hc₀ : 0 < c₀ := lt_of_lt_of_le
    (by norm_num : (0 : ℝ) < 1/3)
    completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  exact mul_pos hc₀ nativeSourceEuler_schur_odd_two_pos

/-- Exact even Euler mass balance at `n = 2`, with its prefix invertibility
discharged by the source-first 2×2 certificate. -/
theorem nativeSchurEuler_even_orderTwo_mass_balance :
    (10 : ℝ)*nativeSourceSchurRemainder 0 2 =
      nativeThetaPositiveMass (nativeSchurEulerPolynomial 0 2) -
        nativeThetaNegativeMass (nativeSchurEulerPolynomial 0 2) := by
  calc
    (10 : ℝ)*nativeSourceSchurRemainder 0 2 =
        nativeXiPolynomialIntegral (nativeSchurEulerPolynomial 0 2) := by
      simpa using nativeSchurEuler_even_balance 2 nativeSourceEuler_even_prefix_two_isUnit
    _ = nativeThetaPositiveMass (nativeSchurEulerPolynomial 0 2) -
        nativeThetaNegativeMass (nativeSchurEulerPolynomial 0 2) :=
      nativeXiPolynomialIntegral_eq_masses _

/-- Exact odd Euler mass balance at `n = 2`; the surviving source square and
the full negative mass are both retained. -/
theorem nativeSchurEuler_odd_orderTwo_mass_balance :
    (12 : ℝ)*nativeSourceSchurRemainder 1 2 =
      2*c₀*(nativeSchurCriticalReadout 1 2)^2 +
        nativeThetaPositiveMass (nativeSchurEulerPolynomial 1 2) -
          nativeThetaNegativeMass (nativeSchurEulerPolynomial 1 2) := by
  exact nativeSchurEuler_odd_mass_balance 2 nativeSourceEuler_odd_prefix_two_isUnit

/-- The even order-two Euler inequality is proved by the independent
source-first tenth-order certificate, after converting its scalar to the
canonical 3×3 determinant. -/
theorem nativeSchurEuler_even_orderTwo_mass_gate :
    nativeThetaNegativeMass (nativeSchurEulerPolynomial 0 2) <
      nativeThetaPositiveMass (nativeSchurEulerPolynomial 0 2) := by
  exact (nativeSchurEuler_even_pos_iff_mass_balance 2
    nativeSourceEuler_even_prefix_two_isUnit).mp nativeSourceEuler_even_remainder_two_pos

/-- The odd order-two Euler inequality follows from the source-first
twelfth-order certificate. The negative mass and the readout square remain
explicit in the exact balance. -/
theorem nativeSchurEuler_odd_orderTwo_mass_gate :
    nativeThetaNegativeMass (nativeSchurEulerPolynomial 1 2) <
      2*c₀*(nativeSchurCriticalReadout 1 2)^2 +
        nativeThetaPositiveMass (nativeSchurEulerPolynomial 1 2) := by
  exact (nativeSchurEuler_odd_pos_iff_mass_balance 2
    nativeSourceEuler_odd_prefix_two_isUnit).mp nativeSourceEuler_odd_remainder_two_pos

end
end CarrySelfAdjointOperator
