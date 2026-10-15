import CarrySelfAdjointOperator.NativeCompletedSourceFourthPositiveChannel
import CarrySelfAdjointOperator.NativeSourceSchurThetaMasses

/-! The fourth actual source scale is a positive multiple of the existing
all-order theta Schur family, at s=1,n=1. The common representation retains
signed densities; no all-order mass dominance is inferred from this member. -/
namespace CarrySelfAdjointOperator.SourcePositiveReduction
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

local notation "m" => canonicalCompletedNativeLogDerivativeMoment
local notation "c₀" => completedNativeRealEvenCharacteristicCoefficient 0

/-- Singleton elimination keeps the original source coupling. -/
theorem sourceMomentSchur_singleton (q : ℕ → ℝ) (s : ℕ) :
    sourceMomentSchur q s 1 = q (2+s)-q (1+s)^2/q s := by
  simp [sourceMomentSchur, sourceMomentCoupling, sourceMomentMatrix,
    Matrix.inv_subsingleton, Ring.inverse_eq_inv, Matrix.mulVec, dotProduct,
    pow_two, div_eq_mul_inv, mul_comm]
  ring

theorem nativeSourceSchur_shifted_one_eq :
    sourceMomentSchur m 1 1 = (m 1*m 3-m 2^2)/m 1 := by
  rw [sourceMomentSchur_singleton]
  norm_num only [Nat.reduceAdd]
  field_simp [nativeMoment_one_pos.ne']

theorem nativeSourceSchurRemainder_shifted_one_eq :
    nativeSourceSchurRemainder 1 1 = c₀*((m 1*m 3-m 2^2)/m 1) := by
  rw [nativeSourceSchurRemainder_eq, nativeSourceSchur_shifted_one_eq]

theorem nativeSourceSchurRemainder_shifted_one_pos :
    0 < nativeSourceSchurRemainder 1 1 := by
  rw [nativeSourceSchurRemainder_shifted_one_eq]
  have hc : 0 < c₀ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/3)
    completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  exact mul_pos hc (div_pos nativeMoment_shifted_discriminant_pos nativeMoment_one_pos)

/-- A new strict sign for the s=1,n=1 member of the SAME theta family. -/
theorem nativeSchurThetaIntegral_shifted_one_pos :
    0 < nativeXiPolynomialIntegral (nativeSchurThetaPolynomial 1 1) := by
  rw [nativeSchurThetaPolynomial_integral]
  exact nativeSourceSchurRemainder_shifted_one_pos

theorem nativeSchurThetaMasses_shifted_one_dominance :
    nativeThetaNegativeMass (nativeSchurThetaPolynomial 1 1) <
      nativeThetaPositiveMass (nativeSchurThetaPolynomial 1 1) := by
  exact (nativeSourceSchurRemainder_pos_iff_thetaMassDominance 1 1).mp
    nativeSourceSchurRemainder_shifted_one_pos

theorem nativeSchurThetaMasses_shifted_one_strict :
    0 < nativeThetaNegativeMass (nativeSchurThetaPolynomial 1 1) ∧
      nativeThetaNegativeMass (nativeSchurThetaPolynomial 1 1) <
        nativeThetaPositiveMass (nativeSchurThetaPolynomial 1 1) :=
  ⟨nativeSchurThetaPolynomial_odd_negativeMass_pos 1,
    nativeSchurThetaMasses_shifted_one_dominance⟩

theorem nativeSchurThetaPolynomial_shifted_one_top :
    (nativeSchurThetaPolynomial 1 1).coeff 8 = -(1/10080 : ℝ) := by
  have h := nativeSchurThetaPolynomial_coeff_top 1 1
  norm_num at h
  exact h

/-- Exact transport from the common theta Schur integral to the derivative
of the actual third residual response. The coefficient is source-derived. -/
theorem chainScale_three_eq_theta_integral :
    chainScale 3 = m 1^2/(c₀*(m 0*m 2-m 1^2)^2) *
      nativeXiPolynomialIntegral (nativeSchurThetaPolynomial 1 1) := by
  rw [chainScale_three_eq, nativeSchurThetaPolynomial_integral,
    nativeSourceSchurRemainder_shifted_one_eq]
  field_simp [nativeMoment_one_pos.ne',
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero]

theorem chainScale_three_theta_factor_pos :
    0 < m 1^2/(c₀*(m 0*m 2-m 1^2)^2) := by
  have hc : 0 < c₀ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/3)
    completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  exact div_pos (sq_pos_of_pos nativeMoment_one_pos)
    (mul_pos hc (sq_pos_of_pos nativeMoment_first_discriminant_pos))

end
end CarrySelfAdjointOperator.SourcePositiveReduction
