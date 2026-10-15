import CarrySelfAdjointOperator.NativeThetaCofactorMargin
import CarrySelfAdjointOperator.NativeSourceThetaProjectiveValve

/-! The existing projective valve controls the central coefficient of every
fully synthesized theta polynomial. Its RAW mass coefficients have a negative
2x2 Hankel minor on the actual source. This does not concern the canonical
curvature moments, which remain a different sequence. -/
namespace CarrySelfAdjointOperator
open scoped BigOperators
open PowerSeries ProjectiveValve Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "m" => canonicalCompletedNativeLogDerivativeMoment
local notation "c₀" => completedNativeRealEvenCharacteristicCoefficient 0

def nativeValveMassCoefficient (n : ℕ) : ℝ :=
  PowerSeries.coeff n (projectiveValveMass (PowerSeries.mk m))

@[simp] theorem nativeValveMassCoefficient_zero : nativeValveMassCoefficient 0 = 1 := by
  simpa only [nativeValveMassCoefficient,PowerSeries.coeff_zero_eq_constantCoeff] using
    projectiveValveMass_constantCoeff (PowerSeries.mk m)

theorem nativeValveMassCoefficient_recurrence (n : ℕ) :
    ((n+1 : ℕ) : ℝ)*nativeValveMassCoefficient (n+1) =
      ∑ k ∈ Finset.range (n+1), m k*nativeValveMassCoefficient (n-k) := by
  have h := congrArg (PowerSeries.coeff n) (derivative_projectiveValveMass (PowerSeries.mk m))
  rw [PowerSeries.coeff_derivative,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [PowerSeries.coeff_mk,nativeValveMassCoefficient,mul_comm,Nat.cast_add,Nat.cast_one,Nat.succ_eq_add_one] using h

theorem nativeValveMassCoefficient_one : nativeValveMassCoefficient 1 = m 0 := by
  simpa using nativeValveMassCoefficient_recurrence 0

theorem nativeValveMassCoefficient_two :
    nativeValveMassCoefficient 2 = ((m 0)^2+m 1)/2 := by
  have h := nativeValveMassCoefficient_recurrence 1
  norm_num [Finset.sum_range_succ,nativeValveMassCoefficient_one] at h
  nlinarith

theorem nativeValveMass_second_hankel_minor :
    nativeValveMassCoefficient 0*nativeValveMassCoefficient 2-(nativeValveMassCoefficient 1)^2 =
      -completedNativeRealEvenCharacteristicCoefficient 2/c₀ := by
  rw [nativeValveMassCoefficient_zero,nativeValveMassCoefficient_one,nativeValveMassCoefficient_two]
  have h0 := canonicalCompletedNativeLogDerivativeMoment_real_recurrence 0
  have h1 := canonicalCompletedNativeLogDerivativeMoment_real_recurrence 1
  norm_num [Finset.sum_range_succ] at h0 h1
  have hc1 : completedNativeRealEvenCharacteristicCoefficient 1 = -(m 0)*c₀ := by linarith
  rw [hc1] at h1
  field_simp [completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero]
  nlinarith

theorem nativeCharacteristicCoefficient_two_pos :
    0 < completedNativeRealEvenCharacteristicCoefficient 2 := by
  rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder 2]
  norm_num
  exact completedNativeXiCosineMoment_pos 2

theorem nativeValveMass_second_hankel_minor_neg :
    nativeValveMassCoefficient 0*nativeValveMassCoefficient 2-(nativeValveMassCoefficient 1)^2 < 0 := by
  rw [nativeValveMass_second_hankel_minor]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos nativeCharacteristicCoefficient_two_pos)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/3)
      completedNativeRealEvenCharacteristicCoefficient_zero_ge_third)

theorem nativeValveMass_second_toeplitz_minor_pos :
    0 < (nativeValveMassCoefficient 1)^2-nativeValveMassCoefficient 0*nativeValveMassCoefficient 2 := by
  linarith [nativeValveMass_second_hankel_minor_neg]

/-- The raw valve mass is not a positive moment measure for the needed
Hankel geometry, even though its curvature is exactly the native moments. -/
theorem nativeValveMass_hankel_two_not_posSemidef :
    ¬(sourceMomentMatrix nativeValveMassCoefficient 0 2).PosSemidef := by
  intro h
  have hv := h.dotProduct_mulVec_nonneg (![(-nativeValveMassCoefficient 1),1] : Fin 2 → ℝ)
  norm_num [sourceMomentMatrix,dotProduct,Matrix.mulVec,Fin.sum_univ_two] at hv
  have hn := nativeValveMass_second_hankel_minor_neg
  rw [nativeValveMassCoefficient_zero] at hn
  nlinarith

/-- A coefficient identity at every order, BEFORE the theta integration. -/
theorem nativeThetaMomentPolynomial_coeff_two_valve (n : ℕ) :
    (nativeThetaMomentPolynomial n).coeff 2 = nativeValveMassCoefficient n/(2*c₀) := by
  rw [nativeThetaMomentPolynomial_eq_valve_convolution]
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_smul,Polynomial.coeff_monomial,smul_eq_mul]
  rw [Finset.sum_eq_single n]
  · simp only [Nat.sub_self,if_true]
    norm_num [nativeThetaMomentTopCoefficient,nativeValveMassCoefficient]
    ring
  · intro k hk hkn
    have hkn' : 2*(n-k)+2 ≠ 2 := by have := Finset.mem_range.mp hk; omega
    rw [if_neg hkn']
    ring
  · simp

/-- The actual critical polynomial uses a signed Hankel quadratic of the
valve coefficients at its u^2 coefficient; ALL ordered crosses remain. -/
theorem nativeSchurThetaPolynomial_coeff_two_valve (s n : ℕ) :
    (nativeSchurThetaPolynomial s n).coeff 2 =
      (1/2 : ℝ)*(∑ i : Fin (n+1), ∑ j : Fin (n+1),
        nativeSchurCriticalCoefficients s n i*nativeSchurCriticalCoefficients s n j*
          nativeValveMassCoefficient (i.val+j.val+s)) := by
  simp only [nativeSchurThetaPolynomial,nativeThetaQuadraticPolynomial,
    Polynomial.coeff_smul,Polynomial.finsetSum_coeff,smul_eq_mul,
    nativeThetaMomentPolynomial_coeff_two_valve,← mul_div_assoc,← Finset.sum_div]
  field_simp [completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero]

end
end CarrySelfAdjointOperator
