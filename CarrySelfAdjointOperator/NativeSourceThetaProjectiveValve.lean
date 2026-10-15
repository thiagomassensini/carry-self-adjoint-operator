import CarrySelfAdjointOperator.NativeSourceThetaGreenTransport
import CarrySelfAdjointOperator.NativeMomentProjectiveValveBridge

/-! The source-polynomial transform is the existing projective valve mass
acting on its derivative numerator. This is an exact scalar formal-series
identity; it is not a Hilbert Gram or positivity theorem. -/
namespace CarrySelfAdjointOperator
open scoped BigOperators
open PowerSeries ProjectiveValve
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

def nativeThetaPolynomialSeries (u : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun n => (nativeThetaMomentPolynomial n).eval u)

def nativeThetaNumeratorSeries (u : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun n => nativeThetaMomentTopCoefficient n * u^(2*n+2))

/-- The polynomial recursion holds before integration, in the same formal
series ring as the existing native projective valve. -/
theorem completedNativeEvenFormalSeries_mul_thetaPolynomialSeries (u : ℝ) :
    completedNativeEvenFormalSeries * nativeThetaPolynomialSeries u =
      nativeThetaNumeratorSeries u := by
  ext n
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [completedNativeEvenFormalSeries, nativeThetaPolynomialSeries,
    nativeThetaNumeratorSeries, coeff_mk]
  rw [Finset.sum_range_succ]
  have hp := congrArg (Polynomial.eval u) (nativeThetaMomentPolynomial_eq n)
  simp only [Polynomial.eval_smul, Polynomial.eval_sub, Polynomial.eval_monomial,
    Polynomial.eval_finsetSum, smul_eq_mul] at hp
  have hs : (∑ k ∈ Finset.range n,
      (nativeThetaMomentPolynomial k).eval u *
        completedNativeRealEvenCharacteristicCoefficient (n-k)) =
      ∑ k ∈ Finset.range n, completedNativeRealEvenCharacteristicCoefficient (n-k) *
        (nativeThetaMomentPolynomial k).eval u := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hs, hp]
  simp only [Nat.sub_self]
  field_simp [completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero]
  ring

/-- Applying the EXISTING valve, with its fixed normalization, gives the
whole source polynomial series. No coefficient sign is assumed. -/
theorem nativeThetaPolynomialSeries_eq_projectiveValve (u : ℝ) :
    nativeThetaPolynomialSeries u =
      projectiveValveMass (PowerSeries.mk canonicalCompletedNativeLogDerivativeMoment) *
        (PowerSeries.C (completedNativeRealEvenCharacteristicCoefficient 0)⁻¹ *
          nativeThetaNumeratorSeries u) := by
  have hnorm : normalizedCompletedNativeEvenFormalSeries * nativeThetaPolynomialSeries u =
      PowerSeries.C (completedNativeRealEvenCharacteristicCoefficient 0)⁻¹ *
        nativeThetaNumeratorSeries u := by
    rw [normalizedCompletedNativeEvenFormalSeries, mul_assoc,
      completedNativeEvenFormalSeries_mul_thetaPolynomialSeries]
  rw [projectiveValveMass_nativeMoments_eq_reciprocal, ← hnorm, ← mul_assoc,
    PowerSeries.inv_mul_cancel _ (by simp), one_mul]

/-- Coefficient form of the same valve convolution, at arbitrary order. -/
theorem nativeThetaMomentPolynomial_eval_eq_valve_convolution (u : ℝ) (n : ℕ) :
    (nativeThetaMomentPolynomial n).eval u =
      ∑ k ∈ Finset.range (n+1),
        (PowerSeries.coeff k
          (projectiveValveMass (PowerSeries.mk canonicalCompletedNativeLogDerivativeMoment))) *
          ((completedNativeRealEvenCharacteristicCoefficient 0)⁻¹ *
            nativeThetaMomentTopCoefficient (n-k) * u^(2*(n-k)+2)) := by
  have h := congrArg (PowerSeries.coeff n) (nativeThetaPolynomialSeries_eq_projectiveValve u)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [nativeThetaPolynomialSeries, nativeThetaNumeratorSeries, coeff_mk,
    coeff_C_mul, mul_assoc] using h

theorem nativeThetaMomentPolynomial_eq_valve_convolution (n : ℕ) :
    nativeThetaMomentPolynomial n =
      ∑ k ∈ Finset.range (n+1),
        ((PowerSeries.coeff k
          (projectiveValveMass (PowerSeries.mk canonicalCompletedNativeLogDerivativeMoment))) *
          (completedNativeRealEvenCharacteristicCoefficient 0)⁻¹) •
            Polynomial.monomial (2*(n-k)+2) (nativeThetaMomentTopCoefficient (n-k)) := by
  apply Polynomial.funext
  intro u
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_smul, Polynomial.eval_monomial,
    smul_eq_mul]
  simpa only [mul_assoc] using nativeThetaMomentPolynomial_eval_eq_valve_convolution u n

/-- The fixed Green differential transfer commutes with the actual valve
convolution. This supplies a uniform rule, without any sign assertion. -/
theorem nativeThetaGreenMomentPolynomial_eq_valve_convolution (n : ℕ) :
    nativeThetaGreenPolynomial (nativeThetaMomentPolynomial n) =
      ∑ k ∈ Finset.range (n+1),
        ((PowerSeries.coeff k
          (projectiveValveMass (PowerSeries.mk canonicalCompletedNativeLogDerivativeMoment))) *
          (completedNativeRealEvenCharacteristicCoefficient 0)⁻¹) •
            nativeThetaGreenPolynomial
              (Polynomial.monomial (2*(n-k)+2) (nativeThetaMomentTopCoefficient (n-k))) := by
  rw [nativeThetaMomentPolynomial_eq_valve_convolution, nativeThetaGreenPolynomial_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact nativeThetaGreenPolynomial_smul _ _

end
end CarrySelfAdjointOperator
