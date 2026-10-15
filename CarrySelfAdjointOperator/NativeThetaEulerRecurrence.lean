import CarrySelfAdjointOperator.NativeSourceThetaProjectiveValve

/-! An all-order Euler identity for the ORIGINAL source polynomials. The
identity is derived from the existing valve and its differential equation;
no sign of a source moment or desired Hankel matrix is assumed. -/
namespace CarrySelfAdjointOperator
open PowerSeries ProjectiveValve
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The spatial Euler derivative of the already source-defined family. -/
def nativeThetaEulerPolynomial (n : ℕ) : Polynomial ℝ :=
  Polynomial.X * (nativeThetaMomentPolynomial n).derivative

def nativeThetaEulerSeries (u : ℝ) : PowerSeries ℝ :=
  mk (fun n => (nativeThetaEulerPolynomial n).eval u)

def nativeThetaEulerNumeratorSeries (u : ℝ) : PowerSeries ℝ :=
  mk (fun n => ((2*n+2 : ℕ) : ℝ)*nativeThetaMomentTopCoefficient n*u^(2*n+2))

private theorem monomial_euler (n : ℕ) (a u : ℝ) :
    u*((Polynomial.monomial (2*n+2) a).derivative.eval u) =
      ((2*n+2 : ℕ) : ℝ)*a*u^(2*n+2) := by
  rw [show 2*n+2 = (2*n+1)+1 by omega,
    Polynomial.derivative_monomial_succ, Polynomial.eval_monomial, pow_succ]
  push_cast
  ring

theorem nativeThetaEulerSeries_eq_valve (u : ℝ) :
    nativeThetaEulerSeries u =
      projectiveValveMass (mk canonicalCompletedNativeLogDerivativeMoment) *
        (C (completedNativeRealEvenCharacteristicCoefficient 0)⁻¹ *
          nativeThetaEulerNumeratorSeries u) := by
  ext n
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [nativeThetaEulerSeries, nativeThetaEulerNumeratorSeries, coeff_mk,
    coeff_C_mul, nativeThetaEulerPolynomial, Polynomial.eval_mul, Polynomial.eval_X]
  rw [nativeThetaMomentPolynomial_eq_valve_convolution]
  simp only [Polynomial.derivative_sum, Polynomial.derivative_smul,
    Polynomial.eval_finsetSum, Polynomial.eval_smul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_assoc, mul_comm u, mul_assoc, monomial_euler]
  ring

theorem nativeThetaEulerNumeratorSeries_eq (u : ℝ) :
    nativeThetaEulerNumeratorSeries u =
      C 2 * (nativeThetaNumeratorSeries u + X*(d⁄dX ℝ (nativeThetaNumeratorSeries u))) := by
  ext n
  cases n with
  | zero => simp [nativeThetaEulerNumeratorSeries, nativeThetaNumeratorSeries, mul_assoc]
  | succ n =>
    simp only [nativeThetaEulerNumeratorSeries, nativeThetaNumeratorSeries, coeff_mk,
      coeff_C_mul, map_add, coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

/-- The spatial derivative is constrained by the SAME source's valve
curvature, at every order. This is an identity, not a positivity premise. -/
theorem nativeThetaEulerSeries_source_equation (u : ℝ) :
    nativeThetaEulerSeries u =
      C 2*(nativeThetaPolynomialSeries u+X*(d⁄dX ℝ (nativeThetaPolynomialSeries u))) -
        C 2*X*(mk canonicalCompletedNativeLogDerivativeMoment)*nativeThetaPolynomialSeries u := by
  rw [nativeThetaEulerSeries_eq_valve, nativeThetaEulerNumeratorSeries_eq,
    nativeThetaPolynomialSeries_eq_projectiveValve]
  change _ = C 2*(_+X*((projectiveValveMass (mk canonicalCompletedNativeLogDerivativeMoment)*
    (C (completedNativeRealEvenCharacteristicCoefficient 0)⁻¹ *
      nativeThetaNumeratorSeries u)).derivativeFun)) - _
  rw [derivativeFun_mul, derivativeFun_mul, derivativeFun_C]
  have hv := derivative_projectiveValveMass (mk canonicalCompletedNativeLogDerivativeMoment)
  change (projectiveValveMass (mk canonicalCompletedNativeLogDerivativeMoment)).derivativeFun = _ at hv
  rw [hv]
  rw [show d⁄dX ℝ (nativeThetaNumeratorSeries u) =
    (nativeThetaNumeratorSeries u).derivativeFun by rfl]
  ring

/-- All-order source recurrence, before any Schur projection or readout. -/
theorem nativeThetaEulerPolynomial_eq (n : ℕ) :
    nativeThetaEulerPolynomial n = ((2*n+2 : ℕ) : ℝ) • nativeThetaMomentPolynomial n -
      (2 : ℝ) • ∑ k ∈ Finset.range n, canonicalCompletedNativeLogDerivativeMoment k •
        nativeThetaMomentPolynomial (n-1-k) := by
  apply Polynomial.funext
  intro u
  have h := congrArg (coeff n) (nativeThetaEulerSeries_source_equation u)
  cases n with
  | zero =>
    simpa [nativeThetaEulerSeries, nativeThetaPolynomialSeries,
      Polynomial.eval_sub, Polynomial.eval_smul] using h
  | succ n =>
    simp only [mul_assoc] at h
    simp only [map_sub, map_add, coeff_C_mul, coeff_succ_X_mul,
      coeff_derivative, nativeThetaEulerSeries, nativeThetaPolynomialSeries, coeff_mk] at h
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    simp only [coeff_mk] at h
    simp only [Polynomial.eval_sub, Polynomial.eval_smul, Polynomial.eval_finsetSum,
      smul_eq_mul, Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    push_cast at h ⊢
    linear_combination h

/-- Its scalar integral is the exact source moment convolution. -/
theorem nativeThetaEulerPolynomial_integral (n : ℕ) :
    nativeXiPolynomialIntegral (nativeThetaEulerPolynomial n) =
      ((2*n+2 : ℕ) : ℝ)*canonicalCompletedNativeLogDerivativeMoment n -
        2*∑ k ∈ Finset.range n, canonicalCompletedNativeLogDerivativeMoment k *
          canonicalCompletedNativeLogDerivativeMoment (n-1-k) := by
  rw [nativeThetaEulerPolynomial_eq]
  simp only [map_sub, map_smul, map_sum, smul_eq_mul,
    nativeThetaMomentPolynomial_integral]

end
end CarrySelfAdjointOperator
