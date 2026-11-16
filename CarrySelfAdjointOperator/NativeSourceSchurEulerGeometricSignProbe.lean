import CarrySelfAdjointOperator.NativeSchurEulerBalance
import CarrySelfAdjointOperator.NativeSourceThetaGreenTransport

/-! Exact Green-space form of the critical Euler balances.

This exposes the signed term left after the source orthogonality and the
central Green traces cancel. It makes no assertion about the sign of either
integral or either Schur remainder. -/
namespace CarrySelfAdjointOperator

open Polynomial MeasureTheory Set
open XiThetaCosine
open scoped BigOperators
noncomputable section
set_option autoImplicit false

private theorem nativeSchurEulerPolynomial_center_traces (s n : ℕ) :
    (nativeSchurEulerPolynomial s n).eval 0 = 0 ∧
      (nativeSchurEulerPolynomial s n).derivative.eval 0 = 0 := by
  obtain ⟨hP0, hP1⟩ := nativeSchurThetaPolynomial_center_traces s n
  constructor
  · simp [nativeSchurEulerPolynomial]
  · rw [show nativeSchurEulerPolynomial s n =
      Polynomial.X * (nativeSchurThetaPolynomial s n).derivative by rfl,
    Polynomial.derivative_mul]
    simp only [Polynomial.derivative_X, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, zero_mul, one_mul, add_zero]
    exact hP1

/-- In the even sector, the existing critical direction is orthogonal to the
zeroth old-prefix row itself. Thus its unshifted readout vanishes for every
nonempty invertible prefix; there is no hidden even-sector square term. -/
theorem nativeSchurCriticalReadout_even_eq_zero (n : ℕ) (hn : 0 < n)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 n)) :
    nativeSchurCriticalReadout 0 n = 0 := by
  have h := nativeSchurCriticalCoefficients_orthogonal 0 n hA 0 hn
  simpa [nativeSchurCriticalReadout] using h

/-- Applying the exact Green transport to the Euler derivative introduces no
boundary term: the source polynomial has no constant or linear coefficient. -/
theorem nativeSchurEulerPolynomial_green_integral (s n : ℕ) :
    nativeXiPolynomialIntegral (nativeSchurEulerPolynomial s n) =
      ∫ u in Ioi (0 : ℝ),
        (nativeThetaGreenPolynomial (nativeSchurEulerPolynomial s n)).eval u * thetaTail u := by
  have h := nativeXiPolynomialIntegral_eq_thetaGreen_integral
    (nativeSchurEulerPolynomial s n)
  obtain ⟨h0, h1⟩ := nativeSchurEulerPolynomial_center_traces s n
  rw [h0, h1] at h
  simpa using h

/-- Odd-sector Euler balance after both exact Green transports. The remaining
term is the integral of the Euler-transformed source polynomial; its sign is
left open. -/
theorem nativeSchurEuler_odd_green_balance (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n)) :
    ((4*n+4 : ℕ) : ℝ) *
        (∫ u in Ioi (0 : ℝ),
          (nativeThetaGreenPolynomial (nativeSchurThetaPolynomial 1 n)).eval u * thetaTail u) =
      2 * completedNativeRealEvenCharacteristicCoefficient 0 *
          (nativeSchurCriticalReadout 1 n)^2 +
        ∫ u in Ioi (0 : ℝ),
          (nativeThetaGreenPolynomial (nativeSchurEulerPolynomial 1 n)).eval u * thetaTail u := by
  rw [← nativeSourceSchurRemainder_eq_thetaGreen_integral 1 n,
    nativeSchurEuler_odd_balance n hA,
    nativeSchurEulerPolynomial_green_integral]
  ring

/-- Even-sector balance after exact Green transport. Unlike the odd identity,
there is no residual square term. -/
theorem nativeSchurEuler_even_green_balance (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 n)) :
    ((4*n+2 : ℕ) : ℝ) *
        (∫ u in Ioi (0 : ℝ),
          (nativeThetaGreenPolynomial (nativeSchurThetaPolynomial 0 n)).eval u * thetaTail u) =
      ∫ u in Ioi (0 : ℝ),
        (nativeThetaGreenPolynomial (nativeSchurEulerPolynomial 0 n)).eval u * thetaTail u := by
  rw [← nativeSourceSchurRemainder_eq_thetaGreen_integral 0 n,
    nativeSchurEuler_even_balance n hA,
    nativeSchurEulerPolynomial_green_integral]

end
end CarrySelfAdjointOperator
