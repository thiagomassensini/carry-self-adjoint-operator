import CarrySelfAdjointOperator.NativeSchurEulerBalance

/-! Calibration of the Euler balance on the original first odd source.
The associated external Arb test concerns this exact polynomial. -/
namespace CarrySelfAdjointOperator
open Polynomial Matrix
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

local notation "m" => canonicalCompletedNativeLogDerivativeMoment
local notation "c₀" => completedNativeRealEvenCharacteristicCoefficient 0

theorem nativeSchurTheta_first_odd_moment_polynomial :
    nativeSchurThetaPolynomial 1 0 = (m 0/2) • X^2 - (1/12 : ℝ) • X^4 := by
  apply Polynomial.funext
  intro u
  rw [nativeSchurThetaPolynomial_zero,nativeThetaMomentPolynomial_eq 1]
  norm_num [nativeThetaMomentTopCoefficient,Finset.sum_range_succ,
    Polynomial.eval_smul,Polynomial.eval_sub,Polynomial.eval_monomial]
  rw [nativeThetaMomentPolynomial_eq 0]
  norm_num [nativeThetaMomentTopCoefficient,Polynomial.eval_smul,Polynomial.eval_monomial]
  have h0 := canonicalCompletedNativeLogDerivativeMoment_real_recurrence 0
  norm_num at h0
  field_simp [completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero]
  rw [show completedNativeRealEvenCharacteristicCoefficient 1 = -c₀*m 0 by linarith]
  ring

theorem nativeSchurEuler_first_odd_eval (u : ℝ) :
    (nativeSchurEulerPolynomial 1 0).eval u = m 0*u^2-u^4/3 := by
  rw [nativeSchurEulerPolynomial,nativeSchurTheta_first_odd_moment_polynomial]
  norm_num [Polynomial.derivative_sub,Polynomial.derivative_smul,
    Polynomial.derivative_pow,Polynomial.eval_mul,Polynomial.eval_sub,
    Polynomial.eval_smul,Polynomial.eval_X,Polynomial.eval_pow]
  ring

theorem nativeSchurEuler_first_odd_integral :
    nativeXiPolynomialIntegral (nativeSchurEulerPolynomial 1 0) =
      4*(c₀*m 1)-2*c₀*(m 0)^2 := by
  have hA : (sourceMomentMatrix m 1 0).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (sourceMomentMatrix_isHermitian m 1 0)
    intro x hx
    exact (hx (Subsingleton.elim _ _)).elim
  have h := nativeSchurEuler_odd_balance 0 hA.isUnit
  simp only [nativeSchurCriticalReadout,nativeSchurCriticalCoefficients,
    nativeSourceSchurRemainder_eq,sourceMomentSchur] at h
  norm_num [dotProduct,Fin.sum_univ_one,Fin.snoc] at h
  linarith

end
end CarrySelfAdjointOperator
