import CarrySelfAdjointOperator.NativeSchurEulerBalance
import CarrySelfAdjointOperator.NativeSourceAllOrderSchur

/-! Conditional assembly of the two native Hankel towers from the explicit
Euler/theta mass gates. The mass inequalities remain hypotheses. -/
namespace CarrySelfAdjointOperator

open Matrix
open scoped BigOperators

noncomputable section
set_option autoImplicit false

local notation "m" => canonicalCompletedNativeLogDerivativeMoment
local notation "c₀" => completedNativeRealEvenCharacteristicCoefficient 0

/-- If the even and odd Euler mass gates hold at every order, then the two
initial Hankel towers are positive definite at every dimension. This is
conditional on the displayed source inequalities. -/
theorem nativeSource_even_odd_towers_posDef_of_euler_mass_gates
    (hc₀ : 0 < c₀)
    (hEven : ∀ n,
      nativeThetaNegativeMass (nativeSchurEulerPolynomial 0 n) <
        nativeThetaPositiveMass (nativeSchurEulerPolynomial 0 n))
    (hOdd : ∀ n,
      nativeThetaNegativeMass (nativeSchurEulerPolynomial 1 n) <
        2*c₀*(nativeSchurCriticalReadout 1 n)^2 +
          nativeThetaPositiveMass (nativeSchurEulerPolynomial 1 n)) :
    ∀ n, (sourceMomentMatrix m 0 n).PosDef ∧ (sourceMomentMatrix m 1 n).PosDef := by
  have hbase : (sourceMomentMatrix m 0 0).PosDef ∧
      (sourceMomentMatrix m 1 0).PosDef := by
    constructor
    · apply Matrix.PosDef.of_dotProduct_mulVec_pos (sourceMomentMatrix_isHermitian m 0 0)
      intro x hx
      exact (hx (Subsingleton.elim _ _)).elim
    · apply Matrix.PosDef.of_dotProduct_mulVec_pos (sourceMomentMatrix_isHermitian m 1 0)
      intro x hx
      exact (hx (Subsingleton.elim _ _)).elim
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
      constructor
      · have hA := ih.1
        have hIntegral : 0 < nativeXiPolynomialIntegral (nativeSchurEulerPolynomial 0 n) := by
          rw [nativeXiPolynomialIntegral_eq_masses]
          linarith [hEven n]
        have hFactor : 0 < ((4*n+2 : ℕ) : ℝ) := by positivity
        have hRemainder : 0 < nativeSourceSchurRemainder 0 n := by
          apply (mul_pos_iff_of_pos_left hFactor).mp
          rw [nativeSchurEuler_even_balance n hA.isUnit]
          exact hIntegral
        have hPivot : 0 < sourceMomentSchur m 0 n := by
          rw [nativeSourceSchurRemainder_eq] at hRemainder
          exact (mul_pos_iff_of_pos_left hc₀).mp hRemainder
        exact (sourceMomentMatrix_succ_posDef_iff m 0 n hA).mpr hPivot
      · have hA := ih.2
        have hRemainder : 0 < nativeSourceSchurRemainder 1 n :=
          (nativeSchurEuler_odd_pos_iff_mass_balance n hA.isUnit).2 (hOdd n)
        have hPivot : 0 < sourceMomentSchur m 1 n := by
          rw [nativeSourceSchurRemainder_eq] at hRemainder
          exact (mul_pos_iff_of_pos_left hc₀).mp hRemainder
        exact (sourceMomentMatrix_succ_posDef_iff m 1 n hA).mpr hPivot

/-- Exact even-sector formulation of the remaining Euler mass gate, under the
same invertibility hypothesis required by the existing balance identity. -/
theorem nativeSchurEuler_even_pos_iff_mass_balance (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m 0 n)) :
    0 < nativeSourceSchurRemainder 0 n ↔
      nativeThetaNegativeMass (nativeSchurEulerPolynomial 0 n) <
        nativeThetaPositiveMass (nativeSchurEulerPolynomial 0 n) := by
  have hFactor : 0 < ((4*n+2 : ℕ) : ℝ) := by positivity
  rw [← mul_pos_iff_of_pos_left hFactor,
    nativeSchurEuler_even_balance n hA,
    nativeXiPolynomialIntegral_eq_masses, sub_pos]

end
end CarrySelfAdjointOperator
