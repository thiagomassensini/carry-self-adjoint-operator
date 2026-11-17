import CarrySelfAdjointOperator.NativeHankelPencilCofactor
import CarrySelfAdjointOperator.NativeThetaCofactorSignGate

/-! Bridge the exact bordered theta integral to consecutive source Hankel
determinants. The sign consequence remains conditional. -/
namespace CarrySelfAdjointOperator

noncomputable section
set_option autoImplicit false

local notation "m" => canonicalCompletedNativeLogDerivativeMoment
local notation "c₀" => completedNativeRealEvenCharacteristicCoefficient 0

/-- The integrated cofactor theta polynomial is the product of two consecutive
prefix determinants, with the original completed-source scalar `c₀`. -/
theorem nativeSourceCofactorThetaPolynomial_integral_eq_prefixDet_mul_succ
    (s n : ℕ) :
    nativeXiPolynomialIntegral (nativeSourceCofactorThetaPolynomial s n) =
      c₀ * nativeSourcePrefixDet s n * nativeSourcePrefixDet s (n + 1) := by
  rw [nativeSourceCofactorThetaPolynomial_integral_bordered,
    nativeSourcePrefixDet_succ_eq_borderedScalar]

/-- Conditional sign transfer from the theta integral to the next determinant.
This does not establish positivity of the integral. -/
theorem nativeSourceCofactorThetaPolynomial_integral_pos_iff_nextPrefixDet_pos
    (s n : ℕ) (hc₀ : 0 < c₀) (hτ : 0 < nativeSourcePrefixDet s n) :
    0 < nativeXiPolynomialIntegral (nativeSourceCofactorThetaPolynomial s n) ↔
      0 < nativeSourcePrefixDet s (n + 1) := by
  rw [nativeSourceCofactorThetaPolynomial_integral_eq_prefixDet_mul_succ]
  exact mul_pos_iff_of_pos_left (mul_pos hc₀ hτ)

end
end CarrySelfAdjointOperator
