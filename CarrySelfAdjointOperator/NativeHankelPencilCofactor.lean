import CarrySelfAdjointOperator.NativeThetaCofactorMargin

/-! The polynomial pencil of the canonical source Hankel windows and its
cofactor-direction polynomial. -/
namespace CarrySelfAdjointOperator

open scoped BigOperators Matrix
open Polynomial

noncomputable section
set_option autoImplicit false

local notation "m" => canonicalCompletedNativeLogDerivativeMoment

/-- The source Hankel pencil `X G_{s,n} - K_{s,n}` over `ℝ[X]`. -/
def nativeSourceHankelPencil (s n : ℕ) : Matrix (Fin n) (Fin n) ℝ[X] :=
  fun i j => C (m (i.val + j.val + s)) * X - C (m (i.val + j.val + s + 1))

/-- The determinant polynomial of the canonical source Hankel pencil. -/
def nativeSourceHankelPencilPolynomial (s n : ℕ) : ℝ[X] :=
  (nativeSourceHankelPencil s n).det

/-- The polynomial whose coefficients are the coordinates of the
source-defined cofactor vector. -/
def nativeSourceCofactorPolynomial (s n : ℕ) : ℝ[X] :=
  ∑ j : Fin (n + 1), C (nativeSourceCofactorVector s n j) * X ^ (j : ℕ)

theorem nativeSourceHankelPencilPolynomial_zero (s : ℕ) :
    nativeSourceHankelPencilPolynomial s 0 = nativeSourceCofactorPolynomial s 0 := by
  simp [nativeSourceHankelPencilPolynomial,
    nativeSourceCofactorPolynomial, nativeSourceCofactorVector,
    nativeSourcePrefixDet]

end
end CarrySelfAdjointOperator
