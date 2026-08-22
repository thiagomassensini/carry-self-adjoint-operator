import CarrySelfAdjointOperator.PositiveLowerFactorUniqueness
import Mathlib.LinearAlgebra.Matrix.Invertible
import Mathlib.Tactic

/-!
# Rigidity of positive lower triangular whitenings

An exact whitening `B G Bᵀ = I` with `G > 0` determines

`Bᵀ B = G⁻¹`.

Therefore two lower-triangular whitenings with positive diagonal have the
same transpose Gram matrix and are equal by positive lower-factor uniqueness.
This is the formal uniqueness principle used in the Cholesky argument from
the projective-tower note.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- Every exact whitening of a positive definite matrix has transpose Gram
matrix equal to the inverse of the whitened matrix. -/
theorem transpose_mul_self_eq_invOf_of_whitening
    {N : ℕ} {gram factor : Matrix (Fin N) (Fin N) ℝ}
    (hgram : gram.PosDef)
    (hwhite : finiteJacobiTransport factor gram = 1) :
    factor.transpose * factor = ⅟gram := by
  have hfactorInjective : Function.Injective factor.vecMul :=
    inverseFactor_vecMul_injective_of_whitening hwhite
  have hfactorUnit : IsUnit factor :=
    Matrix.vecMul_injective_iff_isUnit.mp hfactorInjective
  letI : Invertible factor := hfactorUnit.invertible
  letI : Invertible factor.transpose :=
    Matrix.invertibleTranspose factor
  letI : Invertible gram := hgram.isUnit.invertible
  apply Matrix.mul_left_injective_of_invertible gram
  calc
    (factor.transpose * factor) * gram =
        factor.transpose * (factor * gram) := by
      rw [Matrix.mul_assoc]
    _ = factor.transpose * ⅟(factor.transpose) := by
      congr 1
      apply Matrix.mul_left_injective_of_invertible factor.transpose
      calc
        (factor * gram) * factor.transpose = 1 := by
          simpa [finiteJacobiTransport] using hwhite
        _ = ⅟(factor.transpose) * factor.transpose := by
          rw [invOf_mul_self]
    _ = 1 := by rw [mul_invOf_self]
    _ = ⅟gram * gram := by rw [invOf_mul_self]

/-- A positive lower triangular whitening of a positive definite Gram matrix
is unique. -/
theorem positiveLowerWhitening_unique
    {N : ℕ} {gram A B : Matrix (Fin N) (Fin N) ℝ}
    (hgram : gram.PosDef)
    (hA : IsPositiveLowerWhitening gram A)
    (hB : IsPositiveLowerWhitening gram B) :
    A = B := by
  apply positiveLowerFactor_unique_of_transpose_mul_self_eq
    ⟨hA.1, hA.2.1⟩ ⟨hB.1, hB.2.1⟩
  rw [transpose_mul_self_eq_invOf_of_whitening hgram hA.2.2,
    transpose_mul_self_eq_invOf_of_whitening hgram hB.2.2]

end

end CarrySelfAdjointOperator
