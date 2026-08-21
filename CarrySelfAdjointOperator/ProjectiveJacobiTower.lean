import CarrySelfAdjointOperator.FiniteJacobiTransport
import Mathlib.Data.Matrix.Block

/-!
# Exact projective law for the Jacobi tower

The native Hankel pair already restricts exactly from order `N + 1` to order
`N`.  The remaining finite-dimensional issue is the whitening factor.  For
Cholesky whitening, the inverse factor extends in lower block-triangular form.
This file isolates and proves the complete algebraic consequence of that
fact: no entry in the new row/column can feed back into the old Jacobi block.

Thus the projective law is not a convergence estimate.  It is an exact block
identity.  The separate analytic/construction obligation is to build a
whitening tower satisfying the lower-block extension property.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- A larger square matrix extends a smaller one in lower block-triangular
form.  This is the exact shape of a compatible inverse Cholesky factor. -/
def IsLowerBlockExtension
    {ι κ : Type*}
    (small : Matrix ι ι ℝ)
    (large : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Prop :=
  ∃ (lowerLeft : Matrix κ ι ℝ) (lowerRight : Matrix κ κ ℝ),
    large = Matrix.fromBlocks small 0 lowerLeft lowerRight

/-- A larger square matrix has `small` as its upper-left principal block. -/
def IsPrincipalBlockExtension
    {ι κ : Type*}
    (small : Matrix ι ι ℝ)
    (large : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Prop :=
  ∃ (upperRight : Matrix ι κ ℝ) (lowerLeft : Matrix κ ι ℝ)
      (lowerRight : Matrix κ κ ℝ),
    large = Matrix.fromBlocks small upperRight lowerLeft lowerRight

/-- The upper-left block of a Jacobi congruence is unchanged by adjoining new
coordinates whenever the congruence factor is lower block triangular. -/
theorem jacobiCongruence_toBlocks₁₁_of_lowerBlockExtension
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {smallFactor : Matrix ι ι ℝ}
    {largeFactor : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ}
    {smallShifted : Matrix ι ι ℝ}
    {largeShifted : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ}
    (hfactor : IsLowerBlockExtension smallFactor largeFactor)
    (hshifted : IsPrincipalBlockExtension smallShifted largeShifted) :
    (jacobiCongruence largeFactor largeShifted).toBlocks₁₁ =
      jacobiCongruence smallFactor smallShifted := by
  rcases hfactor with ⟨lowerLeftFactor, lowerRightFactor, rfl⟩
  rcases hshifted with
    ⟨upperRightShifted, lowerLeftShifted, lowerRightShifted, rfl⟩
  simp [jacobiCongruence, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply]

/-- Explicit block form of the same projective law.  This is useful when a
concrete recursive Cholesky construction exposes its new row directly. -/
theorem jacobiCongruence_fromBlocks_toBlocks₁₁
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (smallFactor smallShifted : Matrix ι ι ℝ)
    (lowerLeftFactor : Matrix κ ι ℝ)
    (lowerRightFactor : Matrix κ κ ℝ)
    (upperRightShifted : Matrix ι κ ℝ)
    (lowerLeftShifted : Matrix κ ι ℝ)
    (lowerRightShifted : Matrix κ κ ℝ) :
    (jacobiCongruence
        (Matrix.fromBlocks smallFactor 0 lowerLeftFactor lowerRightFactor)
        (Matrix.fromBlocks smallShifted upperRightShifted
          lowerLeftShifted lowerRightShifted)).toBlocks₁₁ =
      jacobiCongruence smallFactor smallShifted := by
  exact jacobiCongruence_toBlocks₁₁_of_lowerBlockExtension
    ⟨lowerLeftFactor, lowerRightFactor, rfl⟩
    ⟨upperRightShifted, lowerLeftShifted, lowerRightShifted, rfl⟩

end

end CarrySelfAdjointOperator
