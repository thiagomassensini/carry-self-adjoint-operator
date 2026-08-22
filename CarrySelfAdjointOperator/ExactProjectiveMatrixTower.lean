import CarrySelfAdjointOperator.ProjectiveJacobiTower
import Mathlib.Tactic

/-!
# Exact projective matrix towers and their cylindrical limit

A family of finite matrices whose order-`N` member is the leading principal
section of order `N + 1` already determines one infinite matrix entry by
entry.  No analytic limit is required for this algebraic construction.

This module packages that statement independently of positivity,
tridiagonality, or a choice of self-adjoint realization.  Those are later
operator-theoretic obligations.  The result here is the exact cylindrical
consistency used by the Jacobi-order route.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- Exact leading-principal compatibility between consecutive finite
sections. -/
def IsExactPrincipalTower
    (matrix : (N : ℕ) → Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ N : ℕ,
    (matrix (N + 1)).submatrix Fin.castSucc Fin.castSucc = matrix N

namespace IsExactPrincipalTower

/-- Consecutive compatibility propagates to every pair of orders `N ≤ M`. -/
theorem submatrix_of_le
    {matrix : (N : ℕ) → Matrix (Fin N) (Fin N) ℝ}
    (htower : IsExactPrincipalTower matrix)
    {N M : ℕ} (hNM : N ≤ M) :
    (matrix M).submatrix (Fin.castLE hNM) (Fin.castLE hNM) = matrix N := by
  induction hNM with
  | refl =>
      ext i j
      rfl
  | @step M hNM ih =>
      ext i j
      have hstep := congrArg
        (fun B : Matrix (Fin M) (Fin M) ℝ =>
          B (Fin.castLE hNM i) (Fin.castLE hNM j))
        (htower M)
      have hprev := congrArg
        (fun B : Matrix (Fin N) (Fin N) ℝ => B i j) ih
      calc
        matrix (M + 1) (Fin.castLE (Nat.le.step hNM) i)
            (Fin.castLE (Nat.le.step hNM) j) =
          matrix M (Fin.castLE hNM i) (Fin.castLE hNM j) := by
            simpa [Matrix.submatrix_apply] using hstep
        _ = matrix N i j := by
            simpa [Matrix.submatrix_apply] using hprev

end IsExactPrincipalTower

/-- Infinite matrix selected by any exact principal tower.  The entry `(i,j)`
is read at the first order containing both coordinates. -/
def exactPrincipalTowerLimit
    (matrix : (N : ℕ) → Matrix (Fin N) (Fin N) ℝ) :
    Matrix ℕ ℕ ℝ :=
  fun i j =>
    matrix (max i j + 1)
      ⟨i, by omega⟩
      ⟨j, by omega⟩

/-- Every finite member of an exact tower is literally the corresponding
leading principal section of its infinite entrywise limit. -/
theorem exactPrincipalTowerLimit_submatrix
    {matrix : (N : ℕ) → Matrix (Fin N) (Fin N) ℝ}
    (htower : IsExactPrincipalTower matrix)
    (N : ℕ) :
    (exactPrincipalTowerLimit matrix).submatrix
        (fun i : Fin N => (i : ℕ))
        (fun i : Fin N => (i : ℕ)) =
      matrix N := by
  ext i j
  let M : ℕ := max (i : ℕ) (j : ℕ) + 1
  have hiM : (i : ℕ) < M := by
    dsimp [M]
    omega
  have hjM : (j : ℕ) < M := by
    dsimp [M]
    omega
  have hMN : M ≤ N := by
    dsimp [M]
    omega
  have hsub := congrArg
    (fun B : Matrix (Fin M) (Fin M) ℝ =>
      B ⟨(i : ℕ), hiM⟩ ⟨(j : ℕ), hjM⟩)
    (htower.submatrix_of_le hMN)
  simpa [exactPrincipalTowerLimit, Matrix.submatrix_apply, M] using hsub.symm

/-- An exact projective tower of finite Jacobi matrices.  Positivity and
tridiagonality are deliberately separate fields: projectivity alone already
constructs the infinite coefficient matrix. -/
structure ExactProjectiveJacobiTower where
  matrix : (N : ℕ) → Matrix (Fin N) (Fin N) ℝ
  projective : IsExactPrincipalTower matrix
  symmetric : ∀ N : ℕ, (matrix N).IsSymm
  positive : ∀ N : ℕ, (matrix N).PosSemidef

namespace ExactProjectiveJacobiTower

/-- Infinite coefficient matrix underlying the tower. -/
def limitMatrix (tower : ExactProjectiveJacobiTower) : Matrix ℕ ℕ ℝ :=
  exactPrincipalTowerLimit tower.matrix

/-- The order-`N` section is recovered exactly from the infinite coefficient
matrix. -/
theorem limitMatrix_submatrix
    (tower : ExactProjectiveJacobiTower) (N : ℕ) :
    tower.limitMatrix.submatrix
        (fun i : Fin N => (i : ℕ))
        (fun i : Fin N => (i : ℕ)) =
      tower.matrix N :=
  exactPrincipalTowerLimit_submatrix tower.projective N

/-- Finite bilinear data computed in the limit matrix agree exactly with the
order-`N` matrix.  This is cylindrical consistency without a numerical
limit. -/
theorem dotProduct_limitSection_mulVec
    (tower : ExactProjectiveJacobiTower)
    (N : ℕ) (x y : Fin N → ℝ) :
    Matrix.dotProduct x
        ((tower.limitMatrix.submatrix
          (fun i : Fin N => (i : ℕ))
          (fun i : Fin N => (i : ℕ))) *ᵥ y) =
      Matrix.dotProduct x (tower.matrix N *ᵥ y) := by
  rw [tower.limitMatrix_submatrix N]

end ExactProjectiveJacobiTower

/-- Exact projectivity predicate for a chosen family of finite Gram
whitenings.  The current canonical LDL construction supplies each order; the
remaining Cholesky/LDL compatibility theorem must inhabit this predicate. -/
def IsExactJacobiWhiteningTower
    (moments : ℕ → ℝ)
    (whitening : (N : ℕ) → FiniteGramWhitening moments N) : Prop :=
  IsExactPrincipalTower
    (fun N => finiteJacobiSection moments N (whitening N))

/-- Once compatible whitenings are constructed, the finite Jacobi sections
canonically determine one infinite coefficient matrix. -/
def jacobiTowerLimitMatrix
    (moments : ℕ → ℝ)
    (whitening : (N : ℕ) → FiniteGramWhitening moments N) :
    Matrix ℕ ℕ ℝ :=
  exactPrincipalTowerLimit
    (fun N => finiteJacobiSection moments N (whitening N))

/-- The exact finite-section law obtained from a compatible whitening tower. -/
theorem jacobiTowerLimitMatrix_submatrix
    (moments : ℕ → ℝ)
    (whitening : (N : ℕ) → FiniteGramWhitening moments N)
    (hprojective : IsExactJacobiWhiteningTower moments whitening)
    (N : ℕ) :
    (jacobiTowerLimitMatrix moments whitening).submatrix
        (fun i : Fin N => (i : ℕ))
        (fun i : Fin N => (i : ℕ)) =
      finiteJacobiSection moments N (whitening N) :=
  exactPrincipalTowerLimit_submatrix hprojective N

end

end CarrySelfAdjointOperator
