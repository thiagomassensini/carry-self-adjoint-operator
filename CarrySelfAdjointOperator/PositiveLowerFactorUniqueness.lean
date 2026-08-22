import CarrySelfAdjointOperator.PositiveLowerWhiteningUniqueness
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Uniqueness of a positive lower triangular square root

For a lower triangular matrix with strictly positive diagonal, the Gram
matrix `Bᵀ B` determines `B` uniquely.  The proof peels the last coordinate:
the bottom-right entry fixes the positive diagonal, the last column fixes the
old part of the last row, and the remaining principal block is handled
inductively.

This is the finite algebraic uniqueness statement needed by the inverse
Cholesky/LDL route.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- Lower triangular matrix with strictly positive diagonal. -/
def IsPositiveLowerFactor
    {N : ℕ} (factor : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ ⦃i j : Fin N⦄, i < j → factor i j = 0) ∧
    (∀ i : Fin N, 0 < factor i i)

/-- A positive lower triangular factor is uniquely determined by `Bᵀ B`. -/
theorem positiveLowerFactor_unique_of_transpose_mul_self_eq
    {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℝ}
    (hA : IsPositiveLowerFactor A)
    (hB : IsPositiveLowerFactor B)
    (hprod : A.transpose * A = B.transpose * B) :
    A = B := by
  induction N generalizing A B with
  | zero =>
      apply Matrix.ext
      intro i
      exact Fin.elim0 i
  | succ N ih =>
      let A₀ : Matrix (Fin N) (Fin N) ℝ :=
        A.submatrix Fin.castSucc Fin.castSucc
      let B₀ : Matrix (Fin N) (Fin N) ℝ :=
        B.submatrix Fin.castSucc Fin.castSucc
      have hAcolLast : ∀ k : Fin N,
          A (Fin.castSucc k) (Fin.last N) = 0 := by
        intro k
        exact hA.1 (Fin.castSucc_lt_last k)
      have hBcolLast : ∀ k : Fin N,
          B (Fin.castSucc k) (Fin.last N) = 0 := by
        intro k
        exact hB.1 (Fin.castSucc_lt_last k)
      have hdiagSq :
          A (Fin.last N) (Fin.last N) *
              A (Fin.last N) (Fin.last N) =
            B (Fin.last N) (Fin.last N) *
              B (Fin.last N) (Fin.last N) := by
        have h := congrArg
          (fun M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ =>
            M (Fin.last N) (Fin.last N)) hprod
        simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at h
        simpa [hAcolLast, hBcolLast] using h
      have hdiag :
          A (Fin.last N) (Fin.last N) =
            B (Fin.last N) (Fin.last N) := by
        nlinarith [hA.2 (Fin.last N), hB.2 (Fin.last N), hdiagSq]
      have hlastRow : ∀ j : Fin N,
          A (Fin.last N) (Fin.castSucc j) =
            B (Fin.last N) (Fin.castSucc j) := by
        intro j
        have h := congrArg
          (fun M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ =>
            M (Fin.castSucc j) (Fin.last N)) hprod
        simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at h
        have hmul :
            A (Fin.last N) (Fin.castSucc j) *
                A (Fin.last N) (Fin.last N) =
              B (Fin.last N) (Fin.castSucc j) *
                B (Fin.last N) (Fin.last N) := by
          simpa [hAcolLast, hBcolLast] using h
        rw [hdiag] at hmul
        nlinarith [hB.2 (Fin.last N)]
      have hprod₀ : A₀.transpose * A₀ = B₀.transpose * B₀ := by
        ext i j
        have h := congrArg
          (fun M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ =>
            M (Fin.castSucc i) (Fin.castSucc j)) hprod
        simp only [Matrix.mul_apply, Matrix.transpose_apply] at h ⊢
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at h
        rw [hlastRow i, hlastRow j] at h
        change
          (∑ x : Fin N,
              A (Fin.castSucc x) (Fin.castSucc i) *
                A (Fin.castSucc x) (Fin.castSucc j)) =
            ∑ x : Fin N,
              B (Fin.castSucc x) (Fin.castSucc i) *
                B (Fin.castSucc x) (Fin.castSucc j)
        exact add_right_cancel h
      have hA₀ : IsPositiveLowerFactor A₀ := by
        constructor
        · intro i j hij
          exact hA.1 (by simpa using hij)
        · intro i
          exact hA.2 (Fin.castSucc i)
      have hB₀ : IsPositiveLowerFactor B₀ := by
        constructor
        · intro i j hij
          exact hB.1 (by simpa using hij)
        · intro i
          exact hB.2 (Fin.castSucc i)
      have hprincipal : A₀ = B₀ :=
        ih hA₀ hB₀ hprod₀
      apply Matrix.ext
      intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · exact hdiag
        · exact hlastRow j
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · rw [hA.1 (Fin.castSucc_lt_last i),
            hB.1 (Fin.castSucc_lt_last i)]
        · have h := congrArg
            (fun M : Matrix (Fin N) (Fin N) ℝ => M i j) hprincipal
          simpa [A₀, B₀] using h

end

end CarrySelfAdjointOperator
