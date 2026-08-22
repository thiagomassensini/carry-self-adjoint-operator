import CarrySelfAdjointOperator.CanonicalLDLWhitening
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Exact prefix compatibility of the canonical LDL lower inverse

This module formalizes the rowwise rigidity argument behind the exact
projective Jacobi tower.

For a positive Hankel Gram matrix, every row of `LDL.lowerInv` is
characterized by three pieces of data:

* a unit pivot;
* strict lower triangular support;
* orthogonality to every earlier Gram column.

Positive definiteness makes that row unique.  Since an old row of the
order-`N+1` factor satisfies the same finite system as the corresponding
order-`N` row, the old principal block is forced to agree exactly.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- Mathlib's Gram--Schmidt realization of `LDL.lowerInv` has unit pivot. -/
theorem ldlLowerInv_diagonal_eq_one
    {N : ℕ} {gram : Matrix (Fin N) (Fin N) ℝ}
    (hgram : gram.PosDef) (i : Fin N) :
    LDL.lowerInv hgram i i = 1 := by
  letI := gram.transpose.toNormedAddCommGroup hgram.transpose
  letI := gram.transpose.toInnerProductSpace hgram.transpose.posSemidef
  have hdef :=
    InnerProductSpace.gramSchmidt_def'' ℝ
      (Pi.basisFun ℝ (Fin N)) i
  have hzero : ∀ k : Fin N, k < i →
      (InnerProductSpace.gramSchmidt ℝ
        (Pi.basisFun ℝ (Fin N)) k) i = 0 := by
    intro k hki
    simpa [LDL.lowerInv] using
      (LDL.lowerInv_triangular hgram hki)
  have hcoord := congrArg (fun v : Fin N → ℝ => v i) hdef
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcoord
  have hsumzero (c : Fin N → ℝ) :
      (∑ k ∈ Finset.Iio i,
        c k *
          (InnerProductSpace.gramSchmidt ℝ
            (Pi.basisFun ℝ (Fin N)) k) i) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hki : k < i := Finset.mem_Iio.mp hk
    rw [hzero k hki, mul_zero]
  rw [hsumzero, add_zero] at hcoord
  have hbasis : (Pi.basisFun ℝ (Fin N) i) i = 1 := by simp
  rw [hbasis] at hcoord
  simpa [LDL.lowerInv] using hcoord.symm

/-- Earlier Gram columns are annihilated by each row of `LDL.lowerInv`. -/
theorem ldlLowerInv_mul_eq_zero_of_lt
    {N : ℕ} {gram : Matrix (Fin N) (Fin N) ℝ}
    (hgram : gram.PosDef) {i j : Fin N} (hji : j < i) :
    (LDL.lowerInv hgram * gram) i j = 0 := by
  letI := gram.transpose.toNormedAddCommGroup hgram.transpose
  letI := gram.transpose.toInnerProductSpace hgram.transpose.posSemidef
  have horth :=
    InnerProductSpace.gramSchmidt_inv_triangular ℝ
      (Pi.basisFun ℝ (Fin N)) hji
  change
    dotProduct
      (Matrix.mulVec gram.transpose (Pi.single j 1))
      (star (LDL.lowerInv hgram i)) = 0 at horth
  rw [Matrix.mulVec_single_one] at horth
  have hsymm : ∀ a b : Fin N, gram a b = gram b a := by
    intro a b
    simpa using hgram.isHermitian.apply b a
  simpa [Matrix.mul_apply, dotProduct, hsymm, mul_comm] using horth

/-- Intrinsic row certificate used by the prefix argument. -/
def IsUnitLowerOrthogonalRow
    {N : ℕ} (gram : Matrix (Fin N) (Fin N) ℝ)
    (pivot : Fin N) (row : Fin N → ℝ) : Prop :=
  row pivot = 1 ∧
    (∀ ⦃k : Fin N⦄, pivot < k → row k = 0) ∧
      (∀ ⦃j : Fin N⦄, j < pivot →
        ∑ k : Fin N, row k * gram k j = 0)

/-- Positivity makes a unit lower Gram-orthogonal row unique. -/
theorem unitLowerOrthogonalRow_unique
    {N : ℕ} {gram : Matrix (Fin N) (Fin N) ℝ}
    (hgram : gram.PosDef) {pivot : Fin N} {x y : Fin N → ℝ}
    (hx : IsUnitLowerOrthogonalRow gram pivot x)
    (hy : IsUnitLowerOrthogonalRow gram pivot y) :
    x = y := by
  classical
  let d : Fin N → ℝ := x - y
  have hd_ge : ∀ k : Fin N, pivot ≤ k → d k = 0 := by
    intro k hpk
    by_cases hki : k = pivot
    · subst k
      simp [d, hx.1, hy.1]
    · have hpk' : pivot < k :=
        lt_of_le_of_ne hpk (Ne.symm hki)
      simp [d, hx.2.1 hpk', hy.2.1 hpk']
  have hd_orth : ∀ j : Fin N, j < pivot →
      ∑ k : Fin N, d k * gram k j = 0 := by
    intro j hj
    simp only [d, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [hx.2.2 hj, hy.2.2 hj, sub_self]
  have hsymm : ∀ a b : Fin N, gram a b = gram b a := by
    intro a b
    simpa using hgram.isHermitian.apply b a
  have hmul : ∀ j : Fin N, j < pivot →
      Matrix.mulVec gram d j = 0 := by
    intro j hj
    simpa [Matrix.mulVec, dotProduct, hsymm, mul_comm] using
      hd_orth j hj
  have hquad : dotProduct d (Matrix.mulVec gram d) = 0 := by
    rw [dotProduct]
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hjp : j < pivot
    · rw [hmul j hjp, mul_zero]
    · have hpj : pivot ≤ j := le_of_not_gt hjp
      rw [hd_ge j hpj, zero_mul]
  have hd_zero : d = 0 := by
    by_contra hd_ne
    have hpos := hgram.dotProduct_mulVec_pos hd_ne
    have : 0 < dotProduct d (Matrix.mulVec gram d) := by
      simpa using hpos
    linarith
  apply funext
  intro k
  have hk := congrFun hd_zero k
  simpa [d, sub_eq_zero] using hk

/-- Every row of `LDL.lowerInv` satisfies the intrinsic row certificate. -/
theorem ldlLowerInv_isUnitLowerOrthogonalRow
    {N : ℕ} {gram : Matrix (Fin N) (Fin N) ℝ}
    (hgram : gram.PosDef) (i : Fin N) :
    IsUnitLowerOrthogonalRow gram i (LDL.lowerInv hgram i) := by
  refine ⟨ldlLowerInv_diagonal_eq_one hgram i, ?_, ?_⟩
  · intro k hik
    exact LDL.lowerInv_triangular hgram hik
  · intro j hji
    simpa [Matrix.mul_apply] using
      (ldlLowerInv_mul_eq_zero_of_lt hgram hji)

/-- The old principal block of the next Hankel `LDL.lowerInv` is exactly the
old factor. -/
theorem ldlLowerInv_hankel_succ_principal
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef)
    (N : ℕ) :
    (LDL.lowerInv (hgram (N + 1))).submatrix
        Fin.castSucc Fin.castSucc =
      LDL.lowerInv (hgram N) := by
  ext i j
  let largeRow : Fin N → ℝ := fun k =>
    LDL.lowerInv (hgram (N + 1))
      (Fin.castSucc i) (Fin.castSucc k)
  let smallRow : Fin N → ℝ := LDL.lowerInv (hgram N) i
  have hlarge :
      IsUnitLowerOrthogonalRow (hankelGram moments N) i largeRow := by
    refine ⟨?_, ?_, ?_⟩
    · exact ldlLowerInv_diagonal_eq_one
        (hgram (N + 1)) (Fin.castSucc i)
    · intro k hik
      exact LDL.lowerInv_triangular
        (hgram (N + 1)) (by simpa using hik)
    · intro k hki
      have hzero :=
        ldlLowerInv_mul_eq_zero_of_lt
          (hgram (N + 1))
          (i := Fin.castSucc i) (j := Fin.castSucc k)
          (by simpa using hki)
      simp only [Matrix.mul_apply] at hzero
      rw [Fin.sum_univ_castSucc] at hzero
      have hlast :
          LDL.lowerInv (hgram (N + 1))
              (Fin.castSucc i) (Fin.last N) = 0 :=
        LDL.lowerInv_triangular
          (hgram (N + 1)) (Fin.castSucc_lt_last i)
      simpa [largeRow, hankelGram, hlast] using hzero
  have hsmall :
      IsUnitLowerOrthogonalRow (hankelGram moments N) i smallRow := by
    simpa [smallRow] using
      ldlLowerInv_isUnitLowerOrthogonalRow (hgram N) i
  have hrows : largeRow = smallRow :=
    unitLowerOrthogonalRow_unique (hgram N) hlarge hsmall
  have hentry := congrFun hrows j
  simpa [largeRow, smallRow, Matrix.submatrix_apply] using hentry

/-- Prefix compatibility of `LDL.lowerInv` throughout the Hankel tower. -/
theorem ldlLowerInvPrincipalCompatible
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef) :
    ∀ N : ℕ,
      (LDL.lowerInv (hgram (N + 1))).submatrix
          Fin.castSucc Fin.castSucc =
        LDL.lowerInv (hgram N) :=
  ldlLowerInv_hankel_succ_principal moments hgram

end

end CarrySelfAdjointOperator
