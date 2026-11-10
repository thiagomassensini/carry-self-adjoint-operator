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

/-- Augment `G` by `b` and a zero last row. -/
def lastRowZeroExtension {R : Type*} [Zero R] {n : ℕ}
    (G : Matrix (Fin n) (Fin n) R) (b : Fin n → R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i j => Fin.lastCases 0 (fun i => Fin.lastCases (b i) (fun j => G i j) j) i

/-- The last adjugate column of the zero-row extension is the standard
cofactor direction, without any invertibility assumption. -/
theorem lastRowZeroExtension_adjugate_lastColumn {R : Type*} [CommRing R]
    {n : ℕ} (G : Matrix (Fin n) (Fin n) R) (b : Fin n → R) (i : Fin n) :
    (lastRowZeroExtension G b).adjugate i.castSucc (Fin.last n) =
      -((G.adjugate *ᵥ b) i) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      let M := (lastRowZeroExtension G b).submatrix
        (Fin.last (n + 1)).succAbove i.castSucc.succAbove
      have hM : M = (lastRowZeroExtension G b).submatrix
          (Fin.last (n + 1)).succAbove i.castSucc.succAbove := rfl
      have hdet := Matrix.det_succ_column M (Fin.last n)
      -- The inner minor is the corresponding minor of `G`.
      have hminor (k : Fin (n + 1)) :
          (M.submatrix k.succAbove (Fin.last n).succAbove).det =
            (G.submatrix k.succAbove i.succAbove).det := by
        congr 1
        ext a c
        simp [M, Matrix.submatrix_apply, Fin.succAbove_last,
          Fin.castSucc_succAbove_castSucc, lastRowZeroExtension]
      rw [← hM, hdet]
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      rw [hminor k]
      have hsign :
          (-1 : R) ^ ((↑(Fin.last (n + 1)) + ↑i.castSucc : ℕ)) *
              (-1 : R) ^ ((↑k + ↑(Fin.last n) : ℕ)) =
                -((-1 : R) ^ ((↑k + ↑i : ℕ))) := by
        simp only [Fin.val_last, Fin.val_castSucc]
        rw [← pow_add]
        rw [show n + 1 + ↑i + (↑k + n) = (↑k + ↑i) + (2 * n + 1) by omega]
        simp [pow_add, pow_mul]
      calc
        (-1 : R) ^ ((↑(Fin.last (n + 1)) + ↑i.castSucc : ℕ)) *
            ((-1 : R) ^ ((↑k + ↑(Fin.last n) : ℕ)) * M k (Fin.last n) *
              (G.submatrix k.succAbove i.succAbove).det) =
            ((-1 : R) ^ ((↑(Fin.last (n + 1)) + ↑i.castSucc : ℕ)) *
              (-1 : R) ^ ((↑k + ↑(Fin.last n) : ℕ))) *
              (M k (Fin.last n)) *
              (G.submatrix k.succAbove i.succAbove).det := by ring
        _ = -(((-1 : R) ^ ((↑k + ↑i : ℕ))) *
              (G.submatrix k.succAbove i.succAbove).det * b k) := by
            rw [hsign]
            simp [M, lastRowZeroExtension]
            ring

theorem lastRowZeroExtension_adjugate_last {R : Type*} [CommRing R]
    {n : ℕ} (G : Matrix (Fin n) (Fin n) R) (b : Fin n → R) :
    (lastRowZeroExtension G b).adjugate (Fin.last n) (Fin.last n) = G.det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hmat : (lastRowZeroExtension G b).submatrix
      (Fin.last n).succAbove (Fin.last n).succAbove = G := by
    ext i j
    simp [lastRowZeroExtension]
  rw [hmat]
  simp

def nativeSourceAugmentedZeroMatrix (s n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  lastRowZeroExtension (sourceMomentMatrix m s n) (sourceMomentCoupling m s n)

theorem nativeSourceAugmentedZeroMatrix_adjugate_lastColumn (s n : ℕ) :
    (fun j => (nativeSourceAugmentedZeroMatrix s n).adjugate j (Fin.last n)) =
      nativeSourceCofactorVector s n := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [nativeSourceAugmentedZeroMatrix, lastRowZeroExtension_adjugate_last]
    simp [nativeSourceCofactorVector, nativeSourcePrefixDet]
  · rw [nativeSourceAugmentedZeroMatrix, lastRowZeroExtension_adjugate_lastColumn]
    simp [nativeSourceCofactorVector, nativeSourcePrefixDet]

def nativeSourceAugmentedZeroPolynomialMatrix (s n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ[X] :=
  (nativeSourceAugmentedZeroMatrix s n).map C

theorem nativeSourceAugmentedZeroPolynomialMatrix_adjugate_lastColumn (s n : ℕ) :
    (fun j => (nativeSourceAugmentedZeroPolynomialMatrix s n).adjugate j (Fin.last n)) =
      fun j => C (nativeSourceCofactorVector s n j) := by
  funext j
  change (C.mapMatrix (nativeSourceAugmentedZeroMatrix s n)).adjugate j (Fin.last n) = _
  rw [← RingHom.map_adjugate]
  simp only [RingHom.mapMatrix_apply]
  exact congrArg C (congrFun (nativeSourceAugmentedZeroMatrix_adjugate_lastColumn s n) j)

def nativeSourceBorderedPolynomialMatrix (s n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ[X] :=
  (nativeSourceAugmentedZeroPolynomialMatrix s n).updateRow (Fin.last n)
    (fun j => X ^ (j : ℕ))

theorem nativeSourceBorderedPolynomialMatrix_topEntry (s n : ℕ)
    (i : Fin n) (j : Fin (n + 1)) :
    nativeSourceBorderedPolynomialMatrix s n i.castSucc j =
      C (m (i.val + j.val + s)) := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [nativeSourceBorderedPolynomialMatrix, nativeSourceAugmentedZeroPolynomialMatrix,
      nativeSourceAugmentedZeroMatrix, lastRowZeroExtension, sourceMomentMatrix,
      sourceMomentCoupling]
  · simp [nativeSourceBorderedPolynomialMatrix, nativeSourceAugmentedZeroPolynomialMatrix,
      nativeSourceAugmentedZeroMatrix, lastRowZeroExtension, sourceMomentMatrix,
      sourceMomentCoupling]

theorem nativeSourceBorderedPolynomialMatrix_det (s n : ℕ) :
    (nativeSourceBorderedPolynomialMatrix s n).det = nativeSourceCofactorPolynomial s n := by
  let A := nativeSourceAugmentedZeroPolynomialMatrix s n
  let B := nativeSourceBorderedPolynomialMatrix s n
  have hminor (j : Fin (n + 1)) :
      B.submatrix (Fin.last n).succAbove j.succAbove =
        A.submatrix (Fin.last n).succAbove j.succAbove := by
    ext i k
    simp [A, B, nativeSourceBorderedPolynomialMatrix, Matrix.updateRow_apply,
      Fin.succAbove_last]
  rw [Matrix.det_succ_row B (Fin.last n)]
  unfold nativeSourceCofactorPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  have hm := congrArg Matrix.det (hminor j)
  have hadj := Matrix.adjugate_fin_succ_eq_det_submatrix A j (Fin.last n)
  calc
    (-1 : ℝ[X]) ^ ((↑(Fin.last n) + ↑j : ℕ)) * B (Fin.last n) j *
        (B.submatrix (Fin.last n).succAbove j.succAbove).det =
      B (Fin.last n) j *
        ((-1 : ℝ[X]) ^ ((↑(Fin.last n) + ↑j : ℕ)) *
          (A.submatrix (Fin.last n).succAbove j.succAbove).det) := by
            rw [hm]
            ring
    _ = B (Fin.last n) j * A.adjugate j (Fin.last n) := by
          rw [← hadj]
    _ = B (Fin.last n) j * C (nativeSourceCofactorVector s n j) := by
          rw [congrFun (nativeSourceAugmentedZeroPolynomialMatrix_adjugate_lastColumn s n) j]
    _ = C (nativeSourceCofactorVector s n j) * X ^ (j : ℕ) := by
          simp [B, nativeSourceBorderedPolynomialMatrix, Matrix.updateRow_apply]

/-- The upper triangular column transform taking consecutive bordered
columns to their first differences with scale `X`. -/
def sourceHankelColumnDifferenceMatrix (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ[X] :=
  fun i j => if i = j then 1 else if j.val = i.val + 1 then -X else 0

theorem sourceHankelColumnDifferenceMatrix_det (n : ℕ) :
    (sourceHankelColumnDifferenceMatrix n).det = 1 := by
  have ht : (sourceHankelColumnDifferenceMatrix n).BlockTriangular id := by
    intro i j hij
    change j < i at hij
    have hne : i ≠ j := ne_of_gt hij
    have hnext : j.val ≠ i.val + 1 := by omega
    simp [sourceHankelColumnDifferenceMatrix, hne, hnext]
  rw [Matrix.det_of_upperTriangular ht]
  simp [sourceHankelColumnDifferenceMatrix]

theorem matrix_mul_sourceHankelColumnDifference_zero
    (n : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ[X]) (i : Fin (n + 1)) :
    (M * sourceHankelColumnDifferenceMatrix n) i 0 = M i 0 := by
  simp [Matrix.mul_apply, sourceHankelColumnDifferenceMatrix, Finset.sum_ite_eq']

theorem matrix_mul_sourceHankelColumnDifference_succ
    (n : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ[X])
    (i : Fin (n + 1)) (j : Fin n) :
    (M * sourceHankelColumnDifferenceMatrix n) i j.succ =
      M i j.succ - X * M i j.castSucc := by
  classical
  rw [Matrix.mul_apply]
  have hentry (k : Fin (n + 1)) :
      sourceHankelColumnDifferenceMatrix n k j.succ =
        (if k = j.succ then (1 : ℝ[X]) else 0) +
          (if k = j.castSucc then -X else 0) := by
    by_cases hk₁ : k = j.succ
    · subst k
      have hne : j.succ ≠ j.castSucc := by intro h; have := congrArg Fin.val h; simp at this
      simp [sourceHankelColumnDifferenceMatrix, hne]
    by_cases hk₂ : k = j.castSucc
    · subst k
      have hne : j.castSucc ≠ j.succ := by intro h; have := congrArg Fin.val h; simp at this
      simp [sourceHankelColumnDifferenceMatrix, hne]
    have hneq : k.val ≠ j.val := by
      intro h
      exact hk₂ (Fin.ext h)
    simp [sourceHankelColumnDifferenceMatrix, hk₁, hk₂, hneq.symm, Fin.val_succ]
  simp_rw [hentry]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq', sub_eq_add_neg, mul_comm]

theorem nativeSourceBordered_mul_columnDifference_minor (s n : ℕ) :
    ((nativeSourceBorderedPolynomialMatrix s n) *
        sourceHankelColumnDifferenceMatrix n).submatrix
        (Fin.last n).succAbove (0 : Fin (n + 1)).succAbove =
      -(nativeSourceHankelPencil s n) := by
  ext i j
  simp only [Matrix.submatrix_apply, Fin.succAbove_last, Fin.zero_succAbove]
  rw [matrix_mul_sourceHankelColumnDifference_succ]
  rw [nativeSourceBorderedPolynomialMatrix_topEntry s n i j.succ,
    nativeSourceBorderedPolynomialMatrix_topEntry s n i j.castSucc]
  simp [nativeSourceHankelPencil]
  ring

/-- The source cofactor polynomial is the determinant polynomial of the
arbitrary-order Hankel pencil. This identity is division-free and applies
even when a source prefix is singular. -/
theorem nativeSourceHankelPencilPolynomial_eq_cofactor (s n : ℕ) :
    nativeSourceHankelPencilPolynomial s n = nativeSourceCofactorPolynomial s n := by
  let B := nativeSourceBorderedPolynomialMatrix s n
  let T := sourceHankelColumnDifferenceMatrix n
  let U := B * T
  have hrowZero : U (Fin.last n) 0 = 1 := by
    change (B * sourceHankelColumnDifferenceMatrix n) (Fin.last n) 0 = 1
    rw [matrix_mul_sourceHankelColumnDifference_zero]
    simp [B, nativeSourceBorderedPolynomialMatrix, Matrix.updateRow_apply]
  have hrowSucc (j : Fin n) : U (Fin.last n) j.succ = 0 := by
    change (B * sourceHankelColumnDifferenceMatrix n) (Fin.last n) j.succ = 0
    rw [matrix_mul_sourceHankelColumnDifference_succ]
    simp [B, nativeSourceBorderedPolynomialMatrix, Matrix.updateRow_apply]
    ring
  have hdetExpand : U.det =
      (-1 : ℝ[X]) ^ n *
        (U.submatrix (Fin.last n).succAbove (0 : Fin (n + 1)).succAbove).det := by
    rw [Matrix.det_succ_row U (Fin.last n), Fin.sum_univ_succ]
    simp [hrowZero, hrowSucc, Fin.val_last]
  have hminor := congrArg Matrix.det
    (nativeSourceBordered_mul_columnDifference_minor s n)
  simp only [Matrix.det_neg, Fintype.card_fin] at hminor
  have hnegpow : (-1 : ℝ[X]) ^ n * (-1) ^ n = 1 := by
    rw [← mul_pow]
    simp
  have hUdet : U.det = (nativeSourceHankelPencil s n).det := by
    calc
      U.det = (-1 : ℝ[X]) ^ n *
          (U.submatrix (Fin.last n).succAbove (0 : Fin (n + 1)).succAbove).det := hdetExpand
      _ = (-1 : ℝ[X]) ^ n * ((-1 : ℝ[X]) ^ n *
          (nativeSourceHankelPencil s n).det) := by rw [hminor]
      _ = (nativeSourceHankelPencil s n).det := by rw [← mul_assoc, hnegpow, one_mul]
  have hdetTransform : U.det = B.det := by
    dsimp [U, T]
    rw [Matrix.det_mul, sourceHankelColumnDifferenceMatrix_det, mul_one]
  calc
    nativeSourceHankelPencilPolynomial s n = (nativeSourceHankelPencil s n).det := rfl
    _ = U.det := hUdet.symm
    _ = B.det := hdetTransform
    _ = nativeSourceCofactorPolynomial s n := nativeSourceBorderedPolynomialMatrix_det s n

theorem nativeSourceHankelPencilPolynomial_zero (s : ℕ) :
    nativeSourceHankelPencilPolynomial s 0 = nativeSourceCofactorPolynomial s 0 := by
  simp [nativeSourceHankelPencilPolynomial,
    nativeSourceCofactorPolynomial, nativeSourceCofactorVector,
    nativeSourcePrefixDet]

end
end CarrySelfAdjointOperator
