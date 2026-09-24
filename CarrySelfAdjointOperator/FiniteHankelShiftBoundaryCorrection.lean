import CarrySelfAdjointOperator.LogarithmicMomentHankel
import CarrySelfAdjointOperator.FiniteNativeDepthCameraCommutator
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Finite Hankel shift and its last-column correction

For a prefix of length `N + 1`, multiplication by the moment variable is the
raising shift on every non-final monomial.  The final monomial leaves the
prefix.  This file isolates that elementary finite algebra from the separate
all-order positivity gate.

The chosen shift is the transpose of the repository's `finiteDepthShift`:
it sends `e_j` to `e_(j+1)` and kills the final basis vector.  This is the
orientation for which `G * S` agrees with the shifted Hankel matrix on all
but its final column.
-/

open scoped Matrix MatrixOrder

namespace CarrySelfAdjointOperator

noncomputable section

open NativeCarrySpectralWeyl.Finite

/-- Truncated multiplication-by-the-moment-variable on a prefix of length
`N + 1`.  It is the raising orientation of the existing finite depth shift. -/
def finiteHankelRaisingShift (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (finiteDepthShift (N + 1)).transpose

/-- The last-coordinate row functional of a finite prefix. -/
def finiteHankelLastRow (N : ℕ) : Fin (N + 1) → ℝ :=
  fun j => if j = Fin.last N then 1 else 0

/-- The literal last-column defect of the finite Hankel multiplication law. -/
def finiteHankelShiftBoundaryCorrection
    (moments : ℕ → ℝ) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j => if j = Fin.last N then shiftedHankel moments (N + 1) i j else 0

/-- On every nonfinal column, the raising shift advances the second Hankel
index by one. -/
theorem hankelGram_mul_finiteHankelRaisingShift_castSucc
    (moments : ℕ → ℝ) (N : ℕ) (i : Fin (N + 1)) (j : Fin N) :
    (hankelGram moments (N + 1) * finiteHankelRaisingShift N) i
        (Fin.castSucc j) =
      shiftedHankel moments (N + 1) i (Fin.castSucc j) := by
  classical
  unfold finiteHankelRaisingShift
  rw [Matrix.mul_apply]
  let k : Fin (N + 1) := Fin.succ j
  rw [Finset.sum_eq_single k]
  · simp [finiteDepthShift, k, hankelGram, shiftedHankel]
    apply congrArg moments
    omega
  · intro b _ hb
    have hne : j.val + 1 ≠ b.val := by
      intro h
      apply hb
      apply Fin.ext
      simpa [k] using h.symm
    simp [finiteDepthShift, hne]
  · simp [k]

/-- The truncated raising shift has no final column. -/
theorem hankelGram_mul_finiteHankelRaisingShift_last
    (moments : ℕ → ℝ) (N : ℕ) (i : Fin (N + 1)) :
    (hankelGram moments (N + 1) * finiteHankelRaisingShift N) i
        (Fin.last N) = 0 := by
  classical
  unfold finiteHankelRaisingShift
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro j _
  have hne : N + 1 ≠ j.val := by
    exact (Nat.ne_of_lt j.isLt).symm
  simp [finiteDepthShift, hne]

/-- Exact finite Hankel multiplication law.  The only failure of the
infinite shift relation is its final column. -/
theorem shiftedHankel_eq_hankelGram_mul_finiteHankelRaisingShift_add_boundary
    (moments : ℕ → ℝ) (N : ℕ) :
    shiftedHankel moments (N + 1) =
      hankelGram moments (N + 1) * finiteHankelRaisingShift N +
        finiteHankelShiftBoundaryCorrection moments N := by
  ext i j
  simp only [Matrix.add_apply]
  refine Fin.lastCases ?_ (fun j => ?_) j
  ·
      rw [hankelGram_mul_finiteHankelRaisingShift_last]
      simp [finiteHankelShiftBoundaryCorrection]
  ·
      rw [hankelGram_mul_finiteHankelRaisingShift_castSucc]
      simp [finiteHankelShiftBoundaryCorrection]

/-- The finite Galerkin multiplication matrix, defined whenever the unshifted
Hankel Gram is nonsingular.  Positivity is used only to obtain this inverse;
no native positivity claim is made in this file. -/
def finiteHankelGalerkinMultiplication
    (moments : ℕ → ℝ) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (hankelGram moments (N + 1))⁻¹ * shiftedHankel moments (N + 1)

/-- The boundary column in
`A = S + c e_last^T`: it is exactly `G⁻¹ K e_last`. -/
def finiteHankelGalerkinBoundaryColumn
    (moments : ℕ → ℝ) (N : ℕ) : Fin (N + 1) → ℝ :=
  fun i => finiteHankelGalerkinMultiplication moments N i (Fin.last N)

/-- Rank-one matrix formed by a column and the last-coordinate row. -/
def finiteHankelLastColumnRankOne
    (N : ℕ) (c : Fin (N + 1) → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j => c i * finiteHankelLastRow N j

@[simp] theorem finiteHankelShiftBoundaryCorrection_last
    (moments : ℕ → ℝ) (N : ℕ) (i : Fin (N + 1)) :
    finiteHankelShiftBoundaryCorrection moments N i (Fin.last N) =
      shiftedHankel moments (N + 1) i (Fin.last N) := by
  simp [finiteHankelShiftBoundaryCorrection]

@[simp] theorem finiteHankelShiftBoundaryCorrection_castSucc
    (moments : ℕ → ℝ) (N : ℕ) (i : Fin (N + 1)) (j : Fin N) :
    finiteHankelShiftBoundaryCorrection moments N i (Fin.castSucc j) = 0 := by
  simp [finiteHankelShiftBoundaryCorrection]

@[simp] theorem finiteHankelRaisingShift_last
    (N : ℕ) (i : Fin (N + 1)) :
    finiteHankelRaisingShift N i (Fin.last N) = 0 := by
  unfold finiteHankelRaisingShift
  have hne : N + 1 ≠ i.val := (Nat.ne_of_lt i.isLt).symm
  simp [finiteDepthShift, hne]

/-- `G A = K` is the defining Galerkin identity. -/
theorem hankelGram_mul_finiteHankelGalerkinMultiplication
    (moments : ℕ → ℝ) (N : ℕ)
    (hG : (hankelGram moments (N + 1)).PosDef) :
    hankelGram moments (N + 1) *
        finiteHankelGalerkinMultiplication moments N =
      shiftedHankel moments (N + 1) := by
  unfold finiteHankelGalerkinMultiplication
  letI := hG.isUnit.invertible
  rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]

/-- `A` is self-adjoint for the finite Hankel Gram metric. -/
theorem finiteHankelGalerkinMultiplication_transpose_mul_hankelGram
    (moments : ℕ → ℝ) (N : ℕ)
    (hG : (hankelGram moments (N + 1)).PosDef) :
    (finiteHankelGalerkinMultiplication moments N).transpose *
        hankelGram moments (N + 1) =
      shiftedHankel moments (N + 1) := by
  have hGA := hankelGram_mul_finiteHankelGalerkinMultiplication moments N hG
  calc
    (finiteHankelGalerkinMultiplication moments N).transpose *
        hankelGram moments (N + 1) =
      (hankelGram moments (N + 1) *
        finiteHankelGalerkinMultiplication moments N).transpose := by
          rw [Matrix.transpose_mul, hankelGram_isSymm]
    _ = (shiftedHankel moments (N + 1)).transpose := by rw [hGA]
    _ = shiftedHankel moments (N + 1) := shiftedHankel_isSymm moments (N + 1)

/-- Before identifying its rank, the boundary correction has the transparent
form `G⁻¹ * B`: no moment positivity beyond invertibility is used. -/
theorem finiteHankelGalerkinMultiplication_eq_raisingShift_add_inverseBoundary
    (moments : ℕ → ℝ) (N : ℕ)
    (hG : (hankelGram moments (N + 1)).PosDef) :
    finiteHankelGalerkinMultiplication moments N =
      finiteHankelRaisingShift N +
        (hankelGram moments (N + 1))⁻¹ *
          finiteHankelShiftBoundaryCorrection moments N := by
  unfold finiteHankelGalerkinMultiplication
  rw [shiftedHankel_eq_hankelGram_mul_finiteHankelRaisingShift_add_boundary,
    Matrix.mul_add, ← Matrix.mul_assoc]
  letI := hG.isUnit.invertible
  rw [Matrix.inv_mul_of_invertible, Matrix.one_mul]

/-- Applying `G⁻¹` to the last-column defect remains a last-column matrix;
the column is precisely `G⁻¹ K e_last`. -/
theorem inverse_mul_finiteHankelShiftBoundaryCorrection_eq_lastColumnRankOne
    (moments : ℕ → ℝ) (N : ℕ) :
    (hankelGram moments (N + 1))⁻¹ *
        finiteHankelShiftBoundaryCorrection moments N =
      finiteHankelLastColumnRankOne N
        (finiteHankelGalerkinBoundaryColumn moments N) := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  ·
    unfold finiteHankelLastColumnRankOne finiteHankelLastRow
      finiteHankelGalerkinBoundaryColumn finiteHankelGalerkinMultiplication
    simp only [if_pos, Matrix.mul_apply]
    simp only [mul_one]
    apply Finset.sum_congr rfl
    intro k _
    simp [finiteHankelShiftBoundaryCorrection]
  ·
    unfold finiteHankelLastColumnRankOne finiteHankelLastRow
    simp only [if_neg (Fin.castSucc_ne_last j), mul_zero]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    simp [finiteHankelShiftBoundaryCorrection]

/-- Exact finite compression formula
`A = S + c e_lastᵀ`, where
`c = G⁻¹ K e_last`.  The one-column term is the sole truncation defect. -/
theorem finiteHankelGalerkinMultiplication_eq_raisingShift_add_boundaryColumn
    (moments : ℕ → ℝ) (N : ℕ)
    (hG : (hankelGram moments (N + 1)).PosDef) :
    finiteHankelGalerkinMultiplication moments N =
      finiteHankelRaisingShift N +
        finiteHankelLastColumnRankOne N
          (finiteHankelGalerkinBoundaryColumn moments N) := by
  rw [finiteHankelGalerkinMultiplication_eq_raisingShift_add_inverseBoundary
    moments N hG,
    inverse_mul_finiteHankelShiftBoundaryCorrection_eq_lastColumnRankOne]

/-- The symmetric Euclidean representative of the finite Galerkin
multiplication.  This is exactly `G⁻¹/² K G⁻¹/²`; it is a finite algebraic
construction conditional only on the displayed positive definiteness of `G`.
-/
def finiteHankelWhitenedMultiplication
    (moments : ℕ → ℝ) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  positiveInverseSqrt (hankelGram moments (N + 1)) *
    shiftedHankel moments (N + 1) *
      positiveInverseSqrt (hankelGram moments (N + 1))

/-- The whitened Galerkin multiplication is symmetric. -/
theorem finiteHankelWhitenedMultiplication_isSymm
    (moments : ℕ → ℝ) (N : ℕ)
    (hG : (hankelGram moments (N + 1)).PosDef) :
    (finiteHankelWhitenedMultiplication moments N).IsSymm := by
  change (whitenedMatrix (hankelGram moments (N + 1))
    (shiftedHankel moments (N + 1))).IsSymm
  exact Matrix.isHermitian_iff_isSymm.mp
    (whitenedMatrix_isHermitian hG
      (Matrix.isHermitian_iff_isSymm.mpr
        (shiftedHankel_isSymm moments (N + 1))))

/-- The positive square-root conjugate of `A = G⁻¹K` is the congruence
`G⁻¹/² K G⁻¹/²`.  This is the precise finite version of the Jacobi whitening
identity; no all-order positivity is asserted. -/
theorem finiteHankelSqrt_mul_galerkin_mul_inverseSqrt_eq_whitened
    (moments : ℕ → ℝ) (N : ℕ)
    (hG : (hankelGram moments (N + 1)).PosDef) :
    CFC.sqrt (hankelGram moments (N + 1)) *
        finiteHankelGalerkinMultiplication moments N *
          positiveInverseSqrt (hankelGram moments (N + 1)) =
      finiteHankelWhitenedMultiplication moments N := by
  let G := hankelGram moments (N + 1)
  let W := positiveInverseSqrt G
  have hWsq : W * W = G⁻¹ := positiveInverseSqrt_mul_self hG
  have hsqrtW : CFC.sqrt G * W = 1 := by
    unfold W positiveInverseSqrt
    have hunit : IsUnit (CFC.sqrt G) :=
      (hG.isStrictlyPositive.sqrt G).isUnit
    letI := hunit.invertible
    exact Matrix.mul_inv_of_invertible _
  change CFC.sqrt G * (G⁻¹ * shiftedHankel moments (N + 1)) * W =
    W * shiftedHankel moments (N + 1) * W
  rw [← hWsq]
  calc
    CFC.sqrt G * (W * W * shiftedHankel moments (N + 1)) * W =
        (CFC.sqrt G * W) * W * shiftedHankel moments (N + 1) * W := by
          noncomm_ring
    _ = W * shiftedHankel moments (N + 1) * W := by rw [hsqrtW, Matrix.one_mul]

end

end CarrySelfAdjointOperator
