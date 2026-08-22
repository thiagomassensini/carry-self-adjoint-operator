import CarrySelfAdjointOperator.ExactProjectiveMatrixTower
import CarrySelfAdjointOperator.CanonicalFiniteHeight
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Canonical LDL compatibility as the exact projective Jacobi gate

This module reduces the canonical projective-tower problem to one concrete
prefix identity for the normalized inverse LDL factors.  Once that identity
is supplied, lower triangularity removes the new boundary coordinate from
old rows and the Jacobi congruence restricts exactly.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- A lower-triangular factor whose old principal block and the old principal
block of the shifted matrix are fixed cannot feed the new coordinate back
into the old Jacobi block. -/
theorem finiteJacobiTransport_succ_principal_of_lowerTriangular
    {N : ℕ}
    {smallFactor smallShifted : Matrix (Fin N) (Fin N) ℝ}
    {largeFactor largeShifted : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hfactor :
      largeFactor.submatrix Fin.castSucc Fin.castSucc = smallFactor)
    (hshifted :
      largeShifted.submatrix Fin.castSucc Fin.castSucc = smallShifted)
    (hupperRight : ∀ i : Fin N,
      largeFactor (Fin.castSucc i) (Fin.last N) = 0) :
    (finiteJacobiTransport largeFactor largeShifted).submatrix
        Fin.castSucc Fin.castSucc =
      finiteJacobiTransport smallFactor smallShifted := by
  classical
  have hfactorApply : ∀ i j : Fin N,
      largeFactor (Fin.castSucc i) (Fin.castSucc j) =
        smallFactor i j := by
    intro i j
    have h := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A i j) hfactor
    simpa [Matrix.submatrix_apply] using h
  have hshiftedApply : ∀ i j : Fin N,
      largeShifted (Fin.castSucc i) (Fin.castSucc j) =
        smallShifted i j := by
    intro i j
    have h := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A i j) hshifted
    simpa [Matrix.submatrix_apply] using h
  ext i j
  simp only [finiteJacobiTransport, Matrix.submatrix_apply,
    Matrix.mul_apply, Matrix.transpose_apply]
  rw [Fin.sum_univ_castSucc]
  simp only [hupperRight j, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Fin.sum_univ_castSucc]
  simp [hupperRight i, hfactorApply, hshiftedApply]

/-- Exact prefix compatibility demanded from the canonical normalized inverse
LDL factors.  This is the remaining algebraic gate in the Cholesky/LDL route
from the research note. -/
def IsCanonicalLDLPrincipalCompatible
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef) : Prop :=
  ∀ N : ℕ,
    (canonicalLDLInverseFactor (hgram (N + 1))).submatrix
        Fin.castSucc Fin.castSucc =
      canonicalLDLInverseFactor (hgram N)

/-- Principal compatibility of the canonical LDL factors implies exact
projectivity of the canonical finite Jacobi sections. -/
theorem canonicalFiniteJacobiSection_isExactPrincipalTower
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef)
    (hcompat : IsCanonicalLDLPrincipalCompatible moments hgram) :
    IsExactPrincipalTower
      (fun N => canonicalFiniteJacobiSection moments N (hgram N)) := by
  intro N
  change
    (finiteJacobiTransport
      (canonicalLDLInverseFactor (hgram (N + 1)))
      (shiftedHankel moments (N + 1))).submatrix
        Fin.castSucc Fin.castSucc =
      finiteJacobiTransport
        (canonicalLDLInverseFactor (hgram N))
        (shiftedHankel moments N)
  apply finiteJacobiTransport_succ_principal_of_lowerTriangular
  · exact hcompat N
  · exact shiftedHankel_succ_principal moments N
  · intro i
    exact canonicalLDLInverseFactor_triangular
      (hgram (N + 1)) (Fin.castSucc_lt_last i)

/-- Infinite coefficient matrix selected by the compatible canonical LDL
Jacobi sections. -/
def canonicalJacobiTowerLimitMatrix
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef) :
    Matrix ℕ ℕ ℝ :=
  exactPrincipalTowerLimit
    (fun N => canonicalFiniteJacobiSection moments N (hgram N))

/-- Every canonical finite Jacobi section is exactly recovered from the
infinite coefficient matrix once LDL prefix compatibility is proved. -/
theorem canonicalJacobiTowerLimitMatrix_submatrix
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef)
    (hcompat : IsCanonicalLDLPrincipalCompatible moments hgram)
    (N : ℕ) :
    (canonicalJacobiTowerLimitMatrix moments hgram).submatrix
        (fun i : Fin N => (i : ℕ))
        (fun i : Fin N => (i : ℕ)) =
      canonicalFiniteJacobiSection moments N (hgram N) :=
  exactPrincipalTowerLimit_submatrix
    (canonicalFiniteJacobiSection_isExactPrincipalTower
      moments hgram hcompat) N

end

end CarrySelfAdjointOperator
