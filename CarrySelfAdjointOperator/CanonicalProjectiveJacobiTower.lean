import CarrySelfAdjointOperator.ExactProjectiveMatrixTower
import CarrySelfAdjointOperator.CanonicalFiniteHeight
import CarrySelfAdjointOperator.PositiveLowerWhiteningRigidity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Canonical LDL compatibility as the exact projective Jacobi gate

The normalized inverse LDL factor is lower triangular, has strictly positive
diagonal, and whitens the positive Hankel Gram matrix exactly.  The principal
block of the next-order factor has the same three properties for the old
Hankel section.  Positive lower-whitening rigidity therefore forces equality
with the old canonical factor.

Consequently the canonical finite Jacobi sections form an exact principal
tower and determine one infinite coefficient matrix entry by entry.
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
LDL factors. -/
def IsCanonicalLDLPrincipalCompatible
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef) : Prop :=
  ∀ N : ℕ,
    (canonicalLDLInverseFactor (hgram (N + 1))).submatrix
        Fin.castSucc Fin.castSucc =
      canonicalLDLInverseFactor (hgram N)

/-- The old principal block of the next-order canonical LDL factor is itself
a positive lower triangular whitening of the old Hankel Gram matrix. -/
theorem canonicalLDLInverseFactor_succ_principal_isPositiveLowerWhitening
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef)
    (N : ℕ) :
    IsPositiveLowerWhitening
      (hankelGram moments N)
      ((canonicalLDLInverseFactor (hgram (N + 1))).submatrix
        Fin.castSucc Fin.castSucc) := by
  let largeFactor := canonicalLDLInverseFactor (hgram (N + 1))
  let smallFactor : Matrix (Fin N) (Fin N) ℝ :=
    largeFactor.submatrix Fin.castSucc Fin.castSucc
  have hupperRight : ∀ i : Fin N,
      largeFactor (Fin.castSucc i) (Fin.last N) = 0 := by
    intro i
    exact canonicalLDLInverseFactor_triangular
      (hgram (N + 1)) (Fin.castSucc_lt_last i)
  have hproject :=
    finiteJacobiTransport_succ_principal_of_lowerTriangular
      (smallFactor := smallFactor)
      (smallShifted := hankelGram moments N)
      (largeFactor := largeFactor)
      (largeShifted := hankelGram moments (N + 1))
      rfl (hankelGram_succ_principal moments N) hupperRight
  have hwhite :
      finiteJacobiTransport smallFactor (hankelGram moments N) = 1 := by
    rw [canonicalLDLInverseFactor_whitens (hgram (N + 1))] at hproject
    simpa using hproject.symm
  refine ⟨?_, ?_, hwhite⟩
  · intro i j hij
    exact canonicalLDLInverseFactor_triangular
      (hgram (N + 1)) (by simpa using hij)
  · intro i
    exact canonicalLDLInverseFactor_diag_pos
      (hgram (N + 1)) (Fin.castSucc i)

/-- The normalized inverse LDL factors are canonically compatible under
principal restriction.  This closes the Cholesky/LDL gate from the exact
projective-tower argument. -/
theorem canonicalLDLInverseFactor_succ_principal
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef)
    (N : ℕ) :
    (canonicalLDLInverseFactor (hgram (N + 1))).submatrix
        Fin.castSucc Fin.castSucc =
      canonicalLDLInverseFactor (hgram N) := by
  exact positiveLowerWhitening_unique
    (hgram N)
    (canonicalLDLInverseFactor_succ_principal_isPositiveLowerWhitening
      moments hgram N)
    (canonicalLDLInverseFactor_isPositiveLowerWhitening (hgram N))

/-- Canonical LDL compatibility in the interface consumed by the projective
Jacobi tower. -/
theorem canonicalLDLPrincipalCompatible
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef) :
    IsCanonicalLDLPrincipalCompatible moments hgram := by
  intro N
  exact canonicalLDLInverseFactor_succ_principal moments hgram N

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

/-- The canonical finite Jacobi sections form an exact principal tower with
no external compatibility hypothesis. -/
theorem canonicalFiniteJacobiSection_isExactPrincipalTower_canonical
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef) :
    IsExactPrincipalTower
      (fun N => canonicalFiniteJacobiSection moments N (hgram N)) :=
  canonicalFiniteJacobiSection_isExactPrincipalTower
    moments hgram (canonicalLDLPrincipalCompatible moments hgram)

/-- Infinite coefficient matrix selected by the canonical LDL Jacobi
sections. -/
def canonicalJacobiTowerLimitMatrix
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef) :
    Matrix ℕ ℕ ℝ :=
  exactPrincipalTowerLimit
    (fun N => canonicalFiniteJacobiSection moments N (hgram N))

/-- Every canonical finite Jacobi section is exactly recovered from the
infinite coefficient matrix once LDL prefix compatibility is supplied. -/
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

/-- Unconditional exact recovery of every canonical finite Jacobi section
from the single infinite coefficient matrix, assuming only strict positivity
of the Hankel Gram sections. -/
theorem canonicalJacobiTowerLimitMatrix_submatrix_canonical
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef)
    (N : ℕ) :
    (canonicalJacobiTowerLimitMatrix moments hgram).submatrix
        (fun i : Fin N => (i : ℕ))
        (fun i : Fin N => (i : ℕ)) =
      canonicalFiniteJacobiSection moments N (hgram N) :=
  canonicalJacobiTowerLimitMatrix_submatrix
    moments hgram (canonicalLDLPrincipalCompatible moments hgram) N

end

end CarrySelfAdjointOperator
