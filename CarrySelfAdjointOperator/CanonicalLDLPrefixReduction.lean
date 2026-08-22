import CarrySelfAdjointOperator.CanonicalLDLLowerInvPrefix
import CarrySelfAdjointOperator.ExactProjectiveMatrixTower
import CarrySelfAdjointOperator.CanonicalFiniteHeight
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# From lower-inverse prefixes to the exact canonical Jacobi tower

The rowwise theorem in `CanonicalLDLLowerInvPrefix` gives exact principal
compatibility of Mathlib's unnormalized `LDL.lowerInv`.  This module transports
that identity through:

* the LDL diagonal;
* its positive inverse-square-root normalization;
* the canonical whitening factor;
* the shifted Hankel congruence defining the finite Jacobi sections.

Thus strict positivity of every Hankel Gram section is the only input needed
for exact projectivity of the canonical Jacobi tower.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- A lower-triangular factor whose old principal block and old matrix block
are fixed cannot feed the new coordinate into the old congruence block. -/
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

/-- Compatibility of `LDL.lowerInv` transports to the diagonal LDL matrix. -/
theorem ldlDiag_succ_principal_of_lowerInv
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef)
    (N : ℕ) :
    (LDL.diag (hgram (N + 1))).submatrix
        Fin.castSucc Fin.castSucc =
      LDL.diag (hgram N) := by
  have htransport :=
    finiteJacobiTransport_succ_principal_of_lowerTriangular
      (smallFactor := LDL.lowerInv (hgram N))
      (smallShifted := hankelGram moments N)
      (largeFactor := LDL.lowerInv (hgram (N + 1)))
      (largeShifted := hankelGram moments (N + 1))
      (ldlLowerInv_hankel_succ_principal moments hgram N)
      (hankelGram_succ_principal moments N)
      (fun i => LDL.lowerInv_triangular
        (hgram (N + 1)) (Fin.castSucc_lt_last i))
  rw [LDL.diag_eq_lowerInv_conj (hgram (N + 1)),
    LDL.diag_eq_lowerInv_conj (hgram N)]
  simpa [finiteJacobiTransport,
    Matrix.conjTranspose_eq_transpose_of_trivial] using htransport

/-- Old diagonal entries of the next LDL section equal the old entries. -/
theorem ldlDiagEntries_castSucc_of_lowerInv
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef)
    (N : ℕ) (i : Fin N) :
    LDL.diagEntries (hgram (N + 1)) (Fin.castSucc i) =
      LDL.diagEntries (hgram N) i := by
  have h := congrArg
    (fun D : Matrix (Fin N) (Fin N) ℝ => D i i)
    (ldlDiag_succ_principal_of_lowerInv moments hgram N)
  simpa [LDL.diag, Matrix.submatrix_apply] using h

/-- The positive diagonal normalizing scale is prefix-compatible. -/
theorem canonicalLDLScale_castSucc_of_lowerInv
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef)
    (N : ℕ) (i : Fin N) :
    canonicalLDLScale (hgram (N + 1)) (Fin.castSucc i) =
      canonicalLDLScale (hgram N) i := by
  unfold canonicalLDLScale
  rw [ldlDiagEntries_castSucc_of_lowerInv moments hgram N i]

/-- Prefix compatibility survives the diagonal normalization, so the complete
canonical whitening factors agree on every old principal block. -/
theorem canonicalLDLInverseFactor_succ_principal_of_lowerInv
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef)
    (N : ℕ) :
    (canonicalLDLInverseFactor (hgram (N + 1))).submatrix
        Fin.castSucc Fin.castSucc =
      canonicalLDLInverseFactor (hgram N) := by
  ext i j
  have hlower := congrArg
    (fun L : Matrix (Fin N) (Fin N) ℝ => L i j)
    (ldlLowerInv_hankel_succ_principal moments hgram N)
  simp only [Matrix.submatrix_apply] at hlower
  simp [canonicalLDLInverseFactor, Matrix.submatrix_apply,
    Matrix.diagonal_mul,
    canonicalLDLScale_castSucc_of_lowerInv moments hgram N i,
    hlower]

/-- Exact prefix compatibility interface for the canonical normalized inverse
LDL factors. -/
def IsCanonicalLDLPrincipalCompatible
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef) : Prop :=
  ∀ N : ℕ,
    (canonicalLDLInverseFactor (hgram (N + 1))).submatrix
        Fin.castSucc Fin.castSucc =
      canonicalLDLInverseFactor (hgram N)

/-- Strict positivity of all Hankel Gram sections forces canonical LDL prefix
compatibility; no separate whitening hypothesis remains. -/
theorem canonicalLDLPrincipalCompatible
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef) :
    IsCanonicalLDLPrincipalCompatible moments hgram := by
  intro N
  exact canonicalLDLInverseFactor_succ_principal_of_lowerInv
    moments hgram N

/-- Principal compatibility of canonical factors implies exact projectivity
of the corresponding finite Jacobi sections. -/
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

/-- The canonical finite Jacobi sections form an exact principal tower from
Hankel positivity alone. -/
theorem canonicalFiniteJacobiSection_isExactPrincipalTower_unconditional
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef) :
    IsExactPrincipalTower
      (fun N => canonicalFiniteJacobiSection moments N (hgram N)) :=
  canonicalFiniteJacobiSection_isExactPrincipalTower
    moments hgram (canonicalLDLPrincipalCompatible moments hgram)

/-- Infinite coefficient matrix selected entrywise by the canonical finite
Jacobi tower. -/
def canonicalJacobiTowerLimitMatrix
    (moments : ℕ → ℝ)
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef) :
    Matrix ℕ ℕ ℝ :=
  exactPrincipalTowerLimit
    (fun N => canonicalFiniteJacobiSection moments N (hgram N))

/-- Conditional spelling retained for downstream compatibility. -/
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

/-- Every canonical finite Jacobi section is exactly the corresponding block
of one infinite coefficient matrix, with no external prefix hypothesis. -/
theorem canonicalJacobiTowerLimitMatrix_submatrix_unconditional
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
