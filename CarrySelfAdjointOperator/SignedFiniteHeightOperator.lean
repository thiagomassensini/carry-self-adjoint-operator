import CarrySelfAdjointOperator.CanonicalFiniteHeight
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Signed finite height operator and its parity symmetry

The positive finite height operator is `T_N = J_N⁻¹ᐟ²`.  Its canonical signed
realization is the block operator

`H_N = T_N ⊕ (-T_N)`.

This file formalizes the exact algebra used by the standalone native-carry
laboratory.  The sector-swap reflection is a symmetric involution and
anticommutes with `H_N`.  Thus it exchanges the positive and negative height
sectors.  It must not be confused with the diagonal grading, which labels the
two sectors and commutes with `H_N`.
-/

namespace CarrySelfAdjointOperator

noncomputable section

variable {ι : Type*}

/-- Signed block realization `T ⊕ (-T)` of a finite operator. -/
def signedBlockOperator (positive : Matrix ι ι ℝ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks positive 0 0 (-positive)

/-- Block-diagonal doubling with the same operator in both sectors. -/
def doubledBlockOperator (positive : Matrix ι ι ℝ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks positive 0 0 positive

/-- Symmetric involution exchanging the two signed sectors. -/
def signedSectorReflection [DecidableEq ι] : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks 0 1 1 0

/-- Diagonal grading which is `+1` on the first sector and `-1` on the
second. -/
def signedSectorGrading [DecidableEq ι] : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- A symmetric positive block produces a symmetric signed operator. -/
theorem signedBlockOperator_isSymm
    {positive : Matrix ι ι ℝ} (hpositive : positive.IsSymm) :
    (signedBlockOperator positive).IsSymm := by
  exact hpositive.fromBlocks (by simp) hpositive.neg

/-- The sector reflection is symmetric. -/
theorem signedSectorReflection_isSymm [DecidableEq ι] :
    (signedSectorReflection (ι := ι)).IsSymm := by
  exact Matrix.IsSymm.fromBlocks (by simp) (by simp) (by simp)

/-- The sector reflection squares to the identity. -/
theorem signedSectorReflection_sq [Fintype ι] [DecidableEq ι] :
    signedSectorReflection (ι := ι) * signedSectorReflection (ι := ι) = 1 := by
  simp [signedSectorReflection, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_one]

/-- The diagonal grading is symmetric. -/
theorem signedSectorGrading_isSymm [DecidableEq ι] :
    (signedSectorGrading (ι := ι)).IsSymm := by
  exact Matrix.IsSymm.fromBlocks (by simp) (by simp) (by simp)

/-- The diagonal grading also squares to the identity. -/
theorem signedSectorGrading_sq [Fintype ι] [DecidableEq ι] :
    signedSectorGrading (ι := ι) * signedSectorGrading (ι := ι) = 1 := by
  simp [signedSectorGrading, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_one]

/-- The signed operator is the diagonal grading times the unsigned doubled
operator. -/
theorem signedBlockOperator_eq_grading_mul_doubled
    [Fintype ι] [DecidableEq ι] (positive : Matrix ι ι ℝ) :
    signedBlockOperator positive =
      signedSectorGrading * doubledBlockOperator positive := by
  simp [signedBlockOperator, signedSectorGrading, doubledBlockOperator,
    Matrix.fromBlocks_multiply]

/-- The sector swap anticommutes with the signed height operator. -/
theorem signedSectorReflection_mul_signedBlockOperator
    [Fintype ι] [DecidableEq ι] (positive : Matrix ι ι ℝ) :
    signedSectorReflection * signedBlockOperator positive =
      -(signedBlockOperator positive * signedSectorReflection) := by
  simp [signedSectorReflection, signedBlockOperator,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]

/-- Equivalent conjugation form: reflection reverses the sign of the signed
operator. -/
theorem signedSectorReflection_conj_signedBlockOperator
    [Fintype ι] [DecidableEq ι] (positive : Matrix ι ι ℝ) :
    signedSectorReflection * signedBlockOperator positive *
        signedSectorReflection =
      -signedBlockOperator positive := by
  simp [signedSectorReflection, signedBlockOperator,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]

/-- In contrast, the diagonal grading commutes with the signed operator. -/
theorem signedSectorGrading_commute_signedBlockOperator
    [Fintype ι] [DecidableEq ι] (positive : Matrix ι ι ℝ) :
    Commute signedSectorGrading (signedBlockOperator positive) := by
  show signedSectorGrading * signedBlockOperator positive =
    signedBlockOperator positive * signedSectorGrading
  simp [signedSectorGrading, signedBlockOperator,
    Matrix.fromBlocks_multiply]

/-- The characteristic polynomial of the signed block is exactly the product
of the positive and negative sector characteristic polynomials. -/
theorem signedBlockOperator_charpoly [Fintype ι] [DecidableEq ι]
    (positive : Matrix ι ι ℝ) :
    (signedBlockOperator positive).charpoly =
      positive.charpoly * (-positive).charpoly := by
  simp [signedBlockOperator]

/-- Canonical signed height operator generated from one shifted moment Gram
representation.  No signed target values enter this definition. -/
def canonicalSignedFiniteHeightOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ) (hgram : (hankelGram moments N).PosDef)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  signedBlockOperator
    (canonicalFiniteHeightOperator hrep N hgram hli)

/-- The canonical signed finite height operator is exactly symmetric. -/
theorem canonicalSignedFiniteHeightOperator_isSymm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ) (hgram : (hankelGram moments N).PosDef)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    (canonicalSignedFiniteHeightOperator hrep N hgram hli).IsSymm := by
  exact signedBlockOperator_isSymm
    (canonicalFiniteHeightOperator_isSymm hrep N hgram hli)

/-- The canonical signed operator has the exact sector-factorized
characteristic polynomial. -/
theorem canonicalSignedFiniteHeightOperator_charpoly
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ) (hgram : (hankelGram moments N).PosDef)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    (canonicalSignedFiniteHeightOperator hrep N hgram hli).charpoly =
      (canonicalFiniteHeightOperator hrep N hgram hli).charpoly *
        (-canonicalFiniteHeightOperator hrep N hgram hli).charpoly := by
  exact signedBlockOperator_charpoly
    (canonicalFiniteHeightOperator hrep N hgram hli)

/-- The canonical sector swap reverses the sign of the canonical signed
height operator by exact conjugation. -/
theorem signedSectorReflection_conj_canonicalSignedFiniteHeightOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ) (hgram : (hankelGram moments N).PosDef)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    signedSectorReflection *
        canonicalSignedFiniteHeightOperator hrep N hgram hli *
        signedSectorReflection =
      -canonicalSignedFiniteHeightOperator hrep N hgram hli := by
  exact signedSectorReflection_conj_signedBlockOperator
    (canonicalFiniteHeightOperator hrep N hgram hli)

end

end CarrySelfAdjointOperator
