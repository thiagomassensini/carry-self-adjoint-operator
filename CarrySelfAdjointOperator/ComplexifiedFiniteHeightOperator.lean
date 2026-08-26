import CarrySelfAdjointOperator.GenuineMomentOperatorUniqueness
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Complex coordinates for the finite height operator

The native height matrices have real coefficients because the completed
complex characteristic produces a real logarithmic moment sequence.  This
file records the canonical change of coordinates from those real matrices to
complex Hilbert coordinates.

The complex operator is obtained entrywise through `Complex.ofReal`.  Its
action on a complex vector is exactly the packaging of the two real actions,
its matrix is Hermitian, and its characteristic polynomial is the scalar
extension of the real characteristic polynomial.  Thus complex coordinates
neither introduce nor move a finite height eigenvalue.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

/-- Entrywise scalar extension of a real matrix to complex coordinates. -/
def complexifyRealMatrix {m n : Type*} (A : Matrix m n ℝ) : Matrix m n ℂ :=
  A.map Complex.ofReal

/-- Package two real coordinate vectors as one complex vector. -/
def packageRealVector {n : Type*} (x y : n → ℝ) : n → ℂ :=
  fun i => (x i : ℂ) + Complex.I * (y i : ℂ)

/-- Complexification intertwines matrix action with the two real coordinate
actions.  This is the finite-dimensional `R² ↔ C` identity for an arbitrary
real matrix, before any spectral specialization. -/
theorem complexifyRealMatrix_mulVec_packageRealVector
    {m n : Type*} [Fintype n]
    (A : Matrix m n ℝ) (x y : n → ℝ) :
    Matrix.mulVec (complexifyRealMatrix A) (packageRealVector x y) =
      packageRealVector (Matrix.mulVec A x) (Matrix.mulVec A y) := by
  funext i
  apply Complex.ext <;>
    simp [complexifyRealMatrix, packageRealVector, Matrix.mulVec, dotProduct]

/-- A symmetric real matrix becomes a Hermitian complex matrix under the
canonical scalar extension. -/
theorem complexifyRealMatrix_isHermitian
    {n : Type*} {A : Matrix n n ℝ} (hA : A.IsSymm) :
    (complexifyRealMatrix A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simpa [complexifyRealMatrix] using
    congrArg Complex.ofReal (hA.apply i j)

/-- The positive finite height operator in complex Hilbert coordinates. -/
def complexifiedFiniteHeightOperator
    {N : ℕ} {jacobi : Matrix (Fin N) (Fin N) ℝ}
    (hjacobi : jacobi.PosDef) : Matrix (Fin N) (Fin N) ℂ :=
  complexifyRealMatrix (finiteHeightOperator hjacobi)

/-- The complexified finite height operator acts on both real quadratures by
the original real height operator. -/
theorem complexifiedFiniteHeightOperator_mulVec_packageRealVector
    {N : ℕ} {jacobi : Matrix (Fin N) (Fin N) ℝ}
    (hjacobi : jacobi.PosDef) (x y : Fin N → ℝ) :
    Matrix.mulVec (complexifiedFiniteHeightOperator hjacobi)
        (packageRealVector x y) =
      packageRealVector
        (Matrix.mulVec (finiteHeightOperator hjacobi) x)
        (Matrix.mulVec (finiteHeightOperator hjacobi) y) := by
  exact complexifyRealMatrix_mulVec_packageRealVector
    (finiteHeightOperator hjacobi) x y

/-- The complex-coordinate finite height operator is exactly Hermitian. -/
theorem complexifiedFiniteHeightOperator_isHermitian
    {N : ℕ} {jacobi : Matrix (Fin N) (Fin N) ℝ}
    (hjacobi : jacobi.PosDef) :
    (complexifiedFiniteHeightOperator hjacobi).IsHermitian := by
  exact complexifyRealMatrix_isHermitian
    (finiteHeightOperator_isSymm hjacobi)

/-- Scalar extension preserves the complete characteristic polynomial of the
finite height operator. -/
theorem complexifiedFiniteHeightOperator_charpoly_map
    {N : ℕ} {jacobi : Matrix (Fin N) (Fin N) ℝ}
    (hjacobi : jacobi.PosDef) :
    (complexifiedFiniteHeightOperator hjacobi).charpoly =
      (finiteHeightOperator hjacobi).charpoly.map Complex.ofRealHom := by
  exact Matrix.charpoly_map (finiteHeightOperator hjacobi) Complex.ofRealHom

/-- Exact complex spectral readout: the roots are the same transformed Jacobi
eigenvalues, now regarded as complex scalars. -/
theorem complexifiedFiniteHeightOperator_charpoly
    {N : ℕ} {jacobi : Matrix (Fin N) (Fin N) ℝ}
    (hjacobi : jacobi.PosDef) :
    (complexifiedFiniteHeightOperator hjacobi).charpoly =
      ∏ i : Fin N,
        (Polynomial.X -
          Polynomial.C (finiteHeightEigenvalue hjacobi i : ℂ)) := by
  rw [complexifiedFiniteHeightOperator_charpoly_map,
    finiteHeightOperator_charpoly, Polynomial.map_prod]
  simp

/-- A real finite-height eigenpair is transported verbatim to the complex
operator. -/
theorem complexifiedFiniteHeightOperator_eigenpair_of_real
    {N : ℕ} {jacobi : Matrix (Fin N) (Fin N) ℝ}
    (hjacobi : jacobi.PosDef) (x : Fin N → ℝ) (lambda : ℝ)
    (hx : Matrix.mulVec (finiteHeightOperator hjacobi) x = lambda • x) :
    Matrix.mulVec (complexifiedFiniteHeightOperator hjacobi)
        (packageRealVector x 0) =
      (lambda : ℂ) • packageRealVector x 0 := by
  rw [complexifiedFiniteHeightOperator_mulVec_packageRealVector, hx]
  ext i
  simp [packageRealVector]

/-- The signed finite height operator in complex Hilbert coordinates. -/
def complexifiedCanonicalSignedFiniteHeightOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ) (hgram : (hankelGram moments N).PosDef)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  complexifyRealMatrix
    (canonicalSignedFiniteHeightOperator hrep N hgram hli)

/-- The canonical signed operator remains self-adjoint after passing from real
to complex coordinates. -/
theorem complexifiedCanonicalSignedFiniteHeightOperator_isHermitian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ) (hgram : (hankelGram moments N).PosDef)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    (complexifiedCanonicalSignedFiniteHeightOperator
      hrep N hgram hli).IsHermitian := by
  exact complexifyRealMatrix_isHermitian
    (canonicalSignedFiniteHeightOperator_isSymm hrep N hgram hli)

/-- The signed complex operator has exactly the scalar-extended real
characteristic polynomial. -/
theorem complexifiedCanonicalSignedFiniteHeightOperator_charpoly
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ) (hgram : (hankelGram moments N).PosDef)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    (complexifiedCanonicalSignedFiniteHeightOperator
        hrep N hgram hli).charpoly =
      (canonicalSignedFiniteHeightOperator
        hrep N hgram hli).charpoly.map Complex.ofRealHom := by
  exact Matrix.charpoly_map
    (canonicalSignedFiniteHeightOperator hrep N hgram hli)
    Complex.ofRealHom

/-- The complex signed finite-height operator is uniquely forced by the
completed native/Genuine logarithmic moment sequence.  Passing from the real
carrier to complex coordinates introduces no new operator-level choice. -/
theorem
    complexifiedCanonicalSignedFiniteHeightOperator_eq_of_completedNativeLogDerivativeMoments
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments moments' : ℕ → ℝ} {feature : ℕ → E}
    (hrel : IsCompletedNativeLogDerivativeMomentSequence moments)
    (hrel' : IsCompletedNativeLogDerivativeMomentSequence moments')
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (hrep' : IsShiftedMomentGramRepresentation moments' feature)
    (N : ℕ)
    (hgram : (hankelGram moments N).PosDef)
    (hgram' : (hankelGram moments' N).PosDef)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ)))
    (hli' : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    complexifiedCanonicalSignedFiniteHeightOperator hrep N hgram hli =
      complexifiedCanonicalSignedFiniteHeightOperator
        hrep' N hgram' hli' := by
  have hmoments := hrel.unique hrel'
  subst moments'
  rfl

end

end CarrySelfAdjointOperator
