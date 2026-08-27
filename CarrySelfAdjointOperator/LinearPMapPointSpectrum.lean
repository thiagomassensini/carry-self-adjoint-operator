import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

/-!
# Point spectrum of partial Hilbert-space operators

This file supplies the minimal domain-sensitive eigenvalue predicate needed
for unbounded `LinearPMap`s.  It also records that every eigenvalue of a
complex self-adjoint partial operator is real.
-/

open scoped ComplexConjugate LinearPMap

namespace LinearPMap

noncomputable section

/-- A scalar is an eigenvalue of a partial operator when a nonzero vector in
the natural domain satisfies the eigenvalue equation. -/
def HasEigenvalue
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ.[ℂ] E) (mu : ℂ) : Prop :=
  ∃ x : A.domain, (x : E) ≠ 0 ∧ A x = mu • (x : E)

/-- Every eigenvalue of a complex self-adjoint partial operator is fixed by
complex conjugation. -/
theorem conj_eigenvalue_eq_self_of_isSelfAdjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {A : E →ₗ.[ℂ] E} {mu : ℂ}
    (hA : IsSelfAdjoint A) (hmu : HasEigenvalue A mu) :
    (starRingEnd ℂ) mu = mu := by
  obtain ⟨x, hx, hAx⟩ := hmu
  have hformal : A.IsFormalAdjoint A := by
    have hadjoint := A.adjoint_isFormalAdjoint hA.dense_domain
    rw [LinearPMap.isSelfAdjoint_def.mp hA] at hadjoint
    exact hadjoint
  have hinner := hformal x x
  rw [hAx, inner_smul_left, inner_smul_right] at hinner
  have hnorm : inner ℂ (x : E) (x : E) ≠ 0 := inner_self_ne_zero.mpr hx
  exact mul_right_cancel₀ hnorm hinner

/-- Point-spectrum form of spectral reality for a self-adjoint partial
operator. -/
theorem eigenvalue_im_eq_zero_of_isSelfAdjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {A : E →ₗ.[ℂ] E} {mu : ℂ}
    (hA : IsSelfAdjoint A) (hmu : HasEigenvalue A mu) :
    mu.im = 0 := by
  have hconj := conj_eigenvalue_eq_self_of_isSelfAdjoint hA hmu
  have him := congrArg Complex.im hconj
  rw [Complex.conj_im] at him
  linarith

end


end LinearPMap
