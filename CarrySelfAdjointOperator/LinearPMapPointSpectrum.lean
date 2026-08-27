import CarrySelfAdjointOperator.RealLinearPMapComplexification
import Mathlib.Tactic

/-!
# Point spectrum of partial Hilbert-space operators

This file supplies the minimal domain-sensitive eigenvalue predicate needed
for unbounded `LinearPMap`s.  It also records that every eigenvalue of a
complex self-adjoint partial operator is real.
-/

open scoped ComplexConjugate LinearPMap
open CarrySelfAdjointOperator.RealHilbertComplexification

namespace LinearPMap

noncomputable section

/-- A real scalar is a point eigenvalue of a real partial operator when the
natural domain contains a nonzero eigenvector. -/
def HasRealEigenvalue
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →ₗ.[ℝ] E) (mu : ℝ) : Prop :=
  ∃ x : A.domain, (x : E) ≠ 0 ∧ A x = mu • (x : E)

/-- A scalar is an eigenvalue of a partial operator when a nonzero vector in
the natural domain satisfies the eigenvalue equation. -/
def HasEigenvalue
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ.[ℂ] E) (mu : ℂ) : Prop :=
  ∃ x : A.domain, (x : E) ≠ 0 ∧ A x = mu • (x : E)

/-- A real point eigenvector embeds in the zero-imaginary quadrature of the
canonical complexification, with the same eigenvalue. -/
theorem complexification_hasEigenvalue_of_hasRealEigenvalue
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A : E →ₗ.[ℝ] E} {mu : ℝ}
    (hmu : HasRealEigenvalue A mu) :
    HasEigenvalue A.complexification (mu : ℂ) := by
  obtain ⟨x, hx, hAx⟩ := hmu
  let xc : A.complexification.domain :=
    ⟨CarrySelfAdjointOperator.RealHilbertComplexification.mk (x : E) 0,
      ⟨x.property, A.domain.zero_mem⟩⟩
  have hxcRe : A.complexificationDomainRe xc = x := by
    apply Subtype.ext
    rfl
  have hxcIm : A.complexificationDomainIm xc = 0 := by
    apply Subtype.ext
    rfl
  refine ⟨xc, ?_, ?_⟩
  · intro hzero
    have hre := congrArg
      CarrySelfAdjointOperator.RealHilbertComplexification.re hzero
    exact hx (by simpa [xc] using hre)
  · apply CarrySelfAdjointOperator.RealHilbertComplexification.ext
    · rw [re_complexification_apply, hxcRe]
      rw [re_smul]
      simpa [xc] using hAx
    · rw [im_complexification_apply, hxcIm, A.map_zero]
      rw [im_smul]
      simp [xc]

/-- At a real eigenvalue, a point eigenvector of the complexification yields
a nonzero real or imaginary quadrature eigenvector of the original real
operator. Hence complexification neither creates nor loses real point
spectrum. -/
theorem hasRealEigenvalue_of_complexification_hasEigenvalue
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A : E →ₗ.[ℝ] E} {mu : ℝ}
    (hmu : HasEigenvalue A.complexification (mu : ℂ)) :
    HasRealEigenvalue A mu := by
  obtain ⟨x, hx, hAx⟩ := hmu
  let xr : A.domain := A.complexificationDomainRe x
  let xi : A.domain := A.complexificationDomainIm x
  have hAr : A xr = mu • (xr : E) := by
    have hre := congrArg re hAx
    rw [re_smul] at hre
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero] at hre
    exact hre
  have hAi : A xi = mu • (xi : E) := by
    have him := congrArg im hAx
    rw [im_smul] at him
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_smul, zero_add] at him
    exact him
  by_cases hxr : (xr : E) = 0
  · have hxi : (xi : E) ≠ 0 := by
      intro hxi
      apply hx
      apply CarrySelfAdjointOperator.RealHilbertComplexification.ext
      · exact hxr
      · exact hxi
    exact ⟨xi, hxi, hAi⟩
  · exact ⟨xr, hxr, hAr⟩

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

/-- A point eigenvalue of a positive real partial operator is nonnegative. -/
theorem realEigenvalue_nonneg_of_inner_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A : E →ₗ.[ℝ] E} {mu : ℝ}
    (hpositive : ∀ x : A.domain,
      0 ≤ inner ℝ (A x) (x : E))
    (hmu : HasRealEigenvalue A mu) :
    0 ≤ mu := by
  obtain ⟨x, hx, hAx⟩ := hmu
  have heq := congrArg (fun y : E => inner ℝ y (x : E)) hAx
  rw [real_inner_smul_left] at heq
  have hnormPos : 0 < inner ℝ (x : E) (x : E) :=
    real_inner_self_pos.mpr hx
  nlinarith [hpositive x]

/-- The complexification of a positive maximal real self-adjoint operator
has real nonnegative point spectrum. -/
theorem RealMaximalSelfAdjointData.complexification_eigenvalue_real_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (data : RealMaximalSelfAdjointData E)
    (hpositive : ∀ x : data.operator.domain,
      0 ≤ inner ℝ (data.operator x) (x : E))
    {mu : ℂ}
    (hmu : HasEigenvalue data.complexification mu) :
    mu.im = 0 ∧ 0 ≤ mu.re := by
  have him : mu.im = 0 :=
    eigenvalue_im_eq_zero_of_isSelfAdjoint
      data.complexification_isSelfAdjoint hmu
  have hmuEq : (mu.re : ℂ) = mu := by
    apply Complex.ext
    · simp
    · simp [him]
  have hrealComplex :
      HasEigenvalue data.complexification (mu.re : ℂ) := by
    rw [hmuEq]
    exact hmu
  have hreal : HasRealEigenvalue data.operator mu.re :=
    hasRealEigenvalue_of_complexification_hasEigenvalue hrealComplex
  exact ⟨him, realEigenvalue_nonneg_of_inner_nonneg hpositive hreal⟩

end


end LinearPMap
