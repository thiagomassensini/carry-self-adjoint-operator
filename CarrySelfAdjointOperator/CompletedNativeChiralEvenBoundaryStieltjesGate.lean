import CarrySelfAdjointOperator.CompletedNativeChiralBoundaryParityCoordinates
import CarrySelfAdjointOperator.CanonicalCompletedNativeStieltjesOperator

/-!
# Minimal limiting-boundary gate for the existing Stieltjes construction

The source expression and parity split are proved upstream without canonical
moments. Only their final identification is used here. This is an equivalence,
not a proof of the remaining strict sign and not a finite-step storage estimate.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate Matrix
noncomputable section
set_option autoImplicit false

private def crossQuadratic {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (u : Fin n → ℂ) : ℝ := ∑ i, ∑ j, M i j * (conj (u i)*u j).re

private theorem crossQuadratic_real_imag {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (u : Fin n → ℂ) :
    crossQuadratic M u =
      star (fun i => (u i).re) ⬝ᵥ (M *ᵥ fun i => (u i).re) +
      star (fun i => (u i).im) ⬝ᵥ (M *ᵥ fun i => (u i).im) := by
  change (∑ i, ∑ j, M i j * (conj (u i)*u j).re) =
    (∑ i, (u i).re * ∑ j, M i j * (u j).re) +
    (∑ i, (u i).im * ∑ j, M i j * (u j).im)
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,neg_mul,sub_neg_eq_add,
    Finset.mul_sum,mul_add,Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

private theorem crossQuadratic_ofReal {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (u : Fin n → ℝ) :
    crossQuadratic M (fun i => (u i : ℂ)) = star u ⬝ᵥ (M *ᵥ u) := by
  simp only [crossQuadratic,dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,
    Finset.mul_sum,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    Complex.ofReal_re,Complex.ofReal_im,neg_zero,mul_zero,sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem crossQuadratic_nonneg {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosDef) (u : Fin n → ℂ) : 0 ≤ crossQuadratic M u := by
  rw [crossQuadratic_real_imag]
  exact add_nonneg (hM.posSemidef.dotProduct_mulVec_nonneg _)
    (hM.posSemidef.dotProduct_mulVec_nonneg _)

private theorem crossQuadratic_pos {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosDef) (u : Fin n → ℂ) (hu : u ≠ 0) : 0 < crossQuadratic M u := by
  rw [crossQuadratic_real_imag]
  by_cases hr : (fun i => (u i).re) = 0
  · have hi : (fun i => (u i).im) ≠ 0 := by
      intro hi
      apply hu
      funext i
      apply Complex.ext
      · exact congrFun hr i
      · exact congrFun hi i
    exact add_pos_of_nonneg_of_pos (hM.posSemidef.dotProduct_mulVec_nonneg _)
      (hM.dotProduct_mulVec_pos hi)
  · exact add_pos_of_pos_of_nonneg (hM.dotProduct_mulVec_pos hr)
      (hM.posSemidef.dotProduct_mulVec_nonneg _)

private theorem complex_cast_nonzero {n : ℕ} (u : Fin n → ℝ) (hu : u ≠ 0) :
    (fun i => (u i : ℂ)) ≠ 0 := by
  intro h
  apply hu
  funext i
  have hi := congrArg Complex.re (congrFun h i)
  simpa using hi

/-- Exactly the original raw even boundary sign, with no quantitative margin,
no uniform radial threshold, and no new HP or Hilbert realization premise. -/
theorem nativeSourceEvenBoundary_positive_iff_stieltjes :
    (∀ n : ℕ, 1 ≤ n → ∀ x : Fin (2*n) → ℂ, x ≠ 0 →
      0 < nativeSourceFiniteBoundaryEnergy (2*n) x) ↔
      CanonicalCompletedNativeStieltjesPositivity := by
  constructor
  · intro h n
    by_cases hn : n = 0
    · subst n
      constructor <;> apply Matrix.PosDef.of_dotProduct_mulVec_pos
      · exact Matrix.isHermitian_iff_isSymm.mpr (hankelGram_isSymm _ _)
      · intro u hu
        exact (hu (Subsingleton.elim _ _)).elim
      · exact Matrix.isHermitian_iff_isSymm.mpr (shiftedHankel_isSymm _ _)
      · intro u hu
        exact (hu (Subsingleton.elim _ _)).elim
    · have hn1 : 1 ≤ n := by omega
      have evenTest (u : Fin n → ℝ) (hu : u ≠ 0) :
          0 < star u ⬝ᵥ (hankelGram canonicalCompletedNativeLogDerivativeMoment n *ᵥ u) := by
        let y : Fin n → ℂ := fun i => (u i : ℂ)
        let x := nativeSourceBoundaryFromParity n y 0
        have hx : x ≠ 0 := by
          intro hx
          apply complex_cast_nonzero u hu
          have hy := nativeSourceEvenBoundaryPhase_fromParity n y 0
          rw [show nativeSourceBoundaryFromParity n y 0 = 0 from hx] at hy
          funext i
          simpa [nativeSourceEvenBoundaryPhase,y] using (congrFun hy i).symm
        have hp := h n hn1 x hx
        rw [nativeSourceFiniteBoundaryEnergy_even_split,
          nativeSourceEvenBoundaryPhase_fromParity,nativeSourceOddBoundaryPhase_fromParity] at hp
        simp only [Pi.zero_apply,starRingEnd_apply,star_zero,mul_zero,Complex.zero_re,
          Finset.sum_const_zero,add_zero] at hp
        change 0 < 4 * crossQuadratic (hankelGram primeDepthGeometricMoment n) y at hp
        rw [primeDepthGeometricMoment_eq_canonical,crossQuadratic_ofReal] at hp
        linarith
      have oddTest (u : Fin n → ℝ) (hu : u ≠ 0) :
          0 < star u ⬝ᵥ (shiftedHankel canonicalCompletedNativeLogDerivativeMoment n *ᵥ u) := by
        let z : Fin n → ℂ := fun i => (u i : ℂ)
        let x := nativeSourceBoundaryFromParity n 0 z
        have hx : x ≠ 0 := by
          intro hx
          apply complex_cast_nonzero u hu
          have hz := nativeSourceOddBoundaryPhase_fromParity n 0 z
          rw [show nativeSourceBoundaryFromParity n 0 z = 0 from hx] at hz
          funext i
          simpa [nativeSourceOddBoundaryPhase,z] using (congrFun hz i).symm
        have hp := h n hn1 x hx
        rw [nativeSourceFiniteBoundaryEnergy_even_split,
          nativeSourceEvenBoundaryPhase_fromParity,nativeSourceOddBoundaryPhase_fromParity] at hp
        simp only [Pi.zero_apply,starRingEnd_apply,star_zero,mul_zero,Complex.zero_re,
          Finset.sum_const_zero,zero_add] at hp
        change 0 < 4 * crossQuadratic (shiftedHankel primeDepthGeometricMoment n) z at hp
        rw [primeDepthGeometricMoment_eq_canonical,crossQuadratic_ofReal] at hp
        linarith
      exact ⟨Matrix.PosDef.of_dotProduct_mulVec_pos
        (Matrix.isHermitian_iff_isSymm.mpr (hankelGram_isSymm _ _)) evenTest,
        Matrix.PosDef.of_dotProduct_mulVec_pos
        (Matrix.isHermitian_iff_isSymm.mpr (shiftedHankel_isSymm _ _)) oddTest⟩
  · intro h n _ x hx
    rw [nativeSourceFiniteBoundaryEnergy_even_split]
    change 0 < 4 * (crossQuadratic (hankelGram primeDepthGeometricMoment n)
      (nativeSourceEvenBoundaryPhase n x) + crossQuadratic (shiftedHankel primeDepthGeometricMoment n)
      (nativeSourceOddBoundaryPhase n x))
    rw [primeDepthGeometricMoment_eq_canonical]
    obtain he | ho := nativeSourceBoundaryPhase_nonzero n x hx
    · exact mul_pos (by norm_num) (add_pos_of_pos_of_nonneg
        (crossQuadratic_pos (h n).1 _ he) (crossQuadratic_nonneg (h n).2 _))
    · exact mul_pos (by norm_num) (add_pos_of_nonneg_of_pos
        (crossQuadratic_nonneg (h n).1 _) (crossQuadratic_pos (h n).2 _ ho))
end
end CarrySelfAdjointOperator
