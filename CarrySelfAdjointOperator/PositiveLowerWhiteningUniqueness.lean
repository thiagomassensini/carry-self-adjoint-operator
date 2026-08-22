import CarrySelfAdjointOperator.CanonicalLDLWhitening
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Tactic

/-!
# Positive lower whitening uniqueness

The normalized inverse LDL factor is the inverse Cholesky factor selected by
three intrinsic properties:

* lower triangularity;
* strictly positive diagonal;
* exact whitening `B G Bᵀ = I`.

This module develops that characterization.  Its first step records the unit
diagonal hidden inside Mathlib's unnormalized `LDL.lowerInv`; after the
positive diagonal rescaling, the canonical whitening therefore has strictly
positive diagonal entries.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- Mathlib's inverse LDL factor is unit lower triangular.  The library
already exposes the strict upper-triangular zeros; this theorem records the
missing diagonal normalization forced by Gram--Schmidt on the standard basis. -/
theorem LDL_lowerInv_diag_eq_one
    {N : ℕ} {gram : Matrix (Fin N) (Fin N) ℝ}
    (hgram : gram.PosDef) (i : Fin N) :
    LDL.lowerInv hgram i i = 1 := by
  letI := gram.transpose.toNormedAddCommGroup hgram.transpose
  letI := gram.transpose.toInnerProductSpace hgram.transpose.posSemidef
  let gs : Fin N → (Fin N → ℝ) :=
    InnerProductSpace.gramSchmidt ℝ (Pi.basisFun ℝ (Fin N))
  let coeff : Fin N → ℝ := fun k =>
    inner ℝ (gs k) (Pi.basisFun ℝ (Fin N) i) /
      (‖gs k‖ : ℝ) ^ 2
  have hdecomp :
      Pi.basisFun ℝ (Fin N) i =
        gs i + ∑ k ∈ Finset.Iio i, coeff k • gs k := by
    simpa [gs, coeff] using
      (InnerProductSpace.gramSchmidt_def'' ℝ
        (Pi.basisFun ℝ (Fin N)) i)
  have hzero : ∀ k : Fin N, k < i → gs k i = 0 := by
    intro k hki
    simpa [gs, LDL.lowerInv] using
      (LDL.lowerInv_triangular hgram hki)
  have hsum :
      (∑ k ∈ Finset.Iio i, coeff k • gs k) i = 0 := by
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have hki : k < i := Finset.mem_Iio.mp hk
    simp [hzero k hki]
  have hcoord := congrArg (fun v : Fin N → ℝ => v i) hdecomp
  simp only [Pi.add_apply] at hcoord
  rw [hsum, add_zero] at hcoord
  have hbasis : (Pi.basisFun ℝ (Fin N) i) i = 1 := by simp
  rw [hbasis] at hcoord
  simpa [gs, LDL.lowerInv] using hcoord.symm

/-- Pointwise diagonal formula for the normalized inverse LDL factor. -/
theorem canonicalLDLInverseFactor_diag
    {N : ℕ} {gram : Matrix (Fin N) (Fin N) ℝ}
    (hgram : gram.PosDef) (i : Fin N) :
    canonicalLDLInverseFactor hgram i i =
      canonicalLDLScale hgram i := by
  simp [canonicalLDLInverseFactor, Matrix.mul_apply,
    LDL_lowerInv_diag_eq_one hgram i]

/-- The canonical normalized inverse LDL factor has strictly positive
entries on its diagonal. -/
theorem canonicalLDLInverseFactor_diag_pos
    {N : ℕ} {gram : Matrix (Fin N) (Fin N) ℝ}
    (hgram : gram.PosDef) (i : Fin N) :
    0 < canonicalLDLInverseFactor hgram i i := by
  rw [canonicalLDLInverseFactor_diag hgram i]
  exact canonicalLDLScale_pos hgram i

/-- Intrinsic certificate for the normalized inverse Cholesky/LDL factor. -/
def IsPositiveLowerWhitening
    {N : ℕ} (gram factor : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ ⦃i j : Fin N⦄, i < j → factor i j = 0) ∧
    (∀ i : Fin N, 0 < factor i i) ∧
      finiteJacobiTransport factor gram = 1

/-- The canonical inverse LDL factor satisfies the intrinsic whitening
certificate. -/
theorem canonicalLDLInverseFactor_isPositiveLowerWhitening
    {N : ℕ} {gram : Matrix (Fin N) (Fin N) ℝ}
    (hgram : gram.PosDef) :
    IsPositiveLowerWhitening gram (canonicalLDLInverseFactor hgram) := by
  refine ⟨?_, ?_, canonicalLDLInverseFactor_whitens hgram⟩
  · intro i j hij
    exact canonicalLDLInverseFactor_triangular hgram hij
  · exact canonicalLDLInverseFactor_diag_pos hgram

end

end CarrySelfAdjointOperator
