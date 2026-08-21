import CarrySelfAdjointOperator.GreenWronskianRecomposition
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

/-!
# Hilbert direct-sum realization of a completed product

The scalar product rule for the Green Wronskian has a canonical state-level
realization.  If `A` and `G` have Green states `a_z` and `g_z`, then `A * G`
is represented by the weighted Hilbert direct sum

`G(z) a_z ⊕ A(z) g_z`.

This is the lossless version of multiplicative completion: the two channels
remain separate until the final inner product is taken.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- Binary Hilbert direct sum, represented by the `L²` norm on a product. -/
abbrev BinaryHilbertSum
    (H_A H_G : Type*)
    [NormedAddCommGroup H_A] [InnerProductSpace ℂ H_A]
    [NormedAddCommGroup H_G] [InnerProductSpace ℂ H_G] :=
  WithLp 2 (H_A × H_G)

/-- Weighted direct-sum state dictated by the exact Green product rule. -/
def weightedProductGreenState
    {H_A H_G : Type*}
    [NormedAddCommGroup H_A] [InnerProductSpace ℂ H_A]
    [NormedAddCommGroup H_G] [InnerProductSpace ℂ H_G]
    (A G : ℂ → ℂ) (stateA : ℂ → H_A) (stateG : ℂ → H_G)
    (z : ℂ) : BinaryHilbertSum H_A H_G :=
  WithLp.toLp 2 (G z • stateA z, A z • stateG z)

@[simp] theorem weightedProductGreenState_fst
    {H_A H_G : Type*}
    [NormedAddCommGroup H_A] [InnerProductSpace ℂ H_A]
    [NormedAddCommGroup H_G] [InnerProductSpace ℂ H_G]
    (A G : ℂ → ℂ) (stateA : ℂ → H_A) (stateG : ℂ → H_G)
    (z : ℂ) :
    (WithLp.ofLp (weightedProductGreenState A G stateA stateG z)).1 =
      G z • stateA z :=
  rfl

@[simp] theorem weightedProductGreenState_snd
    {H_A H_G : Type*}
    [NormedAddCommGroup H_A] [InnerProductSpace ℂ H_A]
    [NormedAddCommGroup H_G] [InnerProductSpace ℂ H_G]
    (A G : ℂ → ℂ) (stateA : ℂ → H_A) (stateG : ℂ → H_G)
    (z : ℂ) :
    (WithLp.ofLp (weightedProductGreenState A G stateA stateG z)).2 =
      A z • stateG z :=
  rfl

/-- The direct-sum Gram is exactly the sum of the two weighted channel
Grams. -/
theorem inner_weightedProductGreenState
    {H_A H_G : Type*}
    [NormedAddCommGroup H_A] [InnerProductSpace ℂ H_A]
    [NormedAddCommGroup H_G] [InnerProductSpace ℂ H_G]
    (A G : ℂ → ℂ) (stateA : ℂ → H_A) (stateG : ℂ → H_G)
    (z w : ℂ) :
    inner ℂ
        (weightedProductGreenState A G stateA stateG w)
        (weightedProductGreenState A G stateA stateG z) =
      (starRingEnd ℂ) (G w) * G z * inner ℂ (stateA w) (stateA z) +
        (starRingEnd ℂ) (A w) * A z * inner ℂ (stateG w) (stateG z) := by
  rw [WithLp.prod_inner_apply]
  simp only [weightedProductGreenState, WithLp.ofLp_toLp,
    inner_smul_left, inner_smul_right]
  ring

/-- A nonzero second-factor state survives multiplicative completion whenever
the completion factor is nonzero.  In particular, at a zero of `G` only the
first summand disappears; the provenance carried by `stateG` remains in the
second summand. -/
theorem weightedProductGreenState_ne_zero_of_right
    {H_A H_G : Type*}
    [NormedAddCommGroup H_A] [InnerProductSpace ℂ H_A]
    [NormedAddCommGroup H_G] [InnerProductSpace ℂ H_G]
    (A G : ℂ → ℂ) (stateA : ℂ → H_A) (stateG : ℂ → H_G)
    {z : ℂ} (hA : A z ≠ 0) (hstateG : stateG z ≠ 0) :
    weightedProductGreenState A G stateA stateG z ≠ 0 := by
  intro hzero
  have hpair : (G z • stateA z, A z • stateG z) = 0 := by
    exact (WithLp.toLp_eq_zero 2).mp hzero
  have hright : A z • stateG z = 0 :=
    congrArg Prod.snd hpair
  rcases smul_eq_zero.mp hright with hscalar | hstate
  · exact hA hscalar
  · exact hstateG hstate

/-- Two division-free Green representations combine canonically into a
division-free Green representation of their product, with no mixed-channel
projection or choice of inverse. -/
theorem HasDivisionFreeGreenRepresentation.mul
    {H_A H_G : Type*}
    [NormedAddCommGroup H_A] [InnerProductSpace ℂ H_A]
    [NormedAddCommGroup H_G] [InnerProductSpace ℂ H_G]
    {A PsiA G PsiG : ℂ → ℂ}
    {stateA : ℂ → H_A} {stateG : ℂ → H_G}
    (hA : HasDivisionFreeGreenRepresentation A PsiA stateA)
    (hG : HasDivisionFreeGreenRepresentation G PsiG stateG) :
    HasDivisionFreeGreenRepresentation
      (fun z ↦ A z * G z)
      (productBoundaryCompanion A PsiA G PsiG)
      (weightedProductGreenState A G stateA stateG) := by
  intro z w
  rw [completedGreenWronskian_mul, hA z w, hG z w,
    inner_weightedProductGreenState]
  ring

end

end CarrySelfAdjointOperator
