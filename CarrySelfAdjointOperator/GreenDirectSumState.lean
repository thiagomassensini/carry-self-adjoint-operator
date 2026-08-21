import CarrySelfAdjointOperator.GreenWronskianRecomposition
import Mathlib.Analysis.InnerProductSpace.PiL2
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

/-- Binary Hilbert direct sum, represented as an `L²` dependent product over
two singleton summands. -/
abbrev BinaryHilbertSum
    (H_A H_G : Type*)
    [NormedAddCommGroup H_A] [InnerProductSpace ℂ H_A]
    [NormedAddCommGroup H_G] [InnerProductSpace ℂ H_G] :=
  PiLp 2 (Sum.elim (fun _ : Unit ↦ H_A) (fun _ : Unit ↦ H_G))

/-- Weighted direct-sum state dictated by the exact Green product rule. -/
def weightedProductGreenState
    {H_A H_G : Type*}
    [NormedAddCommGroup H_A] [InnerProductSpace ℂ H_A]
    [NormedAddCommGroup H_G] [InnerProductSpace ℂ H_G]
    (A G : ℂ → ℂ) (stateA : ℂ → H_A) (stateG : ℂ → H_G)
    (z : ℂ) : BinaryHilbertSum H_A H_G :=
  WithLp.toLp 2 fun i ↦
    match i with
    | Sum.inl _ => G z • stateA z
    | Sum.inr _ => A z • stateG z

@[simp] theorem weightedProductGreenState_inl
    {H_A H_G : Type*}
    [NormedAddCommGroup H_A] [InnerProductSpace ℂ H_A]
    [NormedAddCommGroup H_G] [InnerProductSpace ℂ H_G]
    (A G : ℂ → ℂ) (stateA : ℂ → H_A) (stateG : ℂ → H_G)
    (z : ℂ) (u : Unit) :
    weightedProductGreenState A G stateA stateG z (Sum.inl u) =
      G z • stateA z :=
  rfl

@[simp] theorem weightedProductGreenState_inr
    {H_A H_G : Type*}
    [NormedAddCommGroup H_A] [InnerProductSpace ℂ H_A]
    [NormedAddCommGroup H_G] [InnerProductSpace ℂ H_G]
    (A G : ℂ → ℂ) (stateA : ℂ → H_A) (stateG : ℂ → H_G)
    (z : ℂ) (u : Unit) :
    weightedProductGreenState A G stateA stateG z (Sum.inr u) =
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
  rw [PiLp.inner_apply]
  simp [weightedProductGreenState, inner_smul_left, inner_smul_right] <;>
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
  have hcoordinate := congrArg
    (fun x : BinaryHilbertSum H_A H_G ↦ x (Sum.inr ())) hzero
  simp only [weightedProductGreenState_inr, PiLp.zero_apply] at hcoordinate
  exact (smul_ne_zero hA hstateG) hcoordinate

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
