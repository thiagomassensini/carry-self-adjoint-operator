import CarrySelfAdjointOperator.CompletedGreenJetCoefficientRecurrence
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Green-kernel coefficient closure

The concrete Green state is not assumed to take values in a complete space,
and its pointwise Gram identity does not by itself license Hilbert-valued
Taylor differentiation.  The coefficient extraction can instead be carried
out without differentiating the state:

* form normalized forward differences from finitely many state values;
* every finite section is an honest Gram matrix;
* identify the entrywise scalar limit from the Green kernel; and
* use closedness of the positive-semidefinite cone.

This file formalizes the two structural ends of that argument.  It defines
the canonical forward-difference jets and proves that their entrywise Gram
limit gives both Hankel positivity towers.  The remaining analytic task is
now the scalar convergence of those Gram entries.  No Hilbert-valued
analyticity assumption on the original state realization is needed, but the
real-axis diagonal of its scalar kernel must still be controlled: the
division-free Green identity degenerates there.
-/

namespace CarrySelfAdjointOperator

open Filter Topology

noncomputable section

/-- Canonical nonzero real-axis step, viewed in `ℂ`.  Its only role is to
approach the centered origin through points on the real axis. -/
def canonicalGreenJetStep (k : ℕ) : ℂ :=
  (((k : ℂ) + 1)⁻¹)

theorem canonicalGreenJetStep_tendsto_zero :
    Tendsto canonicalGreenJetStep atTop (nhds 0) := by
  change Tendsto (fun k : ℕ ↦ (((k : ℂ) + 1)⁻¹)) atTop (nhds 0)
  simpa [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))

/-- One forward difference of a state-valued function. -/
def completedGreenForwardDifference
    {E : Type*} [AddCommGroup E]
    (h : ℂ) (state : ℂ → E) : ℂ → E :=
  fun z ↦ state (z + h) - state z

/-- The iterated forward difference is an explicit finite linear combination
of sampled state values.  This makes the later positivity argument genuinely
pointwise: no derivative or completion of the state space is hidden here. -/
theorem completedGreenForwardDifference_iter_eq_sum_shift
    {E : Type*} [AddCommGroup E]
    (h : ℂ) (state : ℂ → E) (n : ℕ) (z : ℂ) :
    (completedGreenForwardDifference h)^[n] state z =
      ∑ k ∈ Finset.range (n + 1),
        ((-1 : ℤ) ^ (n - k) * n.choose k) •
          state (z + k • h) := by
  change (fwdDiff h)^[n] state z = _
  exact fwdDiff_iter_eq_sum_shift h state n z

/-- Forward differences commute with an inner product in the second slot. -/
theorem completedGreenForwardDifference_iter_inner_right
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (h : ℂ) (state : ℂ → E) (x : E) (n : ℕ) :
    (completedGreenForwardDifference h)^[n]
        (fun z ↦ inner ℂ x (state z)) =
      fun z ↦ inner ℂ x ((completedGreenForwardDifference h)^[n] state z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      funext z
      simp [completedGreenForwardDifference, inner_sub_right]

/-- Forward differences commute with an inner product in the first slot. -/
theorem completedGreenForwardDifference_iter_inner_left
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (h : ℂ) (state : ℂ → E) (y : E) (n : ℕ) :
    (completedGreenForwardDifference h)^[n]
        (fun z ↦ inner ℂ (state z) y) =
      fun z ↦ inner ℂ ((completedGreenForwardDifference h)^[n] state z) y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      funext z
      simp [completedGreenForwardDifference, inner_sub_left]

/-- Mixed scalar forward differences of a point-state kernel are exactly the
inner product of the corresponding state forward differences. -/
theorem completedGreenKernel_mixedForwardDifference_eq_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (state : ℂ → E) (h : ℂ) (p q : ℕ) :
    (completedGreenForwardDifference h)^[p]
        (fun w ↦ (completedGreenForwardDifference h)^[q]
          (fun z ↦ inner ℂ (state w) (state z)) 0) 0 =
      inner ℂ
        ((completedGreenForwardDifference h)^[p] state 0)
        ((completedGreenForwardDifference h)^[q] state 0) := by
  have hright :
      (fun w ↦ (completedGreenForwardDifference h)^[q]
        (fun z ↦ inner ℂ (state w) (state z)) 0) =
      (fun w ↦ inner ℂ (state w)
        ((completedGreenForwardDifference h)^[q] state 0)) := by
    funext w
    exact congrFun
      (completedGreenForwardDifference_iter_inner_right h state (state w) q) 0
  rw [hright]
  exact congrFun
    (completedGreenForwardDifference_iter_inner_left h state
      ((completedGreenForwardDifference h)^[q] state 0) p) 0

/-- Normalized mixed forward difference of a scalar two-variable kernel. -/
def completedGreenKernelForwardDifference
    (kernel : ℂ → ℂ → ℂ) (h : ℂ) (p q : ℕ) : ℂ :=
  (starRingEnd ℂ) (((Nat.factorial p : ℂ) * h ^ p)⁻¹) *
    (((Nat.factorial q : ℂ) * h ^ q)⁻¹) *
      (completedGreenForwardDifference h)^[p]
        (fun w ↦ (completedGreenForwardDifference h)^[q] (kernel w) 0) 0

/-- The normalized order-`n` forward difference at the centered origin.
The factor `n! * h^n` is exactly the Taylor-coefficient normalization. -/
def completedGreenForwardDifferenceJet
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (state : ℂ → E) (h : ℂ) (n : ℕ) : E :=
  (((Nat.factorial n : ℂ) * h ^ n)⁻¹) •
    (completedGreenForwardDifference h)^[n] state 0

/-- The normalized finite-difference Gram entry is literally the normalized
mixed finite difference of the scalar point-state kernel. -/
theorem inner_completedGreenForwardDifferenceJet_eq_kernelForwardDifference
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (state : ℂ → E) (h : ℂ) (p q : ℕ) :
    inner ℂ
        (completedGreenForwardDifferenceJet state h p)
        (completedGreenForwardDifferenceJet state h q) =
      completedGreenKernelForwardDifference
        (fun w z ↦ inner ℂ (state w) (state z)) h p q := by
  unfold completedGreenForwardDifferenceJet completedGreenKernelForwardDifference
  rw [inner_smul_left, inner_smul_right,
    completedGreenKernel_mixedForwardDifference_eq_inner]
  ring

/-- Even and odd forward-difference jets, sampled at the canonical steps. -/
def completedGreenForwardDifferenceParityJet
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (state : ℂ → E) (k : ℕ) : (ℕ ⊕ ℕ) → E
  | Sum.inl n =>
      completedGreenForwardDifferenceJet state
        (canonicalGreenJetStep k) (2 * n)
  | Sum.inr n =>
      completedGreenForwardDifferenceJet state
        (canonicalGreenJetStep k) (2 * n + 1)

/-- Scalar limit statement left by coefficient extraction.  It only speaks
about inner products of finite linear combinations of point states.  In
particular, it does not assume that the state itself is differentiable or
that its ambient inner-product space is complete.  Proving this limit still
requires a scalar diagonal regularity or minimality statement in addition to
the off-diagonal Green relation. -/
def HasCompletedGreenForwardDifferenceGramLimit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (moments : ℕ → ℝ) (state : ℂ → E) : Prop :=
  ∀ i j : ℕ ⊕ ℕ,
    Tendsto
      (fun k ↦ (inner ℂ
        (completedGreenForwardDifferenceParityJet state k i)
        (completedGreenForwardDifferenceParityJet state k j)).re)
      atTop (nhds (greenWronskianMomentKernel moments i j))

/-- A pointwise limit of real positive-semidefinite matrices is positive
semidefinite.  The proof uses finite support in the defining quadratic form,
so no finite-dimensional norm equivalence is required. -/
theorem matrixPosSemidef_of_tendsto_entrywise
    {n : Type*} [Finite n]
    {A : ℕ → Matrix n n ℝ} {M : Matrix n n ℝ}
    (hA : ∀ k, (A k).PosSemidef)
    (hlim : ∀ i j, Tendsto (fun k ↦ A k i j) atTop (nhds (M i j))) :
    M.PosSemidef := by
  have hMatrix : Tendsto A atTop (nhds M) :=
    tendsto_pi_nhds.2 fun i ↦ tendsto_pi_nhds.2 fun j ↦ hlim i j
  refine ⟨?_, fun x ↦ ?_⟩
  · ext i j
    have heq : (fun k ↦ A k j i) = fun k ↦ A k i j := by
      funext k
      simpa using ((hA k).isHermitian.apply j i).symm
    exact tendsto_nhds_unique (heq ▸ hlim j i) (hlim i j)
  · let q : Matrix n n ℝ → ℝ := fun B ↦
      x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * B i j * xj
    have hqcont : Continuous q := by
      unfold q
      change Continuous (fun (B : Matrix n n ℝ) ↦
        ∑ i ∈ x.support, ∑ j ∈ x.support, star (x i) * B i j * x j)
      fun_prop
    have hq : Tendsto (fun k ↦ q (A k)) atTop (nhds (q M)) :=
      hqcont.continuousAt.tendsto.comp hMatrix
    exact isClosed_Ici.mem_of_tendsto hq
      (Filter.Eventually.of_forall fun k ↦ (hA k).2 x)

/-- Entrywise limits of two families of finite Gram matrices give the
unshifted and shifted Hankel positivity sections simultaneously. -/
theorem hankelPair_posSemidef_of_gramLimits
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} (N : ℕ)
    (evenApprox oddApprox : ℕ → Fin N → E)
    (heven : ∀ i j : Fin N,
      Tendsto (fun k ↦ inner ℝ (evenApprox k i) (evenApprox k j))
        atTop (nhds (moments ((i : ℕ) + (j : ℕ)))))
    (hodd : ∀ i j : Fin N,
      Tendsto (fun k ↦ inner ℝ (oddApprox k i) (oddApprox k j))
        atTop (nhds (moments ((i : ℕ) + (j : ℕ) + 1)))) :
    (hankelGram moments N).PosSemidef ∧
      (shiftedHankel moments N).PosSemidef := by
  constructor
  · apply matrixPosSemidef_of_tendsto_entrywise
      (A := fun k ↦ Matrix.gram ℝ (evenApprox k))
    · exact fun k ↦ Matrix.posSemidef_gram ℝ (evenApprox k)
    · intro i j
      simpa [Matrix.gram_apply] using heven i j
  · apply matrixPosSemidef_of_tendsto_entrywise
      (A := fun k ↦ Matrix.gram ℝ (oddApprox k))
    · exact fun k ↦ Matrix.posSemidef_gram ℝ (oddApprox k)
    · intro i j
      simpa [Matrix.gram_apply] using hodd i j

/-- The forward-difference coefficient limit is sufficient for every finite
Hankel order.  Positivity is inherited from finite state-value Gram matrices
and closedness; Hilbert-valued Taylor jets are not used. -/
theorem hankelPair_posSemidef_of_completedGreenForwardDifferenceGramLimit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {moments : ℕ → ℝ} {state : ℂ → E}
    (hlimit : HasCompletedGreenForwardDifferenceGramLimit moments state)
    (N : ℕ) :
    (hankelGram moments N).PosSemidef ∧
      (shiftedHankel moments N).PosSemidef := by
  letI : InnerProductSpace ℝ E :=
    InnerProductSpace.rclikeToReal ℂ E
  apply hankelPair_posSemidef_of_gramLimits N
      (fun k i ↦ completedGreenForwardDifferenceParityJet state k (Sum.inl i))
      (fun k i ↦ completedGreenForwardDifferenceParityJet state k (Sum.inr i))
  · intro i j
    change Tendsto
      (fun k ↦ (inner ℂ
        (completedGreenForwardDifferenceParityJet state k (Sum.inl i))
        (completedGreenForwardDifferenceParityJet state k (Sum.inl j))).re)
      atTop (nhds (moments ((i : ℕ) + (j : ℕ))))
    simpa [greenWronskianMomentKernel] using hlimit (Sum.inl i) (Sum.inl j)
  · intro i j
    change Tendsto
      (fun k ↦ (inner ℂ
        (completedGreenForwardDifferenceParityJet state k (Sum.inr i))
        (completedGreenForwardDifferenceParityJet state k (Sum.inr j))).re)
      atTop (nhds (moments ((i : ℕ) + (j : ℕ) + 1)))
    simpa [greenWronskianMomentKernel] using hlimit (Sum.inr i) (Sum.inr j)

end

end CarrySelfAdjointOperator
