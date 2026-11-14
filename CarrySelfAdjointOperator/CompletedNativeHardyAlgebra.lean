import CarrySelfAdjointOperator.GreenWronskianHankelBridge
import Mathlib.Tactic

/-!
# Hardy nonrecurrence: finite algebraic bridge

This file isolates the algebraic consequence of a global absence of finite
moment relations.  No positivity assumption is used.  A relation on any tail
is shifted back to the initial sequence by adjoining zero coefficients, and
a Gram representation then turns the absence of relations into independence
of its feature family.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- There is no nonzero finite coefficient family whose moment convolution
vanishes at every subsequent index.  The finite set records arbitrary finite
support; the function is required to vanish away from that set. -/
def NoFiniteMomentRelationAt (moments : ℕ → ℝ) (shift : ℕ) : Prop :=
  ∀ (s : Finset ℕ) (a : ℕ → ℝ),
    (∀ i, i ∉ s → a i = 0) →
    (∀ j : ℕ, ∑ i ∈ s, a i * moments (shift + i + j) = 0) →
    ∀ i, a i = 0

/-- Global absence of a finite relation, in the zero-shift case.  Equivalently,
for every `N` and `a : Fin N → ℝ`, vanishing of the convolution for every
`j : ℕ` forces `a = 0`. -/
abbrev NoFiniteMomentRelation (moments : ℕ → ℝ) : Prop :=
  NoFiniteMomentRelationAt moments 0

/-- A relation on the tail beginning at `shift + 1` becomes a relation on
the tail beginning at `shift` after inserting a zero coefficient at index
zero. -/
theorem noFiniteMomentRelationAt_succ_of_at
    {moments : ℕ → ℝ} {shift : ℕ}
    (hzero : NoFiniteMomentRelationAt moments shift) :
    NoFiniteMomentRelationAt moments (shift + 1) := by
  intro s a haSupport haRel i
  let s' := s.image Nat.succ
  let b : ℕ → ℝ := fun k => if hk : 1 ≤ k then a (k - 1) else 0
  have hbSupport : ∀ k, k ∉ s' → b k = 0 := by
    intro k hk
    by_cases hkOne : 1 ≤ k
    · have hnot : k - 1 ∉ s := by
        intro hmem
        apply hk
        exact Finset.mem_image.mpr ⟨k - 1, hmem, by omega⟩
      simp [b, hkOne, haSupport (k - 1) hnot]
    · simp [b, hkOne]
  have hbRel : ∀ j : ℕ, ∑ k ∈ s', b k * moments (shift + k + j) = 0 := by
    intro j
    have hinj : Set.InjOn Nat.succ (↑s : Set ℕ) := by
      intro x hx y hy hxy
      exact Nat.succ.inj hxy
    rw [Finset.sum_image hinj]
    have hsum :
        (∑ x ∈ s, b (Nat.succ x) * moments (shift + Nat.succ x + j)) =
          ∑ x ∈ s, a x * moments ((shift + 1) + x + j) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [b, Nat.add_left_comm, Nat.add_comm]
    rw [hsum]
    exact haRel j
  have hb := hzero s' b hbSupport hbRel
  simpa [b] using hb (i + 1)

/-- Zero-shift nonrecurrence implies nonrecurrence after any finite shift.
The proof inserts one leading zero at a time. -/
theorem noFiniteMomentRelationAt_of_noFiniteMomentRelation
    {moments : ℕ → ℝ} (hzero : NoFiniteMomentRelation moments)
    (shift : ℕ) : NoFiniteMomentRelationAt moments shift := by
  induction shift with
  | zero => simpa [NoFiniteMomentRelation] using hzero
  | succ shift ih =>
      simpa [Nat.succ_eq_add_one] using
        noFiniteMomentRelationAt_succ_of_at ih

/-- A global zero-shift relation statement can be expressed with finite
vectors indexed by `Fin N`; this is the form used by the moment sequences in
the analytic module. -/
theorem noFiniteMomentRelation_fin
    {moments : ℕ → ℝ} (hzero : NoFiniteMomentRelation moments)
    (N : ℕ) (a : Fin N → ℝ)
    (ha : ∀ j : ℕ, ∑ i : Fin N, a i * moments (i.val + j) = 0) :
    a = 0 := by
  let s := Finset.univ.image (fun i : Fin N => i.val)
  let b : ℕ → ℝ := fun k => if hk : k < N then a ⟨k, hk⟩ else 0
  have hs : ∀ k, k ∉ s → b k = 0 := by
    intro k hk
    by_cases hkn : k < N
    · have hmem : k ∈ s := by
        exact Finset.mem_image.mpr
          ⟨⟨k, hkn⟩, Finset.mem_univ _, rfl⟩
      exact (hk hmem).elim
    · simp [b, hkn]
  have hrel : ∀ j : ℕ, ∑ k ∈ s, b k * moments (k + j) = 0 := by
    intro j
    rw [Finset.sum_image (by
      intro i hi i' hi' heq
      exact Fin.ext heq)]
    have hsum :
        (∑ i : Fin N, b i.val * moments (i.val + j)) =
          ∑ i : Fin N, a i * moments (i.val + j) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [b]
    rw [hsum]
    simpa [Nat.zero_add] using ha j
  have hb := hzero s b hs (by
    intro j
    simpa [Nat.zero_add] using hrel j)
  funext i
  have hi := hb i.val
  simpa [b] using hi

/-- A finite Gram family with moments `h_(shift+i+j)` is linearly independent
when that shifted moment sequence has no finite global relation. -/
theorem linearIndependent_of_noFiniteMomentRelationAt_of_gram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {shift : ℕ} {feature : ℕ → E}
    (hno : NoFiniteMomentRelationAt moments shift)
    (hgram : ∀ i j : ℕ,
      moments (shift + i + j) = Matrix.gram ℝ feature i j) :
    LinearIndependent ℝ feature := by
  rw [linearIndependent_iff']
  intro s a hsum i hi
  let a' : ℕ → ℝ := fun k => if k ∈ s then a k else 0
  have haSupport : ∀ k, k ∉ s → a' k = 0 := by
    intro k hk
    simp [a', hk]
  have hrel : ∀ j : ℕ, ∑ k ∈ s, a k * moments (shift + k + j) = 0 := by
    intro j
    have hinner :
        inner ℝ (∑ k ∈ s, a k • feature k) (feature j) = 0 := by
      rw [hsum]
      simp
    have hinner' := hinner
    rw [real_inner_comm] at hinner'
    rw [inner_sum] at hinner'
    simp only [real_inner_smul_right] at hinner'
    have hmoment :
        (∑ k ∈ s, a k * moments (shift + k + j)) =
          ∑ k ∈ s, a k * inner ℝ (feature j) (feature k) := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        a k * moments (shift + k + j) =
            a k * Matrix.gram ℝ feature k j := by rw [hgram k j]
        _ = a k * inner ℝ (feature j) (feature k) := by
          simp [Matrix.gram, real_inner_comm]
    rw [hmoment]
    exact hinner'
  have hrel' : ∀ j : ℕ, ∑ k ∈ s, a' k * moments (shift + k + j) = 0 := by
    intro j
    rw [← hrel j]
    apply Finset.sum_congr rfl
    intro k hk
    simp [a', hk]
  have hall := hno s a' haSupport hrel'
  simpa [a', hi] using hall i

/-- Convenient zero-shift specialization for an ordinary Hankel moment Gram. -/
theorem linearIndependent_of_noFiniteMomentRelation_of_gram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hno : NoFiniteMomentRelation moments)
    (hgram : ∀ i j : ℕ,
      moments (i + j) = Matrix.gram ℝ feature i j) :
    LinearIndependent ℝ feature := by
  apply linearIndependent_of_noFiniteMomentRelationAt_of_gram hno
  intro i j
  simpa using hgram i j

/-- Convenient shifted specialization for the odd moment Gram. -/
theorem linearIndependent_of_noFiniteMomentRelation_shifted_gram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hno : NoFiniteMomentRelation moments)
    (hgram : ∀ i j : ℕ,
      moments (i + j + 1) = Matrix.gram ℝ feature i j) :
    LinearIndependent ℝ feature := by
  apply linearIndependent_of_noFiniteMomentRelationAt_of_gram
    (noFiniteMomentRelationAt_of_noFiniteMomentRelation hno 1)
  intro i j
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hgram i j

/-- A single Green--Wronskian Gram realization supplies both moment Grams.
Global nonrecurrence then proves independence of the even family and of the
odd family, using the shift-one case for the latter. -/
theorem greenWronskianMomentKernel_independent_of_noFiniteMomentRelation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hno : NoFiniteMomentRelation moments)
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet) :
    LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)) ∧
      LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)) := by
  constructor
  · exact linearIndependent_of_noFiniteMomentRelation_of_gram hno
      (fun i j => greenWronskianMomentKernel_even_momentGram hrep i j)
  · exact linearIndependent_of_noFiniteMomentRelation_shifted_gram hno
      (fun i j => greenWronskianMomentKernel_odd_shiftedMomentGram hrep i j)

end

end CarrySelfAdjointOperator
