import CarrySelfAdjointOperator.GreenJetMaximalAdjointSquare
import Mathlib.Tactic

/-!
# A moment-only criterion for the Green zero-mass gate

The positive self-adjoint Green square has trivial kernel once its head jet
`e_0` belongs to the completed span of the shifted tail `e_1, e_2, ...`.
This file rewrites that Hilbert-space statement as one explicit scalar limit
condition on the logarithmic moments.

For finitely supported coefficients `c`, put

`p_c = sum_n c_n e_(n+1)`.

The squared approximation error is exactly

`h_0 - 2 sum_n c_n h_(n+1)
     + sum_i sum_j c_i c_j h_(i+j+2)`.

Consequently, the head lies in the completed shifted tail if and only if this
quadratic moment defect can be made arbitrarily small.  This introduces no
measure, zero list, or spectral-height datum; it is the scalar limit that must
be discharged from the completed logarithmic response.
-/

open scoped InnerProductSpace BigOperators

namespace CarrySelfAdjointOperator

noncomputable section

@[reducible] private def coherentGreenJetMomentEvenInnerProductSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    InnerProductSpace ℝ (greenJetEvenHilbertSubspace jet) :=
  { (inferInstance :
      InnerProductSpace ℝ (greenJetEvenHilbertSubspace jet)) with
    toNormedSpace := inferInstance }

/-- A finite polynomial combination of the shifted even jets
`e_1, e_2, ...`. -/
def greenJetEvenShiftedTailPolynomial
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) (c : ℕ →₀ ℝ) :
    greenJetEvenHilbertSubspace jet :=
  c.sum fun n a => a • greenJetEvenSectorJet jet (n + 1)

/-- Every shifted-tail polynomial belongs to the algebraic shifted tail. -/
theorem greenJetEvenShiftedTailPolynomial_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) (c : ℕ →₀ ℝ) :
    greenJetEvenShiftedTailPolynomial jet c ∈
      greenJetEvenShiftedTailCore jet := by
  rw [greenJetEvenShiftedTailCore]
  apply Finsupp.mem_span_range_iff_exists_finsupp.mpr
  exact ⟨c, rfl⟩

/-- The even Green-jet Gram entries are the unshifted logarithmic moments. -/
theorem inner_greenJetEvenSectorJet_eq_moment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (i j : ℕ) :
    ⟪greenJetEvenSectorJet jet i,
        greenJetEvenSectorJet jet j⟫_ℝ = moments (i + j) := by
  have h := hrep (Sum.inl i) (Sum.inl j)
  change ⟪jet (Sum.inl i), jet (Sum.inl j)⟫_ℝ = moments (i + j)
  simpa [greenWronskianMomentKernel, Matrix.gram] using h.symm

/-- Scalar quadratic defect for approximating `e_0` by a finite shifted-tail
polynomial. -/
def greenJetEvenHeadTailMomentDefect
    (moments : ℕ → ℝ) (c : ℕ →₀ ℝ) : ℝ :=
  moments 0 -
      2 * c.sum (fun n a => a * moments (n + 1)) +
    c.sum fun i ai =>
      c.sum fun j aj => ai * aj * moments (i + j + 2)

/-- The moment defect is literally the squared Hilbert-space approximation
error. -/
theorem greenJetEvenHeadTailMomentDefect_eq_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (c : ℕ →₀ ℝ) :
    greenJetEvenHeadTailMomentDefect moments c =
      ‖greenJetEvenSectorJet jet 0 -
        greenJetEvenShiftedTailPolynomial jet c‖ ^ 2 := by
  letI : InnerProductSpace ℝ (greenJetEvenHilbertSubspace jet) :=
    coherentGreenJetMomentEvenInnerProductSpace jet
  have h00 :
      ⟪greenJetEvenSectorJet jet 0,
          greenJetEvenSectorJet jet 0⟫_ℝ = moments 0 := by
    simpa using inner_greenJetEvenSectorJet_eq_moment hrep 0 0
  have hp0 :
      ⟪greenJetEvenShiftedTailPolynomial jet c,
          greenJetEvenSectorJet jet 0⟫_ℝ =
        c.sum (fun n a => a * moments (n + 1)) := by
    rw [greenJetEvenShiftedTailPolynomial, Finsupp.sum_inner]
    apply Finsupp.sum_congr
    intro n _hn
    calc
      ⟪c n • greenJetEvenSectorJet jet (n + 1),
          greenJetEvenSectorJet jet 0⟫_ℝ =
          c n * ⟪greenJetEvenSectorJet jet (n + 1),
            greenJetEvenSectorJet jet 0⟫_ℝ := by
              exact real_inner_smul_left _ _ _
      _ = c n * moments (n + 1) := by
        rw [inner_greenJetEvenSectorJet_eq_moment hrep]
  have h0p :
      ⟪greenJetEvenSectorJet jet 0,
          greenJetEvenShiftedTailPolynomial jet c⟫_ℝ =
        c.sum (fun n a => a * moments (n + 1)) := by
    rw [greenJetEvenShiftedTailPolynomial, Finsupp.inner_sum]
    apply Finsupp.sum_congr
    intro n _hn
    calc
      ⟪greenJetEvenSectorJet jet 0,
          c n • greenJetEvenSectorJet jet (n + 1)⟫_ℝ =
          c n * ⟪greenJetEvenSectorJet jet 0,
            greenJetEvenSectorJet jet (n + 1)⟫_ℝ := by
              exact real_inner_smul_right _ _ _
      _ = c n * moments (n + 1) := by
        rw [inner_greenJetEvenSectorJet_eq_moment hrep]
        congr 2
        omega
  have hpp :
      ⟪greenJetEvenShiftedTailPolynomial jet c,
          greenJetEvenShiftedTailPolynomial jet c⟫_ℝ =
        c.sum fun i ai =>
          c.sum fun j aj => ai * aj * moments (i + j + 2) := by
    rw [greenJetEvenShiftedTailPolynomial, Finsupp.sum_inner]
    apply Finsupp.sum_congr
    intro i _hi
    calc
      ⟪c i • greenJetEvenSectorJet jet (i + 1),
          c.sum (fun n a =>
            a • greenJetEvenSectorJet jet (n + 1))⟫_ℝ =
          c i * ⟪greenJetEvenSectorJet jet (i + 1),
            c.sum (fun n a =>
              a • greenJetEvenSectorJet jet (n + 1))⟫_ℝ := by
                exact real_inner_smul_left _ _ _
      _ = c.sum (fun j aj =>
          c i * aj * moments (i + j + 2)) := by
        rw [Finsupp.inner_sum, Finsupp.mul_sum]
        apply Finsupp.sum_congr
        intro j _hj
        calc
          c i * ⟪greenJetEvenSectorJet jet (i + 1),
              c j • greenJetEvenSectorJet jet (j + 1)⟫_ℝ =
              c i * (c j * ⟪greenJetEvenSectorJet jet (i + 1),
                greenJetEvenSectorJet jet (j + 1)⟫_ℝ) := by
                  congr 1
                  exact real_inner_smul_right _ _ _
          _ = c i * c j * moments (i + j + 2) := by
            rw [inner_greenJetEvenSectorJet_eq_moment hrep]
            rw [show (i + 1) + (j + 1) = i + j + 2 by omega]
            ring
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right]
  rw [h00, hp0, h0p, hpp]
  unfold greenJetEvenHeadTailMomentDefect
  ring

/-- Hilbert-space approximation form of the completed head-in-tail gate. -/
theorem greenJetEvenShiftedTailCore_head_mem_iff_norm_approximation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    greenJetEvenSectorJet jet 0 ∈
        (greenJetEvenShiftedTailCore jet).topologicalClosure ↔
      ∀ ε > 0, ∃ c : ℕ →₀ ℝ,
        ‖greenJetEvenSectorJet jet 0 -
          greenJetEvenShiftedTailPolynomial jet c‖ < ε := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨y, hy, hdist⟩ := h ε hε
    change y ∈ Submodule.span ℝ
      (Set.range (fun n : ℕ => greenJetEvenSectorJet jet (n + 1))) at hy
    obtain ⟨c, hc⟩ :=
      Finsupp.mem_span_range_iff_exists_finsupp.mp hy
    refine ⟨c, ?_⟩
    change greenJetEvenShiftedTailPolynomial jet c = y at hc
    rw [hc]
    simpa [dist_eq_norm] using hdist
  · intro h ε hε
    obtain ⟨c, hc⟩ := h ε hε
    refine ⟨greenJetEvenShiftedTailPolynomial jet c,
      greenJetEvenShiftedTailPolynomial_mem jet c, ?_⟩
    simpa [dist_eq_norm] using hc

/-- The explicit moment-only statement that the head-tail defect has infimum
zero over finite shifted-tail polynomials. -/
def HasVanishingGreenJetHeadTailMomentDefect
    (moments : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ c : ℕ →₀ ℝ,
    greenJetEvenHeadTailMomentDefect moments c < ε

/-- The completion gate is exactly the vanishing of the scalar quadratic
moment defect. -/
theorem greenJetEvenShiftedTailCore_head_mem_iff_momentDefect
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet) :
    greenJetEvenSectorJet jet 0 ∈
        (greenJetEvenShiftedTailCore jet).topologicalClosure ↔
      HasVanishingGreenJetHeadTailMomentDefect moments := by
  rw [greenJetEvenShiftedTailCore_head_mem_iff_norm_approximation]
  constructor
  · intro h ε hε
    obtain ⟨c, hc⟩ := h (Real.sqrt ε) (Real.sqrt_pos.2 hε)
    refine ⟨c, ?_⟩
    rw [greenJetEvenHeadTailMomentDefect_eq_norm_sq hrep]
    nlinarith [Real.sq_sqrt (le_of_lt hε),
      Real.sqrt_nonneg ε,
      norm_nonneg
        (greenJetEvenSectorJet jet 0 -
          greenJetEvenShiftedTailPolynomial jet c)]
  · intro h ε hε
    obtain ⟨c, hc⟩ := h (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨c, ?_⟩
    rw [greenJetEvenHeadTailMomentDefect_eq_norm_sq hrep] at hc
    nlinarith [norm_nonneg
      (greenJetEvenSectorJet jet 0 -
        greenJetEvenShiftedTailPolynomial jet c)]

/-- A vanishing scalar moment defect removes the kernel of the canonical
positive self-adjoint Green square. -/
theorem closedGreenJetEnergyAdjointSquare_ker_eq_bot_of_momentDefect
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hvanish : HasVanishingGreenJetHeadTailMomentDefect moments) :
    LinearMap.ker
        (closedGreenJetEnergyAdjointSquare hrep heven hodd).toFun = ⊥ :=
  closedGreenJetEnergyAdjointSquare_ker_eq_bot_of_head_mem_shiftedTail
    hrep heven hodd
      ((greenJetEvenShiftedTailCore_head_mem_iff_momentDefect hrep).2 hvanish)

/-- The same scalar criterion removes the kernel after automatic ambient
Hilbert completion. -/
theorem canonicalCompletedGreenJetEnergyAdjointSquare_ker_eq_bot_of_momentDefect
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hvanish : HasVanishingGreenJetHeadTailMomentDefect moments) :
    LinearMap.ker
      (canonicalCompletedGreenJetEnergyAdjointSquare
        hrep heven hodd).toFun = ⊥ :=
  closedGreenJetEnergyAdjointSquare_ker_eq_bot_of_momentDefect
    (completedGreenJet_gramRepresentation hrep)
    (completedGreenJet_even_linearIndependent heven)
    (completedGreenJet_odd_linearIndependent hodd)
    hvanish

end

end CarrySelfAdjointOperator
