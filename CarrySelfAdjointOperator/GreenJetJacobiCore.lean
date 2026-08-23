import CarrySelfAdjointOperator.GreenJetEnergyFactor
import Mathlib.Tactic

/-!
# The algebraic Green-jet Jacobi core

The closed Green energy factor already gives the canonical map

`B₀ e_n = o_n`

between the even and odd Green-jet sectors.  The same moment kernel forces the
algebraic Jacobi action

`J₀ e_n = e_(n+1)`.

This file constructs `J₀` as a densely defined partial operator and proves the
exact energy identity

`<J₀ x, y> = <B₀ x, B₀ y>`.

Consequently `J₀` is symmetric, positive and closable.  This is the genuine
minimal infinite Jacobi operator carried by the Green jets, before choosing or
proving a self-adjoint extension.  It does not claim that its closure is
already self-adjoint, bounded, injective, or equipped with the inverse-square-
root functional calculus.
-/

open scoped InnerProductSpace LinearPMap RealInnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

/-- Algebraic multiplication by the compact spectral coordinate on the even
Green-jet core: `J₀ e_n = e_(n+1)`. -/
def greenJetJacobiCoreMap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    greenJetEvenOperatorCore jet →ₗ[ℝ]
      greenJetEvenHilbertSubspace jet :=
  (greenJetEvenOperatorCoreBasis heven).constr ℝ
    (fun n => greenJetEvenSectorJet jet (n + 1))

/-- Direct linear-map spelling of the Green energy factor on the Jacobi core. -/
private def greenJetJacobiEnergyFactorMap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    greenJetEvenOperatorCore jet →ₗ[ℝ]
      greenJetOddHilbertSubspace jet :=
  (greenJetEvenOperatorCoreBasis heven).constr ℝ
    (greenJetOddSectorJet jet)

/-- The corresponding densely defined operator on the closed even Green
sector. -/
def greenJetJacobiCore
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    greenJetEvenHilbertSubspace jet →ₗ.[ℝ]
      greenJetEvenHilbertSubspace jet where
  domain := greenJetEvenOperatorCore jet
  toFun := greenJetJacobiCoreMap heven

@[simp] theorem greenJetJacobiCoreMap_jet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (n : ℕ) :
    greenJetJacobiCoreMap heven (greenJetEvenCoreJet jet n) =
      greenJetEvenSectorJet jet (n + 1) := by
  rw [← greenJetEvenOperatorCoreBasis_apply heven n]
  exact (greenJetEvenOperatorCoreBasis heven).constr_basis ℝ
    (fun n => greenJetEvenSectorJet jet (n + 1)) n

@[simp] theorem greenJetJacobiCore_jet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (n : ℕ) :
    greenJetJacobiCore heven (greenJetEvenCoreJet jet n) =
      greenJetEvenSectorJet jet (n + 1) :=
  greenJetJacobiCoreMap_jet heven n

@[simp] private theorem greenJetJacobiEnergyFactorMap_jet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (n : ℕ) :
    greenJetJacobiEnergyFactorMap heven (greenJetEvenCoreJet jet n) =
      greenJetOddSectorJet jet n := by
  rw [← greenJetEvenOperatorCoreBasis_apply heven n]
  exact (greenJetEvenOperatorCoreBasis heven).constr_basis ℝ
    (greenJetOddSectorJet jet) n

/-- Generator identity behind positivity: shifting the even jet in the first
slot gives exactly the odd/odd shifted-moment Gram entry. -/
theorem inner_greenJetEvenSectorJet_succ_eq_inner_greenJetOddSectorJet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (i j : ℕ) :
    ⟪greenJetEvenSectorJet jet (i + 1),
        greenJetEvenSectorJet jet j⟫_ℝ =
      ⟪greenJetOddSectorJet jet i,
        greenJetOddSectorJet jet j⟫_ℝ := by
  have heven := hrep (Sum.inl (i + 1)) (Sum.inl j)
  have hodd := hrep (Sum.inr i) (Sum.inr j)
  change ⟪jet (Sum.inl (i + 1)), jet (Sum.inl j)⟫_ℝ =
    ⟪jet (Sum.inr i), jet (Sum.inr j)⟫_ℝ
  calc
    ⟪jet (Sum.inl (i + 1)), jet (Sum.inl j)⟫_ℝ =
        moments ((i + 1) + j) := by
      simpa [greenWronskianMomentKernel, Matrix.gram] using heven.symm
    _ = moments (i + j + 1) := by
      congr 1
      omega
    _ = ⟪jet (Sum.inr i), jet (Sum.inr j)⟫_ℝ := by
      simpa [greenWronskianMomentKernel, Matrix.gram] using hodd

/-- Generator identity behind symmetry of the Jacobi core. -/
theorem inner_greenJetEvenSectorJet_succ_eq_inner_succ_right
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (i j : ℕ) :
    ⟪greenJetEvenSectorJet jet (i + 1),
        greenJetEvenSectorJet jet j⟫_ℝ =
      ⟪greenJetEvenSectorJet jet i,
        greenJetEvenSectorJet jet (j + 1)⟫_ℝ := by
  have hleft := hrep (Sum.inl (i + 1)) (Sum.inl j)
  have hright := hrep (Sum.inl i) (Sum.inl (j + 1))
  change ⟪jet (Sum.inl (i + 1)), jet (Sum.inl j)⟫_ℝ =
    ⟪jet (Sum.inl i), jet (Sum.inl (j + 1))⟫_ℝ
  calc
    ⟪jet (Sum.inl (i + 1)), jet (Sum.inl j)⟫_ℝ =
        moments ((i + 1) + j) := by
      simpa [greenWronskianMomentKernel, Matrix.gram] using hleft.symm
    _ = moments (i + (j + 1)) := by
      congr 1
      omega
    _ = ⟪jet (Sum.inl i), jet (Sum.inl (j + 1))⟫_ℝ := by
      simpa [greenWronskianMomentKernel, Matrix.gram] using hright

/-- Exact all-core energy identity `J₀ = B₀* B₀` at the quadratic-form
level.  No adjoint operator or measure model is used. -/
theorem greenJetJacobiCore_energyIdentity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    ∀ x y : greenJetEvenOperatorCore jet,
      ⟪greenJetJacobiCoreMap heven x,
          (y : greenJetEvenHilbertSubspace jet)⟫_ℝ =
        ⟪greenJetEnergyFactorCore heven x,
          greenJetEnergyFactorCore heven y⟫_ℝ := by
  let B := greenJetJacobiEnergyFactorMap heven
  have hcore := linearMaps_formalAdjoint_of_basis
    (I := ℕ) (J := ℕ)
    (E₀ := greenJetEvenOperatorCore jet)
    (F₀ := greenJetEvenOperatorCore jet)
    (E₁ := greenJetOddHilbertSubspace jet)
    (F₁ := greenJetEvenHilbertSubspace jet)
    (greenJetEvenOperatorCoreBasis heven)
    (greenJetEvenOperatorCoreBasis heven)
    (greenJetJacobiCoreMap heven)
    (greenJetEvenOperatorCore jet).subtype
    B
    B
    (fun i j => by
      rw [greenJetEvenOperatorCoreBasis_apply heven i,
        greenJetEvenOperatorCoreBasis_apply heven j]
      change
        ⟪greenJetJacobiCoreMap heven (greenJetEvenCoreJet jet i),
            (greenJetEvenCoreJet jet j :
              greenJetEvenHilbertSubspace jet)⟫_ℝ =
          ⟪greenJetJacobiEnergyFactorMap heven (greenJetEvenCoreJet jet i),
            greenJetJacobiEnergyFactorMap heven
              (greenJetEvenCoreJet jet j)⟫_ℝ
      rw [greenJetJacobiCoreMap_jet,
        greenJetJacobiEnergyFactorMap_jet,
        greenJetJacobiEnergyFactorMap_jet]
      exact
          inner_greenJetEvenSectorJet_succ_eq_inner_greenJetOddSectorJet
            hrep i j)
  intro x y
  simpa [B, greenJetJacobiEnergyFactorMap, greenJetEnergyFactorCore] using
    hcore x y

/-- The minimal Green-jet Jacobi operator is symmetric on its algebraic core. -/
theorem greenJetJacobiCore_formalSelfAdjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    ∀ x y : greenJetEvenOperatorCore jet,
      ⟪greenJetJacobiCoreMap heven x,
          (y : greenJetEvenHilbertSubspace jet)⟫_ℝ =
        ⟪(x : greenJetEvenHilbertSubspace jet),
          greenJetJacobiCoreMap heven y⟫_ℝ := by
  have hcore := linearMaps_formalAdjoint_of_basis
    (I := ℕ) (J := ℕ)
    (E₀ := greenJetEvenOperatorCore jet)
    (F₀ := greenJetEvenOperatorCore jet)
    (E₁ := greenJetEvenHilbertSubspace jet)
    (F₁ := greenJetEvenHilbertSubspace jet)
    (greenJetEvenOperatorCoreBasis heven)
    (greenJetEvenOperatorCoreBasis heven)
    (greenJetJacobiCoreMap heven)
    (greenJetEvenOperatorCore jet).subtype
    (greenJetEvenOperatorCore jet).subtype
    (greenJetJacobiCoreMap heven)
    (fun i j => by
      rw [greenJetEvenOperatorCoreBasis_apply heven i,
        greenJetEvenOperatorCoreBasis_apply heven j]
      change
        ⟪greenJetJacobiCoreMap heven (greenJetEvenCoreJet jet i),
            (greenJetEvenCoreJet jet j :
              greenJetEvenHilbertSubspace jet)⟫_ℝ =
          ⟪(greenJetEvenCoreJet jet i :
              greenJetEvenHilbertSubspace jet),
            greenJetJacobiCoreMap heven
              (greenJetEvenCoreJet jet j)⟫_ℝ
      rw [greenJetJacobiCoreMap_jet, greenJetJacobiCoreMap_jet]
      exact
          inner_greenJetEvenSectorJet_succ_eq_inner_succ_right hrep i j)
  exact hcore

/-- Positivity of the Jacobi quadratic form is the squared norm of the Green
energy factor. -/
theorem greenJetJacobiCore_inner_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (x : greenJetEvenOperatorCore jet) :
    0 ≤ ⟪greenJetJacobiCoreMap heven x,
      (x : greenJetEvenHilbertSubspace jet)⟫_ℝ := by
  rw [greenJetJacobiCore_energyIdentity hrep heven x x,
    real_inner_self_eq_norm_sq]
  positivity

/-- The Jacobi core has dense domain in the closed even Green sector. -/
theorem greenJetJacobiCore_dense_domain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    Dense ((greenJetJacobiCore heven).domain :
      Set (greenJetEvenHilbertSubspace jet)) := by
  simpa [greenJetJacobiCore] using greenJetEvenOperatorCore_dense jet

/-- A densely defined symmetric Jacobi core is closable. -/
theorem greenJetJacobiCore_isClosable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    (greenJetJacobiCore heven).IsClosable := by
  let J := greenJetJacobiCore heven
  have hJ : Dense (J.domain : Set (greenJetEvenHilbertSubspace jet)) :=
    greenJetJacobiCore_dense_domain heven
  have hformal : ∀ (x : J.domain) (y : J.domain),
      ⟪J x, (y : greenJetEvenHilbertSubspace jet)⟫_ℝ =
        ⟪(x : greenJetEvenHilbertSubspace jet), J y⟫_ℝ := by
    intro x y
    change
      ⟪greenJetJacobiCoreMap heven x,
          (y : greenJetEvenHilbertSubspace jet)⟫_ℝ =
        ⟪(x : greenJetEvenHilbertSubspace jet),
          greenJetJacobiCoreMap heven y⟫_ℝ
    exact greenJetJacobiCore_formalSelfAdjoint hrep heven x y
  let graphClosure := J.graph.topologicalClosure
  have hvertical :
      ∀ (p : greenJetEvenHilbertSubspace jet ×
          greenJetEvenHilbertSubspace jet)
        (_hp : p ∈ graphClosure) (_hp0 : p.fst = 0), p.snd = 0 := by
    intro p hp hp0
    apply hJ.eq_zero_of_inner_left ℝ
    intro z hz
    let zd : J.domain := ⟨z, hz⟩
    let annihilator : Set (greenJetEvenHilbertSubspace jet ×
        greenJetEvenHilbertSubspace jet) :=
      {q | ⟪q.snd, z⟫_ℝ = ⟪q.fst, J zd⟫_ℝ}
    have hannihilatorClosed : IsClosed annihilator := by
      apply isClosed_eq
      · fun_prop
      · fun_prop
    have hgraph : (J.graph : Set (greenJetEvenHilbertSubspace jet ×
        greenJetEvenHilbertSubspace jet)) ⊆ annihilator := by
      intro q hq
      rcases (LinearPMap.mem_graph_iff J).mp hq with ⟨x, hx, hJx⟩
      change ⟪q.snd, z⟫_ℝ = ⟪q.fst, J zd⟫_ℝ
      rw [← hJx, ← hx]
      exact hformal x zd
    have hpClosure : p ∈ _root_.closure
        (J.graph : Set (greenJetEvenHilbertSubspace jet ×
          greenJetEvenHilbertSubspace jet)) := by
      change p ∈ J.graph.topologicalClosure at hp
      rw [← Submodule.topologicalClosure_coe]
      exact hp
    have hpAnnihilator : p ∈ annihilator :=
      closure_minimal hgraph hannihilatorClosed hpClosure
    change ⟪p.snd, z⟫_ℝ = ⟪p.fst, J zd⟫_ℝ at hpAnnihilator
    simpa [hp0] using hpAnnihilator
  refine ⟨graphClosure.toLinearPMap, ?_⟩
  exact (Submodule.toLinearPMap_graph_eq graphClosure hvertical).symm

/-- Canonical graph closure of the positive symmetric Jacobi core. -/
def closedGreenJetJacobiOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (_hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    greenJetEvenHilbertSubspace jet →ₗ.[ℝ]
      greenJetEvenHilbertSubspace jet :=
  (greenJetJacobiCore heven).closure

/-- The canonical Jacobi closure is closed. -/
theorem closedGreenJetJacobiOperator_isClosed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    (closedGreenJetJacobiOperator hrep heven).IsClosed := by
  exact (greenJetJacobiCore_isClosable hrep heven).closure_isClosed

/-- The algebraic Jacobi domain is a core for the closed realization. -/
theorem closedGreenJetJacobiOperator_hasCore
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    (closedGreenJetJacobiOperator hrep heven).HasCore
      (greenJetJacobiCore heven).domain :=
  (greenJetJacobiCore heven).closureHasCore

end

end CarrySelfAdjointOperator
