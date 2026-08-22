import CarrySelfAdjointOperator.GreenJetParityReflection
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic

/-!
# The closed Green-jet energy factor

The parity-split Green moment kernel contains more than finite Hankel
positivity.  If `e n` and `o n` denote the even and odd Green jets, then

`<e i, e j> = h (i+j)` and `<o i, o j> = h (i+j+1)`.

Consequently the algebraic map `B₀ (e n) = o n` has the algebraic formal
adjoint `C₀ (o n) = e (n+1)`.  Both algebraic jet spans are dense in their
closed parity sectors.  The densely defined formal-adjoint pair therefore
forces `B₀` to be closable, without a measure model or an order-by-order
limit.

This is the operator-theoretic form of the shifted-Hankel Green energy.  Its
closure is the canonical closed factor from which the positive operator
`B* B` is to be constructed.
-/

open scoped InnerProductSpace LinearPMap RealInnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

/-- The canonical Green Hilbert carrier included in the original ambient
inner-product space. -/
def greenJetHilbertSubtype
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    CanonicalGreenJetSignedHeightHilbertSpace jet →ₗ[ℝ] E :=
  (Submodule.span ℝ (Set.range jet)).topologicalClosure.subtype

/-- An even Green jet, now regarded as a vector of the closed even sector. -/
def greenJetEvenSectorJet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) (n : ℕ) :
    greenJetEvenHilbertSubspace jet :=
  ⟨greenJetInHilbert jet (Sum.inl n), greenJetInHilbert_even_mem jet n⟩

/-- An odd Green jet, now regarded as a vector of the closed odd sector. -/
def greenJetOddSectorJet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) (n : ℕ) :
    greenJetOddHilbertSubspace jet :=
  ⟨greenJetInHilbert jet (Sum.inr n), greenJetInHilbert_odd_mem jet n⟩

/-- Global independence of the raw even jets survives bundling in the
canonical Green Hilbert carrier. -/
theorem greenJetInHilbert_even_linearIndependent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    LinearIndependent ℝ
      (fun n : ℕ => greenJetInHilbert jet (Sum.inl n)) := by
  apply LinearIndependent.of_comp (greenJetHilbertSubtype jet)
  simpa [greenJetHilbertSubtype, greenJetInHilbert, Function.comp_def] using heven

/-- Global independence of the raw odd jets survives bundling in the
canonical Green Hilbert carrier. -/
theorem greenJetInHilbert_odd_linearIndependent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    LinearIndependent ℝ
      (fun n : ℕ => greenJetInHilbert jet (Sum.inr n)) := by
  apply LinearIndependent.of_comp (greenJetHilbertSubtype jet)
  simpa [greenJetHilbertSubtype, greenJetInHilbert, Function.comp_def] using hodd

/-- Independence also holds after restricting the even jets to their closed
sector. -/
theorem greenJetEvenSectorJet_linearIndependent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    LinearIndependent ℝ (greenJetEvenSectorJet jet) := by
  apply LinearIndependent.of_comp (greenJetEvenHilbertSubspace jet).subtype
  simpa [greenJetEvenSectorJet, Function.comp_def] using
    (greenJetInHilbert_even_linearIndependent heven)

/-- Independence also holds after restricting the odd jets to their closed
sector. -/
theorem greenJetOddSectorJet_linearIndependent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    LinearIndependent ℝ (greenJetOddSectorJet jet) := by
  apply LinearIndependent.of_comp (greenJetOddHilbertSubspace jet).subtype
  simpa [greenJetOddSectorJet, Function.comp_def] using
    (greenJetInHilbert_odd_linearIndependent hodd)

/-- The algebraic even operator core inside the closed even sector. -/
def greenJetEvenOperatorCore
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    Submodule ℝ (greenJetEvenHilbertSubspace jet) :=
  Submodule.span ℝ (Set.range (greenJetEvenSectorJet jet))

/-- The algebraic odd operator core inside the closed odd sector. -/
def greenJetOddOperatorCore
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    Submodule ℝ (greenJetOddHilbertSubspace jet) :=
  Submodule.span ℝ (Set.range (greenJetOddSectorJet jet))

/-- Canonical basis of the algebraic even core. -/
def greenJetEvenOperatorCoreBasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    Module.Basis ℕ ℝ (greenJetEvenOperatorCore jet) :=
  Module.Basis.span (greenJetEvenSectorJet_linearIndependent heven)

/-- Canonical basis of the algebraic odd core. -/
def greenJetOddOperatorCoreBasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    Module.Basis ℕ ℝ (greenJetOddOperatorCore jet) :=
  Module.Basis.span (greenJetOddSectorJet_linearIndependent hodd)

/-- The canonical core vector over the `n`-th even Green jet. -/
def greenJetEvenCoreJet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) (n : ℕ) : greenJetEvenOperatorCore jet :=
  ⟨greenJetEvenSectorJet jet n,
    Submodule.subset_span (Set.mem_range_self n)⟩

/-- The canonical core vector over the `n`-th odd Green jet. -/
def greenJetOddCoreJet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) (n : ℕ) : greenJetOddOperatorCore jet :=
  ⟨greenJetOddSectorJet jet n,
    Submodule.subset_span (Set.mem_range_self n)⟩

@[simp] theorem greenJetEvenOperatorCoreBasis_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (n : ℕ) :
    greenJetEvenOperatorCoreBasis heven n = greenJetEvenCoreJet jet n := by
  unfold greenJetEvenOperatorCoreBasis greenJetEvenCoreJet
  exact Module.Basis.span_apply
    (greenJetEvenSectorJet_linearIndependent heven) n

@[simp] theorem greenJetOddOperatorCoreBasis_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (n : ℕ) :
    greenJetOddOperatorCoreBasis hodd n = greenJetOddCoreJet jet n := by
  unfold greenJetOddOperatorCoreBasis greenJetOddCoreJet
  exact Module.Basis.span_apply
    (greenJetOddSectorJet_linearIndependent hodd) n

/-- The algebraic Green energy factor `B₀ e_n = o_n`. -/
def greenJetEnergyFactorCore
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    greenJetEvenHilbertSubspace jet →ₗ.[ℝ]
      greenJetOddHilbertSubspace jet where
  domain := greenJetEvenOperatorCore jet
  toFun := (greenJetEvenOperatorCoreBasis heven).constr ℝ
    (greenJetOddSectorJet jet)

/-- The algebraic reverse shift `C₀ o_n = e_(n+1)`. -/
def greenJetEnergyFormalAdjointCore
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    greenJetOddHilbertSubspace jet →ₗ.[ℝ]
      greenJetEvenHilbertSubspace jet where
  domain := greenJetOddOperatorCore jet
  toFun := (greenJetOddOperatorCoreBasis hodd).constr ℝ
    (fun n => greenJetEvenSectorJet jet (n + 1))

/-- The operator-domain copy of the even algebraic core is canonically linearly
equivalent to the core itself.  Keeping this bridge explicit prevents the
domain of a partial operator from being silently identified with its ambient
Hilbert sector. -/
def greenJetEnergyFactorDomainEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    (greenJetEnergyFactorCore heven).domain ≃ₗ[ℝ]
      greenJetEvenOperatorCore jet :=
  LinearEquiv.ofEq _ _ rfl

/-- The analogous canonical bridge for the reverse-shift domain. -/
def greenJetEnergyFormalAdjointDomainEquiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    (greenJetEnergyFormalAdjointCore hodd).domain ≃ₗ[ℝ]
      greenJetOddOperatorCore jet :=
  LinearEquiv.ofEq _ _ rfl

/-- Basis of the exact partial-operator domain, transported from the even
algebraic Green-jet basis. -/
def greenJetEnergyFactorDomainBasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    Module.Basis ℕ ℝ (greenJetEnergyFactorCore heven).domain :=
  (greenJetEvenOperatorCoreBasis heven).map
    (greenJetEnergyFactorDomainEquiv heven).symm

/-- Basis of the exact reverse-shift partial-operator domain. -/
def greenJetEnergyFormalAdjointDomainBasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    Module.Basis ℕ ℝ (greenJetEnergyFormalAdjointCore hodd).domain :=
  (greenJetOddOperatorCoreBasis hodd).map
    (greenJetEnergyFormalAdjointDomainEquiv hodd).symm

@[simp] theorem greenJetEnergyFactorCore_jet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (n : ℕ) :
    greenJetEnergyFactorCore heven (greenJetEvenCoreJet jet n) =
      greenJetOddSectorJet jet n := by
  rw [← greenJetEvenOperatorCoreBasis_apply heven n]
  exact (greenJetEvenOperatorCoreBasis heven).constr_basis ℝ
    (greenJetOddSectorJet jet) n

@[simp] theorem greenJetEnergyFormalAdjointCore_jet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (n : ℕ) :
    greenJetEnergyFormalAdjointCore hodd (greenJetOddCoreJet jet n) =
      greenJetEvenSectorJet jet (n + 1) := by
  rw [← greenJetOddOperatorCoreBasis_apply hodd n]
  exact (greenJetOddOperatorCoreBasis hodd).constr_basis ℝ
    (fun n => greenJetEvenSectorJet jet (n + 1)) n

@[simp] theorem greenJetEnergyFactorDomainBasis_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (n : ℕ) :
    greenJetEnergyFactorCore heven
        (greenJetEnergyFactorDomainBasis heven n) =
      greenJetOddSectorJet jet n := by
  have hbasis : greenJetEnergyFactorDomainBasis heven n =
      (greenJetEvenCoreJet jet n :
        (greenJetEnergyFactorCore heven).domain) := by
    apply Subtype.ext
    simp [greenJetEnergyFactorDomainBasis, greenJetEnergyFactorDomainEquiv,
      greenJetEvenOperatorCoreBasis_apply, greenJetEvenCoreJet]
  rw [hbasis]
  exact greenJetEnergyFactorCore_jet heven n

@[simp] theorem greenJetEnergyFactorDomainBasis_coe
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (n : ℕ) :
    ((greenJetEnergyFactorDomainBasis heven n :
        (greenJetEnergyFactorCore heven).domain) :
      greenJetEvenHilbertSubspace jet) = greenJetEvenSectorJet jet n := by
  have hbasis : greenJetEnergyFactorDomainBasis heven n =
      (greenJetEvenCoreJet jet n :
        (greenJetEnergyFactorCore heven).domain) := by
    apply Subtype.ext
    simp [greenJetEnergyFactorDomainBasis, greenJetEnergyFactorDomainEquiv,
      greenJetEvenOperatorCoreBasis_apply, greenJetEvenCoreJet]
  rw [hbasis]
  rfl

@[simp] theorem greenJetEnergyFactorDomainBasis_subtype
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (n : ℕ) :
    (greenJetEnergyFactorCore heven).domain.subtype
        (greenJetEnergyFactorDomainBasis heven n) =
      greenJetEvenSectorJet jet n := by
  exact greenJetEnergyFactorDomainBasis_coe heven n

@[simp] theorem greenJetEnergyFormalAdjointDomainBasis_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (n : ℕ) :
    greenJetEnergyFormalAdjointCore hodd
        (greenJetEnergyFormalAdjointDomainBasis hodd n) =
      greenJetEvenSectorJet jet (n + 1) := by
  have hbasis : greenJetEnergyFormalAdjointDomainBasis hodd n =
      (greenJetOddCoreJet jet n :
        (greenJetEnergyFormalAdjointCore hodd).domain) := by
    apply Subtype.ext
    simp [greenJetEnergyFormalAdjointDomainBasis,
      greenJetEnergyFormalAdjointDomainEquiv,
      greenJetOddOperatorCoreBasis_apply, greenJetOddCoreJet]
  rw [hbasis]
  exact greenJetEnergyFormalAdjointCore_jet hodd n

@[simp] theorem greenJetEnergyFormalAdjointDomainBasis_coe
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (n : ℕ) :
    ((greenJetEnergyFormalAdjointDomainBasis hodd n :
        (greenJetEnergyFormalAdjointCore hodd).domain) :
      greenJetOddHilbertSubspace jet) = greenJetOddSectorJet jet n := by
  have hbasis : greenJetEnergyFormalAdjointDomainBasis hodd n =
      (greenJetOddCoreJet jet n :
        (greenJetEnergyFormalAdjointCore hodd).domain) := by
    apply Subtype.ext
    simp [greenJetEnergyFormalAdjointDomainBasis,
      greenJetEnergyFormalAdjointDomainEquiv,
      greenJetOddOperatorCoreBasis_apply, greenJetOddCoreJet]
  rw [hbasis]
  rfl

@[simp] theorem greenJetEnergyFormalAdjointDomainBasis_subtype
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (n : ℕ) :
    (greenJetEnergyFormalAdjointCore hodd).domain.subtype
        (greenJetEnergyFormalAdjointDomainBasis hodd n) =
      greenJetOddSectorJet jet n := by
  exact greenJetEnergyFormalAdjointDomainBasis_coe hodd n

/-- The algebraic even core is dense in the closed even Green sector. -/
theorem greenJetEvenOperatorCore_dense
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    Dense (greenJetEvenOperatorCore jet :
      Set (greenJetEvenHilbertSubspace jet)) := by
  rw [Subtype.dense_iff]
  have hmap :
      Submodule.map (greenJetEvenHilbertSubspace jet).subtype
          (greenJetEvenOperatorCore jet) =
        greenJetEvenAlgebraicSubspace jet := by
    rw [greenJetEvenOperatorCore, greenJetEvenAlgebraicSubspace,
      Submodule.map_span]
    congr 1
    ext x
    simp [greenJetEvenSectorJet]
  intro x hx
  change x ∈ _root_.closure
    ((greenJetEvenHilbertSubspace jet).subtype ''
      (greenJetEvenOperatorCore jet :
        Set (greenJetEvenHilbertSubspace jet)))
  rw [← Submodule.map_coe, hmap]
  simpa [greenJetEvenHilbertSubspace,
    Submodule.topologicalClosure_coe] using hx

/-- The algebraic odd core is dense in the closed odd Green sector. -/
theorem greenJetOddOperatorCore_dense
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    Dense (greenJetOddOperatorCore jet :
      Set (greenJetOddHilbertSubspace jet)) := by
  rw [Subtype.dense_iff]
  have hmap :
      Submodule.map (greenJetOddHilbertSubspace jet).subtype
          (greenJetOddOperatorCore jet) =
        greenJetOddAlgebraicSubspace jet := by
    rw [greenJetOddOperatorCore, greenJetOddAlgebraicSubspace,
      Submodule.map_span]
    congr 1
    ext x
    simp [greenJetOddSectorJet]
  intro x hx
  change x ∈ _root_.closure
    ((greenJetOddHilbertSubspace jet).subtype ''
      (greenJetOddOperatorCore jet :
        Set (greenJetOddHilbertSubspace jet)))
  rw [← Submodule.map_coe, hmap]
  simpa [greenJetOddHilbertSubspace,
    Submodule.topologicalClosure_coe] using hx

/-- The shifted moment identity is exactly the generator-level adjoint law
between the Green energy factor and its reverse shift. -/
theorem inner_greenJetOddSectorJet_eq_inner_even_succ
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (i j : ℕ) :
    ⟪greenJetOddSectorJet jet i, greenJetOddSectorJet jet j⟫_ℝ =
      ⟪greenJetEvenSectorJet jet i,
        greenJetEvenSectorJet jet (j + 1)⟫_ℝ := by
  have hodd := hrep (Sum.inr i) (Sum.inr j)
  have heven := hrep (Sum.inl i) (Sum.inl (j + 1))
  change ⟪jet (Sum.inr i), jet (Sum.inr j)⟫_ℝ =
    ⟪jet (Sum.inl i), jet (Sum.inl (j + 1))⟫_ℝ
  calc
    ⟪jet (Sum.inr i), jet (Sum.inr j)⟫_ℝ =
        moments (i + j + 1) := by
      simpa [greenWronskianMomentKernel, Matrix.gram] using hodd.symm
    _ = moments (i + (j + 1)) := by congr 1
    _ = ⟪jet (Sum.inl i), jet (Sum.inl (j + 1))⟫_ℝ := by
      simpa [greenWronskianMomentKernel, Matrix.gram] using heven

/-- A generator-level adjoint identity extends to the full algebraic spans.
This real-Hilbert lemma is separated out because the four maps naturally have
different source and target spaces. -/
theorem linearMaps_formalAdjoint_of_basis
    {I J E₀ F₀ E₁ F₁ : Type*}
    [AddCommMonoid E₀] [Module ℝ E₀]
    [AddCommMonoid F₀] [Module ℝ F₀]
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁]
    (bE : Module.Basis I ℝ E₀) (bF : Module.Basis J ℝ F₀)
    (B : E₀ →ₗ[ℝ] F₁) (includeF : F₀ →ₗ[ℝ] F₁)
    (includeE : E₀ →ₗ[ℝ] E₁) (C : F₀ →ₗ[ℝ] E₁)
    (hgenerator : ∀ i j,
      ⟪B (bE i), includeF (bF j)⟫_ℝ =
        ⟪includeE (bE i), C (bF j)⟫_ℝ) :
    ∀ x y, ⟪B x, includeF y⟫_ℝ = ⟪includeE x, C y⟫_ℝ := by
  intro x y
  have honE :
      (LinearMap.flip (innerₗ F₁) (includeF y)).comp B =
        (LinearMap.flip (innerₗ E₁) (C y)).comp includeE := by
    apply bE.ext
    intro i
    have honF :
        (innerₗ F₁ (B (bE i))).comp includeF =
          (innerₗ E₁ (includeE (bE i))).comp C := by
      apply bF.ext
      intro j
      exact hgenerator i j
    exact LinearMap.congr_fun honF y
  exact LinearMap.congr_fun honE x

/-- The reverse shift satisfies the genuine formal-adjoint identity for the
Green energy factor on their dense algebraic cores.  It is stated directly
over the two parity-sector subtypes so it uses their canonical submodule
scalar actions without an instance-changing coercion. -/
theorem greenJetEnergyFactorCore_formalAdjointIdentity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    ∀ (x : (greenJetEnergyFactorCore heven).domain)
      (y : (greenJetEnergyFormalAdjointCore hodd).domain),
      ⟪greenJetEnergyFactorCore heven x, (y : greenJetOddHilbertSubspace jet)⟫_ℝ =
        ⟪(x : greenJetEvenHilbertSubspace jet),
          greenJetEnergyFormalAdjointCore hodd y⟫_ℝ := by
  intro x y
  have hcore := linearMaps_formalAdjoint_of_basis
    (I := ℕ) (J := ℕ)
    (E₀ := (greenJetEnergyFactorCore heven).domain)
    (F₀ := (greenJetEnergyFormalAdjointCore hodd).domain)
    (E₁ := greenJetEvenHilbertSubspace jet)
    (F₁ := greenJetOddHilbertSubspace jet)
    (greenJetEnergyFactorDomainBasis heven)
    (greenJetEnergyFormalAdjointDomainBasis hodd)
    (greenJetEnergyFactorCore heven).toFun
    (greenJetEnergyFormalAdjointCore hodd).domain.subtype
    (greenJetEnergyFactorCore heven).domain.subtype
    (greenJetEnergyFormalAdjointCore hodd).toFun
    (fun i j => by
      simpa only [LinearPMap.toFun_eq_coe,
        greenJetEnergyFactorDomainBasis_apply,
        greenJetEnergyFactorDomainBasis_coe,
        greenJetEnergyFactorDomainBasis_subtype,
        greenJetEnergyFormalAdjointDomainBasis_apply,
        greenJetEnergyFormalAdjointDomainBasis_coe,
        greenJetEnergyFormalAdjointDomainBasis_subtype] using
          inner_greenJetOddSectorJet_eq_inner_even_succ hrep i j)
  exact hcore x y

/-- A partial real-linear map with a densely defined formal adjoint is
closable.  This graph proof is the real-Hilbert specialization of the usual
adjoint-domain criterion and avoids any choice of extension. -/
theorem linearPMap_isClosable_of_dense_formalAdjoint
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →ₗ.[ℝ] F) (S : F →ₗ.[ℝ] E)
    (hS : Dense (S.domain : Set F))
    (hformal : ∀ (x : T.domain) (y : S.domain),
      ⟪T x, (y : F)⟫_ℝ = ⟪(x : E), S y⟫_ℝ) :
    T.IsClosable := by
  let graphClosure := T.graph.topologicalClosure
  have hvertical :
      ∀ (p : E × F) (_hp : p ∈ graphClosure) (_hp0 : p.fst = 0),
        p.snd = 0 := by
    intro p hp hp0
    apply hS.eq_zero_of_inner_left ℝ
    intro z hz
    let zd : S.domain := ⟨z, hz⟩
    let annihilator : Set (E × F) :=
      {q | ⟪q.snd, z⟫_ℝ = ⟪q.fst, S zd⟫_ℝ}
    have hannihilatorClosed : IsClosed annihilator := by
      apply isClosed_eq
      · fun_prop
      · fun_prop
    have hgraph : (T.graph : Set (E × F)) ⊆ annihilator := by
      intro q hq
      rcases (LinearPMap.mem_graph_iff T).mp hq with ⟨x, hx, hTx⟩
      change ⟪q.snd, z⟫_ℝ = ⟪q.fst, S zd⟫_ℝ
      rw [← hTx, ← hx]
      exact hformal x zd
    have hpClosure : p ∈ _root_.closure (T.graph : Set (E × F)) := by
      change p ∈ T.graph.topologicalClosure at hp
      rw [← Submodule.topologicalClosure_coe]
      exact hp
    have hpAnnihilator : p ∈ annihilator :=
      closure_minimal hgraph hannihilatorClosed hpClosure
    change ⟪p.snd, z⟫_ℝ = ⟪p.fst, S zd⟫_ℝ at hpAnnihilator
    simpa [hp0] using hpAnnihilator
  refine ⟨graphClosure.toLinearPMap, ?_⟩
  exact (Submodule.toLinearPMap_graph_eq graphClosure hvertical).symm

/-- The Green energy factor has dense domain in the even Hilbert sector. -/
theorem greenJetEnergyFactorCore_dense_domain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    Dense ((greenJetEnergyFactorCore heven).domain :
      Set (greenJetEvenHilbertSubspace jet)) := by
  simpa [greenJetEnergyFactorCore] using greenJetEvenOperatorCore_dense jet

/-- The reverse shift has dense domain in the odd Hilbert sector. -/
theorem greenJetEnergyFormalAdjointCore_dense_domain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    Dense ((greenJetEnergyFormalAdjointCore hodd).domain :
      Set (greenJetOddHilbertSubspace jet)) := by
  simpa [greenJetEnergyFormalAdjointCore] using
    greenJetOddOperatorCore_dense jet

/-- The decisive all-order result: the Green energy factor is closable.
Its reverse shift is densely defined and formally adjoint; consequently the
topological closure of the graph of `B₀` is again the graph of an operator. -/
theorem greenJetEnergyFactorCore_isClosable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    (greenJetEnergyFactorCore heven).IsClosable := by
  let B := greenJetEnergyFactorCore heven
  let C := greenJetEnergyFormalAdjointCore hodd
  have hC : Dense (C.domain : Set (greenJetOddHilbertSubspace jet)) :=
    greenJetEnergyFormalAdjointCore_dense_domain hodd
  have hformal : ∀ (x : B.domain) (y : C.domain),
      ⟪B x, (y : greenJetOddHilbertSubspace jet)⟫_ℝ =
        ⟪(x : greenJetEvenHilbertSubspace jet), C y⟫_ℝ :=
    greenJetEnergyFactorCore_formalAdjointIdentity hrep heven hodd
  let graphClosure := B.graph.topologicalClosure
  have hvertical :
      ∀ (p : greenJetEvenHilbertSubspace jet ×
          greenJetOddHilbertSubspace jet)
        (_hp : p ∈ graphClosure) (_hp0 : p.fst = 0), p.snd = 0 := by
    intro p hp hp0
    apply hC.eq_zero_of_inner_left ℝ
    intro z hz
    let zd : C.domain := ⟨z, hz⟩
    let annihilator : Set (greenJetEvenHilbertSubspace jet ×
        greenJetOddHilbertSubspace jet) :=
      {q | ⟪q.snd, z⟫_ℝ = ⟪q.fst, C zd⟫_ℝ}
    have hannihilatorClosed : IsClosed annihilator := by
      apply isClosed_eq
      · fun_prop
      · fun_prop
    have hgraph : (B.graph : Set (greenJetEvenHilbertSubspace jet ×
        greenJetOddHilbertSubspace jet)) ⊆ annihilator := by
      intro q hq
      rcases (LinearPMap.mem_graph_iff B).mp hq with ⟨x, hx, hBx⟩
      change ⟪q.snd, z⟫_ℝ = ⟪q.fst, C zd⟫_ℝ
      rw [← hBx, ← hx]
      exact hformal x zd
    have hpClosure : p ∈ _root_.closure
        (B.graph : Set (greenJetEvenHilbertSubspace jet ×
          greenJetOddHilbertSubspace jet)) := by
      change p ∈ B.graph.topologicalClosure at hp
      rw [← Submodule.topologicalClosure_coe]
      exact hp
    have hpAnnihilator : p ∈ annihilator :=
      closure_minimal hgraph hannihilatorClosed hpClosure
    change ⟪p.snd, z⟫_ℝ = ⟪p.fst, C zd⟫_ℝ at hpAnnihilator
    simpa [hp0] using hpAnnihilator
  refine ⟨graphClosure.toLinearPMap, ?_⟩
  exact (Submodule.toLinearPMap_graph_eq graphClosure hvertical).symm

/-- The canonical closed Green energy factor.  No extension parameter is
chosen: this is the graph closure of the algebraically forced map
`B₀ e_n = o_n`. -/
def closedGreenJetEnergyFactor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (_hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (_hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    greenJetEvenHilbertSubspace jet →ₗ.[ℝ]
      greenJetOddHilbertSubspace jet :=
  (greenJetEnergyFactorCore heven).closure

/-- The closed factor really is closed. -/
theorem closedGreenJetEnergyFactor_isClosed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    (closedGreenJetEnergyFactor hrep heven hodd).IsClosed := by
  exact (greenJetEnergyFactorCore_isClosable hrep heven hodd).closure_isClosed

/-- The algebraic factor is contained in its canonical closed realization. -/
theorem greenJetEnergyFactorCore_le_closed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    greenJetEnergyFactorCore heven ≤
      closedGreenJetEnergyFactor hrep heven hodd :=
  (greenJetEnergyFactorCore heven).le_closure

/-- The original algebraic domain is a core for the closed Green energy
factor. -/
theorem closedGreenJetEnergyFactor_hasCore
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    (closedGreenJetEnergyFactor hrep heven hodd).HasCore
      (greenJetEnergyFactorCore heven).domain :=
  (greenJetEnergyFactorCore heven).closureHasCore

end

end CarrySelfAdjointOperator
