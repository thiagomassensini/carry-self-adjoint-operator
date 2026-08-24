import CarrySelfAdjointOperator.GreenJetJacobiCore
import Mathlib.Tactic

/-!
# The Green-jet Jacobi core as a formal-adjoint square

The all-order Green moment identity supplies two densely defined maps:

* `B₀ e_n = o_n`, the Green energy factor;
* `C₀ o_n = e_(n+1)`, its algebraic formal adjoint.

Their formal-adjoint identity was already proved on the two dense cores.  This
file adds the missing operator-level statement: `B₀` lands in the domain of
`C₀`, and the literal composition `C₀ B₀` is exactly the infinite Jacobi core
`J₀`.  Thus the all-order limit has the factorization `J₀ = C₀ B₀` before any
self-adjoint-extension choice.
-/

open scoped InnerProductSpace LinearPMap RealInnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

/-- The Green energy factor with its codomain restricted to the algebraic odd
core, which is the domain of the formal adjoint. -/
def greenJetEnergyFactorToFormalAdjointDomain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    greenJetEvenOperatorCore jet →ₗ[ℝ]
      greenJetOddOperatorCore jet :=
  (greenJetEvenOperatorCoreBasis heven).constr ℝ
    (greenJetOddCoreJet jet)

@[simp] theorem greenJetEnergyFactorToFormalAdjointDomain_jet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (n : ℕ) :
    greenJetEnergyFactorToFormalAdjointDomain heven
        (greenJetEvenCoreJet jet n) =
      greenJetOddCoreJet jet n := by
  rw [← greenJetEvenOperatorCoreBasis_apply heven n]
  exact (greenJetEvenOperatorCoreBasis heven).constr_basis ℝ
    (greenJetOddCoreJet jet) n

/-- Restricting the codomain loses no information: after inclusion in the
odd Hilbert sector this is the original Green energy factor. -/
theorem greenJetEnergyFactorToFormalAdjointDomain_coe
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (x : greenJetEvenOperatorCore jet) :
    ((greenJetEnergyFactorToFormalAdjointDomain heven x :
        greenJetOddOperatorCore jet) : greenJetOddHilbertSubspace jet) =
      greenJetEnergyFactorCore heven x := by
  let includeOdd := (greenJetOddOperatorCore jet).subtype
  have hmaps :
      includeOdd.comp (greenJetEnergyFactorToFormalAdjointDomain heven) =
        (greenJetEnergyFactorCore heven).toFun := by
    apply (greenJetEvenOperatorCoreBasis heven).ext
    intro n
    rw [greenJetEvenOperatorCoreBasis_apply]
    simp only [LinearMap.comp_apply]
    rw [greenJetEnergyFactorToFormalAdjointDomain_jet]
    change
      ((greenJetOddCoreJet jet n : greenJetOddOperatorCore jet) :
          greenJetOddHilbertSubspace jet) =
        greenJetEnergyFactorCore heven (greenJetEvenCoreJet jet n)
    rw [greenJetEnergyFactorCore_jet]
    rfl
  exact LinearMap.congr_fun hmaps x

/-- Linear-map presentation of the already constructed formal adjoint on its
odd algebraic domain.  Keeping this map in the ordinary `LinearMap` category
avoids changing scalar instances while composing the two core maps. -/
def greenJetEnergyFormalAdjointOnOddCoreMap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    greenJetOddOperatorCore jet →ₗ[ℝ]
      greenJetEvenHilbertSubspace jet :=
  (greenJetOddOperatorCoreBasis hodd).constr ℝ
    (fun n => greenJetEvenSectorJet jet (n + 1))

@[simp] theorem greenJetEnergyFormalAdjointOnOddCoreMap_jet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (n : ℕ) :
    greenJetEnergyFormalAdjointOnOddCoreMap hodd
        (greenJetOddCoreJet jet n) =
      greenJetEvenSectorJet jet (n + 1) := by
  rw [← greenJetOddOperatorCoreBasis_apply hodd n]
  exact (greenJetOddOperatorCoreBasis hodd).constr_basis ℝ
    (fun n => greenJetEvenSectorJet jet (n + 1)) n

/-- The linear-map presentation agrees pointwise with the partial formal
adjoint on its exact domain. -/
theorem greenJetEnergyFormalAdjointOnOddCoreMap_eq_core
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (y : greenJetOddOperatorCore jet) :
    greenJetEnergyFormalAdjointOnOddCoreMap hodd y =
      greenJetEnergyFormalAdjointCore hodd y := by
  rfl

/-- Literal composition of the formal-adjoint pair on their common algebraic
domain. -/
def greenJetFormalAdjointSquareCore
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    greenJetEvenHilbertSubspace jet →ₗ.[ℝ]
      greenJetEvenHilbertSubspace jet where
  domain := greenJetEvenOperatorCore jet
  toFun := (greenJetEnergyFormalAdjointOnOddCoreMap hodd).comp
    (greenJetEnergyFactorToFormalAdjointDomain heven)

/-- The formal-adjoint square acts by the moment-coordinate shift on every
vector of the all-order core. -/
theorem greenJetFormalAdjointSquareCore_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (x : greenJetEvenOperatorCore jet) :
    greenJetFormalAdjointSquareCore heven hodd x =
      greenJetJacobiCore heven x := by
  have hmaps :
      (greenJetEnergyFormalAdjointOnOddCoreMap hodd).comp
          (greenJetEnergyFactorToFormalAdjointDomain heven) =
        greenJetJacobiCoreMap heven := by
    apply (greenJetEvenOperatorCoreBasis heven).ext
    intro n
    rw [greenJetEvenOperatorCoreBasis_apply]
    simp only [LinearMap.comp_apply]
    rw [
      greenJetEnergyFactorToFormalAdjointDomain_jet,
      greenJetEnergyFormalAdjointOnOddCoreMap_jet,
      greenJetJacobiCoreMap_jet]
  exact LinearMap.congr_fun hmaps x

/-- Exact operator-level factorization of the infinite Jacobi core by the
Green energy map and its forced formal adjoint. -/
theorem greenJetFormalAdjointSquareCore_eq_jacobiCore
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    greenJetFormalAdjointSquareCore heven hodd =
      greenJetJacobiCore heven := by
  apply LinearPMap.ext
  · rfl
  intro x _ hx
  exact greenJetFormalAdjointSquareCore_apply heven hodd ⟨x, hx⟩

/-- With the Green moment representation, the two factors in the exact
composition are genuinely formal adjoints on dense domains. -/
theorem greenJetJacobiCore_eq_formalAdjointSquare_with_adjointIdentity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    greenJetJacobiCore heven =
        greenJetFormalAdjointSquareCore heven hodd ∧
      (∀ (x : (greenJetEnergyFactorCore heven).domain)
        (y : (greenJetEnergyFormalAdjointCore hodd).domain),
        ⟪greenJetEnergyFactorCore heven x,
            (y : greenJetOddHilbertSubspace jet)⟫_ℝ =
          ⟪(x : greenJetEvenHilbertSubspace jet),
            greenJetEnergyFormalAdjointCore hodd y⟫_ℝ) := by
  exact ⟨(greenJetFormalAdjointSquareCore_eq_jacobiCore
    heven hodd).symm,
    greenJetEnergyFactorCore_formalAdjointIdentity hrep heven hodd⟩

end

end CarrySelfAdjointOperator
