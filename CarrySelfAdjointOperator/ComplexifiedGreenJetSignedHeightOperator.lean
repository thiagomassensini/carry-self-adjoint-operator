import CarrySelfAdjointOperator.RealLinearPMapComplexification
import CarrySelfAdjointOperator.GreenJetReciprocalSignedHeightOperator

/-!
# Complex global signed-height operator

The global Green-jet reciprocal signed-height operator was constructed over a
real Hilbert carrier and proved maximal real self-adjoint.  This file applies
the domain-sensitive complexification theorem to that concrete operator.

No spectral input is added: the complex operator acts on `x + i y` by applying
the existing real operator independently to `x` and `y`.  Its natural domain
is exactly `D(A) + i D(A)`, and its complex Hilbert adjoint is itself.
-/

open scoped InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

open LinearPMap
open RealHilbertComplexification

/-- Real Hilbert carrier of the closed global signed-height operator. -/
abbrev ClosedGreenJetSignedHeightRealCarrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :=
  WithLp 2 (greenJetEvenHilbertSubspace jet ×
    greenJetOddHilbertSubspace jet)

/-- Canonical complex Hilbert carrier: two real quadratures of the existing
global signed-height space. -/
abbrev ClosedGreenJetSignedHeightComplexCarrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :=
  RealHilbertComplexification
    (ClosedGreenJetSignedHeightRealCarrier jet)

noncomputable instance greenJetEvenHilbertSubspaceCompleteSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (jet : (ℕ ⊕ ℕ) → E) :
    CompleteSpace (greenJetEvenHilbertSubspace jet) :=
  (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe

noncomputable instance greenJetOddHilbertSubspaceCompleteSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (jet : (ℕ ⊕ ℕ) → E) :
    CompleteSpace (greenJetOddHilbertSubspace jet) :=
  (greenJetOddHilbertSubspace_isClosed jet).completeSpace_coe

/-- The concrete global complex signed-height operator. -/
def complexifiedClosedGreenJetReciprocalSignedHeightOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hhead : greenJetEvenSectorJet jet 0 ∈
      (greenJetEvenShiftedTailCore jet).topologicalClosure) :
    ClosedGreenJetSignedHeightComplexCarrier jet →ₗ.[ℂ]
      ClosedGreenJetSignedHeightComplexCarrier jet :=
  (closedGreenJetReciprocalSignedHeightData
    hrep heven hodd hhead).complexification

/-- Exact natural domain, with no bounded extension: both quadratures must
belong to the original real operator domain. -/
theorem mem_complexifiedClosedGreenJetReciprocalSignedHeightOperator_domain_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hhead : greenJetEvenSectorJet jet 0 ∈
      (greenJetEvenShiftedTailCore jet).topologicalClosure)
    (x : ClosedGreenJetSignedHeightComplexCarrier jet) :
    x ∈ (complexifiedClosedGreenJetReciprocalSignedHeightOperator
        hrep heven hodd hhead).domain ↔
      re x ∈ (closedGreenJetReciprocalSignedHeightOperator
          hrep heven hodd hhead).domain ∧
        im x ∈ (closedGreenJetReciprocalSignedHeightOperator
          hrep heven hodd hhead).domain :=
  Iff.rfl

/-- On a packaged domain vector, the complex operator is exactly the two
real actions packaged as one complex vector. -/
theorem complexifiedClosedGreenJetReciprocalSignedHeightOperator_apply_mk
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hhead : greenJetEvenSectorJet jet 0 ∈
      (greenJetEvenShiftedTailCore jet).topologicalClosure)
    (x y : (closedGreenJetReciprocalSignedHeightOperator
      hrep heven hodd hhead).domain) :
    complexifiedClosedGreenJetReciprocalSignedHeightOperator
        hrep heven hodd hhead
        ⟨mk (x : ClosedGreenJetSignedHeightRealCarrier jet)
            (y : ClosedGreenJetSignedHeightRealCarrier jet),
          ⟨x.property, y.property⟩⟩ =
      mk (closedGreenJetReciprocalSignedHeightOperator
          hrep heven hodd hhead x)
        (closedGreenJetReciprocalSignedHeightOperator
          hrep heven hodd hhead y) :=
  rfl

/-- The concrete complex natural domain is dense. -/
theorem complexifiedClosedGreenJetReciprocalSignedHeightOperator_dense_domain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hhead : greenJetEvenSectorJet jet 0 ∈
      (greenJetEvenShiftedTailCore jet).topologicalClosure) :
    Dense ((complexifiedClosedGreenJetReciprocalSignedHeightOperator
      hrep heven hodd hhead).domain :
        Set (ClosedGreenJetSignedHeightComplexCarrier jet)) :=
  (closedGreenJetReciprocalSignedHeightData
    hrep heven hodd hhead).complexification_dense_domain

/-- Exact complex adjoint identity for the global signed-height operator. -/
theorem complexifiedClosedGreenJetReciprocalSignedHeightOperator_adjoint_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hhead : greenJetEvenSectorJet jet 0 ∈
      (greenJetEvenShiftedTailCore jet).topologicalClosure) :
    let data := closedGreenJetReciprocalSignedHeightData
      hrep heven hodd hhead
    LinearPMap.adjoint data.complexification =
      data.complexification :=
  (closedGreenJetReciprocalSignedHeightData
    hrep heven hodd hhead).complexification_adjoint_eq

/-- The concrete global operator is self-adjoint over the complex Hilbert
carrier. -/
theorem complexifiedClosedGreenJetReciprocalSignedHeightOperator_isSelfAdjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hhead : greenJetEvenSectorJet jet 0 ∈
      (greenJetEvenShiftedTailCore jet).topologicalClosure) :
    let data := closedGreenJetReciprocalSignedHeightData
      hrep heven hodd hhead
    IsSelfAdjoint data.complexification :=
  (closedGreenJetReciprocalSignedHeightData
    hrep heven hodd hhead).complexification_isSelfAdjoint

/-- Consequently, the complex global signed-height operator is closed. -/
theorem complexifiedClosedGreenJetReciprocalSignedHeightOperator_isClosed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hhead : greenJetEvenSectorJet jet 0 ∈
      (greenJetEvenShiftedTailCore jet).topologicalClosure) :
    (complexifiedClosedGreenJetReciprocalSignedHeightOperator
      hrep heven hodd hhead).IsClosed :=
  (closedGreenJetReciprocalSignedHeightData
    hrep heven hodd hhead).complexification_isClosed

end

end CarrySelfAdjointOperator
