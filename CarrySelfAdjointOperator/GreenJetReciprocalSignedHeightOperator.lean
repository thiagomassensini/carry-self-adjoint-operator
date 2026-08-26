import CarrySelfAdjointOperator.GreenJetMomentZeroMassCriterion
import CarrySelfAdjointOperator.RealLinearPMapKernelReduction
import Mathlib.Tactic

/-!
# The global reciprocal signed-height operator

The positive global Jacobi operator has already been constructed as the
maximal-adjoint square `J = B* B` of the closed Green energy factor.  The
height operator must therefore be formed after closure, not as a direct limit
of the finite inverse square roots.

This file realizes its signed form without an unbounded functional-calculus
API.  On the Hilbert sum of the even and odd Green sectors it is the reciprocal
off-diagonal block

`H (x, y) = (B⁻¹ y, (B*)⁻¹ x)`.

The completed head-in-shifted-tail identity supplies exactly the two missing
dense-range/injectivity facts.  Under that already isolated zero-mass gate,
the two inverse channels are mutual maximal adjoints, hence `H` is densely
defined, closed, and maximal real self-adjoint.
-/

open scoped InnerProductSpace LinearPMap RealInnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

@[reducible] private def coherentReducedGreenJetEvenInnerProductSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    InnerProductSpace ℝ (greenJetEvenHilbertSubspace jet) :=
  { (inferInstance :
      InnerProductSpace ℝ (greenJetEvenHilbertSubspace jet)) with
    toNormedSpace := inferInstance }

@[reducible] private def coherentReducedGreenJetOddInnerProductSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    InnerProductSpace ℝ (greenJetOddHilbertSubspace jet) :=
  { (inferInstance :
      InnerProductSpace ℝ (greenJetOddHilbertSubspace jet)) with
    toNormedSpace := inferInstance }

/-! ## Dense ranges of the closed Green factor and its adjoint -/

/-- The algebraic Green factor maps its complete even core onto the complete
odd core. -/
theorem greenJetEnergyFactorCore_range_eq_oddCore
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    LinearMap.range (greenJetEnergyFactorCore heven).toFun =
      greenJetOddOperatorCore jet := by
  exact (greenJetEvenOperatorCoreBasis heven).constr_range ℝ

/-- The closed Green factor has dense range unconditionally: its range still
contains the dense odd algebraic core. -/
theorem closedGreenJetEnergyFactor_dense_range
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    Dense (LinearMap.range
      (closedGreenJetEnergyFactor hrep heven hodd).toFun :
        Set (greenJetOddHilbertSubspace jet)) := by
  apply (greenJetOddOperatorCore_dense jet).mono
  intro y hy
  rw [← greenJetEnergyFactorCore_range_eq_oddCore heven] at hy
  rcases hy with ⟨x, hx⟩
  let xc : (closedGreenJetEnergyFactor hrep heven hodd).domain :=
    Submodule.inclusion
      (greenJetEnergyFactorCore_le_closed hrep heven hodd).1 x
  refine ⟨xc, ?_⟩
  rw [← hx]
  exact (LinearPMap.apply_comp_inclusion
    (greenJetEnergyFactorCore_le_closed hrep heven hodd) x).symm

/-- The maximal adjoint of the closed Green factor has dense domain because
it contains the dense algebraic reverse-shift core. -/
theorem closedGreenJetEnergyRealAdjoint_dense_domain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    Dense ((closedGreenJetEnergyRealAdjoint hrep heven hodd).domain :
      Set (greenJetOddHilbertSubspace jet)) := by
  exact (greenJetEnergyFormalAdjointCore_dense_domain hodd).mono
    (greenJetEnergyFormalAdjointCore_le_closedRealAdjoint
      hrep heven hodd).1

/-- The maximal adjoint has dense range precisely once the shifted even tail
is dense. -/
theorem closedGreenJetEnergyRealAdjoint_dense_range_of_head_mem_tail
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hhead : greenJetEvenSectorJet jet 0 ∈
      (greenJetEvenShiftedTailCore jet).topologicalClosure) :
    Dense (LinearMap.range
      (closedGreenJetEnergyRealAdjoint hrep heven hodd).toFun :
        Set (greenJetEvenHilbertSubspace jet)) := by
  have hcoreRange : Dense
      (LinearMap.range (greenJetEnergyFormalAdjointCore hodd).toFun :
        Set (greenJetEvenHilbertSubspace jet)) := by
    rw [greenJetEnergyFormalAdjointCore_range_eq_shiftedTail hodd]
    exact (greenJetEvenShiftedTailCore_dense_iff_head_mem jet).2 hhead
  apply hcoreRange.mono
  rintro y ⟨x, rfl⟩
  let xa : (closedGreenJetEnergyRealAdjoint hrep heven hodd).domain :=
    Submodule.inclusion
      (greenJetEnergyFormalAdjointCore_le_closedRealAdjoint
        hrep heven hodd).1 x
  refine ⟨xa, ?_⟩
  exact (LinearPMap.apply_comp_inclusion
    (greenJetEnergyFormalAdjointCore_le_closedRealAdjoint
      hrep heven hodd) x).symm

/-! ## Canonical support reduction without a zero-mass premise -/

/-- Canonical reciprocal signed-height package on the nonzero support of the
closed Green factor.  It is maximal self-adjoint without a head-in-tail or
zero-mass hypothesis. -/
def closedGreenJetReducedReciprocalSignedHeightData
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    @LinearPMap.RealReducedMaximalSelfAdjointData
      (greenJetEvenHilbertSubspace jet)
      (greenJetOddHilbertSubspace jet)
      (inferInstanceAs (NormedAddCommGroup
        (greenJetEvenHilbertSubspace jet)))
      (coherentReducedGreenJetEvenInnerProductSpace jet)
      (inferInstanceAs (NormedAddCommGroup
        (greenJetOddHilbertSubspace jet)))
      (coherentReducedGreenJetOddInnerProductSpace jet) := by
  letI : CompleteSpace
      (CanonicalGreenJetSignedHeightHilbertSpace jet) := inferInstance
  letI : InnerProductSpace ℝ (greenJetEvenHilbertSubspace jet) :=
    coherentReducedGreenJetEvenInnerProductSpace jet
  letI : InnerProductSpace ℝ (greenJetOddHilbertSubspace jet) :=
    coherentReducedGreenJetOddInnerProductSpace jet
  letI : CompleteSpace (greenJetEvenHilbertSubspace jet) :=
    (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe
  letI : CompleteSpace (greenJetOddHilbertSubspace jet) :=
    (greenJetOddHilbertSubspace_isClosed jet).completeSpace_coe
  let B : greenJetEvenHilbertSubspace jet →ₗ.[ℝ]
      greenJetOddHilbertSubspace jet :=
    closedGreenJetEnergyFactor hrep heven hodd
  let hB : Dense (B.domain : Set (greenJetEvenHilbertSubspace jet)) :=
    closedGreenJetEnergyFactor_dense_domain hrep heven hodd
  have hBadjDomain : Dense ((LinearPMap.realAdjoint
      (E := greenJetEvenHilbertSubspace jet)
      (F := greenJetOddHilbertSubspace jet) B hB).domain :
        Set (greenJetOddHilbertSubspace jet)) := by
    change Dense ((closedGreenJetEnergyRealAdjoint
      hrep heven hodd).domain : Set (greenJetOddHilbertSubspace jet))
    exact closedGreenJetEnergyRealAdjoint_dense_domain hrep heven hodd
  have hBclosed : B.IsClosed :=
    closedGreenJetEnergyFactor_isClosed hrep heven hodd
  have hBrange : Dense (LinearMap.range B.toFun :
      Set (greenJetOddHilbertSubspace jet)) :=
    closedGreenJetEnergyFactor_dense_range hrep heven hodd
  exact B.reducedRealReciprocalOffDiagonalBundle
    hB hBadjDomain hBclosed hBrange

/-- The reduced global signed-height operator itself. -/
def closedGreenJetReducedReciprocalSignedHeightOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    let data := closedGreenJetReducedReciprocalSignedHeightData
      hrep heven hodd
    WithLp 2 (data.sourceSupport × greenJetOddHilbertSubspace jet) →ₗ.[ℝ]
      WithLp 2 (data.sourceSupport × greenJetOddHilbertSubspace jet) :=
  (closedGreenJetReducedReciprocalSignedHeightData
    hrep heven hodd).selfAdjointData.operator

/-- The reduced Green signed-height operator is maximal real self-adjoint. -/
theorem closedGreenJetReducedReciprocalSignedHeightOperator_adjoint_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    let data := closedGreenJetReducedReciprocalSignedHeightData
      hrep heven hodd
    data.selfAdjointData.operator.realAdjoint
        data.selfAdjointData.denseDomain =
      data.selfAdjointData.operator :=
  (closedGreenJetReducedReciprocalSignedHeightData
    hrep heven hodd).selfAdjointData.adjoint_eq

/-! ## The reciprocal signed operator -/

/-- Complete reciprocal signed-height package formed after closure of the
Green factor. -/
def closedGreenJetReciprocalSignedHeightData
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hhead : greenJetEvenSectorJet jet 0 ∈
      (greenJetEvenShiftedTailCore jet).topologicalClosure) :
    LinearPMap.RealMaximalSelfAdjointData
      (WithLp 2 (greenJetEvenHilbertSubspace jet ×
        greenJetOddHilbertSubspace jet)) := by
  letI : CompleteSpace
      (CanonicalGreenJetSignedHeightHilbertSpace jet) := inferInstance
  letI : CompleteSpace (greenJetEvenHilbertSubspace jet) :=
    (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe
  letI : CompleteSpace (greenJetOddHilbertSubspace jet) :=
    (greenJetOddHilbertSubspace_isClosed jet).completeSpace_coe
  let B : greenJetEvenHilbertSubspace jet →ₗ.[ℝ]
      greenJetOddHilbertSubspace jet :=
    closedGreenJetEnergyFactor hrep heven hodd
  let hB : Dense (B.domain : Set (greenJetEvenHilbertSubspace jet)) :=
    closedGreenJetEnergyFactor_dense_domain hrep heven hodd
  have hBadjDomain : Dense ((LinearPMap.realAdjoint
      (E := greenJetEvenHilbertSubspace jet)
      (F := greenJetOddHilbertSubspace jet) B hB).domain :
      Set (greenJetOddHilbertSubspace jet)) := by
    change Dense ((closedGreenJetEnergyRealAdjoint
      hrep heven hodd).domain : Set (greenJetOddHilbertSubspace jet))
    exact closedGreenJetEnergyRealAdjoint_dense_domain hrep heven hodd
  have hBclosed : B.IsClosed :=
    closedGreenJetEnergyFactor_isClosed hrep heven hodd
  have hBrange : Dense (LinearMap.range B.toFun :
      Set (greenJetOddHilbertSubspace jet)) :=
    closedGreenJetEnergyFactor_dense_range hrep heven hodd
  have hBadjRange : Dense (LinearMap.range
      (LinearPMap.realAdjoint
        (E := greenJetEvenHilbertSubspace jet)
        (F := greenJetOddHilbertSubspace jet) B hB).toFun :
        Set (greenJetEvenHilbertSubspace jet)) := by
    change Dense (LinearMap.range
      (closedGreenJetEnergyRealAdjoint hrep heven hodd).toFun :
        Set (greenJetEvenHilbertSubspace jet))
    exact closedGreenJetEnergyRealAdjoint_dense_range_of_head_mem_tail
      hrep heven hodd hhead
  have hBker : LinearMap.ker B.toFun = ⊥ :=
    closedGreenJetEnergyFactor_ker_eq_bot_of_head_mem_shiftedTail
      hrep heven hodd hhead
  exact LinearPMap.realReciprocalOffDiagonalSelfAdjointData
    (E := greenJetEvenHilbertSubspace jet)
    (F := greenJetOddHilbertSubspace jet)
    B hB hBadjDomain hBclosed hBrange hBadjRange hBker

/-- The global signed-height operator itself. -/
def closedGreenJetReciprocalSignedHeightOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hhead : greenJetEvenSectorJet jet 0 ∈
      (greenJetEvenShiftedTailCore jet).topologicalClosure) :
    WithLp 2 (greenJetEvenHilbertSubspace jet ×
        greenJetOddHilbertSubspace jet) →ₗ.[ℝ]
      WithLp 2 (greenJetEvenHilbertSubspace jet ×
        greenJetOddHilbertSubspace jet) :=
  (closedGreenJetReciprocalSignedHeightData
    hrep heven hodd hhead).operator

/-- Both reciprocal channels have dense natural range domains. -/
theorem closedGreenJetReciprocalSignedHeightOperator_dense_domain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hhead : greenJetEvenSectorJet jet 0 ∈
      (greenJetEvenShiftedTailCore jet).topologicalClosure) :
    Dense ((closedGreenJetReciprocalSignedHeightOperator
      hrep heven hodd hhead).domain :
        Set (WithLp 2 (greenJetEvenHilbertSubspace jet ×
          greenJetOddHilbertSubspace jet))) :=
  (closedGreenJetReciprocalSignedHeightData
    hrep heven hodd hhead).denseDomain

/-- Maximal real adjoint with the bundled canonical density proof. -/
def closedGreenJetReciprocalSignedHeightOperatorRealAdjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hhead : greenJetEvenSectorJet jet 0 ∈
      (greenJetEvenShiftedTailCore jet).topologicalClosure) :
    WithLp 2 (greenJetEvenHilbertSubspace jet ×
        greenJetOddHilbertSubspace jet) →ₗ.[ℝ]
      WithLp 2 (greenJetEvenHilbertSubspace jet ×
        greenJetOddHilbertSubspace jet) :=
  let data := closedGreenJetReciprocalSignedHeightData
    hrep heven hodd hhead
  data.operator.realAdjoint data.denseDomain

/-- The global reciprocal signed-height operator is maximal real
self-adjoint. -/
theorem closedGreenJetReciprocalSignedHeightOperator_isMaximalRealSelfAdjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hhead : greenJetEvenSectorJet jet 0 ∈
      (greenJetEvenShiftedTailCore jet).topologicalClosure) :
    closedGreenJetReciprocalSignedHeightOperatorRealAdjoint
        hrep heven hodd hhead =
      closedGreenJetReciprocalSignedHeightOperator
        hrep heven hodd hhead :=
  (closedGreenJetReciprocalSignedHeightData
    hrep heven hodd hhead).adjoint_eq

/-- Consequently the global reciprocal signed-height operator is closed. -/
theorem closedGreenJetReciprocalSignedHeightOperator_isClosed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hhead : greenJetEvenSectorJet jet 0 ∈
      (greenJetEvenShiftedTailCore jet).topologicalClosure) :
    (closedGreenJetReciprocalSignedHeightOperator
      hrep heven hodd hhead).IsClosed :=
  (closedGreenJetReciprocalSignedHeightData
    hrep heven hodd hhead).isClosed

/-- Moment-only wrapper for the same canonical operator. -/
def closedGreenJetMomentReciprocalSignedHeightOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hvanish : HasVanishingGreenJetHeadTailMomentDefect moments) :
    WithLp 2 (greenJetEvenHilbertSubspace jet ×
        greenJetOddHilbertSubspace jet) →ₗ.[ℝ]
      WithLp 2 (greenJetEvenHilbertSubspace jet ×
        greenJetOddHilbertSubspace jet) :=
  closedGreenJetReciprocalSignedHeightOperator hrep heven hodd
    ((greenJetEvenShiftedTailCore_head_mem_iff_momentDefect hrep).2 hvanish)

/-! ## Automatic ambient completion -/

/-- Canonical reduced reciprocal signed-height package after automatic
Hilbert completion.  Unlike the full-carrier wrapper below, this construction
does not require vanishing head-tail moment defect. -/
def canonicalCompletedGreenJetReducedReciprocalSignedHeightData
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    @LinearPMap.RealReducedMaximalSelfAdjointData
      (greenJetEvenHilbertSubspace (completedGreenJet jet))
      (greenJetOddHilbertSubspace (completedGreenJet jet))
      (inferInstanceAs (NormedAddCommGroup
        (greenJetEvenHilbertSubspace (completedGreenJet jet))))
      (coherentReducedGreenJetEvenInnerProductSpace (completedGreenJet jet))
      (inferInstanceAs (NormedAddCommGroup
        (greenJetOddHilbertSubspace (completedGreenJet jet))))
      (coherentReducedGreenJetOddInnerProductSpace (completedGreenJet jet)) :=
  closedGreenJetReducedReciprocalSignedHeightData
    (completedGreenJet_gramRepresentation hrep)
    (completedGreenJet_even_linearIndependent heven)
    (completedGreenJet_odd_linearIndependent hodd)

/-- The automatically completed reduced reciprocal operator is maximal real
self-adjoint, with no zero-mass premise. -/
theorem canonicalCompletedGreenJetReducedReciprocalSignedHeightOperator_adjoint_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    let data := canonicalCompletedGreenJetReducedReciprocalSignedHeightData
      hrep heven hodd
    data.selfAdjointData.operator.realAdjoint
        data.selfAdjointData.denseDomain =
      data.selfAdjointData.operator :=
  (canonicalCompletedGreenJetReducedReciprocalSignedHeightData
    hrep heven hodd).selfAdjointData.adjoint_eq

/-- Canonical reciprocal signed-height package after automatic Hilbert
completion of an arbitrary ambient Green-jet realization. -/
def canonicalCompletedGreenJetMomentReciprocalSignedHeightData
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hvanish : HasVanishingGreenJetHeadTailMomentDefect moments) :
    LinearPMap.RealMaximalSelfAdjointData
      (WithLp 2
        (greenJetEvenHilbertSubspace (completedGreenJet jet) ×
          greenJetOddHilbertSubspace (completedGreenJet jet))) :=
  closedGreenJetReciprocalSignedHeightData
    (completedGreenJet_gramRepresentation hrep)
    (completedGreenJet_even_linearIndependent heven)
    (completedGreenJet_odd_linearIndependent hodd)
    ((greenJetEvenShiftedTailCore_head_mem_iff_momentDefect
      (completedGreenJet_gramRepresentation hrep)).2 hvanish)

/-- Canonical completed global signed-height operator. -/
def canonicalCompletedGreenJetMomentReciprocalSignedHeightOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hvanish : HasVanishingGreenJetHeadTailMomentDefect moments) :
    WithLp 2
        (greenJetEvenHilbertSubspace (completedGreenJet jet) ×
          greenJetOddHilbertSubspace (completedGreenJet jet)) →ₗ.[ℝ]
      WithLp 2
        (greenJetEvenHilbertSubspace (completedGreenJet jet) ×
          greenJetOddHilbertSubspace (completedGreenJet jet)) :=
  (canonicalCompletedGreenJetMomentReciprocalSignedHeightData
    hrep heven hodd hvanish).operator

/-- The automatically completed reciprocal operator has dense domain. -/
theorem canonicalCompletedGreenJetMomentReciprocalSignedHeightOperator_dense_domain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hvanish : HasVanishingGreenJetHeadTailMomentDefect moments) :
    Dense ((canonicalCompletedGreenJetMomentReciprocalSignedHeightOperator
      hrep heven hodd hvanish).domain :
        Set (WithLp 2
          (greenJetEvenHilbertSubspace (completedGreenJet jet) ×
            greenJetOddHilbertSubspace (completedGreenJet jet)))) :=
  (canonicalCompletedGreenJetMomentReciprocalSignedHeightData
    hrep heven hodd hvanish).denseDomain

/-- The automatically completed reciprocal operator is maximal real
self-adjoint. -/
theorem canonicalCompletedGreenJetMomentReciprocalSignedHeightOperator_adjoint_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hvanish : HasVanishingGreenJetHeadTailMomentDefect moments) :
    let data := canonicalCompletedGreenJetMomentReciprocalSignedHeightData
      hrep heven hodd hvanish
    data.operator.realAdjoint data.denseDomain = data.operator :=
  (canonicalCompletedGreenJetMomentReciprocalSignedHeightData
    hrep heven hodd hvanish).adjoint_eq

/-- The automatically completed reciprocal operator is closed. -/
theorem canonicalCompletedGreenJetMomentReciprocalSignedHeightOperator_isClosed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (hvanish : HasVanishingGreenJetHeadTailMomentDefect moments) :
    (canonicalCompletedGreenJetMomentReciprocalSignedHeightOperator
      hrep heven hodd hvanish).IsClosed :=
  (canonicalCompletedGreenJetMomentReciprocalSignedHeightData
    hrep heven hodd hvanish).isClosed

end

end CarrySelfAdjointOperator
