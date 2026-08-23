import CarrySelfAdjointOperator.GreenJetEnergyFactor
import CarrySelfAdjointOperator.CanonicalLDLPrefixReduction
import CarrySelfAdjointOperator.CompletedGreenJetSignedHeightIntertwiner

/-!
# Exact current status of the infinite height construction

This module packages what the current theorem graph really obtains from one
all-order Green--Wronskian moment-kernel realization with globally independent
even and odd jets:

* strict positivity of every Hankel pair;
* positive-definite canonical finite Jacobi sections;
* exact principal compatibility and one entrywise infinite Jacobi matrix;
* a canonical closed Green energy factor on dense parity cores; and
* exact isometric compatibility of all finite signed-height carriers.

It deliberately stops before declaring an infinite self-adjoint height
operator.  The entrywise matrix is not yet a `LinearPMap`; the closed factor
has not yet been promoted to the positive self-adjoint operator `B† B`; and
the finite inverse square roots are not yet proved to intertwine under the
cutoff inclusions.  Those are operator-theoretic obligations, not aliases for
the results below.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- All-order strict positivity of the unshifted Hankel sections supplied by
one globally independent even Green-jet family. -/
theorem canonicalGreenJetHankelGramPosDef
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (N : ℕ) :
    (hankelGram moments N).PosDef :=
  hankelGram_posDef_of_gramRepresentation
    (greenWronskianMomentKernel_even_momentGram hrep) N
    (greenJetEven_prefix_linearIndependent heven N)

/-- All-order strict positivity of the shifted Hankel sections supplied by
one globally independent odd Green-jet family. -/
theorem canonicalGreenJetShiftedHankelPosDef
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) :
    (shiftedHankel moments N).PosDef :=
  shiftedHankel_posDef_of_gramRepresentation
    (greenWronskianMomentKernel_odd_shiftedMomentGram hrep) N
    (greenJetOdd_prefix_linearIndependent hodd N)

/-- Every canonical finite Jacobi section is positive definite under the same
single all-order Green-jet realization. -/
theorem canonicalGreenJetFiniteJacobi_posDef
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) :
    (canonicalFiniteJacobiSection moments N
      (canonicalGreenJetHankelGramPosDef hrep heven N)).PosDef :=
  canonicalFiniteJacobiSection_posDef_of_shiftedGram
    (greenWronskianMomentKernel_odd_shiftedMomentGram hrep) N
    (canonicalGreenJetHankelGramPosDef hrep heven N)
    (greenJetOdd_prefix_linearIndependent hodd N)

/-- The canonical Jacobi tower determines one infinite coefficient matrix and
every finite Jacobi section is literally its corresponding principal block. -/
theorem canonicalGreenJetJacobiLimit_submatrix
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (N : ℕ) :
    (canonicalJacobiTowerLimitMatrix moments
        (canonicalGreenJetHankelGramPosDef hrep heven)).submatrix
          (fun i : Fin N => (i : ℕ))
          (fun i : Fin N => (i : ℕ)) =
      canonicalFiniteJacobiSection moments N
        (canonicalGreenJetHankelGramPosDef hrep heven N) :=
  canonicalJacobiTowerLimitMatrix_submatrix_unconditional
    moments (canonicalGreenJetHankelGramPosDef hrep heven) N

/-- The same all-order realization supplies the canonical closed energy
factor.  This is the exact operatorial endpoint currently proved before the
construction of `B† B`. -/
theorem canonicalGreenJetClosedEnergyFactor_isClosed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    (closedGreenJetEnergyFactor hrep heven hodd).IsClosed :=
  closedGreenJetEnergyFactor_isClosed hrep heven hodd

end

end CarrySelfAdjointOperator
