import CarrySelfAdjointOperator.GreenJetEnergyFactor
import CarrySelfAdjointOperator.CanonicalLDLPrefixReduction
import CarrySelfAdjointOperator.CompletedGreenJetSignedHeightIntertwiner
import CarrySelfAdjointOperator.GreenJetJacobiFiniteCompression
import CarrySelfAdjointOperator.GreenJetMaximalAdjointSquare
import CarrySelfAdjointOperator.GreenJetReciprocalSignedHeightOperator

/-!
# Exact current status of the infinite height construction

This module packages what the current theorem graph really obtains from one
all-order Green--Wronskian moment-kernel realization with globally independent
even and odd jets:

* strict positivity of every Hankel pair;
* positive-definite canonical finite Jacobi sections;
* exact principal compatibility and one entrywise infinite Jacobi matrix;
* a canonical closed Green energy factor on dense parity cores;
* a positive symmetric Jacobi `LinearPMap` on the dense even core;
* the exact formal-adjoint factorization `J₀ = C₀ B₀`;
* the canonical positive self-adjoint realization `J = B* B` after completion;
* the exact operator inclusion `J₀ ≤ J`;
* equality of every finite compression of `J` with the projective matrix;
* the kernel chain `ker J = 0 ↔ ker closure(B₀) = 0 ↔ B₀⁻¹ is closable`; and
* without that zero-mass gate, the canonical restriction to `(ker B)ᗮ`
  and a global signed reciprocal block there which is densely defined,
  closed, and maximal real self-adjoint;
* once the exact zero-mass gate is supplied, the full-carrier signed
  reciprocal block `H(x,y) = (B⁻¹y,(B*)⁻¹x)` which is densely defined,
  closed, and maximal real self-adjoint;
* the exact two-step law `(Jx,0) ↦ (0,Bx) ↦ (x,0)`, identifying the
  first channel of `H²` with the natural inverse of `J`; and
* exact isometric compatibility of all finite signed-height carriers.

The infinite positive Jacobi operator is therefore no longer an extension
parameter.  The signed reciprocal realization now supplies a global operator
whose square is `J⁻¹` on the natural first-channel range, without requiring a
direct construction of `J^(-1/2)` through an unbounded Borel functional
calculus API.  The reduced source removes the zero mode canonically, so its
construction, completed moment resolvent, and closed-graph limit do not
require the head--tail approximation.  That approximation remains equivalent
to replacing the reduced even source by the full even carrier.  Identifying
the concrete projective TFVD jets with the canonical Green moment kernel is
still required to instantiate the reduced certificate without inputs; the
radial normalized Taylor carrier cannot supply this identification because
its first odd complex jet vanishes.  After that carrier identification,
identifying the nonzero spectrum of the reduced operator with all Genuine zero
heights is a separate theorem.  No critical-line confinement theorem follows
from self-adjointness alone.
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
factor from which the maximal-adjoint square is constructed. -/
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
