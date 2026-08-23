import CarrySelfAdjointOperator.CompletedTfvdCanonicalSourceIntertwining
import CarrySelfAdjointOperator.CompletedGammaCauchyScalarization
import CarrySelfAdjointOperator.GreenJetEnergyFactor
import CarrySelfAdjointOperator.CanonicalLDLPrefixReduction
import NativeCarryC3Crosswalk.FinalGenuineZeroConfinement

/-!
# Exact C3 confinement and all-order height closure reduction

This file joins the two theorem surfaces without pretending that their final
concrete certificates have already been constructed.

For zero confinement, the sole remaining datum is the completed
Wronskian/Cauchy scalarization of the canonical six-camera source.  The source
itself is no longer abstract: the preceding module identifies it literally
with the public full-ledger TFVD/C3 source, and its nondegeneracy is proved
upstream.

For the height operator, one all-order Green--Wronskian moment-kernel Gram
realization with globally independent even and odd jets supplies, at once:

* strict positivity of both Hankel towers;
* exact projectivity of the canonical finite Jacobi sections; and
* the canonical closed Green energy factor.

No zero table, fitted matrix, order-specific positivity premise, or external
whitening compatibility enters either reduction.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Exact remaining scalarization datum for the canonical source which PR #6
identifies with the completed public TFVD/C3 ledger source. -/
def CanonicalCompletedC3GammaCauchyScalarizationReduction : Prop :=
  HasCanonicalCompletedNativeGammaCauchyScalarization
    canonicalCompletedC3SixCameraSource

/-- Once the exact scalarization is available, the canonical full-ledger C3
source gives the unconditional public Genuine-zero confinement statement.
The source-nonvanishing obligation is discharged internally. -/
theorem finalGenuineZeroConfinement_of_canonicalCompletedC3ScalarizationReduction
    (hscalar : CanonicalCompletedC3GammaCauchyScalarizationReduction) :
    NativeCarryC3Crosswalk.FinalGenuineZeroConfinement := by
  intro s hs hzero
  apply riemannZeta_zero_re_eq_half_of_canonicalC3SixCameraScalarization
    hscalar hs
  rw [← nativeScalar_eq_riemannZeta hs,
    nativeScalar_eq_genuineContinuation hs, hzero]

/-- Strict positivity of every unshifted Hankel section from one global even
Green-jet family. -/
theorem allOrderHankelGramPosDefReduction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (N : ℕ) :
    (hankelGram moments N).PosDef :=
  hankelGram_posDef_of_gramRepresentation
    (greenWronskianMomentKernel_even_momentGram hrep) N
    (greenJetEven_prefix_linearIndependent heven N)

/-- Strict positivity of every shifted Hankel section from one global odd
Green-jet family. -/
theorem allOrderShiftedHankelPosDefReduction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) :
    (shiftedHankel moments N).PosDef :=
  shiftedHankel_posDef_of_gramRepresentation
    (greenWronskianMomentKernel_odd_shiftedMomentGram hrep) N
    (greenJetOdd_prefix_linearIndependent hodd N)

/-- One all-order Green kernel plus global parity-jet independence closes all
finite positivity premises, the exact canonical Jacobi tower, and the closed
infinite Green energy factor simultaneously. -/
theorem allOrderHeightClosure_of_greenMomentKernelReduction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    ∃ hgram : ∀ N : ℕ, (hankelGram moments N).PosDef,
      (∀ N : ℕ, (shiftedHankel moments N).PosDef) ∧
      IsExactPrincipalTower
        (fun N => canonicalFiniteJacobiSection moments N (hgram N)) ∧
      (closedGreenJetEnergyFactor hrep heven hodd).IsClosed := by
  let hgram : ∀ N : ℕ, (hankelGram moments N).PosDef :=
    allOrderHankelGramPosDefReduction hrep heven
  refine ⟨hgram, allOrderShiftedHankelPosDefReduction hrep hodd, ?_, ?_⟩
  · exact canonicalFiniteJacobiSection_isExactPrincipalTower_unconditional
      moments hgram
  · exact closedGreenJetEnergyFactor_isClosed hrep heven hodd

end

end CarrySelfAdjointOperator
