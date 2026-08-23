import CarrySelfAdjointOperator.CompletedTfvdCanonicalSourceIntertwining
import CarrySelfAdjointOperator.CompletedGammaCauchyScalarization
import CarrySelfAdjointOperator.GreenJetEnergyFactor
import CarrySelfAdjointOperator.CanonicalLDLPrefixReduction
import NativeCarryC3Crosswalk.FinalGenuineZeroConfinement

/-!
# Canonical C3 confinement and all-order height closure audit

This file joins the current public C3 and private height-operator theorem
surfaces without replacing any missing implication by a friendly name.

The completed six-camera source is already the public full-ledger TFVD/C3
source, and its nondegeneracy is already proved.  Zero confinement therefore
needs only its completed Wronskian/Cauchy scalarization.

Independently, one all-order Green--Wronskian moment-kernel Gram realization
with globally independent even and odd jets supplies strict positivity of both
Hankel towers, exact projectivity of the canonical finite Jacobi sections, and
the canonical closed Green energy factor.

The final structure below records those four concrete obligations separately:
scalarization, the polarized moment kernel, even-jet independence, and odd-jet
independence.  No zero table, fitted matrix, order-specific positivity premise,
or external whitening compatibility is accepted.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Exact remaining scalarization datum for the canonical source identified
with the public completed TFVD/C3 ledger source. -/
def CanonicalCompletedC3GammaCauchyScalarization : Prop :=
  HasCanonicalCompletedNativeGammaCauchyScalarization
    canonicalCompletedC3SixCameraSource

/-- Once the exact scalarization is available, source nondegeneracy is already
internal and the public Genuine-zero confinement statement follows. -/
theorem finalGenuineZeroConfinement_of_canonicalC3HeightClosureScalarization
    (hscalar : CanonicalCompletedC3GammaCauchyScalarization) :
    NativeCarryC3Crosswalk.FinalGenuineZeroConfinement := by
  intro s hs hzero
  apply riemannZeta_zero_re_eq_half_of_canonicalC3SixCameraScalarization
    hscalar hs
  rw [← nativeScalar_eq_riemannZeta hs,
    nativeScalar_eq_genuineContinuation hs, hzero]

/-- Strict positivity of every unshifted Hankel section from one globally
independent even Green-jet family. -/
theorem allOrderHankelGramPosDef
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (N : ℕ) :
    (hankelGram moments N).PosDef :=
  hankelGram_posDef_of_gramRepresentation
    (greenWronskianMomentKernel_even_momentGram hrep) N
    (greenJetEven_prefix_linearIndependent heven N)

/-- Strict positivity of every shifted Hankel section from one globally
independent odd Green-jet family. -/
theorem allOrderShiftedHankelPosDef
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
theorem allOrderHeightClosure_of_greenMomentKernel
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
    allOrderHankelGramPosDef hrep heven
  refine ⟨hgram, allOrderShiftedHankelPosDef hrep hodd, ?_, ?_⟩
  · exact canonicalFiniteJacobiSection_isExactPrincipalTower_unconditional
      moments hgram
  · exact closedGreenJetEnergyFactor_isClosed hrep heven hodd

/-- Complete typed contract for the theorem surfaces that must be instantiated
by the actual completed C3 state.  The fields are independent obligations;
none is defined in terms of the desired conclusions. -/
structure CanonicalC3HeightClosureCertificate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (moments : ℕ → ℝ) (jet : (ℕ ⊕ ℕ) → E) : Prop where
  scalarization : CanonicalCompletedC3GammaCauchyScalarization
  momentKernel :
    IsGreenWronskianMomentKernelGramRepresentation moments jet
  evenIndependent :
    LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))
  oddIndependent :
    LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))

/-- A concrete inhabitant of the four-field certificate closes zero
confinement and the whole current all-order height-operator reduction at once. -/
theorem finalConfinement_and_heightClosure_of_certificate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (certificate : CanonicalC3HeightClosureCertificate moments jet) :
    NativeCarryC3Crosswalk.FinalGenuineZeroConfinement ∧
      ∃ hgram : ∀ N : ℕ, (hankelGram moments N).PosDef,
        (∀ N : ℕ, (shiftedHankel moments N).PosDef) ∧
        IsExactPrincipalTower
          (fun N => canonicalFiniteJacobiSection moments N (hgram N)) ∧
        (closedGreenJetEnergyFactor certificate.momentKernel
          certificate.evenIndependent certificate.oddIndependent).IsClosed := by
  constructor
  · exact finalGenuineZeroConfinement_of_canonicalC3HeightClosureScalarization
      certificate.scalarization
  · exact allOrderHeightClosure_of_greenMomentKernel
      certificate.momentKernel certificate.evenIndependent
        certificate.oddIndependent

end

end CarrySelfAdjointOperator
