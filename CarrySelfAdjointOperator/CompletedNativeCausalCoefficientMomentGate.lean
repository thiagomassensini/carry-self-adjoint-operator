import CarrySelfAdjointOperator.CompletedC3RecoveredDslopePositivityGate
import CarrySelfAdjointOperator.CompletedNativeCausalCoefficientGram
import Mathlib.Tactic

/-!
# Causal coefficient gate for the completed native moments

The division-free polarized coefficient recurrence is sufficient to identify
every parity Gram entry with the canonical completed-native moment kernel.
This file records its first two diagonal consequences and the direct HP
constructor, then audits the zeroth vector of the existing finite causal TFVD
Gram.  The causal Gram is positive definite, but its first vector has its own
explicit normalization; it is not renamed as the canonical zeroth moment.
-/

open scoped ComplexOrder InnerProductSpace lp ENNReal NNReal

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-! ## First consequences of the coefficient recurrence -/

/-- The recurrence fixes the first even Gram coefficient without requiring a
Taylor-state presentation. -/
theorem IsPolarizedGreenCoefficientEquation.coeff_zero_zero
    {moments : ℕ → ℝ} {coeff : ℕ → ℕ → ℂ}
    (hcoeff : IsPolarizedGreenCoefficientEquation moments coeff) :
    coeff 0 0 = (moments 0 : ℂ) := by
  simpa [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient] using
    (polarizedGreenCoefficient_unique hcoeff 0 0)

/-- The first odd Gram coefficient is the first shifted moment. -/
theorem IsPolarizedGreenCoefficientEquation.coeff_one_one
    {moments : ℕ → ℝ} {coeff : ℕ → ℕ → ℂ}
    (hcoeff : IsPolarizedGreenCoefficientEquation moments coeff) :
    coeff 1 1 = (moments 1 : ℂ) := by
  simpa [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient] using
    (polarizedGreenCoefficient_unique hcoeff 1 1)

/-- The first mixed coefficient vanishes at the complex level. -/
theorem IsPolarizedGreenCoefficientEquation.coeff_zero_one
    {moments : ℕ → ℝ} {coeff : ℕ → ℕ → ℂ}
    (hcoeff : IsPolarizedGreenCoefficientEquation moments coeff) :
    coeff 0 1 = 0 := by
  simpa [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient] using
    (polarizedGreenCoefficient_unique hcoeff 0 1)

/-- Any Hilbert-valued coefficient solution realizes the zeroth moment as the
squared norm of its centered Taylor vector. -/
theorem completedGreenJetCoefficientEquation_inner_zero_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {moments : ℕ → ℝ} {state : ℂ → E}
    (hcoeff : HasCompletedGreenJetCoefficientEquation moments state) :
    inner ℂ (state 0) (state 0) = (moments 0 : ℂ) := by
  have h := polarizedGreenCoefficient_unique hcoeff 0 0
  simpa [HasCompletedGreenJetCoefficientEquation,
    completedGreenTaylorJet, polarizedGreenMomentCoefficient,
    evenMomentDiagonalCoefficient] using h

/-- The first raw odd Taylor vector must similarly realize the first shifted
moment. -/
theorem completedGreenJetCoefficientEquation_inner_one_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {moments : ℕ → ℝ} {state : ℂ → E}
    (hcoeff : HasCompletedGreenJetCoefficientEquation moments state) :
    inner ℂ (completedGreenTaylorJet state 1)
        (completedGreenTaylorJet state 1) = (moments 1 : ℂ) := by
  have h := polarizedGreenCoefficient_unique hcoeff 1 1
  simpa [HasCompletedGreenJetCoefficientEquation,
    polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient] using h

/-- The coefficient equation also forces the first mixed parity product to
vanish before any scalar real-part projection. -/
theorem completedGreenJetCoefficientEquation_inner_zero_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {moments : ℕ → ℝ} {state : ℂ → E}
    (hcoeff : HasCompletedGreenJetCoefficientEquation moments state) :
    inner ℂ (state 0) (completedGreenTaylorJet state 1) = 0 := by
  have h := polarizedGreenCoefficient_unique hcoeff 0 1
  simpa [HasCompletedGreenJetCoefficientEquation,
    completedGreenTaylorJet, polarizedGreenMomentCoefficient,
    evenMomentDiagonalCoefficient] using h

/-! ## State-free polarized vector interface -/

/-- Parity packaging of a raw all-order coefficient-vector family. -/
def polarizedCoefficientParityJet
    {E : Type*} (rawJet : ℕ → E) : (ℕ ⊕ ℕ) → E
  | Sum.inl n => rawJet (2 * n)
  | Sum.inr n => rawJet (2 * n + 1)

/-- Division-free coefficient equation read directly as the Gram of a raw
vector family.  Unlike `HasCompletedGreenJetCoefficientEquation`, this
interface does not require that the vectors are complex Taylor derivatives of
one state. -/
def HasPolarizedCoefficientVectorEquation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (moments : ℕ → ℝ) (rawJet : ℕ → E) : Prop :=
  IsPolarizedGreenCoefficientEquation moments fun p q ↦
    inner ℂ (rawJet p) (rawJet q)

/-- The state-free coefficient equation determines the complete complex
moment Gram of the parity-packaged vectors. -/
theorem complexGreenWronskianMomentKernel_of_vectorCoefficientEquation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {moments : ℕ → ℝ} {rawJet : ℕ → E}
    (hcoeff : HasPolarizedCoefficientVectorEquation moments rawJet) :
    IsComplexGreenWronskianMomentKernelGramRepresentation moments
      (polarizedCoefficientParityJet rawJet) := by
  intro i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          have h := polarizedGreenCoefficient_unique hcoeff (2 * i) (2 * j)
          simpa [greenWronskianMomentKernel,
            polarizedCoefficientParityJet] using h.symm
      | inr j =>
          have h := polarizedGreenCoefficient_unique hcoeff (2 * i) (2 * j + 1)
          simpa [greenWronskianMomentKernel,
            polarizedCoefficientParityJet] using h.symm
  | inr i =>
      cases j with
      | inl j =>
          have h := polarizedGreenCoefficient_unique hcoeff (2 * i + 1) (2 * j)
          simpa [greenWronskianMomentKernel,
            polarizedCoefficientParityJet] using h.symm
      | inr j =>
          have h := polarizedGreenCoefficient_unique hcoeff
            (2 * i + 1) (2 * j + 1)
          simpa [greenWronskianMomentKernel,
            polarizedCoefficientParityJet] using h.symm

/-- A state-free vector solution with independent parity families supplies
the real HP carrier certificate directly. -/
theorem completedNativeRealHPCarrierCertificate_of_vectorCoefficientEquation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {rawJet : ℕ → E}
    (hcoeff : HasPolarizedCoefficientVectorEquation
      canonicalCompletedNativeLogDerivativeMoment rawJet)
    (heven : LinearIndependent ℂ (fun n : ℕ ↦ rawJet (2 * n)))
    (hodd : LinearIndependent ℂ (fun n : ℕ ↦ rawJet (2 * n + 1))) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    CompletedNativeRealHPCarrierCertificate
      (polarizedCoefficientParityJet rawJet) := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have hcomplex :=
    complexGreenWronskianMomentKernel_of_vectorCoefficientEquation hcoeff
  refine
    { momentKernel := ?_
      evenIndependent := heven.restrict_scalars' ℝ
      oddIndependent := hodd.restrict_scalars' ℝ }
  intro i j
  change greenWronskianMomentKernel
      canonicalCompletedNativeLogDerivativeMoment i j =
    (inner ℂ (polarizedCoefficientParityJet rawJet i)
      (polarizedCoefficientParityJet rawJet j)).re
  have h := congrArg Complex.re (hcomplex i j)
  simpa using h

/-! ## Direct coefficient-equation HP constructor -/

/-- A concrete coefficient equation and complex-linear independence of both
parity families give the carrier-correct real HP certificate directly. -/
theorem completedNativeRealHPCarrierCertificate_of_coefficientEquation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {state : ℂ → E}
    (hcoeff : HasCompletedGreenJetCoefficientEquation
      canonicalCompletedNativeLogDerivativeMoment state)
    (heven : LinearIndependent ℂ
      (fun n : ℕ ↦ completedGreenParityJet state (Sum.inl n)))
    (hodd : LinearIndependent ℂ
      (fun n : ℕ ↦ completedGreenParityJet state (Sum.inr n))) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    CompletedNativeRealHPCarrierCertificate
      (completedGreenParityJet state) := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have hcomplex := complexGreenWronskianMomentKernel_of_coefficientEquation
    hcoeff
  refine
    { momentKernel := ?_
      evenIndependent := heven.restrict_scalars' ℝ
      oddIndependent := hodd.restrict_scalars' ℝ }
  intro i j
  change greenWronskianMomentKernel
      canonicalCompletedNativeLogDerivativeMoment i j =
    (inner ℂ (completedGreenParityJet state i)
      (completedGreenParityJet state j)).re
  have h := congrArg Complex.re (hcomplex i j)
  simpa using h

/-! ## Zeroth finite causal-vector audit -/

/-- Before causal transport, the first finite coefficient vector is the
single logarithmic slope at the spectral coordinate `2`. -/
theorem nativeOddLogPowerSlopeJetFinite_one_zero_apply_zero :
    nativeOddLogPowerSlopeJetFinite 1 (0 : Fin 1) (0 : Fin 1) =
      nativeCriticalDirichletAmplitude 2 * (Real.log 2 : ℂ) := by
  simp [nativeOddLogPowerSlopeJetFinite, nativeOddLogPowerSlopeJet]

/-- The corresponding reconstructed TFVD vector is supported at the first
vertical coordinate with exactly that coefficient. -/
theorem canonicalFiniteNativeTfvdSlopeJet_one_zero :
    canonicalFiniteNativeTfvdSlopeJet 1 (0 : Fin 1) =
      ((nativeCriticalDirichletAmplitude 2 * (Real.log 2 : ℂ)) : ℂ) •
        (lp.single 2 (0 : ℕ) (1 : ℂ) : CarryVerticalL2) := by
  rw [canonicalFiniteNativeTfvdSlopeJet,
    finiteSlopeCoefficientSynthesisLinearMap_apply,
    finiteSlopeCoefficientState]
  simp only [Fin.sum_univ_one,
    nativeOddLogPowerSlopeJetFinite_one_zero_apply_zero]
  congr

/-- Consequently the raw order-one TFVD Gram starts with the squared modulus
of the explicit logarithmic slope.  Identifying this scalar with the
completed-native zeroth moment would be an additional theorem. -/
theorem inner_canonicalFiniteNativeTfvdSlopeJet_one_zero :
    inner ℂ
        (canonicalFiniteNativeTfvdSlopeJet 1 (0 : Fin 1))
        (canonicalFiniteNativeTfvdSlopeJet 1 (0 : Fin 1)) =
      (starRingEnd ℂ)
          (nativeCriticalDirichletAmplitude 2 * (Real.log 2 : ℂ)) *
        (nativeCriticalDirichletAmplitude 2 * (Real.log 2 : ℂ)) := by
  rw [canonicalFiniteNativeTfvdSlopeJet_one_zero,
    inner_smul_left, inner_smul_right]
  simp

end

end CarrySelfAdjointOperator
