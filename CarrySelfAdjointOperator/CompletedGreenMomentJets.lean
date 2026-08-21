import CarrySelfAdjointOperator.GreenWronskianHankelBridge
import CarrySelfAdjointOperator.CompletedNativeC3LedgerState
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Completed Green moment jets

The completed native characteristic is even in the centered height variable.
Its logarithmic derivative therefore has an odd Taylor expansion whose
polarized divided-difference kernel splits into an even/even Hankel block and
an odd/odd shifted-Hankel block.

`GreenWronskianHankelBridge` already proves the finite matrix consequence once
that parity-split coefficient kernel is a Gram kernel.  This file attaches the
interface to an actual completed Green state rather than to an unrelated
feature family:

* the state satisfies the division-free two-variable Green identity on a
  neighborhood of the expansion center;
* the completed scalar is nonzero at the center, so state normalization is
  legitimate there;
* the parity-split Taylor jets of that normalized state realize the exact
  moment kernel.

The last item is the remaining coefficient-extraction theorem.  Once it is
supplied, positivity of both Hankel sections follows simultaneously at every
finite order.  No target height, zero table, fitted matrix, or order-specific
positivity premise enters this interface.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- A two-variable division-free Green representation restricted to a domain.
This is the local form needed for Taylor expansion at the centered origin. -/
def HasDivisionFreeGreenRepresentationOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (domain : Set ℂ) (F Psi : ℂ → ℂ) (state : ℂ → E) : Prop :=
  ∀ z ∈ domain, ∀ w ∈ domain,
    completedGreenWronskian F Psi z w =
      (z - (starRingEnd ℂ) w) * inner ℂ (state w) (state z)

/-- Normalize a completed Green state by the scalar value and by `sqrt 2`.
The extra factor is forced by the convention

`m(z) = 2 * z * sum_n h_n z^(2n)`.

The definition is total.  The certificate below separately records that the
scalar is nonzero at the Taylor center. -/
def normalizedCompletedGreenState
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : ℂ → ℂ) (state : ℂ → E) (z : ℂ) : E :=
  (((Real.sqrt 2 : ℝ) : ℂ) * F z)⁻¹ • state z

/-- Taylor coefficient of a Hilbert-valued state at the centered origin. -/
def completedGreenTaylorJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (state : ℂ → E) (n : ℕ) : E :=
  ((Nat.factorial n : ℂ)⁻¹) • iteratedDeriv n state 0

/-- Interleave the even and odd Taylor jets in the index type used by the
Green--Wronskian Hankel bridge. -/
def completedGreenParityJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (state : ℂ → E) : (ℕ ⊕ ℕ) → E
  | Sum.inl n => completedGreenTaylorJet state (2 * n)
  | Sum.inr n => completedGreenTaylorJet state (2 * n + 1)

/-- Complex Hilbert realization of the real parity-split moment kernel.  The
right side is automatically Hermitian; the explicit cast records that every
moment coefficient is real. -/
def IsComplexGreenWronskianMomentKernelGramRepresentation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (moments : ℕ → ℝ) (jet : (ℕ ⊕ ℕ) → E) : Prop :=
  ∀ i j : ℕ ⊕ ℕ,
    (greenWronskianMomentKernel moments i j : ℂ) =
      inner ℂ (jet i) (jet j)

/-- A complex Gram realization becomes the real Gram realization consumed by
`GreenWronskianHankelBridge` after restriction of scalars. -/
theorem hankelPair_posSemidef_of_complexGreenWronskianMomentKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsComplexGreenWronskianMomentKernelGramRepresentation
      moments jet)
    (N : ℕ) :
    (hankelGram moments N).PosSemidef ∧
      (shiftedHankel moments N).PosSemidef := by
  letI : InnerProductSpace ℝ E :=
    InnerProductSpace.rclikeToReal ℂ E
  have hreal :
      IsGreenWronskianMomentKernelGramRepresentation
        (E := E) moments jet := by
    intro i j
    change greenWronskianMomentKernel moments i j =
      (inner ℂ (jet i) (jet j)).re
    have h := congrArg Complex.re (hrep i j)
    simpa using h
  exact hankelPair_posSemidef_of_greenWronskianMomentKernel
    (E := E) hreal N

/-- Exact certificate expected from the completed two-variable Green state.
It retains the state-level Green identity and makes the sole remaining Taylor
coefficient statement explicit. -/
structure CompletedGreenMomentJetCertificate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (domain : Set ℂ) (F Psi : ℂ → ℂ) (state : ℂ → E)
    (moments : ℕ → ℝ) : Prop where
  zero_mem_domain : (0 : ℂ) ∈ domain
  center_ne_zero : F 0 ≠ 0
  greenRepresentationOn :
    HasDivisionFreeGreenRepresentationOn domain F Psi state
  momentKernel :
    IsComplexGreenWronskianMomentKernelGramRepresentation moments
      (completedGreenParityJet
        (normalizedCompletedGreenState F state))

/-- The completed Green moment-jet certificate removes both finite Hankel
positivity premises at once. -/
theorem hankelPair_posSemidef_of_completedGreenMomentJets
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {domain : Set ℂ} {F Psi : ℂ → ℂ} {state : ℂ → E}
    {moments : ℕ → ℝ}
    (certificate :
      CompletedGreenMomentJetCertificate domain F Psi state moments)
    (N : ℕ) :
    (hankelGram moments N).PosSemidef ∧
      (shiftedHankel moments N).PosSemidef :=
  hankelPair_posSemidef_of_complexGreenWronskianMomentKernel
    certificate.momentKernel N

/-- Natural centered-height domain corresponding to the open critical strip. -/
def completedNativeHeightDomain : Set ℂ :=
  {z | operatorHeightParameter z ∈ genuineCriticalStrip}

@[simp] theorem zero_mem_completedNativeHeightDomain :
    (0 : ℂ) ∈ completedNativeHeightDomain := by
  change operatorHeightParameter 0 ∈ genuineCriticalStrip
  constructor <;> norm_num [operatorHeightParameter]

/-- The two full factor Green representations combine into a local
representation of the actual completed native characteristic and its concrete
C3 provenance ledger.  The canonical derivative companion agrees with the
product companion throughout the centered-height strip. -/
theorem completedNativeC3ProductLedger_greenRepresentationOn_of_factors
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState) :
    HasDivisionFreeGreenRepresentationOn
      completedNativeHeightDomain
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion
      (completedNativeC3ProductLedgerState xiState) := by
  intro z hz w hw
  change operatorHeightParameter z ∈ genuineCriticalStrip at hz
  change operatorHeightParameter w ∈ genuineCriticalStrip at hw
  have hproduct := (hxi.mul hnative) z w
  change completedGreenWronskian
      (fun u ↦ nativeXiCompletionFactor u * nativeHeightScalar u)
      completedNativeOperatorBoundaryCompanion z w = _
  calc
    completedGreenWronskian
        (fun u ↦ nativeXiCompletionFactor u * nativeHeightScalar u)
        completedNativeOperatorBoundaryCompanion z w =
      completedGreenWronskian
        (fun u ↦ nativeXiCompletionFactor u * nativeHeightScalar u)
        (productBoundaryCompanion
          nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion
          nativeHeightScalar nativeHeightScalarBoundaryCompanion) z w := by
            unfold completedGreenWronskian
            rw [completedNativeOperatorBoundaryCompanion_eq_product hz,
              completedNativeOperatorBoundaryCompanion_eq_product hw]
    _ = _ := by
      simpa [completedNativeC3ProductLedgerState] using hproduct

/-- Concrete certificate name for the actual xi-completed native scalar and
its provenance-preserving C3 product ledger. -/
def HasCanonicalCompletedNativeGreenMomentJets
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (moments : ℕ → ℝ) : Prop :=
  CompletedGreenMomentJetCertificate
    completedNativeHeightDomain
    completedNativeOperatorCharacteristic
    completedNativeOperatorBoundaryCompanion
    (completedNativeC3ProductLedgerState xiState)
    moments

/-- Once the factor Green identities and the exact coefficient extraction are
available, the concrete completed native chain supplies the full moment-jet
certificate. -/
theorem hasCanonicalCompletedNativeGreenMomentJets_of_factors
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (moments : ℕ → ℝ)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hcenter : completedNativeOperatorCharacteristic 0 ≠ 0)
    (hcoefficients :
      IsComplexGreenWronskianMomentKernelGramRepresentation moments
        (completedGreenParityJet
          (normalizedCompletedGreenState
            completedNativeOperatorCharacteristic
            (completedNativeC3ProductLedgerState xiState)))) :
    HasCanonicalCompletedNativeGreenMomentJets xiState moments := by
  exact
    { zero_mem_domain := zero_mem_completedNativeHeightDomain
      center_ne_zero := hcenter
      greenRepresentationOn :=
        completedNativeC3ProductLedger_greenRepresentationOn_of_factors
          xiState hxi hnative
      momentKernel := hcoefficients }

/-- End-to-end finite positivity theorem for the concrete completed native
state.  The only inputs not already structural are the two factor Green
representations, center nonvanishing, and the exact Taylor coefficient
identity. -/
theorem hankelPair_posSemidef_of_canonicalCompletedNativeGreenMomentJets
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (moments : ℕ → ℝ)
    (certificate :
      HasCanonicalCompletedNativeGreenMomentJets xiState moments)
    (N : ℕ) :
    (hankelGram moments N).PosSemidef ∧
      (shiftedHankel moments N).PosSemidef :=
  hankelPair_posSemidef_of_completedGreenMomentJets certificate N

end

end CarrySelfAdjointOperator
