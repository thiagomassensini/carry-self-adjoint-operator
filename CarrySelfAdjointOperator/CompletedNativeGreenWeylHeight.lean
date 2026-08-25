import CarrySelfAdjointOperator.CompletedNativeWeylMoments
import CarrySelfAdjointOperator.CompletedGreenJetCoefficientRecurrence
import CarrySelfAdjointOperator.GreenJetReciprocalSignedHeightOperator
import CarrySelfAdjointOperator.BR2IncidenceStrictPositivity
import Mathlib.Tactic

/-!
# Completed Genuine--Green--Weyl--height composition

This file gives the typed end-to-end interface for the root-free operator
chain.  It deliberately uses the concrete completed native characteristic
and the concrete normalized C3 product ledger.  A certificate records that
one real moment sequence is simultaneously

* the division-free logarithmic derivative sequence of the completed
  Genuine characteristic; and
* the parity-split Gram sequence of that completed Green ledger.

The same certificate then constructs the canonical completed reciprocal
signed-height operator as a maximal real self-adjoint operator.  The
coefficient identity, global jet independence, and zero-mass completion are
kept as named fields instead of being hidden by the final constructor.
-/

namespace CarrySelfAdjointOperator

open FiniteNativeCarryOperator.Camera

noncomputable section

/-- The actual normalized Green state whose Taylor jets feed the Weyl/Jacobi
construction. -/
def canonicalCompletedNativeNormalizedGreenState
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) :
    ℂ → BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier :=
  normalizedCompletedGreenState
    completedNativeOperatorCharacteristic
    (completedNativeC3ProductLedgerState xiState)

/-- The parity-split Green jets of the actual completed C3 product ledger. -/
def canonicalCompletedNativeGreenParityJet
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) :
    (ℕ ⊕ ℕ) → BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier :=
  completedGreenParityJet
    (canonicalCompletedNativeNormalizedGreenState xiState)

/-- Exact provenance certificate consumed by the global height constructor.
It is parameterized by the concrete xi state and by one moment sequence; no
abstract characteristic or unrelated Green feature family is accepted. -/
structure CompletedNativeGreenWeylHeightCertificate
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (moments : ℕ → ℝ) : Prop where
  logarithmicMoments :
    IsCompletedNativeLogDerivativeMomentSequence moments
  greenMomentJets :
    HasCanonicalCompletedNativeGreenMomentJets xiState moments
  evenIndependent :
    LinearIndependent ℝ
      (fun n : ℕ ↦ canonicalCompletedNativeGreenParityJet xiState (Sum.inl n))
  oddIndependent :
    LinearIndependent ℝ
      (fun n : ℕ ↦ canonicalCompletedNativeGreenParityJet xiState (Sum.inr n))
  headTailMomentDefect :
    HasVanishingGreenJetHeadTailMomentDefect moments

/-- The two factor Green identities and the all-order coefficient equation
construct the concrete Green half of the certificate.  The logarithmic
identity is stated independently, so the same `moments` must pass both sides
of the Genuine--Green seam. -/
theorem completedNativeGreenWeylHeightCertificate_of_factors
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (moments : ℕ → ℝ)
    (hlog : IsCompletedNativeLogDerivativeMomentSequence moments)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hcoeff : HasCompletedGreenJetCoefficientEquation moments
      (canonicalCompletedNativeNormalizedGreenState xiState))
    (heven : LinearIndependent ℝ
      (fun n : ℕ ↦ canonicalCompletedNativeGreenParityJet xiState (Sum.inl n)))
    (hodd : LinearIndependent ℝ
      (fun n : ℕ ↦ canonicalCompletedNativeGreenParityJet xiState (Sum.inr n)))
    (hvanish : HasVanishingGreenJetHeadTailMomentDefect moments) :
    CompletedNativeGreenWeylHeightCertificate xiState moments := by
  refine
    { logarithmicMoments := hlog
      greenMomentJets := ?_
      evenIndependent := heven
      oddIndependent := hodd
      headTailMomentDefect := hvanish }
  exact hasCanonicalCompletedNativeGreenMomentJets_of_factors
    xiState moments hxi hnative
      (complexGreenWronskianMomentKernel_of_coefficientEquation hcoeff)

/-- Incidence transport discharges both global independence fields.  Thus the
strictness part of the completed operator requires only the one injective
vector bridge from the native bracket incidences to the actual Green jets. -/
theorem completedNativeGreenWeylHeightCertificate_of_incidenceTransport
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (xiState : ℂ → Hxi) (moments : ℕ → ℝ)
    (hlog : IsCompletedNativeLogDerivativeMomentSequence moments)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hcoeff : HasCompletedGreenJetCoefficientEquation moments
      (canonicalCompletedNativeNormalizedGreenState xiState))
    (transport : CanonicalCompletedNativeBR2IncidenceJetTransport
      base radius xiState)
    (hvanish : HasVanishingGreenJetHeadTailMomentDefect moments) :
    CompletedNativeGreenWeylHeightCertificate xiState moments :=
  completedNativeGreenWeylHeightCertificate_of_factors
    xiState moments hlog hxi hnative hcoeff
      (transport.even_linearIndependent hbase hradius)
      (transport.odd_linearIndependent hbase hradius)
      hvanish

namespace CompletedNativeGreenWeylHeightCertificate

/-- Two certificates over the same completed Genuine characteristic cannot
carry different moment sequences. -/
theorem moments_unique
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments moments' : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments)
    (certificate' :
      CompletedNativeGreenWeylHeightCertificate xiState moments') :
    moments = moments' :=
  certificate.logarithmicMoments.unique certificate'.logarithmicMoments

/-- The root-free chain constructs a canonical global maximal self-adjoint
signed-height package on the Hilbert completion of the concrete Green jets. -/
def toMaximalSelfAdjointHeightData
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    LinearPMap.RealMaximalSelfAdjointData
      (WithLp 2
        (greenJetEvenHilbertSubspace
            (completedGreenJet
              (canonicalCompletedNativeGreenParityJet xiState)) ×
          greenJetOddHilbertSubspace
            (completedGreenJet
              (canonicalCompletedNativeGreenParityJet xiState)))) := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  have hcomplex := certificate.greenMomentJets.momentKernel
  have hreal : IsGreenWronskianMomentKernelGramRepresentation
      moments (canonicalCompletedNativeGreenParityJet xiState) := by
    intro i j
    change greenWronskianMomentKernel moments i j =
      (inner ℂ
        (canonicalCompletedNativeGreenParityJet xiState i)
        (canonicalCompletedNativeGreenParityJet xiState j)).re
    have h := congrArg Complex.re (hcomplex i j)
    simpa [canonicalCompletedNativeGreenParityJet,
      canonicalCompletedNativeNormalizedGreenState] using h
  exact canonicalCompletedGreenJetMomentReciprocalSignedHeightData
    hreal certificate.evenIndependent certificate.oddIndependent
      certificate.headTailMomentDefect

/-- The operator produced by the complete provenance certificate is maximal
real self-adjoint. -/
theorem heightOperator_adjoint_eq
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let data := certificate.toMaximalSelfAdjointHeightData
    data.operator.realAdjoint data.denseDomain = data.operator := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  exact certificate.toMaximalSelfAdjointHeightData.adjoint_eq

end CompletedNativeGreenWeylHeightCertificate

end

end CarrySelfAdjointOperator
