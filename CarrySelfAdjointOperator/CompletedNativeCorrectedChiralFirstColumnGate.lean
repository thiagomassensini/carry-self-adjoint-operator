import CarrySelfAdjointOperator.CompletedNativeTfvdSixChannelJet
import CarrySelfAdjointOperator.ProjectiveValveFirstColumnMomentGate
import Mathlib.Tactic

/-!
# Corrected chiral first-column gate for a Hilbert jet carrier

The completed six-source TFVD ledger already supplies the scalar corrected
chiral first column before it is recognized as a moment.  This file makes the
remaining Hilbertian seam type-exact.

For a proposed fixed-carrier family `rawJet`, its first column must be read
by the *geometric* six-analysis TFVD jet.  Together with a native Gram-shift,
this is equivalent to the complete polarized moment equation.  No vector is
defined from moments here, and no positive kernel or HP premise is added.
-/

open scoped InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- A Hilbert jet has corrected-native chiral boundary calibration when its
first Gram column is the scalar boundary coefficient already read from the
completed causal/chiral construction. -/
def HasCorrectedNativeChiralFirstColumnGram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (M : ℕ) (rawJet : ℕ → E) : Prop :=
  ∀ p : ℕ,
    inner ℂ (rawJet p) (rawJet 0) =
      canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p

/-- The corrected chiral boundary coefficient is precisely the scalar
boundary target used by the abstract first-column reduction.  The proof goes
through the completed causal/chiral coefficient theorem, not through a
definition of a vector in terms of moments. -/
theorem canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_firstColumnTarget
    (M p : ℕ) :
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p =
      oddMomentResponseCoefficient
        canonicalCompletedNativeLogDerivativeMoment (p + 1) := by
  calc
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p =
        polarizedGreenMomentCoefficient
          canonicalCompletedNativeLogDerivativeMoment p 0 :=
      canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_polarizedMoment
        M p 0
    _ = oddMomentResponseCoefficient
          canonicalCompletedNativeLogDerivativeMoment (p + 1) := by
      simp [polarizedGreenMomentCoefficient, oddMomentResponseCoefficient]

/-- With a native Gram-shift, the full moment equation is equivalent to the
corrected-native chiral first column. -/
theorem hasNativePolarizedCoefficientVectorEquation_iff_correctedChiralFirstColumnGram_of_transport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (M : ℕ) (rawJet : ℕ → E)
    (htransport : ∀ p q : ℕ,
      inner ℂ (rawJet p) (rawJet (q + 1)) =
        inner ℂ (rawJet (p + 1)) (rawJet q)) :
    HasPolarizedCoefficientVectorEquation
        canonicalCompletedNativeLogDerivativeMoment rawJet ↔
      HasCorrectedNativeChiralFirstColumnGram M rawJet := by
  rw [hasNativePolarizedCoefficientVectorEquation_iff_firstColumn_of_transport
    rawJet htransport]
  constructor
  · intro h p
    calc
      inner ℂ (rawJet p) (rawJet 0) =
          oddMomentResponseCoefficient
            canonicalCompletedNativeLogDerivativeMoment (p + 1) := h p
      _ = canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p :=
        (canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_firstColumnTarget
          M p).symm
  · intro h p
    calc
      inner ℂ (rawJet p) (rawJet 0) =
          canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p := h p
      _ = oddMomentResponseCoefficient
            canonicalCompletedNativeLogDerivativeMoment (p + 1) :=
        canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_firstColumnTarget M p

/-- The corrected first-column calibration is equivalently a fully geometric
six-analysis TFVD statement.  Its target is a central jet of the completed
lossless ledger with Green ports, structural channels, tail, and chart still
present; it is not defined from the moment sequence. -/
theorem correctedChiralFirstColumnGram_iff_sixAnalysisJet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (M : ℕ) (rawJet : ℕ → E)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    HasCorrectedNativeChiralFirstColumnGram M rawJet ↔
      ∀ p : ℕ,
        inner ℂ (rawJet p) (rawJet 0) =
          canonicalC3BracketTfvdSixAnalysisJetCoefficient
            M p q hqpos.le hq1 S := by
  constructor
  · intro h p
    calc
      inner ℂ (rawJet p) (rawJet 0) =
          canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p := h p
      _ = canonicalC3BracketTfvdSixAnalysisJetCoefficient
            M p q hqpos.le hq1 S :=
        canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_sixAnalysisJet
          M p q hqpos hq1 S
  · intro h p
    calc
      inner ℂ (rawJet p) (rawJet 0) =
          canonicalC3BracketTfvdSixAnalysisJetCoefficient
            M p q hqpos.le hq1 S := h p
      _ = canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p :=
        (canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_sixAnalysisJet
          M p q hqpos hq1 S).symm

/-- Complete geometric version of the first-column frontier: for a shifted
Hilbert jet, it is enough and necessary to pair its first vector against the
six-analysis TFVD central jet. -/
theorem hasNativePolarizedCoefficientVectorEquation_iff_sixAnalysisJet_of_transport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (M : ℕ) (rawJet : ℕ → E)
    (htransport : ∀ p q : ℕ,
      inner ℂ (rawJet p) (rawJet (q + 1)) =
        inner ℂ (rawJet (p + 1)) (rawJet q))
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    HasPolarizedCoefficientVectorEquation
        canonicalCompletedNativeLogDerivativeMoment rawJet ↔
      ∀ p : ℕ,
        inner ℂ (rawJet p) (rawJet 0) =
          canonicalC3BracketTfvdSixAnalysisJetCoefficient
            M p q hqpos.le hq1 S := by
  calc
    HasPolarizedCoefficientVectorEquation
        canonicalCompletedNativeLogDerivativeMoment rawJet ↔
      HasCorrectedNativeChiralFirstColumnGram M rawJet :=
      hasNativePolarizedCoefficientVectorEquation_iff_correctedChiralFirstColumnGram_of_transport
        M rawJet htransport
    _ ↔ _ := correctedChiralFirstColumnGram_iff_sixAnalysisJet
      M rawJet q hqpos hq1 S

/-- Once a geometrically defined fixed-carrier jet proves this six-analysis
first-column identity, the existing first-column API yields the HP carrier
certificate.  The only additional inputs are the actual Gram-shift and the
two parity independence proofs of that candidate. -/
theorem completedNativeRealHPCarrierCertificate_of_sixAnalysisJet_and_transport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (M : ℕ) (rawJet : ℕ → E)
    (htransport : ∀ p q : ℕ,
      inner ℂ (rawJet p) (rawJet (q + 1)) =
        inner ℂ (rawJet (p + 1)) (rawJet q))
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (hfirst : ∀ p : ℕ,
      inner ℂ (rawJet p) (rawJet 0) =
        canonicalC3BracketTfvdSixAnalysisJetCoefficient
          M p q hqpos.le hq1 S)
    (heven : LinearIndependent ℂ (fun n : ℕ ↦ rawJet (2 * n)))
    (hodd : LinearIndependent ℂ (fun n : ℕ ↦ rawJet (2 * n + 1))) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    CompletedNativeRealHPCarrierCertificate
      (polarizedCoefficientParityJet rawJet) := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  apply completedNativeRealHPCarrierCertificate_of_firstColumn_and_transport
    rawJet htransport
  · intro p
    calc
      inner ℂ (rawJet p) (rawJet 0) =
          canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p :=
        (correctedChiralFirstColumnGram_iff_sixAnalysisJet
          M rawJet q hqpos hq1 S).mpr hfirst p
      _ = oddMomentResponseCoefficient
            canonicalCompletedNativeLogDerivativeMoment (p + 1) :=
        canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_firstColumnTarget M p
  · exact heven
  · exact hodd

end

end CarrySelfAdjointOperator
