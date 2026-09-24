import CarrySelfAdjointOperator.ProjectiveValveMomentFrontier
import CarrySelfAdjointOperator.NativeMomentProjectiveValveBridge
import CarrySelfAdjointOperator.TfvdBoundaryCompletedTransport
import Mathlib.Tactic

/-!
# First-column calibration after lossless TFVD reconstruction

The projective valve fixes the *scalar* completed-native moment series. A
lossless TFVD analysis fixes how a vertical state retains its trace and
second-difference channels. Neither fact alone identifies a Hilbert Gram.

For a proposed fixed-carrier vector family `rawJet`, the remaining metric
condition has two pieces: its first column must equal the completed response,
and its Gram must transport one raw order from right to left. When the latter
transport law is already native to the candidate (as for the seeded clock
atlas), this file makes the first-column condition the only remaining metric
gate.

This is deliberately conditional. The current finite causal TFVD Gram is
strictly positive, but no theorem yet supplies its all-order fixed-carrier
Gram-shift law or its first-column calibration. TFVD reconstruction is
lossless analysis/synthesis; it must not be mistaken for either metric
identity.
-/

namespace CarrySelfAdjointOperator

open scoped InnerProductSpace

noncomputable section

/-- If a proposed Hilbert jet already obeys the interior polarized transport,
then its complete coefficient equation is equivalent to calibrating its first
column against the completed-native response. This is the exact sense in
which a candidate with native shift reduces the moment frontier to one
boundary gate. -/
theorem hasPolarizedCoefficientVectorEquation_iff_firstColumn_of_transport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (moments : ℕ → ℝ) (rawJet : ℕ → E)
    (htransport : ∀ p q : ℕ,
      inner ℂ (rawJet p) (rawJet (q + 1)) =
        inner ℂ (rawJet (p + 1)) (rawJet q)) :
    HasPolarizedCoefficientVectorEquation moments rawJet ↔
      ∀ p : ℕ,
        inner ℂ (rawJet p) (rawJet 0) =
          oddMomentResponseCoefficient moments (p + 1) := by
  change IsPolarizedGreenCoefficientEquation moments
    (fun p q => inner ℂ (rawJet p) (rawJet q)) ↔ _
  rw [polarizedGreenCoefficientEquation_iff_boundary_transport]
  constructor
  · exact fun h => h.1
  · intro hboundary
    exact ⟨hboundary, htransport⟩

/-- For the actual native moment sequence, an all-order shifted candidate has
the moment Gram exactly when its first column is the completed ledger/response
column. No positivity is assumed here. -/
theorem hasNativePolarizedCoefficientVectorEquation_iff_firstColumn_of_transport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (rawJet : ℕ → E)
    (htransport : ∀ p q : ℕ,
      inner ℂ (rawJet p) (rawJet (q + 1)) =
        inner ℂ (rawJet (p + 1)) (rawJet q)) :
    HasPolarizedCoefficientVectorEquation
        canonicalCompletedNativeLogDerivativeMoment rawJet ↔
      ∀ p : ℕ,
        inner ℂ (rawJet p) (rawJet 0) =
          oddMomentResponseCoefficient
            canonicalCompletedNativeLogDerivativeMoment (p + 1) :=
  hasPolarizedCoefficientVectorEquation_iff_firstColumn_of_transport
    canonicalCompletedNativeLogDerivativeMoment rawJet htransport

/-- Once an all-order shifted candidate is calibrated on its first column and
its parity families are independent, the existing downstream constructor
supplies the real HP carrier certificate. TFVD contributes only when an
actual `rawJet` is later shown to arise from its lossless completed channels. -/
theorem completedNativeRealHPCarrierCertificate_of_firstColumn_and_transport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (rawJet : ℕ → E)
    (htransport : ∀ p q : ℕ,
      inner ℂ (rawJet p) (rawJet (q + 1)) =
        inner ℂ (rawJet (p + 1)) (rawJet q))
    (hboundary : ∀ p : ℕ,
      inner ℂ (rawJet p) (rawJet 0) =
        oddMomentResponseCoefficient
          canonicalCompletedNativeLogDerivativeMoment (p + 1))
    (heven : LinearIndependent ℂ (fun n : ℕ => rawJet (2 * n)))
    (hodd : LinearIndependent ℂ (fun n : ℕ => rawJet (2 * n + 1))) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    CompletedNativeRealHPCarrierCertificate
      (polarizedCoefficientParityJet rawJet) := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  apply completedNativeRealHPCarrierCertificate_of_vectorCoefficientEquation
  · exact
      (hasNativePolarizedCoefficientVectorEquation_iff_firstColumn_of_transport
        rawJet htransport).2 hboundary
  · exact heven
  · exact hodd

end

end CarrySelfAdjointOperator
