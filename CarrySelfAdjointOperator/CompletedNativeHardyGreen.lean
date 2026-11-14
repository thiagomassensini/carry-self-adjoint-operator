import CarrySelfAdjointOperator.CompletedNativeHardyAlgebra
import CarrySelfAdjointOperator.CompletedNativeHardyAnalytic
import CarrySelfAdjointOperator.CompletedNativeHPGateAudit

/-!
# Real Green carrier from Hardy nonrecurrence

This consumer keeps the Green--Wronskian Gram representation explicit.  The
positive-real-zero hypothesis proves the two independence fields through the
nonrecurrence theorem; no positivity or spectral construction is assumed.
-/

namespace CarrySelfAdjointOperator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {jet : (ℕ ⊕ ℕ) → E}

/-- Infinitely many positive real zeros and the correct Green Gram identity
construct the carrier-honest real HP certificate. -/
theorem completedNativeRealHPCarrierCertificate_of_infinitePositiveRealNativeZeros
    (hHardy : InfinitePositiveRealNativeZeros)
    (hrep : IsGreenWronskianMomentKernelGramRepresentation
      canonicalCompletedNativeLogDerivativeMoment jet) :
    CompletedNativeRealHPCarrierCertificate jet := by
  have hno :=
    canonicalCompletedNativeLogDerivativeMoment_noFiniteMomentRelation_of_infinitePositiveRealNativeZeros
      hHardy
  obtain ⟨heven, hodd⟩ :=
    greenWronskianMomentKernel_independent_of_noFiniteMomentRelation hno hrep
  exact ⟨hrep, heven, hodd⟩

/-- Every finite canonical Hankel pair is strictly positive under the same
real-zero and Green Gram hypotheses. -/
theorem hankelPair_posDef_of_infinitePositiveRealNativeZeros
    (hHardy : InfinitePositiveRealNativeZeros)
    (hrep : IsGreenWronskianMomentKernelGramRepresentation
      canonicalCompletedNativeLogDerivativeMoment jet)
    (N : ℕ) :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment N).PosDef ∧
      (shiftedHankel canonicalCompletedNativeLogDerivativeMoment N).PosDef :=
  (completedNativeRealHPCarrierCertificate_of_infinitePositiveRealNativeZeros
    hHardy hrep).hankelPair_posDef N

end CarrySelfAdjointOperator
