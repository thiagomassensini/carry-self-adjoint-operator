import CarrySelfAdjointOperator.CanonicalLDLPrefixReduction
import CarrySelfAdjointOperator.SignedFiniteHeightOperator
import CarrySelfAdjointOperator.GreenJetReciprocalSignedHeightOperator
import CarrySelfAdjointOperator.CompletedNativeWeylMoments
import Mathlib.Tactic

/-!
# Genuine moment provenance determines the height operators

The division-free identity

`q * Phi = -Phi'`

already determines the complete logarithmic moment sequence once `Phi 0` is
nonzero.  This file transports that uniqueness through every root-free
operator constructed from those moments.  Consequently neither the Hankel
pair, the canonical Jacobi tower, nor the finite or completed signed-height
operator has any remaining moment-level freedom.

These statements do not replace the analytic coefficient gate identifying
the concrete completed Green jet with the logarithmic moments of `Phi`.  They
show that after that identification there is no second choice of Weyl data or
height operator.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- The unshifted Hankel tower is fixed by the completed characteristic. -/
theorem hankelGram_eq_of_logDerivativeMomentSequence
    {phi moments moments' : ℕ → ℝ}
    (hphi : phi 0 ≠ 0)
    (hrel : IsLogDerivativeMomentSequence phi moments)
    (hrel' : IsLogDerivativeMomentSequence phi moments')
    (N : ℕ) :
    hankelGram moments N = hankelGram moments' N := by
  rw [hrel.unique hphi hrel']

/-- The shifted Hankel tower is fixed by the same characteristic. -/
theorem shiftedHankel_eq_of_logDerivativeMomentSequence
    {phi moments moments' : ℕ → ℝ}
    (hphi : phi 0 ≠ 0)
    (hrel : IsLogDerivativeMomentSequence phi moments)
    (hrel' : IsLogDerivativeMomentSequence phi moments')
    (N : ℕ) :
    shiftedHankel moments N = shiftedHankel moments' N := by
  rw [hrel.unique hphi hrel']

/-- The canonical finite Jacobi section admits no choice after its Genuine
logarithmic moments have been identified. -/
theorem canonicalFiniteJacobiSection_eq_of_logDerivativeMomentSequence
    {phi moments moments' : ℕ → ℝ}
    (hphi : phi 0 ≠ 0)
    (hrel : IsLogDerivativeMomentSequence phi moments)
    (hrel' : IsLogDerivativeMomentSequence phi moments')
    (N : ℕ)
    (hgram : (hankelGram moments N).PosDef)
    (hgram' : (hankelGram moments' N).PosDef) :
    canonicalFiniteJacobiSection moments N hgram =
      canonicalFiniteJacobiSection moments' N hgram' := by
  have hmoments := hrel.unique hphi hrel'
  subst moments'
  rfl

/-- The entrywise projective Jacobi limit is fixed by the Genuine
logarithmic moments. -/
theorem canonicalJacobiTowerLimitMatrix_eq_of_logDerivativeMomentSequence
    {phi moments moments' : ℕ → ℝ}
    (hphi : phi 0 ≠ 0)
    (hrel : IsLogDerivativeMomentSequence phi moments)
    (hrel' : IsLogDerivativeMomentSequence phi moments')
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef)
    (hgram' : ∀ N : ℕ, (hankelGram moments' N).PosDef) :
    canonicalJacobiTowerLimitMatrix moments hgram =
      canonicalJacobiTowerLimitMatrix moments' hgram' := by
  have hmoments := hrel.unique hphi hrel'
  subst moments'
  rfl

/-- The positive finite height operator `J_N⁻¹ᐟ²` is fixed by the Genuine
moments, independently of the proof objects used to construct it. -/
theorem canonicalFiniteHeightOperator_eq_of_logDerivativeMomentSequence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {phi moments moments' : ℕ → ℝ} {feature : ℕ → E}
    (hphi : phi 0 ≠ 0)
    (hrel : IsLogDerivativeMomentSequence phi moments)
    (hrel' : IsLogDerivativeMomentSequence phi moments')
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (hrep' : IsShiftedMomentGramRepresentation moments' feature)
    (N : ℕ)
    (hgram : (hankelGram moments N).PosDef)
    (hgram' : (hankelGram moments' N).PosDef)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ)))
    (hli' : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    canonicalFiniteHeightOperator hrep N hgram hli =
      canonicalFiniteHeightOperator hrep' N hgram' hli' := by
  have hmoments := hrel.unique hphi hrel'
  subst moments'
  rfl

/-- The signed finite height operator is likewise forced by `Phi`; no list of
target heights can alter it. -/
theorem canonicalSignedFiniteHeightOperator_eq_of_logDerivativeMomentSequence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {phi moments moments' : ℕ → ℝ} {feature : ℕ → E}
    (hphi : phi 0 ≠ 0)
    (hrel : IsLogDerivativeMomentSequence phi moments)
    (hrel' : IsLogDerivativeMomentSequence phi moments')
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (hrep' : IsShiftedMomentGramRepresentation moments' feature)
    (N : ℕ)
    (hgram : (hankelGram moments N).PosDef)
    (hgram' : (hankelGram moments' N).PosDef)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ)))
    (hli' : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    canonicalSignedFiniteHeightOperator hrep N hgram hli =
      canonicalSignedFiniteHeightOperator hrep' N hgram' hli' := by
  have hmoments := hrel.unique hphi hrel'
  subst moments'
  rfl

/-- On one completed Green carrier, the global maximal self-adjoint
reciprocal signed-height operator is fixed by the Genuine characteristic.
Different proofs of the Green realization, independence, or zero-mass gate
cannot change the operator. -/
theorem
    canonicalCompletedGreenJetMomentReciprocalSignedHeightOperator_eq_of_logDerivativeMomentSequence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {phi moments moments' : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hphi : phi 0 ≠ 0)
    (hrel : IsLogDerivativeMomentSequence phi moments)
    (hrel' : IsLogDerivativeMomentSequence phi moments')
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (hrep' : IsGreenWronskianMomentKernelGramRepresentation moments' jet)
    (heven : LinearIndependent ℝ (fun n : ℕ ↦ jet (Sum.inl n)))
    (heven' : LinearIndependent ℝ (fun n : ℕ ↦ jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ ↦ jet (Sum.inr n)))
    (hodd' : LinearIndependent ℝ (fun n : ℕ ↦ jet (Sum.inr n)))
    (hvanish : HasVanishingGreenJetHeadTailMomentDefect moments)
    (hvanish' : HasVanishingGreenJetHeadTailMomentDefect moments') :
    canonicalCompletedGreenJetMomentReciprocalSignedHeightOperator
        hrep heven hodd hvanish =
      canonicalCompletedGreenJetMomentReciprocalSignedHeightOperator
        hrep' heven' hodd' hvanish' := by
  have hmoments := hrel.unique hphi hrel'
  subst moments'
  rfl

/-! ## Concrete completed-native specialization -/

/-- Two Green/Weyl moment realizations of the actual completed native
characteristic produce the same finite Jacobi section. -/
theorem canonicalFiniteJacobiSection_eq_of_completedNativeLogDerivativeMoments
    {moments moments' : ℕ → ℝ}
    (hrel : IsCompletedNativeLogDerivativeMomentSequence moments)
    (hrel' : IsCompletedNativeLogDerivativeMomentSequence moments')
    (N : ℕ)
    (hgram : (hankelGram moments N).PosDef)
    (hgram' : (hankelGram moments' N).PosDef) :
    canonicalFiniteJacobiSection moments N hgram =
      canonicalFiniteJacobiSection moments' N hgram' := by
  have hmoments := hrel.unique hrel'
  subst moments'
  rfl

/-- The complete projective Jacobi matrix is uniquely forced by the concrete
completed Genuine characteristic. -/
theorem
    canonicalJacobiTowerLimitMatrix_eq_of_completedNativeLogDerivativeMoments
    {moments moments' : ℕ → ℝ}
    (hrel : IsCompletedNativeLogDerivativeMomentSequence moments)
    (hrel' : IsCompletedNativeLogDerivativeMomentSequence moments')
    (hgram : ∀ N : ℕ, (hankelGram moments N).PosDef)
    (hgram' : ∀ N : ℕ, (hankelGram moments' N).PosDef) :
    canonicalJacobiTowerLimitMatrix moments hgram =
      canonicalJacobiTowerLimitMatrix moments' hgram' := by
  have hmoments := hrel.unique hrel'
  subst moments'
  rfl

/-- On one completed Green carrier, the maximal self-adjoint height operator
is uniquely forced by the concrete completed Genuine characteristic. -/
theorem
    canonicalCompletedGreenJetMomentReciprocalSignedHeightOperator_eq_of_completedNativeLogDerivativeMoments
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments moments' : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrel : IsCompletedNativeLogDerivativeMomentSequence moments)
    (hrel' : IsCompletedNativeLogDerivativeMomentSequence moments')
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (hrep' : IsGreenWronskianMomentKernelGramRepresentation moments' jet)
    (heven : LinearIndependent ℝ (fun n : ℕ ↦ jet (Sum.inl n)))
    (heven' : LinearIndependent ℝ (fun n : ℕ ↦ jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ ↦ jet (Sum.inr n)))
    (hodd' : LinearIndependent ℝ (fun n : ℕ ↦ jet (Sum.inr n)))
    (hvanish : HasVanishingGreenJetHeadTailMomentDefect moments)
    (hvanish' : HasVanishingGreenJetHeadTailMomentDefect moments') :
    canonicalCompletedGreenJetMomentReciprocalSignedHeightOperator
        hrep heven hodd hvanish =
      canonicalCompletedGreenJetMomentReciprocalSignedHeightOperator
        hrep' heven' hodd' hvanish' := by
  have hmoments := hrel.unique hrel'
  subst moments'
  rfl

end

end CarrySelfAdjointOperator
