import CarrySelfAdjointOperator.CompletedNativeTfvdGreenMomentGramBridge
import CarrySelfAdjointOperator.CompletedNativeHPGateAudit
import CarrySelfAdjointOperator.CompletedNativeXiCosineMomentHerglotzGate
import Mathlib.Tactic

/-!
# No-go for the complex Taylor realization of the native Green residual

The normalized product ledger has zero first complex odd Taylor jet, because
its carrier is not complex differentiable at the centered origin.  The
completed forward-difference Green carrier, however, has first odd diagonal
equal to the canonical shifted moment `h₁`.  Thus the Taylor-to-limit Gram
residual cannot vanish for this radial complex Taylor realization.

This is a carrier correction, not a failure of the native operator chain.  It
forces the remaining proof to use the real TFVD/enriched carrier and its
center--leg or endpoint--bulk--return readout.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

local instance canonicalResidualRealInnerProductSpace
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    [CompleteSpace Hxi] :
    InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
  InnerProductSpace.rclikeToReal ℂ _

/-- The odd `(0,0)` residual is exactly the shifted moment `h₁` in the
complex Taylor realization, hence it is nonzero whenever `h₁ ≠ 0`. -/
theorem canonicalCompletedNativeGreenForwardDifferenceGramResidual_odd_zero_eq_moment_one
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    [CompleteSpace Hxi]
    (xiState : ℂ → Hxi)
    (hkernel :
      HasCompletedNativeRealAxisNormalizedGreenKernel
        (completedNativeC3ProductLedgerState xiState)) :
    canonicalCompletedNativeGreenForwardDifferenceGramResidual
        xiState hkernel (Sum.inr 0) (Sum.inr 0) =
      (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) := by
  let limitJet :=
    canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
      (completedNativeC3ProductLedgerState xiState) hkernel
  have hkernel' :
      IsGreenWronskianMomentKernelGramRepresentation
        canonicalCompletedNativeLogDerivativeMoment limitJet :=
    canonicalCompletedNativeGreenForwardDifferenceLimitParityJet_momentKernel
      (completedNativeC3ProductLedgerState xiState) hkernel
  have h := hkernel' (Sum.inr 0) (Sum.inr 0)
  have hreal :
      (inner ℂ (limitJet (Sum.inr 0)) (limitJet (Sum.inr 0))).re =
        canonicalCompletedNativeLogDerivativeMoment 1 := by
    change greenWronskianMomentKernel
        canonicalCompletedNativeLogDerivativeMoment
        (Sum.inr 0) (Sum.inr 0) =
      (inner ℂ (limitJet (Sum.inr 0)) (limitJet (Sum.inr 0))).re at h
    simpa [greenWronskianMomentKernel] using h.symm
  unfold canonicalCompletedNativeGreenForwardDifferenceGramResidual
  rw [show canonicalCompletedNativeGreenParityJet xiState (Sum.inr 0) = 0 by
    exact canonicalCompletedNativeGreenParityJet_firstOdd_eq_zero xiState]
  simp only [inner_zero_left, sub_zero]
  exact_mod_cast hreal

/-- The proposed all-index residual-zero gate is impossible for the current
complex Taylor ledger as soon as the shifted native moment is nonzero. -/
theorem not_forall_canonicalCompletedNativeGreenForwardDifferenceGramResidual_eq_zero
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    [CompleteSpace Hxi]
    (xiState : ℂ → Hxi)
    (hkernel :
      HasCompletedNativeRealAxisNormalizedGreenKernel
        (completedNativeC3ProductLedgerState xiState))
    (h₁ : canonicalCompletedNativeLogDerivativeMoment 1 ≠ 0) :
    ¬ ∀ i j,
        canonicalCompletedNativeGreenForwardDifferenceGramResidual
          xiState hkernel i j = 0 := by
  intro hzero
  have hodd :=
    canonicalCompletedNativeGreenForwardDifferenceGramResidual_odd_zero_eq_moment_one
      xiState hkernel
  rw [hzero (Sum.inr 0) (Sum.inr 0)] at hodd
  exact h₁ (by exact_mod_cast hodd.symm)

/-- The already formalized low-order Xi/cosine certificate makes the shifted
moment strictly positive, so the preceding obstruction is unconditional. -/
theorem canonicalCompletedNativeLogDerivativeMoment_one_ne_zero :
    canonicalCompletedNativeLogDerivativeMoment 1 ≠ 0 := by
  have hlow := canonicalCompletedNativeLowOrderHerglotzCurvaturePositive
  have hmoment :=
    (canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp
      hlow).2
  exact ne_of_gt hmoment

theorem not_forall_canonicalCompletedNativeGreenForwardDifferenceGramResidual_eq_zero_unconditional
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    [CompleteSpace Hxi]
    (xiState : ℂ → Hxi)
    (hkernel :
      HasCompletedNativeRealAxisNormalizedGreenKernel
        (completedNativeC3ProductLedgerState xiState)) :
    ¬ ∀ i j,
        canonicalCompletedNativeGreenForwardDifferenceGramResidual
          xiState hkernel i j = 0 :=
  not_forall_canonicalCompletedNativeGreenForwardDifferenceGramResidual_eq_zero
    xiState hkernel canonicalCompletedNativeLogDerivativeMoment_one_ne_zero

end

end CarrySelfAdjointOperator
