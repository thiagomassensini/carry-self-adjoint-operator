import CarrySelfAdjointOperator.CompletedC3NaimarkCoisometricBlock
import CarrySelfAdjointOperator.CompletedTfvdGreenAllOrderIntertwining
import CarrySelfAdjointOperator.CompletedNativeTfvdCoefficientJetHPCarrier
import Mathlib.Tactic

/-!
# Audit of the already constructed completed C3 dressed state

The lossless Naimark block, the completed ambient/Gamma correction, and the
oriented ordinary/log-jet/residual carrier are related but are not the same
defect construction.

This module records the two shortest vector-level conclusions of that audit.

* The completed ambient response already lies in the Naimark port.  Its
  complementary Naimark escape is therefore zero and cannot itself supply
  the nonzero completed-native defect jets.
* The existing oriented ordinary/log-jet/residual state maps canonically to
  the concrete positive real-axis carrier.  If the already named concrete
  sewing equality is supplied, its first even and odd Green jets realize
  exactly `h₀` and `h₁`, and both jets are nonzero.

No theta estimate is used in either statement.  The second statement keeps
the concrete sewing equality visible as the remaining premise.
-/

open scoped InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-! ## The response has no complementary Naimark escape -/

/-- The completed ambient response is already a promoted camera vector, so
the complementary Naimark projection annihilates it. -/
theorem canonicalCompletedC3AmbientPortEscape_completedResponse_eq_zero
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3AmbientPortEscape
        (completedC3SymplecticNaimarkState
          (operatorHeightParameter z) hzHalf) = 0 := by
  rw [canonicalCompletedC3AmbientPortEscape_apply,
    canonicalCompletedC3AmbientPortProjection_completedSymplecticState]
  exact sub_self _

/-- Real-axis wrapper for the most direct candidate obtained by taking the
Naimark escape of the completed response. -/
def canonicalCompletedC3RealAxisResponseNaimarkEscapeState
    (z : ℂ) :
      NativeCarrySpectralWeyl.Infinite.RealifiedNaimarkComplexification :=
  canonicalCompletedC3AmbientPortEscape
    (canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisState z)

@[simp] theorem canonicalCompletedC3RealAxisResponseNaimarkEscapeState_eq_zero
    (z : ℂ) :
    canonicalCompletedC3RealAxisResponseNaimarkEscapeState z = 0 := by
  unfold canonicalCompletedC3RealAxisResponseNaimarkEscapeState
    canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisState
  exact canonicalCompletedC3AmbientPortEscape_completedResponse_eq_zero
    (z.re : ℂ) (ofReal_mem_completedNativeHeightDomain z.re).1

/-! ## The existing dressed carrier reaches the moment/operator tower -/

/-- The already constructed concrete dressed state is literally the
canonical image of the completed oriented ordinary/log-jet/residual state.
This is a vector identity before any Gram or Taylor readout. -/
theorem canonicalCompletedC3ExistingDressedState_eq_orientedImage
    (time : ℝ) :
    canonicalCompletedC3RealAxisPositiveState (time : ℂ) =
      completedC3OrientedGreenFrameToPositiveCarrier
        (canonicalCompletedC3OrientedGreenFrameState
          (nativeLine time) (nativeLine_mem_genuineCriticalStrip time)) := by
  exact
    (completedC3OrientedGreenFrameToPositiveCarrier_nativeLine_eq_positiveState
      time).symm

/-- Conditional low-order handoff.  The only premise is the concrete
channel-complete sewing equality already isolated in the repository.  Once
it is available, the first even and odd forward-difference limit jets have
squared norms `h₀` and `h₁`; global independence already proves that both
vectors are nonzero. -/
theorem canonicalCompletedC3ExistingDressedJets_lowOrder_of_sewing
    (hsewing : CanonicalCompletedC3ConcreteRealAxisPositiveSewing) :
    let hkernel :=
      hasCompletedNativeRealAxisNormalizedGreenKernel_of_concreteC3Sewing
        hsewing
    letI : InnerProductSpace ℝ CanonicalCompletedC3RealAxisPositiveCarrier :=
      InnerProductSpace.rclikeToReal ℂ
        CanonicalCompletedC3RealAxisPositiveCarrier
    let jet := canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
      canonicalCompletedC3ConcreteRealAxisGreenState hkernel
    inner ℝ (jet (Sum.inl 0)) (jet (Sum.inl 0)) =
        canonicalCompletedNativeLogDerivativeMoment 0 ∧
      inner ℝ (jet (Sum.inr 0)) (jet (Sum.inr 0)) =
        canonicalCompletedNativeLogDerivativeMoment 1 ∧
      jet (Sum.inl 0) ≠ 0 ∧ jet (Sum.inr 0) ≠ 0 := by
  dsimp only
  letI : InnerProductSpace ℝ CanonicalCompletedC3RealAxisPositiveCarrier :=
    InnerProductSpace.rclikeToReal ℂ
      CanonicalCompletedC3RealAxisPositiveCarrier
  let hkernel :=
    hasCompletedNativeRealAxisNormalizedGreenKernel_of_concreteC3Sewing
      hsewing
  let jet := canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
    canonicalCompletedC3ConcreteRealAxisGreenState hkernel
  let certificate : CompletedNativeRealHPCarrierCertificate jet :=
    completedNativeRealHPCarrierCertificate_of_concreteC3Kernel hkernel
  have heven := certificate.momentKernel (Sum.inl 0) (Sum.inl 0)
  have hodd := certificate.momentKernel (Sum.inr 0) (Sum.inr 0)
  refine ⟨?_, ?_, certificate.evenIndependent.ne_zero 0,
    certificate.oddIndependent.ne_zero 0⟩
  · simpa [jet, greenWronskianMomentKernel, Matrix.gram] using heven.symm
  · simpa [jet, greenWronskianMomentKernel, Matrix.gram] using hodd.symm

end

end CarrySelfAdjointOperator
