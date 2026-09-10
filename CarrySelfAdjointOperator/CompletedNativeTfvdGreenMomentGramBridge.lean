import CarrySelfAdjointOperator.CompletedNativeTfvdWronskianMoments
import CarrySelfAdjointOperator.CompletedTfvdGreenAllOrderIntertwining
import CarrySelfAdjointOperator.CompletedGreenForwardDifferenceVectorLimit
import CarrySelfAdjointOperator.CompletedNativeCausalCoefficientMomentGate
import Mathlib.Tactic

/-!
# Camera-free TFVD-Green moment Gram bridge

The completed bracket--TFVD Wronskian already fixes the canonical native
logarithmic moments exactly, at every finite carrier cutoff. The completed
TFVD-Green intertwiner is likewise a vector equality before scalar readout.

This module keeps the remaining Gram seam explicit. The concrete
HasCanonicalCompletedNativeGreenMomentJets certificate asks for the
inner products of the Taylor jets of the normalized product ledger. The
forward-difference completion already supplies a real Green Gram of its own
limit jet. The residual below is the exact difference between these two
readouts; no camera limit or fitted realization is introduced.
-/

namespace CarrySelfAdjointOperator

noncomputable section

attribute [local instance 10000] NormedSpace.complexToReal
attribute [local instance 10000] Complex.instNormedAddCommGroup

open NativeCarrySpectralWeyl.Infinite

local instance cameraFreeNaimarkComplexInnerProductSpace :
    InnerProductSpace ℂ RealifiedNaimarkComplexification :=
  RealHilbertComplexification.instInnerProductSpaceComplexOfReal

open CPFormal.Analytic.Cp

/-- The exact scalar moment identity used by the camera-free bridge. -/
theorem cameraFreeTfvdWronskianMoment_eq_canonical
    (M n : ℕ) :
    canonicalC3BracketTfvdMoment M n =
      canonicalCompletedNativeLogDerivativeMoment n :=
  canonicalC3BracketTfvdMoment_eq_canonical M n

/-- The all-order vector TFVD-Green intertwiner retained as a public
crosswalk. It is an equality of port-valued functions, before any scalar
moment readout. -/
theorem cameraFreeTfvdGreenPort_vector_intertwiner :
    canonicalCompletedTfvdGreenPortState =
      NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3 :=
  canonicalCompletedTfvdGreenPortState_eq_bracketGreenPort

/-- The same vector intertwiner after the existing Naimark promotion and every
finite forward-difference parity jet. -/
theorem cameraFreeTfvdGreenNaimark_forwardDifference_intertwiner
    (k : ℕ) :
    completedGreenForwardDifferenceParityJet
        canonicalCompletedTfvdGreenNaimarkState k =
      completedGreenForwardDifferenceParityJet
        (fun z =>
          (NativeCarryC3Crosswalk.c3SixCameraNaimarkRealization
            (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
              3 z) :
            CarryGammaComplexNaimark)) k :=
  canonicalCompletedTfvdGreenNaimark_forwardDifferenceParityJet_eq_bracket k

/-- Complex defect of the actual normalized completed Green Taylor-jet Gram
from the prescribed parity-split native moment kernel. -/
def canonicalCompletedNativeGreenMomentGramDefect
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (moments : ℕ → ℝ)
    (i j : ℕ ⊕ ℕ) : ℂ :=
  (greenWronskianMomentKernel moments i j : ℂ) -
    inner ℂ
      (canonicalCompletedNativeGreenParityJet xiState i)
      (canonicalCompletedNativeGreenParityJet xiState j)

/-- The desired complex Green moment-kernel statement is exactly the
vanishing of the displayed Taylor-jet defect. -/
theorem isComplexGreenMomentKernel_iff_canonicalGreenMomentGramDefect_zero
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (moments : ℕ → ℝ) :
    IsComplexGreenWronskianMomentKernelGramRepresentation moments
        (canonicalCompletedNativeGreenParityJet xiState) ↔
      ∀ i j,
        canonicalCompletedNativeGreenMomentGramDefect xiState moments i j = 0 := by
  constructor
  · intro h i j
    simp only [canonicalCompletedNativeGreenMomentGramDefect]
    rw [h i j]
    simp
  · intro h i j
    exact sub_eq_zero.mp (h i j)

/-- With the already-separated factor Green representations supplied, the
full native certificate is equivalent to the single displayed Taylor-jet
Gram defect. The factor identities remain explicit hypotheses. -/
theorem hasCanonicalCompletedNativeGreenMomentJets_iff_defect_zero_of_factors
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (moments : ℕ → ℝ)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState) :
    HasCanonicalCompletedNativeGreenMomentJets xiState moments ↔
      ∀ i j,
        canonicalCompletedNativeGreenMomentGramDefect xiState moments i j = 0 := by
  constructor
  · intro h
    exact
      (isComplexGreenMomentKernel_iff_canonicalGreenMomentGramDefect_zero
        xiState moments).mp h.momentKernel
  · intro h
    exact
      hasCanonicalCompletedNativeGreenMomentJets_of_factors
        xiState moments hxi hnative
        ((isComplexGreenMomentKernel_iff_canonicalGreenMomentGramDefect_zero
          xiState moments).mpr h)

/-- Exact residual comparing the actual Taylor-jet Gram with the real Gram
readout of the existing completed forward-difference limit jet. The cast of
the real limit pairing is deliberate: the limit theorem currently exposes
the real restriction-of-scalars Gram, while the target certificate is the
stronger complex Gram statement. -/
def canonicalCompletedNativeGreenForwardDifferenceGramResidual
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi] [CompleteSpace Hxi]
    (xiState : ℂ → Hxi)
    (hkernel :
      HasCompletedNativeRealAxisNormalizedGreenKernel
        (completedNativeC3ProductLedgerState xiState))
    (i j : ℕ ⊕ ℕ) : ℂ :=
  ((inner ℂ
      (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        (completedNativeC3ProductLedgerState xiState) hkernel i)
      (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        (completedNativeC3ProductLedgerState xiState) hkernel j)).re : ℂ) -
    inner ℂ
      (canonicalCompletedNativeGreenParityJet xiState i)
      (canonicalCompletedNativeGreenParityJet xiState j)

/-- Exact residual comparing the actual Taylor-jet Gram with the real Gram
readout of the existing completed forward-difference limit jet. -/
theorem canonicalCompletedNativeGreenMomentGramDefect_eq_forwardDifferenceResidual
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi] [CompleteSpace Hxi]
    (xiState : ℂ → Hxi)
    (hkernel :
      HasCompletedNativeRealAxisNormalizedGreenKernel
        (completedNativeC3ProductLedgerState xiState))
    (i j : ℕ ⊕ ℕ) :
    canonicalCompletedNativeGreenMomentGramDefect
        xiState canonicalCompletedNativeLogDerivativeMoment i j =
      canonicalCompletedNativeGreenForwardDifferenceGramResidual
        xiState hkernel i j := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  let limitJet :=
    canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
      (completedNativeC3ProductLedgerState xiState) hkernel
  have hkernel' :
      IsGreenWronskianMomentKernelGramRepresentation
        canonicalCompletedNativeLogDerivativeMoment limitJet :=
    canonicalCompletedNativeGreenForwardDifferenceLimitParityJet_momentKernel
      (completedNativeC3ProductLedgerState xiState) hkernel
  have h := hkernel' i j
  change greenWronskianMomentKernel
      canonicalCompletedNativeLogDerivativeMoment i j =
    (inner ℂ (limitJet i) (limitJet j)).re at h
  have hcast :
      (greenWronskianMomentKernel
          canonicalCompletedNativeLogDerivativeMoment i j : ℂ) =
        ((inner ℂ (limitJet i) (limitJet j)).re : ℂ) := by
    exact_mod_cast h
  simp [canonicalCompletedNativeGreenMomentGramDefect,
    canonicalCompletedNativeGreenForwardDifferenceGramResidual, limitJet,
    hcast]

/-- If the explicit Taylor-to-forward-difference residual vanishes, the
factor-level Green hypotheses produce the full canonical moment-jet
certificate. -/
theorem hasCanonicalCompletedNativeGreenMomentJets_of_forwardDifferenceResidual_zero
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi] [CompleteSpace Hxi]
    (xiState : ℂ → Hxi)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hkernel :
      HasCompletedNativeRealAxisNormalizedGreenKernel
        (completedNativeC3ProductLedgerState xiState))
    (hresidual : ∀ i j,
      canonicalCompletedNativeGreenForwardDifferenceGramResidual
        xiState hkernel i j = 0) :
    HasCanonicalCompletedNativeGreenMomentJets xiState
      canonicalCompletedNativeLogDerivativeMoment := by
  apply
    (hasCanonicalCompletedNativeGreenMomentJets_iff_defect_zero_of_factors
      xiState canonicalCompletedNativeLogDerivativeMoment hxi hnative).mpr
  intro i j
  rw [canonicalCompletedNativeGreenMomentGramDefect_eq_forwardDifferenceResidual
    xiState hkernel i j]
  exact hresidual i j

end

end CarrySelfAdjointOperator
