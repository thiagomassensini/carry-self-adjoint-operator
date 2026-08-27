import CarrySelfAdjointOperator.BR2GreenFrameIncidenceTransport
import CarrySelfAdjointOperator.CompletedGreenForwardDifferenceVectorLimit
import CarrySelfAdjointOperator.CompletedNativeHPGateAudit
import Mathlib.Tactic

/-!
# BR2 Green-frame jet and the completed dslope limit

This file places the BR2 incidence jet and the canonical completed-native
forward-difference (`dslope`) jet in the same concrete all-bases Green-frame
carrier.  The analysis map is continuous and injective, so no Hilbert-state
information or structural channel is discarded.

The final identification is reduced exactly to vector convergence of the
analyzed finite forward-difference approximants.  Equivalently, it is the
statement that their vector defect against the BR2 jet tends to zero.  No
scalar Gram readout, zero specialization, or spectral hypothesis is used.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter
open GreenFrame.Concrete

noncomputable section

/-! ## Continuous all-bases analysis -/

/-- Continuous realization of the raw all-bases Green analysis on the
completed TFVD carrier. -/
def canonicalCompletedGreenFrameAnalysisCLM :
    CarryVerticalL2 →L[ℂ] CanonicalCompletedGreenFrameCarrier :=
  (concreteAnalysisOperator canonicalCarryInfinitePartition).comp
    carryVerticalL2GreenFrameStateEquiv.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem canonicalCompletedGreenFrameAnalysisCLM_apply
    (x : CarryVerticalL2) :
    canonicalCompletedGreenFrameAnalysisCLM x =
      canonicalCompletedGreenFrameAnalysis x :=
  rfl

theorem canonicalCompletedGreenFrameAnalysisCLM_injective :
    Function.Injective canonicalCompletedGreenFrameAnalysisCLM :=
  canonicalCompletedGreenFrameAnalysis_injective

/-! ## The canonical dslope jet in the split Green carrier -/

/-- Analyze the canonical completed-native forward-difference limit jet in
the same split Green-frame carrier as the BR2 incidence jet. -/
def canonicalCompletedNativeGreenFrameDslopeJet
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    (ℕ ⊕ ℕ) → CanonicalCompletedGreenFrameCarrier :=
  fun i ↦ canonicalCompletedGreenFrameAnalysisCLM
    (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
      state hkernel i)

/-- The analyzed finite forward-difference approximants converge to the
analyzed canonical dslope jet, component by component. -/
theorem canonicalCompletedGreenFrame_forwardDifference_tendsto_dslope
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (i : ℕ ⊕ ℕ) :
    Tendsto
      (fun k ↦ canonicalCompletedGreenFrameAnalysisCLM
        (completedGreenForwardDifferenceParityJet
          (normalizedCompletedGreenState
            completedNativeOperatorCharacteristic state) k i))
      atTop
      (nhds (canonicalCompletedNativeGreenFrameDslopeJet
        state hkernel i)) := by
  exact
    (canonicalCompletedGreenFrameAnalysisCLM.continuous.tendsto
      (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        state hkernel i)).comp
      (completedGreenForwardDifferenceParityJet_tendsto_canonicalNativeLimit
        state hkernel i)

/-! ## Exact vector identification criteria -/

/-- Green-frame analysis does not weaken the desired identification: equality
of the analyzed jets is equivalent to equality of the original Hilbert jets. -/
theorem canonicalCompletedNativeGreenFrameDslopeJet_eq_br2_iff
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (base radius : ℕ) :
    canonicalCompletedNativeGreenFrameDslopeJet state hkernel =
        br2CameraBracketGreenFrameParityJet base radius ↔
      canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
          state hkernel =
        br2CameraBracketProjectiveHilbertParityJet base radius := by
  constructor
  · intro h
    funext i
    apply canonicalCompletedGreenFrameAnalysisCLM_injective
    exact congrFun h i
  · intro h
    funext i
    exact congrArg canonicalCompletedGreenFrameAnalysisCLM (congrFun h i)

/-- For each parity/order component, the dslope--BR2 identification is exactly
the convergence of the analyzed finite approximants to that BR2 component. -/
theorem canonicalCompletedNativeGreenFrameDslopeJet_apply_eq_br2_iff_tendsto
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (base radius : ℕ)
    (i : ℕ ⊕ ℕ) :
    canonicalCompletedNativeGreenFrameDslopeJet state hkernel i =
        br2CameraBracketGreenFrameParityJet base radius i ↔
      Tendsto
        (fun k ↦ canonicalCompletedGreenFrameAnalysisCLM
          (completedGreenForwardDifferenceParityJet
            (normalizedCompletedGreenState
              completedNativeOperatorCharacteristic state) k i))
        atTop
        (nhds (br2CameraBracketGreenFrameParityJet base radius i)) := by
  constructor
  · intro h
    simpa [h] using
      canonicalCompletedGreenFrame_forwardDifference_tendsto_dslope
        state hkernel i
  · intro h
    exact tendsto_nhds_unique
      (canonicalCompletedGreenFrame_forwardDifference_tendsto_dslope
        state hkernel i) h

/-- Full all-order identification criterion in the common Green-frame
carrier.  This is the vector gate, with every split channel retained. -/
theorem canonicalCompletedNativeGreenFrameDslopeJet_eq_br2_iff_tendsto
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (base radius : ℕ) :
    canonicalCompletedNativeGreenFrameDslopeJet state hkernel =
        br2CameraBracketGreenFrameParityJet base radius ↔
      ∀ i : ℕ ⊕ ℕ,
        Tendsto
          (fun k ↦ canonicalCompletedGreenFrameAnalysisCLM
            (completedGreenForwardDifferenceParityJet
              (normalizedCompletedGreenState
                completedNativeOperatorCharacteristic state) k i))
          atTop
          (nhds (br2CameraBracketGreenFrameParityJet base radius i)) := by
  constructor
  · intro h i
    exact
      (canonicalCompletedNativeGreenFrameDslopeJet_apply_eq_br2_iff_tendsto
        state hkernel base radius i).mp (congrFun h i)
  · intro h
    funext i
    exact
      (canonicalCompletedNativeGreenFrameDslopeJet_apply_eq_br2_iff_tendsto
        state hkernel base radius i).mpr (h i)

/-- The same componentwise gate written as disappearance of the full vector
defect. -/
theorem canonicalCompletedNativeGreenFrameDslopeJet_apply_eq_br2_iff_defect_tendsto_zero
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (base radius : ℕ)
    (i : ℕ ⊕ ℕ) :
    canonicalCompletedNativeGreenFrameDslopeJet state hkernel i =
        br2CameraBracketGreenFrameParityJet base radius i ↔
      Tendsto
        (fun k ↦ canonicalCompletedGreenFrameAnalysisCLM
            (completedGreenForwardDifferenceParityJet
              (normalizedCompletedGreenState
                completedNativeOperatorCharacteristic state) k i) -
          br2CameraBracketGreenFrameParityJet base radius i)
        atTop (nhds 0) := by
  constructor
  · intro h
    have ht :=
      (canonicalCompletedGreenFrame_forwardDifference_tendsto_dslope
        state hkernel i).sub_const
        (br2CameraBracketGreenFrameParityJet base radius i)
    simpa [h] using ht
  · intro h
    have ht :=
      (canonicalCompletedGreenFrame_forwardDifference_tendsto_dslope
        state hkernel i).sub_const
        (br2CameraBracketGreenFrameParityJet base radius i)
    have hz := tendsto_nhds_unique ht h
    exact sub_eq_zero.mp hz

/-- All-order equality is equivalent to disappearance of the complete
Green-frame vector defect in every parity/order component. -/
theorem canonicalCompletedNativeGreenFrameDslopeJet_eq_br2_iff_defect_tendsto_zero
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (base radius : ℕ) :
    canonicalCompletedNativeGreenFrameDslopeJet state hkernel =
        br2CameraBracketGreenFrameParityJet base radius ↔
      ∀ i : ℕ ⊕ ℕ,
        Tendsto
          (fun k ↦ canonicalCompletedGreenFrameAnalysisCLM
              (completedGreenForwardDifferenceParityJet
                (normalizedCompletedGreenState
                  completedNativeOperatorCharacteristic state) k i) -
            br2CameraBracketGreenFrameParityJet base radius i)
          atTop (nhds 0) := by
  constructor
  · intro h i
    exact
      (canonicalCompletedNativeGreenFrameDslopeJet_apply_eq_br2_iff_defect_tendsto_zero
        state hkernel base radius i).mp (congrFun h i)
  · intro h
    funext i
    exact
      (canonicalCompletedNativeGreenFrameDslopeJet_apply_eq_br2_iff_defect_tendsto_zero
        state hkernel base radius i).mpr (h i)

/-! ## Direct handoff to the real HP carrier -/

/-- Vanishing of the analyzed vector defect constructs the canonical real
TFVD/Green moment transport on the actual dslope limit jet. -/
def canonicalCompletedNativeRealTfvdGreenMomentTransport_of_greenFrameDefect
    {base radius : ℕ}
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (hdefect : ∀ i : ℕ ⊕ ℕ,
      Tendsto
        (fun k ↦ canonicalCompletedGreenFrameAnalysisCLM
            (completedGreenForwardDifferenceParityJet
              (normalizedCompletedGreenState
                completedNativeOperatorCharacteristic state) k i) -
          br2CameraBracketGreenFrameParityJet base radius i)
        atTop (nhds 0)) :
    CanonicalCompletedNativeRealTfvdGreenMomentTransport base radius := by
  apply
    canonicalCompletedNativeRealTfvdGreenMomentTransport_of_vectorLimit_eq_projective
      state hkernel hasCompletedNativeGreenKernelTwoStepLimit
  exact
    (canonicalCompletedNativeGreenFrameDslopeJet_eq_br2_iff state hkernel
      base radius).mp
      ((canonicalCompletedNativeGreenFrameDslopeJet_eq_br2_iff_defect_tendsto_zero
        state hkernel base radius).mpr hdefect)

/-- The same vector no-defect statement, together with the already proved
BR2 support facts, fills the carrier-correct HP certificate. -/
theorem completedNativeRealHPCarrierCertificate_of_greenFrameDefect
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (hdefect : ∀ i : ℕ ⊕ ℕ,
      Tendsto
        (fun k ↦ canonicalCompletedGreenFrameAnalysisCLM
            (completedGreenForwardDifferenceParityJet
              (normalizedCompletedGreenState
                completedNativeOperatorCharacteristic state) k i) -
          br2CameraBracketGreenFrameParityJet base radius i)
        atTop (nhds 0)) :
    @CompletedNativeRealHPCarrierCertificate
      CanonicalCompletedTfvdGreenHilbertCarrier (by infer_instance)
      canonicalCompletedTfvdGreenRealInnerProductSpace
      (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        state hkernel) := by
  let transport :=
    canonicalCompletedNativeRealTfvdGreenMomentTransport_of_greenFrameDefect
      state hkernel hdefect
  simpa [transport,
    canonicalCompletedNativeRealTfvdGreenMomentTransport_of_greenFrameDefect,
    canonicalCompletedNativeRealTfvdGreenMomentTransport_of_vectorLimit_eq_projective,
    canonicalCompletedNativeRealTfvdGreenMomentTransport_of_vectorLimit,
    canonicalCompletedNativeGreenForwardDifferenceLimitParityJet] using
    (completedNativeRealHPCarrierCertificate_of_tfvdGreenMomentTransport
      hbase hradius transport)

end

end CarrySelfAdjointOperator
