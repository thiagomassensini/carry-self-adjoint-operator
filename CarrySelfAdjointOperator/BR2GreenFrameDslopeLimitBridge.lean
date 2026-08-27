import CarrySelfAdjointOperator.BR2GreenFrameIncidenceTransport
import CarrySelfAdjointOperator.CompletedGreenForwardDifferenceVectorLimit
import CarrySelfAdjointOperator.CompletedNativeHPGateAudit
import GreenFrame.Concrete.Analysis.CanonicalParseval
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
open FiniteNativeCarryOperator.Camera
open GreenFrame.Concrete
open NativeCarrySpectralWeyl.Camera
open scoped ComplexOrder

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

/-! ## Canonical Parseval realization of the completed Green kernel -/

/-- Canonical isometric all-bases analysis of the completed TFVD carrier.
The inverse square root of the concrete frame operator is applied at source
level, before the four Green-frame coordinates are read. -/
def canonicalCompletedGreenFrameParsevalAnalysis :
    CarryVerticalL2 →ₗᵢ[ℂ] CanonicalCompletedGreenFrameCarrier :=
  (canonicalParseval
      (concreteSplitFrameBounds
        canonicalCarryInfinitePartition).toComplexFrameBounds).comp
    carryVerticalL2GreenFrameStateEquiv.toLinearIsometry

/-- Parseval transport preserves the complete complex inner product, not
only the norm or a final real scalar readout. -/
theorem canonicalCompletedGreenFrameParsevalAnalysis_inner
    (x y : CarryVerticalL2) :
    inner ℂ
        (canonicalCompletedGreenFrameParsevalAnalysis x)
        (canonicalCompletedGreenFrameParsevalAnalysis y) =
      inner ℂ x y := by
  exact canonicalCompletedGreenFrameParsevalAnalysis.inner_map_map x y

/-- The normalized completed-native state transported into the concrete
all-bases Green-frame carrier.  Its seed, residual, depth-one, and bulk
coordinates remain literal orthogonal coordinates of the target. -/
def canonicalCompletedNativeParsevalGreenFrameState
    (state : ℂ → CarryVerticalL2) (z : ℂ) :
    CanonicalCompletedGreenFrameCarrier :=
  canonicalCompletedGreenFrameParsevalAnalysis
    (normalizedCompletedGreenState
      completedNativeOperatorCharacteristic state z)

/-- The total completed-native `dslope` is the positive Hilbert product of
the transported states in the same all-bases Green-frame carrier. -/
theorem canonicalCompletedNativeParsevalGreenFrameState_inner_eq_dslope
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (x z : ℝ)
    (hxF : completedNativeOperatorCharacteristic (x : ℂ) ≠ 0)
    (hzF : completedNativeOperatorCharacteristic (z : ℂ) ≠ 0) :
    inner ℂ
        (canonicalCompletedNativeParsevalGreenFrameState state (x : ℂ))
        (canonicalCompletedNativeParsevalGreenFrameState state (z : ℂ)) =
      dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) (x : ℂ) (z : ℂ) := by
  rw [canonicalCompletedNativeParsevalGreenFrameState,
    canonicalCompletedNativeParsevalGreenFrameState,
    canonicalCompletedGreenFrameParsevalAnalysis_inner]
  exact hkernel x z hxF hzF

/-- Orthogonal expansion of the transported product into the four concrete
all-bases Green-frame channels.  No coordinate is added in `ℂ` before this
identity is formed. -/
theorem canonicalCompletedNativeParsevalGreenFrameState_inner_eq_channelSum
    (state : ℂ → CarryVerticalL2) (z w : ℂ) :
    let stateZ := canonicalCompletedNativeParsevalGreenFrameState state z
    let stateW := canonicalCompletedNativeParsevalGreenFrameState state w
    inner ℂ stateZ stateW =
      inner ℂ stateZ.fst.fst.fst stateW.fst.fst.fst +
        inner ℂ stateZ.fst.fst.snd stateW.fst.fst.snd +
        inner ℂ stateZ.fst.snd stateW.fst.snd +
        inner ℂ stateZ.snd stateW.snd := by
  dsimp only
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply,
    WithLp.prod_inner_apply]
  rfl

/-- Channel-separated form of the exact positive `dslope` realization.
The four summands are respectively seed, residual, depth-one Green, and bulk
Green. -/
theorem canonicalCompletedNativeParsevalGreenFrame_dslope_eq_channelSum
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (x z : ℝ)
    (hxF : completedNativeOperatorCharacteristic (x : ℂ) ≠ 0)
    (hzF : completedNativeOperatorCharacteristic (z : ℂ) ≠ 0) :
    let stateX :=
      canonicalCompletedNativeParsevalGreenFrameState state (x : ℂ)
    let stateZ :=
      canonicalCompletedNativeParsevalGreenFrameState state (z : ℂ)
    dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) (x : ℂ) (z : ℂ) =
      inner ℂ stateX.fst.fst.fst stateZ.fst.fst.fst +
        inner ℂ stateX.fst.fst.snd stateZ.fst.fst.snd +
        inner ℂ stateX.fst.snd stateZ.fst.snd +
        inner ℂ stateX.snd stateZ.snd := by
  dsimp only
  rw [← canonicalCompletedNativeParsevalGreenFrameState_inner_eq_channelSum]
  exact (canonicalCompletedNativeParsevalGreenFrameState_inner_eq_dslope
    state hkernel x z hxF hzF).symm

/-- Every finite real-axis section of the completed `dslope` kernel is
positive semidefinite because all entries are products of the same Parseval
Green-frame states. -/
theorem canonicalCompletedNativeDslopeKernel_posSemidef_of_greenState
    {ι : Type*} [Finite ι]
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (point : ι → ℝ)
    (hF : ∀ i, completedNativeOperatorCharacteristic (point i : ℂ) ≠ 0) :
    (Matrix.of fun i j ↦
      dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion)
        (point i : ℂ) (point j : ℂ)).PosSemidef := by
  rw [show
      Matrix.of (fun i j ↦
        dslope
          (completedGreenNormalizedResponse
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion)
          (point i : ℂ) (point j : ℂ)) =
        Matrix.gram ℂ (fun i ↦
          canonicalCompletedNativeParsevalGreenFrameState
            state (point i : ℂ)) by
    ext i j
    exact
      (canonicalCompletedNativeParsevalGreenFrameState_inner_eq_dslope
        state hkernel (point i) (point j) (hF i) (hF j)).symm]
  exact Matrix.posSemidef_gram ℂ _

/-! ## Order-zero anchoring and phase audit -/

/-- The zeroth even forward-difference component is the centered state itself;
there is no limiting operation in this component. -/
@[simp] theorem completedGreenForwardDifferenceParityJet_inl_zero
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (state : ℂ → E) (k : ℕ) :
    completedGreenForwardDifferenceParityJet state k (Sum.inl 0) =
      state 0 := by
  simp [completedGreenForwardDifferenceParityJet,
    completedGreenForwardDifferenceJet]

/-- A global sign change of a state realization does not change its normalized
real-axis Green kernel. -/
theorem HasCompletedNativeRealAxisNormalizedGreenKernel.neg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {state : ℂ → E}
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    HasCompletedNativeRealAxisNormalizedGreenKernel
      (fun z ↦ -state z) := by
  intro x z hx hz
  rw [show normalizedCompletedGreenState
        completedNativeOperatorCharacteristic (fun u ↦ -state u) (x : ℂ) =
      -normalizedCompletedGreenState
        completedNativeOperatorCharacteristic state (x : ℂ) by
    simp [normalizedCompletedGreenState],
    show normalizedCompletedGreenState
        completedNativeOperatorCharacteristic (fun u ↦ -state u) (z : ℂ) =
      -normalizedCompletedGreenState
        completedNativeOperatorCharacteristic state (z : ℂ) by
      simp [normalizedCompletedGreenState],
    inner_neg_neg]
  exact hkernel x z hx hz

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

/-- The selected dslope limit has the expected exact zeroth component. -/
theorem canonicalCompletedNativeGreenFrameDslopeJet_inl_zero
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    canonicalCompletedNativeGreenFrameDslopeJet state hkernel (Sum.inl 0) =
      canonicalCompletedGreenFrameAnalysisCLM
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic state 0) := by
  apply congrArg canonicalCompletedGreenFrameAnalysisCLM
  have hlimit :=
    completedGreenForwardDifferenceParityJet_tendsto_canonicalNativeLimit
      state hkernel (Sum.inl 0)
  have hconstant :
      Tendsto
        (fun k ↦ completedGreenForwardDifferenceParityJet
          (normalizedCompletedGreenState
            completedNativeOperatorCharacteristic state) k (Sum.inl 0))
        atTop
        (nhds (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic state 0)) := by
    simpa only [completedGreenForwardDifferenceParityJet_inl_zero] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ ↦ normalizedCompletedGreenState
          completedNativeOperatorCharacteristic state 0)
        atTop
        (nhds (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic state 0)))
  exact tendsto_nhds_unique hlimit hconstant

/-- The zeroth BR2 Green-frame component is nonzero in every supported
camera/radius pair. -/
theorem br2CameraBracketGreenFrameParityJet_inl_zero_ne_zero
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    br2CameraBracketGreenFrameParityJet base radius (Sum.inl 0) ≠ 0 := by
  intro hzero
  have hstate : br2CameraBracketVerticalState base radius 0 = 0 := by
    apply canonicalCompletedGreenFrameAnalysis_injective
    simpa [br2CameraBracketGreenFrameParityJet,
      br2CameraBracketProjectiveHilbertParityJet] using hzero
  have hcoordinate := congrArg
    (fun x : CarryVerticalL2 ↦ x (alignedCenter base 0)) hstate
  rw [br2CameraBracketVerticalState_apply_alignedCenter
    hbase hradius 0 0] at hcoordinate
  simp at hcoordinate

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

/-- At order zero the vector convergence gate is exactly an anchoring
identity.  Completion and cutoff estimates cannot alter this component. -/
theorem canonicalCompletedNativeGreenFrame_evenZero_defect_tendsto_zero_iff_anchor
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (base radius : ℕ) :
    Tendsto
        (fun k ↦ canonicalCompletedGreenFrameAnalysisCLM
            (completedGreenForwardDifferenceParityJet
              (normalizedCompletedGreenState
                completedNativeOperatorCharacteristic state) k (Sum.inl 0)) -
          br2CameraBracketGreenFrameParityJet base radius (Sum.inl 0))
        atTop (nhds 0) ↔
      normalizedCompletedGreenState
          completedNativeOperatorCharacteristic state 0 =
        br2CameraBracketVerticalState base radius 0 := by
  rw [←
    canonicalCompletedNativeGreenFrameDslopeJet_apply_eq_br2_iff_defect_tendsto_zero
      state hkernel base radius (Sum.inl 0)]
  rw [canonicalCompletedNativeGreenFrameDslopeJet_inl_zero]
  constructor
  · intro h
    apply canonicalCompletedGreenFrameAnalysisCLM_injective
    simpa [br2CameraBracketGreenFrameParityJet,
      br2CameraBracketProjectiveHilbertParityJet] using h
  · intro h
    exact congrArg canonicalCompletedGreenFrameAnalysisCLM
      (by simpa [br2CameraBracketProjectiveHilbertParityJet] using h)

/-- Named form of the full vector convergence gate. -/
def HasCanonicalCompletedNativeGreenFrameDslopeBR2DefectLimit
    (state : ℂ → CarryVerticalL2) (base radius : ℕ) : Prop :=
  ∀ i : ℕ ⊕ ℕ,
    Tendsto
      (fun k ↦ canonicalCompletedGreenFrameAnalysisCLM
          (completedGreenForwardDifferenceParityJet
            (normalizedCompletedGreenState
              completedNativeOperatorCharacteristic state) k i) -
        br2CameraBracketGreenFrameParityJet base radius i)
      atTop (nhds 0)

/-- A state and its global negative cannot both converge to the same nonzero
BR2 jet.  This is the exact phase obstruction hidden by scalar kernel data. -/
theorem not_both_greenFrameDslopeBR2DefectLimit_state_neg
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    ¬(HasCanonicalCompletedNativeGreenFrameDslopeBR2DefectLimit
          state base radius ∧
      HasCanonicalCompletedNativeGreenFrameDslopeBR2DefectLimit
          (fun z ↦ -state z) base radius) := by
  rintro ⟨hstate, hnegState⟩
  have hanchor :=
    (canonicalCompletedNativeGreenFrame_evenZero_defect_tendsto_zero_iff_anchor
      state hkernel base radius).mp (hstate (Sum.inl 0))
  have hnegAnchor :=
    (canonicalCompletedNativeGreenFrame_evenZero_defect_tendsto_zero_iff_anchor
      (fun z ↦ -state z) hkernel.neg base radius).mp
      (hnegState (Sum.inl 0))
  have hneg :
      -br2CameraBracketVerticalState base radius 0 =
        br2CameraBracketVerticalState base radius 0 := by
    calc
      -br2CameraBracketVerticalState base radius 0 =
          -normalizedCompletedGreenState
            completedNativeOperatorCharacteristic state 0 :=
        congrArg Neg.neg hanchor.symm
      _ = normalizedCompletedGreenState
          completedNativeOperatorCharacteristic (fun z ↦ -state z) 0 := by
        simp [normalizedCompletedGreenState]
      _ = br2CameraBracketVerticalState base radius 0 := hnegAnchor
  have hadd :
      br2CameraBracketVerticalState base radius 0 +
          br2CameraBracketVerticalState base radius 0 = 0 :=
    neg_eq_iff_add_eq_zero.mp hneg
  have hzero : br2CameraBracketVerticalState base radius 0 = 0 := by
    have htwo :
        (2 : ℂ) • br2CameraBracketVerticalState base radius 0 = 0 := by
      simpa [two_smul ℂ] using hadd
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  apply br2CameraBracketGreenFrameParityJet_inl_zero_ne_zero hbase hradius
  simp [br2CameraBracketGreenFrameParityJet,
    br2CameraBracketProjectiveHilbertParityJet, hzero]

/-- Consequently the normalized scalar kernel interface alone cannot prove
the raw BR2-coordinate convergence for every realization of that kernel. -/
theorem not_forall_greenFrameDslopeBR2DefectLimit_of_kernel
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    ¬(∀ candidate : ℂ → CarryVerticalL2,
      HasCompletedNativeRealAxisNormalizedGreenKernel candidate →
      HasCanonicalCompletedNativeGreenFrameDslopeBR2DefectLimit
        candidate base radius) := by
  intro hall
  exact not_both_greenFrameDslopeBR2DefectLimit_state_neg
    hbase hradius state hkernel
      ⟨hall state hkernel, hall (fun z ↦ -state z) hkernel.neg⟩

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
