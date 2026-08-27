import CarrySelfAdjointOperator.CompletedC3GreenFrameOrientedCarrier
import CarrySelfAdjointOperator.CompletedC3FinalReadoutKernelBridge
import Mathlib.Tactic

/-!
# Structural readout recovered from the oriented C3 Green-frame carrier

The raw concrete Green-frame analysis has a canonical bounded synthesis.  It
is obtained from the adjoint of the Parseval-normalized analysis and the
inverse square root of the frame operator.  This file uses that synthesis to
recover the ordered ordinary/log-jet source from its analyzed coefficients.

Three copies retain the sources at `z`, `w`, and the reflected parameter of
`z`, together with each precompression residual.  The structural readout of
this oriented carrier is proved equal, coordinate by coordinate, to the
existing provenance/off-diagonal/readout-residual state.  No scalar kernel,
zero specialization, or positivity assumption is used in the reconstruction.
-/

open scoped InnerProduct InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter
open GreenFrame.Concrete

noncomputable section

private abbrev canonicalGreenFrameRawOperator :
    State →L[ℂ] CanonicalCompletedGreenFrameCarrier :=
  concreteAnalysisOperator canonicalCarryInfinitePartition

private abbrev canonicalGreenFrameBounds :
    ComplexFrameBounds canonicalGreenFrameRawOperator :=
  (concreteSplitFrameBounds canonicalCarryInfinitePartition).toComplexFrameBounds

/-! ## Canonical bounded synthesis -/

/-- The frame operator as a unit of the Banach algebra of continuous
endomorphisms. -/
private noncomputable def canonicalGreenFrameOperatorUnit :
    (State →L[ℂ] State)ˣ :=
  (frameOperator_isUnit canonicalGreenFrameBounds).unit

/-- Canonical bounded inverse of the concrete frame operator. -/
private noncomputable def canonicalGreenFrameOperatorInverse :
    State →L[ℂ] State :=
  ↑canonicalGreenFrameOperatorUnit.inv

/-- Bounded synthesis for the raw concrete Green-frame coefficients. -/
def canonicalGreenFrameRawSynthesis :
    CanonicalCompletedGreenFrameCarrier →L[ℂ] State :=
  canonicalGreenFrameOperatorInverse.comp ((canonicalGreenFrameRawOperator)†)

/-- The bounded synthesis is a left inverse of the concrete raw analysis. -/
@[simp] theorem canonicalGreenFrameRawSynthesis_analysis
    (x : State) :
    canonicalGreenFrameRawSynthesis (canonicalGreenFrameRawOperator x) = x := by
  have hunit :
      (↑canonicalGreenFrameOperatorUnit.inv : State →L[ℂ] State) ∘L
          (↑canonicalGreenFrameOperatorUnit : State →L[ℂ] State) = 1 := by
    simpa only [ContinuousLinearMap.mul_def] using
      canonicalGreenFrameOperatorUnit.inv_val
  have hoperator :
      (↑canonicalGreenFrameOperatorUnit : State →L[ℂ] State) =
        frameOperator canonicalGreenFrameRawOperator :=
    (frameOperator_isUnit canonicalGreenFrameBounds).unit_spec
  have happ := congrArg (fun A : State →L[ℂ] State => A x) hunit
  unfold canonicalGreenFrameRawSynthesis
  change canonicalGreenFrameOperatorInverse
      (frameOperator canonicalGreenFrameRawOperator x) = x
  simpa [canonicalGreenFrameOperatorInverse, hoperator] using happ

/-- Reindex the synthesized concrete state back to the completed TFVD
carrier. -/
def canonicalCompletedGreenFrameSynthesis :
    CanonicalCompletedGreenFrameCarrier →L[ℂ] CarryVerticalL2 :=
  carryVerticalL2GreenFrameStateEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    canonicalGreenFrameRawSynthesis

/-- The completed synthesis recovers every completed TFVD state exactly. -/
@[simp] theorem canonicalCompletedGreenFrameSynthesis_analysis
    (x : CarryVerticalL2) :
    canonicalCompletedGreenFrameSynthesis
        (canonicalCompletedGreenFrameAnalysisCLM x) = x := by
  change carryVerticalL2GreenFrameStateEquiv.symm
      (canonicalGreenFrameRawSynthesis
        (canonicalGreenFrameRawOperator
          (carryVerticalL2GreenFrameStateEquiv x))) = x
  rw [canonicalGreenFrameRawSynthesis_analysis]
  exact carryVerticalL2GreenFrameStateEquiv.symm_apply_apply x

/-- Synthesize the ordinary and logarithmic coordinates independently. -/
def canonicalCompletedC3GreenFramePairSynthesis :
    (CanonicalCompletedGreenFrameCarrier ×
      CanonicalCompletedGreenFrameCarrier) →L[ℂ]
      CanonicalCompletedC3HilbertState :=
  canonicalCompletedGreenFrameSynthesis.prodMap
    canonicalCompletedGreenFrameSynthesis

/-- The pair synthesis is a left inverse of the oriented pair intertwiner. -/
@[simp] theorem canonicalCompletedC3GreenFramePairSynthesis_intertwiner
    (state : CanonicalCompletedC3HilbertState) :
    canonicalCompletedC3GreenFramePairSynthesis
        (canonicalCompletedC3GreenFramePairIntertwiner state) = state := by
  change
    (canonicalCompletedGreenFrameSynthesis
        (canonicalCompletedGreenFrameAnalysisCLM state.1),
      canonicalCompletedGreenFrameSynthesis
        (canonicalCompletedGreenFrameAnalysisCLM state.2)) = state
  rw [canonicalCompletedGreenFrameSynthesis_analysis,
    canonicalCompletedGreenFrameSynthesis_analysis]

/-! ## Three-source oriented carrier -/

/-- Three oriented Green-frame states at `z`, `w`, and the reflected
parameter of `z`.  Every state still contains its precompression residual. -/
abbrev CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert :=
  WithLp 2
    (CanonicalCompletedC3OrientedGreenFrameCarrier ×
      WithLp 2
        (CanonicalCompletedC3OrientedGreenFrameCarrier ×
          CanonicalCompletedC3OrientedGreenFrameCarrier))

namespace CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert

def zState
    (state : CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert) :
    CanonicalCompletedC3OrientedGreenFrameCarrier :=
  state.fst

def wState
    (state : CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert) :
    CanonicalCompletedC3OrientedGreenFrameCarrier :=
  state.snd.fst

def reflectedZState
    (state : CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert) :
    CanonicalCompletedC3OrientedGreenFrameCarrier :=
  state.snd.snd

/-- Recover the three ordinary/log-jet Hilbert sources from the analyzed
Green-frame coordinates.  The residual coordinates remain present in the
domain and are not identified with either source channel. -/
def recoveredHilbertSource
    (state : CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert) :
    CanonicalC3AllCutoffMixedSourceHilbert :=
  WithLp.toLp 2
    (canonicalCompletedC3GreenFramePairSynthesis state.zState.1,
      WithLp.toLp 2
        (canonicalCompletedC3GreenFramePairSynthesis state.wState.1,
          canonicalCompletedC3GreenFramePairSynthesis
            state.reflectedZState.1))

/-- Structural readout after bounded synthesis of all three oriented
ordinary/log-jet sources. -/
def structuralReadout
    (M : ℕ) (directParameter reflectedParameter : ℂ)
    (state : CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert) :
    CanonicalC3MixedStructuralChannelHilbert :=
  CanonicalC3AllCutoffMixedSourceHilbert.structuralReadout
    M directParameter reflectedParameter state.recoveredHilbertSource

/-- Pythagorean audit of the three oriented sources.  In particular, the
three precompression residuals are still coordinates of the norm identity. -/
theorem norm_sq_eq_source_sum
    (state : CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert) :
    ‖state‖ ^ 2 =
      ‖state.zState‖ ^ 2 +
        ‖state.wState‖ ^ 2 + ‖state.reflectedZState‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2 state,
    WithLp.prod_norm_sq_eq_of_L2 state.snd]
  unfold zState wState reflectedZState
  ring

end CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert

/-- The concrete three-source cutoff carrier, including all three retained
precompression residuals. -/
def canonicalC3AllCutoffMixedOrientedGreenFramePrefixState
    (M : ℕ) (z w : ℂ) :
    CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert :=
  WithLp.toLp 2
    (canonicalCompletedC3OrientedGreenFramePrefixState M z,
      WithLp.toLp 2
        (canonicalCompletedC3OrientedGreenFramePrefixState M w,
          canonicalCompletedC3OrientedGreenFramePrefixState M
            (reflectedParameter z)))

@[simp] theorem
    canonicalC3AllCutoffMixedOrientedGreenFramePrefixState_zState
    (M : ℕ) (z w : ℂ) :
    (canonicalC3AllCutoffMixedOrientedGreenFramePrefixState M z w).zState =
      canonicalCompletedC3OrientedGreenFramePrefixState M z :=
  rfl

@[simp] theorem
    canonicalC3AllCutoffMixedOrientedGreenFramePrefixState_wState
    (M : ℕ) (z w : ℂ) :
    (canonicalC3AllCutoffMixedOrientedGreenFramePrefixState M z w).wState =
      canonicalCompletedC3OrientedGreenFramePrefixState M w :=
  rfl

@[simp] theorem
    canonicalC3AllCutoffMixedOrientedGreenFramePrefixState_reflectedZState
    (M : ℕ) (z w : ℂ) :
    (canonicalC3AllCutoffMixedOrientedGreenFramePrefixState M z w).reflectedZState =
      canonicalCompletedC3OrientedGreenFramePrefixState M
        (reflectedParameter z) :=
  rfl

/-- Bounded synthesis of the three analyzed cutoff sources recovers exactly
the pre-existing all-cutoff Hilbert source. -/
theorem
    canonicalC3AllCutoffMixedOrientedGreenFramePrefixState_recoveredHilbertSource_eq
    (M : ℕ) (z w : ℂ) :
    (canonicalC3AllCutoffMixedOrientedGreenFramePrefixState M z w).recoveredHilbertSource =
      canonicalC3AllCutoffMixedSourcePrefixState M z w := by
  unfold
    CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert.recoveredHilbertSource
    CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert.zState
    CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert.wState
    CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert.reflectedZState
    canonicalC3AllCutoffMixedOrientedGreenFramePrefixState
    canonicalC3AllCutoffMixedSourcePrefixState
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · change canonicalCompletedC3GreenFramePairSynthesis
        (canonicalCompletedC3OrientedGreenFramePrefixState M z).1 =
      canonicalCompletedC3HilbertPrefixState z (3 * M)
    rw [canonicalCompletedC3OrientedGreenFramePrefixState_fst,
      canonicalCompletedC3GreenFramePairSynthesis_intertwiner]
  · apply congrArg (WithLp.toLp 2)
    apply Prod.ext
    · change canonicalCompletedC3GreenFramePairSynthesis
          (canonicalCompletedC3OrientedGreenFramePrefixState M w).1 =
        canonicalCompletedC3HilbertPrefixState w (3 * M)
      rw [canonicalCompletedC3OrientedGreenFramePrefixState_fst,
        canonicalCompletedC3GreenFramePairSynthesis_intertwiner]
    · change canonicalCompletedC3GreenFramePairSynthesis
          (canonicalCompletedC3OrientedGreenFramePrefixState M
            (reflectedParameter z)).1 =
        canonicalCompletedC3HilbertPrefixState
          (reflectedParameter z) (3 * M)
      rw [canonicalCompletedC3OrientedGreenFramePrefixState_fst,
        canonicalCompletedC3GreenFramePairSynthesis_intertwiner]

/-- Vector-level structural sewing: bounded readout of the three-source
oriented Green-frame carrier is exactly the finite structural state. -/
theorem
    canonicalC3AllCutoffMixedOrientedGreenFramePrefixState_structuralReadout_eq
    (M : ℕ) (z w : ℂ) :
    CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert.structuralReadout
        M w (reflectedParameter z)
        (canonicalC3AllCutoffMixedOrientedGreenFramePrefixState M z w) =
      canonicalC3FiniteMixedHeightStructuralChannelState M z w := by
  rw [CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert.structuralReadout,
    canonicalC3AllCutoffMixedOrientedGreenFramePrefixState_recoveredHilbertSource_eq,
    canonicalC3AllCutoffMixedSourcePrefixState_structuralReadout_eq]

/-! ## Exact insertion into the completed kernel ledger -/

/-- Structural state read from the oriented Green-frame sources at the two
real-axis kernel parameters. -/
def canonicalCompletedC3AllCutoffOrientedStructuralState
    (M : ℕ) (z w : ℂ) : CanonicalC3MixedStructuralChannelHilbert :=
  CanonicalC3AllCutoffMixedOrientedGreenFrameSourceHilbert.structuralReadout
    M (operatorHeightParameter w)
      (reflectedParameter (operatorHeightParameter z))
    (canonicalC3AllCutoffMixedOrientedGreenFramePrefixState M
      (operatorHeightParameter z) (operatorHeightParameter w))

/-- The oriented-source readout is exactly the structural coordinate already
stored by the enriched kernel ledger. -/
theorem canonicalCompletedC3AllCutoffOrientedStructuralState_eq_ledger
    (M : ℕ) (z w : ℂ) :
    canonicalCompletedC3AllCutoffOrientedStructuralState M z w =
      (canonicalCompletedC3AllCutoffKernelLedgerState M z w).structural := by
  rw [canonicalCompletedC3AllCutoffOrientedStructuralState,
    canonicalC3AllCutoffMixedOrientedGreenFramePrefixState_structuralReadout_eq,
    canonicalCompletedC3AllCutoffKernelLedgerState_structural]

/-- Green provenance is recovered as the first vector coordinate. -/
theorem canonicalCompletedC3AllCutoffOrientedStructuralState_greenProvenance
    (M : ℕ) (z w : ℂ) :
    (canonicalCompletedC3AllCutoffOrientedStructuralState M z w).fst =
      canonicalC3FiniteMixedHeightGreenProvenanceChannel M
        (operatorHeightParameter z) (operatorHeightParameter w) := by
  rw [canonicalCompletedC3AllCutoffOrientedStructuralState_eq_ledger]
  exact
    canonicalCompletedC3AllCutoffKernelLedgerState_greenProvenanceCoordinate
      M z w

/-- The off-diagonal channel is recovered independently as the second vector
coordinate. -/
theorem canonicalCompletedC3AllCutoffOrientedStructuralState_offDiagonal
    (M : ℕ) (z w : ℂ) :
    (canonicalCompletedC3AllCutoffOrientedStructuralState M z w).snd.fst =
      canonicalC3FiniteMixedHeightOffDiagonalChannel M
        (operatorHeightParameter z) (operatorHeightParameter w) := by
  rw [canonicalCompletedC3AllCutoffOrientedStructuralState_eq_ledger]
  exact
    canonicalCompletedC3AllCutoffKernelLedgerState_offDiagonalCoordinate
      M z w

/-- The scalar-synthesis residual is recovered independently as the third
vector coordinate. -/
theorem canonicalCompletedC3AllCutoffOrientedStructuralState_readoutResidual
    (M : ℕ) (z w : ℂ) :
    (canonicalCompletedC3AllCutoffOrientedStructuralState M z w).snd.snd =
      canonicalC3FiniteMixedHeightReadoutResidualChannel M
        (operatorHeightParameter z) (operatorHeightParameter w) := by
  rw [canonicalCompletedC3AllCutoffOrientedStructuralState_eq_ledger]
  exact
    canonicalCompletedC3AllCutoffKernelLedgerState_readoutResidualCoordinate
      M z w

/-- Final mixed readout with the structural coordinate supplied by the
oriented Green-frame source.  Radial Naimark, tail, xi, and archimedean
coordinates remain the independently retained coordinates of the ledger. -/
def canonicalCompletedC3AllCutoffOrientedFinalReadout
    (M : ℕ) (z w : ℂ) : ℂ :=
  let ledger := canonicalCompletedC3AllCutoffKernelLedgerState M z w
  ledger.xiWeight *
      (ledger.radialComplexReadout +
        canonicalC3MixedStructuralScalarReadout
          (canonicalCompletedC3AllCutoffOrientedStructuralState M z w) +
        ledger.tail) +
    ledger.archimedeanChart

/-- Replacing the structural coordinate by its oriented-source readout does
not change the completed final readout. -/
theorem canonicalCompletedC3AllCutoffOrientedFinalReadout_eq_ledger
    (M : ℕ) (z w : ℂ) :
    canonicalCompletedC3AllCutoffOrientedFinalReadout M z w =
      (canonicalCompletedC3AllCutoffKernelLedgerState M z w).finalReadout := by
  rw [canonicalCompletedC3AllCutoffOrientedFinalReadout,
    CanonicalCompletedC3AllCutoffKernelLedgerHilbert.finalReadout,
    CanonicalCompletedC3AllCutoffKernelLedgerHilbert.rawReadout,
    canonicalCompletedC3AllCutoffOrientedStructuralState_eq_ledger]

/-- Off-diagonal normalization of the oriented final readout. -/
def canonicalCompletedC3AllCutoffOrientedOffDiagonalKernelReadout
    (M : ℕ) (x z : ℂ) : ℂ :=
  canonicalCompletedC3AllCutoffOrientedFinalReadout M z x /
    (mixedHermitianWeight canonicalC3ChartFactorHeight z x *
      ((2 : ℂ) *
        (starRingEnd ℂ) (completedNativeOperatorCharacteristic x) *
        completedNativeOperatorCharacteristic z) *
      (z - (starRingEnd ℂ) x))

/-- The oriented off-diagonal readout is the previously proved canonical
all-cutoff readout. -/
theorem
    canonicalCompletedC3AllCutoffOrientedOffDiagonalKernelReadout_eq_ledger
    (M : ℕ) (x z : ℂ) :
    canonicalCompletedC3AllCutoffOrientedOffDiagonalKernelReadout M x z =
      canonicalCompletedC3AllCutoffOffDiagonalKernelReadout M x z := by
  rw [canonicalCompletedC3AllCutoffOrientedOffDiagonalKernelReadout,
    canonicalCompletedC3AllCutoffOffDiagonalKernelReadout,
    canonicalCompletedC3AllCutoffOrientedFinalReadout_eq_ledger]

/-- Canonical removable closure of the oriented readout on the real axis. -/
def canonicalCompletedC3AllCutoffOrientedRealKernelReadout
    (M : ℕ) (x z : ℝ) : ℂ :=
  if x = z then
    deriv
      (completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion) (x : ℂ)
  else
    canonicalCompletedC3AllCutoffOrientedOffDiagonalKernelReadout
      M (x : ℂ) (z : ℂ)

/-- The oriented real-axis readout agrees with the existing all-cutoff
readout before any use of the `dslope` theorem. -/
theorem canonicalCompletedC3AllCutoffOrientedRealKernelReadout_eq_ledger
    (M : ℕ) (x z : ℝ) :
    canonicalCompletedC3AllCutoffOrientedRealKernelReadout M x z =
      canonicalCompletedC3AllCutoffRealKernelReadout M x z := by
  by_cases hxz : x = z
  · simp [canonicalCompletedC3AllCutoffOrientedRealKernelReadout,
      canonicalCompletedC3AllCutoffRealKernelReadout, hxz]
  · simp [canonicalCompletedC3AllCutoffOrientedRealKernelReadout,
      canonicalCompletedC3AllCutoffRealKernelReadout, hxz,
      canonicalCompletedC3AllCutoffOrientedOffDiagonalKernelReadout_eq_ledger]

/-- Final scalar identification: the mixed readout of the oriented
Green-frame source is exactly the completed `dslope` kernel. -/
theorem canonicalCompletedC3AllCutoffOrientedRealKernelReadout_eq_dslope
    (M : ℕ) (x z : ℝ)
    (hxF : completedNativeOperatorCharacteristic (x : ℂ) ≠ 0)
    (hzF : completedNativeOperatorCharacteristic (z : ℂ) ≠ 0) :
    canonicalCompletedC3AllCutoffOrientedRealKernelReadout M x z =
      dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) (x : ℂ) (z : ℂ) := by
  rw [canonicalCompletedC3AllCutoffOrientedRealKernelReadout_eq_ledger,
    canonicalCompletedC3AllCutoffRealKernelReadout_eq_dslope M x z hxF hzF]

/-- Exact identification of the complete oriented C3 readout with the
positive Parseval product in the concrete all-bases Green-frame carrier.
The left side still contains radial, provenance, off-diagonal, residual,
tail, xi, and chart channels; the right side changes only their final Hilbert
presentation. -/
theorem
    canonicalCompletedC3AllCutoffOrientedRealKernelReadout_eq_parsevalInner
    (M : ℕ)
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (x z : ℝ)
    (hxF : completedNativeOperatorCharacteristic (x : ℂ) ≠ 0)
    (hzF : completedNativeOperatorCharacteristic (z : ℂ) ≠ 0) :
    canonicalCompletedC3AllCutoffOrientedRealKernelReadout M x z =
      inner ℂ
        (canonicalCompletedNativeParsevalGreenFrameState state (x : ℂ))
        (canonicalCompletedNativeParsevalGreenFrameState state (z : ℂ)) := by
  rw [canonicalCompletedC3AllCutoffOrientedRealKernelReadout_eq_dslope
      M x z hxF hzF,
    canonicalCompletedNativeParsevalGreenFrameState_inner_eq_dslope
      state hkernel x z hxF hzF]

/-- Fully channel-separated version of the same identification.  The
oriented C3 ledger is synthesized only after it has been identified with the
orthogonal seed, residual, depth-one Green, and bulk Green products. -/
theorem
    canonicalCompletedC3AllCutoffOrientedRealKernelReadout_eq_parsevalChannelSum
    (M : ℕ)
    (state : ℂ → CarryVerticalL2)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (x z : ℝ)
    (hxF : completedNativeOperatorCharacteristic (x : ℂ) ≠ 0)
    (hzF : completedNativeOperatorCharacteristic (z : ℂ) ≠ 0) :
    let stateX :=
      canonicalCompletedNativeParsevalGreenFrameState state (x : ℂ)
    let stateZ :=
      canonicalCompletedNativeParsevalGreenFrameState state (z : ℂ)
    canonicalCompletedC3AllCutoffOrientedRealKernelReadout M x z =
      inner ℂ stateX.fst.fst.fst stateZ.fst.fst.fst +
        inner ℂ stateX.fst.fst.snd stateZ.fst.fst.snd +
        inner ℂ stateX.fst.snd stateZ.fst.snd +
        inner ℂ stateX.snd stateZ.snd := by
  dsimp only
  rw [canonicalCompletedC3AllCutoffOrientedRealKernelReadout_eq_dslope
      M x z hxF hzF,
    canonicalCompletedNativeParsevalGreenFrame_dslope_eq_channelSum
      state hkernel x z hxF hzF]

/-! ## Forward-difference limit of the oriented readout -/

/-- Complex-argument wrapper used by the mixed forward-difference API. -/
def canonicalCompletedC3AllCutoffOrientedRealAxisKernelReadout
    (M : ℕ) (x z : ℂ) : ℂ :=
  canonicalCompletedC3AllCutoffOrientedRealKernelReadout M x.re z.re

/-- On every finite sampling grid, the oriented mixed readout eventually
agrees exactly with the scalar `dslope` kernel. -/
theorem
    canonicalCompletedC3AllCutoffOrientedRealAxisKernelForwardDifference_eventuallyEq_dslope
    (M p q : ℕ) :
    (fun k ↦ completedGreenKernelForwardDifference
      (canonicalCompletedC3AllCutoffOrientedRealAxisKernelReadout M)
      (canonicalGreenJetStep k) p q) =ᶠ[atTop]
    (fun k ↦ completedGreenKernelForwardDifference
      (fun x z ↦ dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) x z)
      (canonicalGreenJetStep k) p q) := by
  have hp : ∀ᶠ k : ℕ in atTop,
      ∀ i ∈ Finset.range (p + 1),
        completedNativeOperatorCharacteristic
          (i • canonicalGreenJetStep k) ≠ 0 := by
    rw [eventually_all_finset]
    intro i hi
    exact
      completedNativeOperatorCharacteristic_nsmul_canonicalGreenJetStep_eventually_ne_zero i
  have hq : ∀ᶠ k : ℕ in atTop,
      ∀ j ∈ Finset.range (q + 1),
        completedNativeOperatorCharacteristic
          (j • canonicalGreenJetStep k) ≠ 0 := by
    rw [eventually_all_finset]
    intro j hj
    exact
      completedNativeOperatorCharacteristic_nsmul_canonicalGreenJetStep_eventually_ne_zero j
  filter_upwards [hp, hq] with k hkP hkQ
  apply completedGreenKernelForwardDifference_eq_of_eq_on_grid
  intro i hi j hj
  rw [nsmul_canonicalGreenJetStep_eq_ofReal,
    nsmul_canonicalGreenJetStep_eq_ofReal]
  exact
    canonicalCompletedC3AllCutoffOrientedRealKernelReadout_eq_dslope M
      ((i : ℝ) * ((k : ℝ) + 1)⁻¹)
      ((j : ℝ) * ((k : ℝ) + 1)⁻¹)
      (by simpa [canonicalGreenJetStep] using hkP i hi)
      (by simpa [canonicalGreenJetStep] using hkQ j hj)

/-- Every mixed forward difference of the oriented source readout converges
to the canonical completed-native moment. -/
theorem
    canonicalCompletedC3AllCutoffOrientedRealAxisKernelForwardDifference_tendsto_moment
    (M p q : ℕ) :
    Tendsto
      (fun k ↦ completedGreenKernelForwardDifference
        (canonicalCompletedC3AllCutoffOrientedRealAxisKernelReadout M)
        (canonicalGreenJetStep k) p q)
      atTop
      (nhds
        (polarizedGreenMomentCoefficient
          canonicalCompletedNativeLogDerivativeMoment p q)) := by
  exact
    (completedNativeGreenKernelForwardDifference_dslope_tendsto p q).congr'
      (canonicalCompletedC3AllCutoffOrientedRealAxisKernelForwardDifference_eventuallyEq_dslope
        M p q).symm

/-- The same convergence in the four parity blocks consumed by the completed
Green Hankel/Jacobi construction. -/
theorem
    canonicalCompletedC3AllCutoffOrientedRealAxisKernelParityForwardDifference_tendsto
    (M : ℕ) (i j : ℕ ⊕ ℕ) :
    Tendsto
      (fun k ↦
        (completedGreenKernelForwardDifference
          (canonicalCompletedC3AllCutoffOrientedRealAxisKernelReadout M)
          (canonicalGreenJetStep k)
          (completedGreenParityOrder i)
          (completedGreenParityOrder j)).re)
      atTop
      (nhds
        (greenWronskianMomentKernel
          canonicalCompletedNativeLogDerivativeMoment i j)) := by
  have heq :=
    canonicalCompletedC3AllCutoffOrientedRealAxisKernelForwardDifference_eventuallyEq_dslope
      M (completedGreenParityOrder i) (completedGreenParityOrder j)
  have hre :
      (fun k ↦
        (completedGreenKernelForwardDifference
          (canonicalCompletedC3AllCutoffOrientedRealAxisKernelReadout M)
          (canonicalGreenJetStep k)
          (completedGreenParityOrder i)
          (completedGreenParityOrder j)).re) =ᶠ[atTop]
      (fun k ↦
        (completedGreenKernelForwardDifference
          (fun x z ↦ dslope
            (completedGreenNormalizedResponse
              completedNativeOperatorCharacteristic
              completedNativeOperatorBoundaryCompanion) x z)
          (canonicalGreenJetStep k)
          (completedGreenParityOrder i)
          (completedGreenParityOrder j)).re) := by
    filter_upwards [heq] with k hk
    exact congrArg Complex.re hk
  exact
    (completedNativeGreenKernelForwardDifference_dslope_re_tendsto i j).congr'
      hre.symm

end

end CarrySelfAdjointOperator
