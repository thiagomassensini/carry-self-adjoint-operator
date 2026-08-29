import CarrySelfAdjointOperator.CompletedC3CompressedWronskianChannelGate
import CarrySelfAdjointOperator.CompletedC3EnrichedSymplecticNoLeakBridge
import CarrySelfAdjointOperator.CompletedC3ArchimedeanChartOperatorCarrier
import CarrySelfAdjointOperator.CompletedC3FullWronskianOperatorCarrier
import CarrySelfAdjointOperator.CompletedC3FinalReadoutKernelBridge
import Mathlib.Tactic

/-!
# Recovered enriched carrier for the completed C3 Wronskian

The direct compressed Gram does not contain the reflected Green quadrature.
The missing radial coordinate is already reconstructed exactly from the
ordinary and log-jet completed states.  This module places that recovered
pair in a fixed Hilbert carrier and keeps the finite structural triple, tail,
xi weight, and archimedean operator states in separate orthogonal blocks.

Only the final readout is scalar.  Its cutoff limit is the crossed completed
Wronskian, with no positivity, zero, resolvent, or sewing hypothesis.
-/

open scoped ComplexConjugate InnerProductSpace Topology lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-! ## Recovered reflected radial block -/

/-- The two completed `l2` states entering the reflected static Green
pairing.  The second coordinate is reconstructed from ordinary and log-jet
data at the unreflected parameter. -/
abbrev CanonicalCompletedC3RecoveredRadialPairHilbert :=
  WithLp 2 (CarryVerticalL2 × CarryVerticalL2)

namespace CanonicalCompletedC3RecoveredRadialPairHilbert

def target (state : CanonicalCompletedC3RecoveredRadialPairHilbert) :
    CarryVerticalL2 :=
  state.fst

def recoveredSource (state : CanonicalCompletedC3RecoveredRadialPairHilbert) :
    CarryVerticalL2 :=
  state.snd

/-- The radial scalarization is delayed until both completed vectors have
been retained. -/
def readout (z w : ℂ)
    (state : CanonicalCompletedC3RecoveredRadialPairHilbert) : ℂ :=
  canonicalC3MixedRadialCoefficient
      (operatorHeightParameter w) (operatorHeightParameter z) *
    inner ℂ state.target state.recoveredSource

end CanonicalCompletedC3RecoveredRadialPairHilbert

/-- Canonical completed radial pair. -/
def canonicalCompletedC3RecoveredRadialPairState
    (z w : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    CanonicalCompletedC3RecoveredRadialPairHilbert :=
  WithLp.toLp 2
    (canonicalCompletedC3DirichletGradientState
        (operatorHeightParameter z) hzStrip.1,
      canonicalCompletedC3RecoveredReflectedGradientState
        (operatorHeightParameter w)
        (by simpa [reflectedParameter] using sub_pos.mpr hwStrip.2))

/-- The recovered radial pair realizes exactly the completed static Green
channel in the Wronskian orientation. -/
theorem canonicalCompletedC3RecoveredRadialPairState_readout
    (z w : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    CanonicalCompletedC3RecoveredRadialPairHilbert.readout z w
        (canonicalCompletedC3RecoveredRadialPairState
          z w hzStrip hwStrip) =
      canonicalCompletedC3AllOrderStaticSymplecticGreenReadout
        z w hzStrip hwStrip := by
  exact
    (canonicalCompletedC3AllOrderStaticSymplecticGreenReadout_eq_recoveredStateInner
      z w hzStrip hwStrip).symm

/-! ## Full enriched all-cutoff carrier -/

/-- The two archimedean states retained before application of the crossed
symplectic operator. -/
abbrev CanonicalCompletedC3ArchimedeanChartStatePairHilbert :=
  WithLp 2
    (CanonicalCompletedC3ArchimedeanChartOperatorCarrier ×
      CanonicalCompletedC3ArchimedeanChartOperatorCarrier)

/-- Fixed carrier for the recovered radial pair, the three structural
coordinates, the exact head-tail correction, the xi weight, and both
archimedean operator states. -/
abbrev CanonicalCompletedC3RecoveredAllCutoffLedgerHilbert :=
  WithLp 2
    (CanonicalCompletedC3RecoveredRadialPairHilbert ×
      WithLp 2
        (CanonicalC3MixedStructuralChannelHilbert ×
          WithLp 2
            (ℂ × WithLp 2
              (ℂ × CanonicalCompletedC3ArchimedeanChartStatePairHilbert))))

namespace CanonicalCompletedC3RecoveredAllCutoffLedgerHilbert

def radial (state : CanonicalCompletedC3RecoveredAllCutoffLedgerHilbert) :
    CanonicalCompletedC3RecoveredRadialPairHilbert :=
  state.fst

def structural
    (state : CanonicalCompletedC3RecoveredAllCutoffLedgerHilbert) :
    CanonicalC3MixedStructuralChannelHilbert :=
  state.snd.fst

def tail (state : CanonicalCompletedC3RecoveredAllCutoffLedgerHilbert) : ℂ :=
  state.snd.snd.fst

def xiWeight
    (state : CanonicalCompletedC3RecoveredAllCutoffLedgerHilbert) : ℂ :=
  state.snd.snd.snd.fst

def archimedeanResponse
    (state : CanonicalCompletedC3RecoveredAllCutoffLedgerHilbert) :
    CanonicalCompletedC3ArchimedeanChartOperatorCarrier :=
  state.snd.snd.snd.snd.fst

def archimedeanSource
    (state : CanonicalCompletedC3RecoveredAllCutoffLedgerHilbert) :
    CanonicalCompletedC3ArchimedeanChartOperatorCarrier :=
  state.snd.snd.snd.snd.snd

/-- Final scalar readout.  No structural coordinate is discarded before
`canonicalC3MixedStructuralScalarReadout`, and the chart contribution is
read by its already constructed bounded operator. -/
def readout (z w : ℂ)
    (state : CanonicalCompletedC3RecoveredAllCutoffLedgerHilbert) : ℂ :=
  state.xiWeight *
      (CanonicalCompletedC3RecoveredRadialPairHilbert.readout z w
          state.radial +
        canonicalC3MixedStructuralScalarReadout state.structural +
        state.tail) +
    inner ℂ state.archimedeanResponse
      (canonicalCompletedC3ArchimedeanChartOperator state.archimedeanSource)

/-- Pythagorean audit of the enriched carrier before its final scalar
readout.  In particular, the recovered reflected source cannot cancel a
structural, tail, weight, or chart coordinate at the vector level. -/
theorem norm_sq_eq_channel_sum
    (state : CanonicalCompletedC3RecoveredAllCutoffLedgerHilbert) :
    ‖state‖ ^ 2 =
      ‖state.radial.target‖ ^ 2 +
      ‖state.radial.recoveredSource‖ ^ 2 +
      ‖state.structural‖ ^ 2 +
      ‖state.tail‖ ^ 2 +
      ‖state.xiWeight‖ ^ 2 +
      ‖state.archimedeanResponse‖ ^ 2 +
      ‖state.archimedeanSource‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2 state,
    WithLp.prod_norm_sq_eq_of_L2 state.fst,
    WithLp.prod_norm_sq_eq_of_L2 state.snd,
    WithLp.prod_norm_sq_eq_of_L2 state.snd.snd,
    WithLp.prod_norm_sq_eq_of_L2 state.snd.snd.snd,
    WithLp.prod_norm_sq_eq_of_L2 state.snd.snd.snd.snd]
  unfold radial structural tail xiWeight archimedeanResponse
    archimedeanSource
    CanonicalCompletedC3RecoveredRadialPairHilbert.target
    CanonicalCompletedC3RecoveredRadialPairHilbert.recoveredSource
  ring

end CanonicalCompletedC3RecoveredAllCutoffLedgerHilbert

/-- Enriched state at cutoff `M`.  Only the structural and head-tail blocks
vary with `M`; the radial and archimedean blocks are already completed. -/
def canonicalCompletedC3RecoveredAllCutoffLedgerState
    (M : ℕ) (z w : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    CanonicalCompletedC3RecoveredAllCutoffLedgerHilbert :=
  WithLp.toLp 2
    (canonicalCompletedC3RecoveredRadialPairState z w hzStrip hwStrip,
      WithLp.toLp 2
        (canonicalC3FiniteMixedHeightStructuralChannelState M
            (operatorHeightParameter w) (operatorHeightParameter z),
          WithLp.toLp 2
            (canonicalC3MixedHeightTailCompletionDefect M w z,
              WithLp.toLp 2
                (mixedHermitianWeight nativeXiCompletionFactor w z,
                  WithLp.toLp 2
                    (canonicalCompletedC3ArchimedeanChartOperatorState z,
                      canonicalCompletedC3ArchimedeanChartOperatorState w)))))

@[simp] theorem canonicalCompletedC3RecoveredAllCutoffLedgerState_radial
    (M : ℕ) (z w : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    (canonicalCompletedC3RecoveredAllCutoffLedgerState
      M z w hzStrip hwStrip).radial =
        canonicalCompletedC3RecoveredRadialPairState z w hzStrip hwStrip :=
  rfl

@[simp] theorem canonicalCompletedC3RecoveredAllCutoffLedgerState_structural
    (M : ℕ) (z w : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    (canonicalCompletedC3RecoveredAllCutoffLedgerState
      M z w hzStrip hwStrip).structural =
        canonicalC3FiniteMixedHeightStructuralChannelState M
          (operatorHeightParameter w) (operatorHeightParameter z) :=
  rfl

@[simp] theorem canonicalCompletedC3RecoveredAllCutoffLedgerState_tail
    (M : ℕ) (z w : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    (canonicalCompletedC3RecoveredAllCutoffLedgerState
      M z w hzStrip hwStrip).tail =
        canonicalC3MixedHeightTailCompletionDefect M w z :=
  rfl

@[simp] theorem canonicalCompletedC3RecoveredAllCutoffLedgerState_xiWeight
    (M : ℕ) (z w : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    (canonicalCompletedC3RecoveredAllCutoffLedgerState
      M z w hzStrip hwStrip).xiWeight =
        mixedHermitianWeight nativeXiCompletionFactor w z :=
  rfl

@[simp] theorem
    canonicalCompletedC3RecoveredAllCutoffLedgerState_archimedeanResponse
    (M : ℕ) (z w : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    (canonicalCompletedC3RecoveredAllCutoffLedgerState
      M z w hzStrip hwStrip).archimedeanResponse =
        canonicalCompletedC3ArchimedeanChartOperatorState z :=
  rfl

@[simp] theorem
    canonicalCompletedC3RecoveredAllCutoffLedgerState_archimedeanSource
    (M : ℕ) (z w : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    (canonicalCompletedC3RecoveredAllCutoffLedgerState
      M z w hzStrip hwStrip).archimedeanSource =
        canonicalCompletedC3ArchimedeanChartOperatorState w :=
  rfl

/-- Exact expansion of the enriched readout.  The reflected radial pairing,
the three-coordinate structural readout, the head-tail return, the xi weight,
and the crossed chart operator remain visibly distinct. -/
theorem canonicalCompletedC3RecoveredAllCutoffLedgerState_readout_eq_channels
    (M : ℕ) (z w : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    CanonicalCompletedC3RecoveredAllCutoffLedgerHilbert.readout z w
        (canonicalCompletedC3RecoveredAllCutoffLedgerState
          M z w hzStrip hwStrip) =
      mixedHermitianWeight nativeXiCompletionFactor w z *
          (canonicalCompletedC3AllOrderStaticSymplecticGreenReadout
              z w hzStrip hwStrip +
            canonicalC3FiniteMixedHeightStructuralDefect M
              (operatorHeightParameter w) (operatorHeightParameter z) +
            canonicalC3MixedHeightTailCompletionDefect M w z) +
        canonicalCompletedC3ArchimedeanChartMixedChannel w z := by
  rw [CanonicalCompletedC3RecoveredAllCutoffLedgerHilbert.readout,
    canonicalCompletedC3RecoveredAllCutoffLedgerState_xiWeight,
    canonicalCompletedC3RecoveredAllCutoffLedgerState_radial,
    canonicalCompletedC3RecoveredRadialPairState_readout,
    canonicalCompletedC3RecoveredAllCutoffLedgerState_structural,
    canonicalC3MixedStructuralScalarReadout_state,
    canonicalCompletedC3RecoveredAllCutoffLedgerState_tail,
    canonicalCompletedC3RecoveredAllCutoffLedgerState_archimedeanResponse,
    canonicalCompletedC3RecoveredAllCutoffLedgerState_archimedeanSource,
    ← canonicalCompletedC3ArchimedeanChartMixedChannel_eq_operatorInner]

/-- The enriched cutoff carrier converges to the crossed completed
Wronskian.  This is the completed sewing supplied by ordinary/log-jet
reconstruction plus the already proved structural and head-tail limits. -/
theorem canonicalCompletedC3RecoveredAllCutoffLedgerState_readout_tendsto_wronskian
    {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ =>
        CanonicalCompletedC3RecoveredAllCutoffLedgerHilbert.readout z w
          (canonicalCompletedC3RecoveredAllCutoffLedgerState
            M z w hzStrip hwStrip))
      atTop
      (nhds
        (mixedHermitianWeight canonicalC3ChartFactorHeight w z *
          completedGreenWronskian
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion w z)) := by
  rw [completedFNegFPrimeWronskian_crossedChart_eq_static_add_channels
    z w hzStrip hwStrip]
  have hstruct :=
    canonicalC3FiniteMixedHeightStructuralDefect_tendsto_allOrderLimit
      hzStrip hwStrip
  have htail :=
    canonicalC3MixedHeightTailCompletionDefect_tendsto_zero
      hwStrip.1 hzStrip.1
  have hraw :
      Tendsto
        (fun M : ℕ =>
          canonicalCompletedC3AllOrderStaticSymplecticGreenReadout
                z w hzStrip hwStrip +
            canonicalC3FiniteMixedHeightStructuralDefect M
              (operatorHeightParameter w) (operatorHeightParameter z) +
            canonicalC3MixedHeightTailCompletionDefect M w z)
        atTop
        (nhds
          (canonicalCompletedC3AllOrderStaticSymplecticGreenReadout
              z w hzStrip hwStrip +
            canonicalCompletedC3AllOrderStructuralChannelLimit
              z w hzStrip hwStrip + 0)) :=
    (tendsto_const_nhds.add hstruct).add htail
  have hweight : Tendsto
      (fun _ : ℕ => mixedHermitianWeight nativeXiCompletionFactor w z)
      atTop
      (nhds (mixedHermitianWeight nativeXiCompletionFactor w z)) :=
    tendsto_const_nhds
  have harch : Tendsto
      (fun _ : ℕ => canonicalCompletedC3ArchimedeanChartMixedChannel w z)
      atTop
      (nhds (canonicalCompletedC3ArchimedeanChartMixedChannel w z)) :=
    tendsto_const_nhds
  have hfinal := (hweight.mul hraw).add harch
  simpa only [add_zero,
    canonicalCompletedC3RecoveredAllCutoffLedgerState_readout_eq_channels]
    using hfinal

/-- The enriched geometric ledger converges to the bounded one-point
Wronskian operator readout already constructed from the completed trace
state.  No operator is reconstructed here: this is the commuting square from
the recovered pair carrier to the existing full carrier. -/
theorem canonicalCompletedC3RecoveredAllCutoffLedgerState_readout_tendsto_fullOperatorInner
    (N : ℕ) {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ =>
        CanonicalCompletedC3RecoveredAllCutoffLedgerHilbert.readout z w
          (canonicalCompletedC3RecoveredAllCutoffLedgerState
            M z w hzStrip hwStrip))
      atTop
      (nhds
        (inner ℂ
          (canonicalCompletedC3FullWronskianOperatorState N z)
          (canonicalCompletedC3FullWronskianOperator
            (canonicalCompletedC3FullWronskianOperatorState N w)))) := by
  have hlimit :=
    canonicalCompletedC3RecoveredAllCutoffLedgerState_readout_tendsto_wronskian
      hzStrip hwStrip
  have hcompanion : completedNativeOperatorBoundaryCompanion =
      (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u) := by
    funext u
    exact completedNativeOperatorBoundaryCompanion_eq_neg_deriv u
  rw [hcompanion,
    completedFNegFPrimeWronskian_eq_fullOperatorInner
      N hwStrip hzStrip] at hlimit
  exact hlimit

/-! ## Canonical normalization after the enriched readout -/

/-- Normalize the recovered enriched readout only after all vector channels
have been retained.  This is the same chart, characteristic, and separation
factor used by the exact all-cutoff kernel ledger. -/
def canonicalCompletedC3RecoveredAllCutoffOffDiagonalKernelReadout
    (M : ℕ) (x z : ℂ)
    (hxStrip : operatorHeightParameter x ∈ genuineCriticalStrip)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) : ℂ :=
  CanonicalCompletedC3RecoveredAllCutoffLedgerHilbert.readout x z
      (canonicalCompletedC3RecoveredAllCutoffLedgerState
        M x z hxStrip hzStrip) /
    (mixedHermitianWeight canonicalC3ChartFactorHeight z x *
      ((2 : ℂ) *
        (starRingEnd ℂ) (completedNativeOperatorCharacteristic x) *
        completedNativeOperatorCharacteristic z) *
      (z - (starRingEnd ℂ) x))

/-- After canonical normalization, the recovered carrier converges to the
existing exact off-diagonal completed kernel. -/
theorem canonicalCompletedC3RecoveredAllCutoffOffDiagonalKernelReadout_tendsto
    (N : ℕ) {x z : ℂ}
    (hxStrip : operatorHeightParameter x ∈ genuineCriticalStrip)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ =>
        canonicalCompletedC3RecoveredAllCutoffOffDiagonalKernelReadout
          M x z hxStrip hzStrip)
      atTop
      (nhds (canonicalCompletedC3AllCutoffOffDiagonalKernelReadout N x z)) := by
  have hlimit :=
    canonicalCompletedC3RecoveredAllCutoffLedgerState_readout_tendsto_wronskian
      hxStrip hzStrip
  have hcompanion : completedNativeOperatorBoundaryCompanion =
      (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u) := by
    funext u
    exact completedNativeOperatorBoundaryCompanion_eq_neg_deriv u
  rw [hcompanion] at hlimit
  have hdiv := hlimit.div_const
    (mixedHermitianWeight canonicalC3ChartFactorHeight z x *
      ((2 : ℂ) *
        (starRingEnd ℂ) (completedNativeOperatorCharacteristic x) *
        completedNativeOperatorCharacteristic z) *
      (z - (starRingEnd ℂ) x))
  have htarget :
      canonicalCompletedC3AllCutoffOffDiagonalKernelReadout N x z =
        (mixedHermitianWeight canonicalC3ChartFactorHeight z x *
            completedGreenWronskian
              completedNativeOperatorCharacteristic
              (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
              z x) /
          (mixedHermitianWeight canonicalC3ChartFactorHeight z x *
            ((2 : ℂ) *
              (starRingEnd ℂ) (completedNativeOperatorCharacteristic x) *
              completedNativeOperatorCharacteristic z) *
            (z - (starRingEnd ℂ) x)) := by
    rw [canonicalCompletedC3AllCutoffOffDiagonalKernelReadout,
      canonicalCompletedC3AllCutoffKernelLedgerState_finalReadout_eq_completedWronskian
        N hzStrip hxStrip]
  rw [htarget]
  simpa only [
    canonicalCompletedC3RecoveredAllCutoffOffDiagonalKernelReadout] using hdiv

/-- Division-free completion followed by the canonical nonzero cancellation
converges to the conjugate-polarized divided response. -/
theorem canonicalCompletedC3RecoveredAllCutoffOffDiagonalKernelReadout_tendsto_polarizedResponse
    {x z : ℂ}
    (hxStrip : operatorHeightParameter x ∈ genuineCriticalStrip)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hxF : completedNativeOperatorCharacteristic x ≠ 0)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hsep : z ≠ (starRingEnd ℂ) x) :
    Tendsto
      (fun M : ℕ =>
        canonicalCompletedC3RecoveredAllCutoffOffDiagonalKernelReadout
          M x z hxStrip hzStrip)
      atTop
      (nhds
        ((z - (starRingEnd ℂ) x)⁻¹ *
          (completedGreenNormalizedResponse
              completedNativeOperatorCharacteristic
              completedNativeOperatorBoundaryCompanion z -
            (starRingEnd ℂ)
              (completedGreenNormalizedResponse
                completedNativeOperatorCharacteristic
                completedNativeOperatorBoundaryCompanion x)))) := by
  have hlimit :=
    canonicalCompletedC3RecoveredAllCutoffOffDiagonalKernelReadout_tendsto
      0 hxStrip hzStrip
  rw [canonicalCompletedC3AllCutoffOffDiagonalKernelReadout_eq
    0 hxStrip hzStrip hxF hzF hsep] at hlimit
  exact hlimit

/-- Canonical real-axis removable closure of the recovered enriched readout.
The collision value is the derivative specified by `dslope`, not an
independent diagonal normalization. -/
def canonicalCompletedC3RecoveredAllCutoffRealKernelReadout
    (M : ℕ) (x z : ℝ) : ℂ :=
  if x = z then
    deriv
      (completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion) (x : ℂ)
  else
    canonicalCompletedC3RecoveredAllCutoffOffDiagonalKernelReadout
      M (x : ℂ) (z : ℂ)
      (by constructor <;> norm_num [operatorHeightParameter])
      (by constructor <;> norm_num [operatorHeightParameter])

/-- The total normalized recovered kernel converges to the canonical
completed-native `dslope`, including the removable diagonal. -/
theorem canonicalCompletedC3RecoveredAllCutoffRealKernelReadout_tendsto_dslope
    {x z : ℝ}
    (hxF : completedNativeOperatorCharacteristic (x : ℂ) ≠ 0)
    (hzF : completedNativeOperatorCharacteristic (z : ℂ) ≠ 0) :
    Tendsto
      (fun M : ℕ =>
        canonicalCompletedC3RecoveredAllCutoffRealKernelReadout M x z)
      atTop
      (nhds
        (dslope
          (completedGreenNormalizedResponse
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion) (x : ℂ) (z : ℂ))) := by
  by_cases hxz : x = z
  · subst z
    simp [canonicalCompletedC3RecoveredAllCutoffRealKernelReadout,
      dslope_same]
  · have hxStrip : operatorHeightParameter (x : ℂ) ∈
        genuineCriticalStrip := by
      constructor <;> norm_num [operatorHeightParameter]
    have hzStrip : operatorHeightParameter (z : ℂ) ∈
        genuineCriticalStrip := by
      constructor <;> norm_num [operatorHeightParameter]
    have hsep : (z : ℂ) ≠ (starRingEnd ℂ) (x : ℂ) := by
      simpa using
        (show (z : ℂ) ≠ (x : ℂ) by exact_mod_cast (Ne.symm hxz))
    have hlimit :=
      canonicalCompletedC3RecoveredAllCutoffOffDiagonalKernelReadout_tendsto_polarizedResponse
        hxStrip hzStrip hxF hzF hsep
    have hxStar : (starRingEnd ℂ) (x : ℂ) = (x : ℂ) := by
      simp
    have htarget :
        (z - (starRingEnd ℂ) (x : ℂ))⁻¹ *
            (completedGreenNormalizedResponse
                completedNativeOperatorCharacteristic
                completedNativeOperatorBoundaryCompanion (z : ℂ) -
              (starRingEnd ℂ)
                (completedGreenNormalizedResponse
                  completedNativeOperatorCharacteristic
                  completedNativeOperatorBoundaryCompanion (x : ℂ))) =
          dslope
            (completedGreenNormalizedResponse
              completedNativeOperatorCharacteristic
              completedNativeOperatorBoundaryCompanion) (x : ℂ) (z : ℂ) := by
      rw [completedNativeGreenNormalizedResponse_ofReal_conj, hxStar,
        dslope_of_ne, slope_def_module]
      · simp only [smul_eq_mul]
      · exact_mod_cast (Ne.symm hxz)
    rw [← htarget]
    simpa [canonicalCompletedC3RecoveredAllCutoffRealKernelReadout, hxz]
      using hlimit

end

end CarrySelfAdjointOperator
