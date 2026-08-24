import CarrySelfAdjointOperator.CompletedC3FNegFPrimeMixedKernel
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

/-!
# Orthogonal no-cancellation for the completed C3 structural channels

The finite mixed Green--Wronskian ledger retains three structural scalar
channels: Green provenance, ordered off-diagonal provenance, and the height
readout residual.  Their scalar synthesis is not injective, so cancellation
cannot be excluded after those channels have already been added in `ℂ`.

This file records the lossless alternative.  The three actual channels are
placed in an `L²` direct sum and their squared norm is proved to be exactly
the sum of the three squared channel norms.  Consequently this orthogonal
energy tends to zero exactly when all three channels tend to zero separately.
At an off-critical Genuine zero that is impossible: the previously computed
structural scalar limit is the nonzero negative radial kernel.  Thus at least
one structural channel survives in completion, even though scalar readouts
may cancel against another channel.
-/

open scoped ComplexConjugate Topology

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open Filter

noncomputable section

/-! ## The three retained structural channels -/

/-- Green-provenance coordinate of the canonical height-rotated C3 ledger. -/
def canonicalC3FiniteMixedHeightGreenProvenanceChannel
    (M : ℕ) (z w : ℂ) : ℂ :=
  canonicalMixedBoundaryGreenProvenance
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z w

/-- Ordered off-diagonal coordinate of the canonical height-rotated ledger. -/
def canonicalC3FiniteMixedHeightOffDiagonalChannel
    (M : ℕ) (z w : ℂ) : ℂ :=
  canonicalMixedBoundaryCrossProvenance
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z w

/-- Height-readout residual coordinate of the canonical mixed ledger. -/
def canonicalC3FiniteMixedHeightReadoutResidualChannel
    (M : ℕ) (z w : ℂ) : ℂ :=
  canonicalMixedBoundaryHeightReadoutResidualCorrection
    M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z w

/-- The existing structural defect is exactly the scalar sum of the three
retained coordinates. -/
theorem canonicalC3FiniteMixedHeightStructuralDefect_eq_channelSum
    (M : ℕ) (z w : ℂ) :
    canonicalC3FiniteMixedHeightStructuralDefect M z w =
      canonicalC3FiniteMixedHeightGreenProvenanceChannel M z w +
        canonicalC3FiniteMixedHeightOffDiagonalChannel M z w +
          canonicalC3FiniteMixedHeightReadoutResidualChannel M z w := by
  rfl

/-! ## Lossless direct-sum carrier -/

/-- Orthogonal Hilbert carrier for provenance, off-diagonal, and residual
coordinates.  The nesting only realizes a three-fold `L²` direct sum. -/
abbrev CanonicalC3MixedStructuralChannelHilbert :=
  WithLp 2 (ℂ × WithLp 2 (ℂ × ℂ))

/-- The three actual finite structural coordinates before scalar synthesis. -/
def canonicalC3FiniteMixedHeightStructuralChannelState
    (M : ℕ) (z w : ℂ) : CanonicalC3MixedStructuralChannelHilbert :=
  WithLp.toLp 2
    (canonicalC3FiniteMixedHeightGreenProvenanceChannel M z w,
      WithLp.toLp 2
        (canonicalC3FiniteMixedHeightOffDiagonalChannel M z w,
          canonicalC3FiniteMixedHeightReadoutResidualChannel M z w))

/-- Final scalar addition on the three-channel Hilbert carrier. -/
def canonicalC3MixedStructuralScalarReadout
    (x : CanonicalC3MixedStructuralChannelHilbert) : ℂ :=
  x.fst + x.snd.fst + x.snd.snd

/-- Scalar addition has a nontrivial kernel.  This is the precise reason why
no-cancellation cannot be recovered from the scalar readout alone. -/
theorem canonicalC3MixedStructuralScalarReadout_not_injective :
    ¬ Function.Injective canonicalC3MixedStructuralScalarReadout := by
  intro hinjective
  let x : CanonicalC3MixedStructuralChannelHilbert :=
    WithLp.toLp 2
      ((1 : ℂ), WithLp.toLp 2 (-(1 : ℂ), 0))
  have hreadout :
      canonicalC3MixedStructuralScalarReadout x =
        canonicalC3MixedStructuralScalarReadout 0 := by
    simp [canonicalC3MixedStructuralScalarReadout, x]
  have hx := hinjective hreadout
  have hfst := congrArg
    (fun y : CanonicalC3MixedStructuralChannelHilbert => y.fst) hx
  norm_num [x] at hfst

/-- Reading the actual direct-sum state recovers the existing scalar
structural defect, but only after the three coordinates have been retained. -/
theorem canonicalC3MixedStructuralScalarReadout_state
    (M : ℕ) (z w : ℂ) :
    canonicalC3MixedStructuralScalarReadout
        (canonicalC3FiniteMixedHeightStructuralChannelState M z w) =
      canonicalC3FiniteMixedHeightStructuralDefect M z w := by
  rw [canonicalC3FiniteMixedHeightStructuralDefect_eq_channelSum]
  rfl

/-- Positive energy of the uncollapsed three-channel structural state. -/
def canonicalC3FiniteMixedHeightStructuralChannelEnergy
    (M : ℕ) (z w : ℂ) : ℝ :=
  ‖canonicalC3FiniteMixedHeightGreenProvenanceChannel M z w‖ ^ 2 +
    ‖canonicalC3FiniteMixedHeightOffDiagonalChannel M z w‖ ^ 2 +
      ‖canonicalC3FiniteMixedHeightReadoutResidualChannel M z w‖ ^ 2

/-- Pythagorean identity for the actual structural channels. -/
theorem canonicalC3FiniteMixedHeightStructuralChannelState_norm_sq
    (M : ℕ) (z w : ℂ) :
    ‖canonicalC3FiniteMixedHeightStructuralChannelState M z w‖ ^ 2 =
      canonicalC3FiniteMixedHeightStructuralChannelEnergy M z w := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change
    ‖canonicalC3FiniteMixedHeightGreenProvenanceChannel M z w‖ ^ 2 +
        (‖canonicalC3FiniteMixedHeightOffDiagonalChannel M z w‖ ^ 2 +
          ‖canonicalC3FiniteMixedHeightReadoutResidualChannel M z w‖ ^ 2) = _
  unfold canonicalC3FiniteMixedHeightStructuralChannelEnergy
  ring

/-- At a fixed cutoff the orthogonal energy vanishes exactly when every
structural coordinate vanishes. -/
theorem canonicalC3FiniteMixedHeightStructuralChannelEnergy_eq_zero_iff
    (M : ℕ) (z w : ℂ) :
    canonicalC3FiniteMixedHeightStructuralChannelEnergy M z w = 0 ↔
      canonicalC3FiniteMixedHeightGreenProvenanceChannel M z w = 0 ∧
        canonicalC3FiniteMixedHeightOffDiagonalChannel M z w = 0 ∧
          canonicalC3FiniteMixedHeightReadoutResidualChannel M z w = 0 := by
  rw [← canonicalC3FiniteMixedHeightStructuralChannelState_norm_sq M z w]
  simp [canonicalC3FiniteMixedHeightStructuralChannelState]

/-! ## No-cancellation in completion -/

/-- A three-channel quadratic energy tends to zero exactly when all three
complex channels tend to zero. -/
theorem threeComplexChannelEnergy_tendsto_zero_iff
    (a b c : ℕ → ℂ) :
    Tendsto
        (fun M : ℕ => ‖a M‖ ^ 2 + ‖b M‖ ^ 2 + ‖c M‖ ^ 2)
        atTop (nhds 0) ↔
      Tendsto a atTop (nhds 0) ∧
        Tendsto b atTop (nhds 0) ∧
          Tendsto c atTop (nhds 0) := by
  constructor
  · intro henergy
    have haSq : Tendsto (fun M => ‖a M‖ ^ 2) atTop (nhds 0) :=
      squeeze_zero (fun M => sq_nonneg ‖a M‖) (fun M => by
        nlinarith [sq_nonneg ‖b M‖, sq_nonneg ‖c M‖]) henergy
    have hbSq : Tendsto (fun M => ‖b M‖ ^ 2) atTop (nhds 0) :=
      squeeze_zero (fun M => sq_nonneg ‖b M‖) (fun M => by
        nlinarith [sq_nonneg ‖a M‖, sq_nonneg ‖c M‖]) henergy
    have hcSq : Tendsto (fun M => ‖c M‖ ^ 2) atTop (nhds 0) :=
      squeeze_zero (fun M => sq_nonneg ‖c M‖) (fun M => by
        nlinarith [sq_nonneg ‖a M‖, sq_nonneg ‖b M‖]) henergy
    have channel_tendsto_zero
        (f : ℕ → ℂ)
        (hf : Tendsto (fun M => ‖f M‖ ^ 2) atTop (nhds 0)) :
        Tendsto f atTop (nhds 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hf
      change Tendsto (fun M => √(‖f M‖ ^ 2)) atTop (nhds (√0)) at hsqrt
      simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
    exact
      ⟨channel_tendsto_zero a haSq,
        channel_tendsto_zero b hbSq,
        channel_tendsto_zero c hcSq⟩
  · rintro ⟨ha, hb, hc⟩
    simpa using ((ha.norm.pow 2).add (hb.norm.pow 2)).add (hc.norm.pow 2)

/-- Applied to the concrete C3 ledger, zero orthogonal energy is equivalent
to separate vanishing of provenance, off-diagonal, and residual channels. -/
theorem canonicalC3FiniteMixedHeightStructuralChannelEnergy_tendsto_zero_iff
    (z w : ℂ) :
    Tendsto
        (fun M : ℕ =>
          canonicalC3FiniteMixedHeightStructuralChannelEnergy M z w)
        atTop (nhds 0) ↔
      Tendsto
          (fun M : ℕ =>
            canonicalC3FiniteMixedHeightGreenProvenanceChannel M z w)
          atTop (nhds 0) ∧
        Tendsto
            (fun M : ℕ =>
              canonicalC3FiniteMixedHeightOffDiagonalChannel M z w)
            atTop (nhds 0) ∧
          Tendsto
              (fun M : ℕ =>
                canonicalC3FiniteMixedHeightReadoutResidualChannel M z w)
              atTop (nhds 0) := by
  simpa [canonicalC3FiniteMixedHeightStructuralChannelEnergy] using
    threeComplexChannelEnergy_tendsto_zero_iff
      (fun M => canonicalC3FiniteMixedHeightGreenProvenanceChannel M z w)
      (fun M => canonicalC3FiniteMixedHeightOffDiagonalChannel M z w)
      (fun M => canonicalC3FiniteMixedHeightReadoutResidualChannel M z w)

/-- At an off-critical Genuine zero, the orthogonal structural energy cannot
vanish in completion.  Hence scalar cancellation does not erase the channel
state. -/
theorem
    canonicalC3FiniteMixedHeightStructuralChannelEnergy_not_tendsto_zero_of_offCritical_genuineZero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    ¬ Tendsto
      (fun M : ℕ =>
        canonicalC3FiniteMixedHeightStructuralChannelEnergy M s s)
      atTop (nhds 0) := by
  intro henergy
  have hchannels :=
    (canonicalC3FiniteMixedHeightStructuralChannelEnergy_tendsto_zero_iff
      s s).1 henergy
  have hsum := (hchannels.1.add hchannels.2.1).add hchannels.2.2
  have hdefect :
      Tendsto
        (fun M : ℕ => canonicalC3FiniteMixedHeightStructuralDefect M s s)
        atTop (nhds 0) := by
    simpa [canonicalC3FiniteMixedHeightStructuralDefect_eq_channelSum] using
      hsum
  exact
    canonicalC3FiniteMixedHeightStructuralDefect_not_tendsto_zero_of_offCritical_genuineZero
      hs hzero hoff hdefect

/-- Equivalently, at least one of the three concrete structural channels
fails to disappear at an off-critical Genuine zero. -/
theorem canonicalC3MixedHeight_one_structuralChannel_survives_of_offCritical_genuineZero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    (¬ Tendsto
      (fun M : ℕ =>
        canonicalC3FiniteMixedHeightGreenProvenanceChannel M s s)
      atTop (nhds 0)) ∨
    (¬ Tendsto
      (fun M : ℕ =>
        canonicalC3FiniteMixedHeightOffDiagonalChannel M s s)
      atTop (nhds 0)) ∨
    (¬ Tendsto
      (fun M : ℕ =>
        canonicalC3FiniteMixedHeightReadoutResidualChannel M s s)
      atTop (nhds 0)) := by
  by_cases hp : Tendsto
      (fun M : ℕ =>
        canonicalC3FiniteMixedHeightGreenProvenanceChannel M s s)
      atTop (nhds 0)
  · by_cases ho : Tendsto
        (fun M : ℕ =>
          canonicalC3FiniteMixedHeightOffDiagonalChannel M s s)
        atTop (nhds 0)
    · by_cases hr : Tendsto
          (fun M : ℕ =>
            canonicalC3FiniteMixedHeightReadoutResidualChannel M s s)
          atTop (nhds 0)
      · exfalso
        apply
          canonicalC3FiniteMixedHeightStructuralChannelEnergy_not_tendsto_zero_of_offCritical_genuineZero
            hs hzero hoff
        exact
          (canonicalC3FiniteMixedHeightStructuralChannelEnergy_tendsto_zero_iff
            s s).2 ⟨hp, ho, hr⟩
      · exact Or.inr (Or.inr hr)
    · exact Or.inr (Or.inl ho)
  · exact Or.inl hp

/-- In fact the orthogonal structural energy is strictly positive at all
sufficiently large cutoffs at an off-critical Genuine zero. -/
theorem
    canonicalC3FiniteMixedHeightStructuralChannelEnergy_eventually_pos_of_offCritical_genuineZero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    ∀ᶠ M : ℕ in atTop,
      0 < canonicalC3FiniteMixedHeightStructuralChannelEnergy M s s := by
  have hkernel :
      canonicalCompletedC3MixedRadialGreenKernel s s hs.1
          (by simpa [reflectedParameter] using sub_pos.mpr hs.2) ≠ 0 := by
    intro hvanish
    exact hoff
      ((canonicalCompletedC3MixedRadialGreenKernel_self_eq_zero_iff hs).1
        hvanish)
  have hlimit :=
    canonicalC3FiniteMixedHeightStructuralDefect_tendsto_neg_radial_at_genuineZero
      hs hzero
  have hdefectNonzero :
      ∀ᶠ M : ℕ in atTop,
        canonicalC3FiniteMixedHeightStructuralDefect M s s ≠ 0 :=
    hlimit.eventually_ne (neg_ne_zero.mpr hkernel)
  filter_upwards [hdefectNonzero] with M hdefect
  have henergyNonneg :
      0 ≤ canonicalC3FiniteMixedHeightStructuralChannelEnergy M s s := by
    unfold canonicalC3FiniteMixedHeightStructuralChannelEnergy
    positivity
  apply lt_of_le_of_ne henergyNonneg
  intro hzeroEnergy
  have hchannels :=
    (canonicalC3FiniteMixedHeightStructuralChannelEnergy_eq_zero_iff M s s).1
      hzeroEnergy.symm
  apply hdefect
  rw [canonicalC3FiniteMixedHeightStructuralDefect_eq_channelSum,
    hchannels.1, hchannels.2.1, hchannels.2.2]
  simp

/-! ## The radial channel retained with the complete raw ledger -/

/-- The finite radial Green channel before it is added to provenance,
off-diagonal, residual, and tail-completion channels. -/
def canonicalC3FiniteMixedRadialGreenChannel
    (M : ℕ) (z w : ℂ) : ℂ :=
  greenForm (𝕜 := ℂ)
    (finiteC3GenuineBracketGreenBoundaryPair (3 * M) w)
    (finiteC3GenuineBracketGreenBoundaryPair
      (3 * M) (reflectedParameter z))

/-- Lossless carrier for the complete raw finite sewing.  Its coordinates are
the radial Green channel, the three-channel structural state, and the
tail-completion channel. -/
abbrev CanonicalC3MixedRawNoLeakChannelHilbert :=
  WithLp 2
    (ℂ × WithLp 2 (CanonicalC3MixedStructuralChannelHilbert × ℂ))

/-- The complete raw finite sewing before its five channels are added in
`ℂ`.  The arguments are centered-height coordinates, as in the raw completed
Wronskian. -/
def canonicalC3FiniteMixedRawNoLeakChannelState
    (M : ℕ) (z w : ℂ) : CanonicalC3MixedRawNoLeakChannelHilbert :=
  WithLp.toLp 2
    (canonicalC3FiniteMixedRadialGreenChannel M
        (operatorHeightParameter z) (operatorHeightParameter w),
      WithLp.toLp 2
        (canonicalC3FiniteMixedHeightStructuralChannelState M
            (operatorHeightParameter z) (operatorHeightParameter w),
          canonicalC3MixedHeightTailCompletionDefect M z w))

/-- Scalar synthesis of the five retained raw sewing channels. -/
def canonicalC3MixedRawNoLeakScalarReadout
    (x : CanonicalC3MixedRawNoLeakChannelHilbert) : ℂ :=
  x.fst + canonicalC3MixedStructuralScalarReadout x.snd.fst + x.snd.snd

/-- The lossless state recovers the raw completed Wronskian only at the final
scalar readout. -/
theorem canonicalC3MixedRawNoLeakScalarReadout_state
    (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalC3MixedRawNoLeakScalarReadout
        (canonicalC3FiniteMixedRawNoLeakChannelState M z w) =
      canonicalCompletedC3RawHeightMixedWronskian z w := by
  rw [canonicalCompletedC3RawHeightMixedWronskian_eq_green_add_channels
    M hz hw]
  unfold canonicalC3MixedRawNoLeakScalarReadout
    canonicalC3FiniteMixedRawNoLeakChannelState
    canonicalC3FiniteMixedRadialGreenChannel
  change
    greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (operatorHeightParameter w))
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter (operatorHeightParameter z))) +
        canonicalC3MixedStructuralScalarReadout
          (canonicalC3FiniteMixedHeightStructuralChannelState M
            (operatorHeightParameter z) (operatorHeightParameter w)) +
        canonicalC3MixedHeightTailCompletionDefect M z w =
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (operatorHeightParameter w))
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter (operatorHeightParameter z))) +
        canonicalC3FiniteMixedHeightStructuralDefect M
          (operatorHeightParameter z) (operatorHeightParameter w) +
        canonicalC3MixedHeightTailCompletionDefect M z w
  rw [canonicalC3MixedStructuralScalarReadout_state]

/-- At a Genuine zero the final scalar readout of the full five-channel raw
ledger is exactly zero at every cutoff. -/
theorem canonicalC3MixedRawNoLeakScalarReadout_eq_zero_at_genuineZero
    (M : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    canonicalC3MixedRawNoLeakScalarReadout
        (canonicalC3FiniteMixedRawNoLeakChannelState M
          (centeredHeightParameter s) (centeredHeightParameter s)) = 0 := by
  rw [canonicalC3MixedRawNoLeakScalarReadout_state M
    (by simpa using hs) (by simpa using hs)]
  exact canonicalCompletedC3RawHeightMixedWronskian_self_eq_zero_of_genuine_zero
    hs hzero

/-- Positive energy of the complete uncollapsed raw sewing ledger. -/
def canonicalC3FiniteMixedRawNoLeakChannelEnergy
    (M : ℕ) (z w : ℂ) : ℝ :=
  ‖canonicalC3FiniteMixedRadialGreenChannel M
      (operatorHeightParameter z) (operatorHeightParameter w)‖ ^ 2 +
    canonicalC3FiniteMixedHeightStructuralChannelEnergy M
      (operatorHeightParameter z) (operatorHeightParameter w) +
    ‖canonicalC3MixedHeightTailCompletionDefect M z w‖ ^ 2

/-- Pythagorean identity for all five raw sewing channels. -/
theorem canonicalC3FiniteMixedRawNoLeakChannelState_norm_sq
    (M : ℕ) (z w : ℂ) :
    ‖canonicalC3FiniteMixedRawNoLeakChannelState M z w‖ ^ 2 =
      canonicalC3FiniteMixedRawNoLeakChannelEnergy M z w := by
  unfold canonicalC3FiniteMixedRawNoLeakChannelState
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change
    ‖canonicalC3FiniteMixedRadialGreenChannel M
        (operatorHeightParameter z) (operatorHeightParameter w)‖ ^ 2 +
        (‖canonicalC3FiniteMixedHeightStructuralChannelState M
            (operatorHeightParameter z) (operatorHeightParameter w)‖ ^ 2 +
          ‖canonicalC3MixedHeightTailCompletionDefect M z w‖ ^ 2) =
      canonicalC3FiniteMixedRawNoLeakChannelEnergy M z w
  rw [canonicalC3FiniteMixedHeightStructuralChannelState_norm_sq]
  unfold canonicalC3FiniteMixedRawNoLeakChannelEnergy
  ring

/-- The radial coordinate converges to the completed radial Green kernel. -/
theorem canonicalC3FiniteMixedRadialGreenChannel_tendsto_completed
    {z w : ℂ} (hw : 0 < w.re)
    (hzReflected : 0 < (reflectedParameter z).re) :
    Tendsto
      (fun M : ℕ => canonicalC3FiniteMixedRadialGreenChannel M z w)
      atTop
      (nhds
        (canonicalCompletedC3MixedRadialGreenKernel z w hw hzReflected)) := by
  simpa [canonicalC3FiniteMixedRadialGreenChannel] using
    (finiteC3MixedRadialGreen_tendsto_completed
      (z := z) (w := w) hw hzReflected)

/-- Off the critical line, the radial coordinate of the full raw ledger is
eventually nonzero. -/
theorem canonicalC3FiniteMixedRawNoLeakRadial_eventually_ne_zero_of_offCritical
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    ∀ᶠ M : ℕ in atTop,
      canonicalC3FiniteMixedRadialGreenChannel M s s ≠ 0 := by
  have hkernel :
      canonicalCompletedC3MixedRadialGreenKernel s s hs.1
          (by simpa [reflectedParameter] using sub_pos.mpr hs.2) ≠ 0 := by
    intro hvanish
    exact hoff
      ((canonicalCompletedC3MixedRadialGreenKernel_self_eq_zero_iff hs).1
        hvanish)
  exact
    (canonicalC3FiniteMixedRadialGreenChannel_tendsto_completed
      hs.1 (by simpa [reflectedParameter] using sub_pos.mpr hs.2)).eventually_ne
        hkernel

/-- Exact no-cancellation witness on the real C3 ledger: at an off-critical
Genuine zero the scalar readout is zero at every cutoff, while the uncollapsed
five-channel state is nonzero at all sufficiently large cutoffs. -/
theorem
    canonicalC3MixedRawNoLeak_scalarZero_but_channelStateEventuallyNonzero_of_offCritical_genuineZero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    ∀ᶠ M : ℕ in atTop,
      canonicalC3MixedRawNoLeakScalarReadout
          (canonicalC3FiniteMixedRawNoLeakChannelState M
            (centeredHeightParameter s) (centeredHeightParameter s)) = 0 ∧
        canonicalC3FiniteMixedRawNoLeakChannelState M
            (centeredHeightParameter s) (centeredHeightParameter s) ≠ 0 := by
  filter_upwards
    [canonicalC3FiniteMixedRawNoLeakRadial_eventually_ne_zero_of_offCritical
      hs hoff] with M hradial
  constructor
  · exact canonicalC3MixedRawNoLeakScalarReadout_eq_zero_at_genuineZero
      M hs hzero
  · intro hstate
    have hfst := congrArg
      (fun x : CanonicalC3MixedRawNoLeakChannelHilbert => x.fst) hstate
    apply hradial
    simpa [canonicalC3FiniteMixedRawNoLeakChannelState] using hfst

/-- Consequently the positive energy of the uncollapsed raw ledger cannot
converge to zero at an off-critical Genuine zero. -/
theorem
    canonicalC3FiniteMixedRawNoLeakChannelEnergy_not_tendsto_zero_of_offCritical
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    ¬ Tendsto
      (fun M : ℕ =>
        canonicalC3FiniteMixedRawNoLeakChannelEnergy M
          (centeredHeightParameter s) (centeredHeightParameter s))
      atTop (nhds 0) := by
  intro henergy
  have hradialSq :
      Tendsto
        (fun M : ℕ =>
          ‖canonicalC3FiniteMixedRadialGreenChannel M s s‖ ^ 2)
        atTop (nhds 0) := by
    apply squeeze_zero
    · intro M
      positivity
    · intro M
      simpa [canonicalC3FiniteMixedRawNoLeakChannelEnergy] using
        (show
          ‖canonicalC3FiniteMixedRadialGreenChannel M s s‖ ^ 2 ≤
            ‖canonicalC3FiniteMixedRadialGreenChannel M s s‖ ^ 2 +
              canonicalC3FiniteMixedHeightStructuralChannelEnergy M s s +
              ‖canonicalC3MixedHeightTailCompletionDefect M
                (centeredHeightParameter s) (centeredHeightParameter s)‖ ^ 2 by
          have hstruct :
              0 ≤ canonicalC3FiniteMixedHeightStructuralChannelEnergy M s s := by
            unfold canonicalC3FiniteMixedHeightStructuralChannelEnergy
            positivity
          have htail :
              0 ≤ ‖canonicalC3MixedHeightTailCompletionDefect M
                (centeredHeightParameter s) (centeredHeightParameter s)‖ ^ 2 :=
            sq_nonneg _
          linarith)
    · simpa [canonicalC3FiniteMixedRawNoLeakChannelEnergy] using henergy
  have hradialZero :
      Tendsto
        (fun M : ℕ => canonicalC3FiniteMixedRadialGreenChannel M s s)
        atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hradialSq
    change Tendsto
      (fun M : ℕ => √(‖canonicalC3FiniteMixedRadialGreenChannel M s s‖ ^ 2))
      atTop (nhds (√0)) at hsqrt
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  have hgreen :=
    canonicalC3FiniteMixedRadialGreenChannel_tendsto_completed
      (z := s) (w := s) hs.1
      (by simpa [reflectedParameter] using sub_pos.mpr hs.2)
  have hkernelZero :
      canonicalCompletedC3MixedRadialGreenKernel s s hs.1
          (by simpa [reflectedParameter] using sub_pos.mpr hs.2) = 0 :=
    tendsto_nhds_unique hgreen hradialZero
  exact hoff
    ((canonicalCompletedC3MixedRadialGreenKernel_self_eq_zero_iff hs).1
      hkernelZero)

end

end CarrySelfAdjointOperator
