import CarrySelfAdjointOperator.CanonicalCompletedC3GammaLedgerNumerator
import Mathlib.Tactic

/-!
# Canonical completed C3 gamma/ledger boundary defect

The positive gamma Gram and the completed all-cutoff ledger have already been
reduced to two concrete boundary readouts.  This file records their literal
difference without hiding any ledger channel.  The defect is independent of
the cutoff, and its vanishing is exactly the final gamma--`dslope` sewing.

In particular, completion cannot make this defect disappear by itself: the
normalized completed ledger is already cutoff-independent.  At a nonreal
zero of the completed characteristic the ledger numerator is zero, while the
gamma boundary readout is nonzero.  Thus vanishing of this concrete defect is
precisely the substantive boundary identification.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- The completed ledger numerator with every structural channel visible.
The final division is exactly the normalization used by the polarized
gamma/ledger comparison. -/
def canonicalCompletedC3AllCutoffChannelSeparatedLedgerNumerator
    (M : ℕ) (z w : ℂ) : ℂ :=
  (mixedHermitianWeight nativeXiCompletionFactor w z *
          (canonicalC3MixedRadialCoefficient
                (operatorHeightParameter w) (operatorHeightParameter z) *
              inner ℂ
                (canonicalCompletedC3DirichletGradientPrefixState
                  (operatorHeightParameter z) (3 * M))
                (canonicalCompletedC3DirichletGradientPrefixState
                  (reflectedParameter (operatorHeightParameter w)) (3 * M)) +
            canonicalC3FiniteMixedHeightGreenProvenanceChannel M
              (operatorHeightParameter w) (operatorHeightParameter z) +
            canonicalC3FiniteMixedHeightOffDiagonalChannel M
              (operatorHeightParameter w) (operatorHeightParameter z) +
            canonicalC3FiniteMixedHeightReadoutResidualChannel M
              (operatorHeightParameter w) (operatorHeightParameter z) +
            canonicalC3MixedHeightTailCompletionDefect M w z) +
        canonicalCompletedC3ArchimedeanChartMixedChannel w z) /
      (mixedHermitianWeight canonicalC3ChartFactorHeight w z *
        ((2 : ℂ) *
          conj (completedNativeOperatorCharacteristic z) *
          completedNativeOperatorCharacteristic w))

/-- The named channel-separated numerator is literally the complete ledger
numerator.  No strip, nonvanishing, or separation assumption is used. -/
theorem canonicalCompletedC3AllCutoffChannelSeparatedLedgerNumerator_eq_ledger
    (M : ℕ) (z w : ℂ) :
    canonicalCompletedC3AllCutoffChannelSeparatedLedgerNumerator M z w =
      canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M z w := by
  unfold canonicalCompletedC3AllCutoffChannelSeparatedLedgerNumerator
    canonicalCompletedC3AllCutoffPolarizedLedgerNumerator
    CanonicalCompletedC3AllCutoffKernelLedgerHilbert.finalReadout
    CanonicalCompletedC3AllCutoffKernelLedgerHilbert.rawReadout
    canonicalC3MixedStructuralScalarReadout
  rw [canonicalCompletedC3AllCutoffKernelLedgerState_xiWeight,
    canonicalCompletedC3AllCutoffKernelLedgerState_radial_eq_greenForm,
    greenForm_finiteC3GenuineBracket_twoParameter_eq_coefficient_mul_gram,
    c3RawGammaGram_eq_inner_completedPrefix,
    canonicalCompletedC3AllCutoffKernelLedgerState_greenProvenanceCoordinate,
    canonicalCompletedC3AllCutoffKernelLedgerState_offDiagonalCoordinate,
    canonicalCompletedC3AllCutoffKernelLedgerState_readoutResidualCoordinate,
    canonicalCompletedC3AllCutoffKernelLedgerState_tail,
    canonicalCompletedC3AllCutoffKernelLedgerState_archimedeanChart]
  ring

/-- Literal mismatch between the complete Cauchy boundary readout of the
positive gamma states and the complete normalized ledger numerator. -/
def canonicalCompletedC3GammaLedgerBoundaryDefect
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
    canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M z w

/-- The defect keeps the radial, Green-provenance, off-diagonal, residual,
tail, xi, and archimedean channels visible on the ledger side. -/
theorem canonicalCompletedC3GammaLedgerBoundaryDefect_eq_channelSeparated
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3GammaLedgerBoundaryDefect M z w hz hw =
      canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
        canonicalCompletedC3AllCutoffChannelSeparatedLedgerNumerator M z w := by
  rw [canonicalCompletedC3GammaLedgerBoundaryDefect,
    canonicalCompletedC3AllCutoffChannelSeparatedLedgerNumerator_eq_ledger]

/-- Head--tail completion makes the normalized ledger numerator independent
of the cutoff, even when its denominator vanishes. -/
theorem canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_cutoff_independent
    (M N : ℕ) {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M z w =
      canonicalCompletedC3AllCutoffPolarizedLedgerNumerator N z w := by
  unfold canonicalCompletedC3AllCutoffPolarizedLedgerNumerator
  rw [canonicalCompletedC3AllCutoffKernelLedgerState_finalReadout_cutoff_independent
    M N hwStrip hzStrip]

/-- Consequently the concrete gamma/ledger boundary defect cannot change
with the cutoff. -/
theorem canonicalCompletedC3GammaLedgerBoundaryDefect_cutoff_independent
    (M N : ℕ) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3GammaLedgerBoundaryDefect M z w hz hw =
      canonicalCompletedC3GammaLedgerBoundaryDefect N z w hz hw := by
  unfold canonicalCompletedC3GammaLedgerBoundaryDefect
  rw [canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_cutoff_independent
    M N hzStrip hwStrip]

/-- The cutoff sequence of defects converges to any one of its values because
it is already constant after exact head--tail completion. -/
theorem canonicalCompletedC3GammaLedgerBoundaryDefect_tendsto
    (N : ℕ) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦ canonicalCompletedC3GammaLedgerBoundaryDefect
        M z w hz hw)
      atTop
      (nhds (canonicalCompletedC3GammaLedgerBoundaryDefect N z w hz hw)) := by
  have hconstant :
      (fun M : ℕ ↦ canonicalCompletedC3GammaLedgerBoundaryDefect
          M z w hz hw) =
        (fun _ : ℕ ↦ canonicalCompletedC3GammaLedgerBoundaryDefect
          N z w hz hw) := by
    funext M
    exact canonicalCompletedC3GammaLedgerBoundaryDefect_cutoff_independent
      M N hz hw hzStrip hwStrip
  rw [hconstant]
  exact tendsto_const_nhds

/-- Zero defect is exactly the final positive gamma--`dslope` sewing. -/
theorem canonicalCompletedC3GammaLedgerBoundaryDefect_eq_zero_iff_kernel_eq_dslope
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3GammaLedgerBoundaryDefect M z w hz hw = 0 ↔
      canonicalCompletedC3PolarizedGammaKernel z w hz hw =
        canonicalCompletedNativePolarizedDslopeKernel z w := by
  rw [canonicalCompletedC3GammaLedgerBoundaryDefect, sub_eq_zero]
  exact
    (canonicalCompletedC3PolarizedGammaKernel_eq_dslope_iff_ledgerNumerator
      M z w hz hw hzStrip hwStrip hzF hwF hsep).symm

/-- Passing the defect to the cutoff limit is equivalent to proving the same
pointwise gamma--`dslope` identity; completion contributes no extra
cancellation. -/
theorem canonicalCompletedC3GammaLedgerBoundaryDefect_tendsto_zero_iff
    (N : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    Tendsto
        (fun M : ℕ ↦ canonicalCompletedC3GammaLedgerBoundaryDefect
          M z w hz hw)
        atTop (nhds 0) ↔
      canonicalCompletedC3PolarizedGammaKernel z w hz hw =
        canonicalCompletedNativePolarizedDslopeKernel z w := by
  rw [← canonicalCompletedC3GammaLedgerBoundaryDefect_eq_zero_iff_kernel_eq_dslope
    N z w hz hw hzStrip hwStrip hzF hwF hsep]
  constructor
  · intro hzero
    exact tendsto_nhds_unique
      (canonicalCompletedC3GammaLedgerBoundaryDefect_tendsto
        N hz hw hzStrip hwStrip)
      hzero
  · intro hpoint
    simpa [hpoint] using
      (canonicalCompletedC3GammaLedgerBoundaryDefect_tendsto
        N hz hw hzStrip hwStrip)

/-- The concrete gamma state is nonzero at every nonreal point whose native
parameter lies in the open strip. -/
theorem canonicalCompletedC3PolarizedGammaState_ne_zero
    {z : ℂ} (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hz : z.im ≠ 0) :
    canonicalCompletedC3PolarizedGammaState z hz ≠ 0 := by
  intro hstate
  change
    (carryGammaSource z hz (canonicalCompletedC3SixCameraSource z) :
      WithLp 2 (NaimarkSpace × NaimarkSpace)) = 0 at hstate
  apply canonicalCompletedC3SixCameraSource_ne_zero hzStrip
  apply carryGammaSource_injective z hz
  simpa using hstate

/-- Hence the diagonal polarized gamma boundary readout is nonzero. -/
theorem canonicalCompletedC3PolarizedGammaBoundaryReadout_diagonal_ne_zero
    {z : ℂ} (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hz : z.im ≠ 0) :
    canonicalCompletedC3PolarizedGammaBoundaryReadout z z hz hz ≠ 0 := by
  rw [canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel]
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    intro hconj
    apply hz
    have him : z.im = -z.im := by
      calc
        z.im = (conj z).im := congrArg Complex.im hconj
        _ = -z.im := Complex.conj_im z
    linarith
  · rw [canonicalCompletedC3PolarizedGammaKernel_diagonal_eq_norm_sq]
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr
        (canonicalCompletedC3PolarizedGammaState_ne_zero hzStrip hz)))

/-- At a nonreal zero of the completed characteristic, the normalized ledger
numerator is zero while the positive gamma boundary readout is not.  The
final boundary defect therefore cannot vanish there. -/
theorem canonicalCompletedC3GammaLedgerBoundaryDefect_ne_zero_of_characteristic_zero
    (M : ℕ) {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hz : z.im ≠ 0)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    canonicalCompletedC3GammaLedgerBoundaryDefect M z z hz hz ≠ 0 := by
  have hledger :
      canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M z z = 0 := by
    simp [canonicalCompletedC3AllCutoffPolarizedLedgerNumerator, hzero]
  rw [canonicalCompletedC3GammaLedgerBoundaryDefect, hledger, sub_zero]
  exact canonicalCompletedC3PolarizedGammaBoundaryReadout_diagonal_ne_zero
    hzStrip hz

end

end CarrySelfAdjointOperator
