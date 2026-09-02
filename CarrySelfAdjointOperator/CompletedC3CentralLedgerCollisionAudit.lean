import CarrySelfAdjointOperator.CanonicalCompletedC3GammaLedgerNumerator
import CarrySelfAdjointOperator.CompletedC3ConcreteDressedLowOrderAudit
import CarrySelfAdjointOperator.CompletedC3CausalChiralKernelObstruction
import Mathlib.Tactic

/-!
# Central collision audit for the completed C3 ledger

The old finite Green-return scouts suggest a fixed-parameter contraction from
one chiral channel to the other.  On the completed C3 carrier that route is
already obstructed by the thirteen-state kernel audit.  The honest remaining
low-order problem is therefore the collision of the channel-complete ledger.

This file opens that collision without discarding any channel.  It proves:

* the fully channel-separated normalized numerator vanishes at `(0,0)`;
* its first variation in the second leg is exactly the zeroth completed-native
  logarithmic moment `h₀`;
* sewing that first variation to the concrete one-point positive Gram is
  equivalent to the already isolated negative residual-square correction.

The total first variation is thus fixed.  What remains is a channelwise
diagonal-extension theorem identifying how radial, provenance, off-diagonal,
readout-residual, tail-completion, xi-weight, and archimedean contributions
sum to that derivative.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section

/-! ## The channel-separated numerator at a fixed central first leg -/

/-- The completed ledger numerator with its seven scalar channels still
visible, specialized only by fixing the first Hermitian leg at the Taylor
center.  No spectral separation is divided out. -/
def canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator
    (M : ℕ) (w : ℂ) : ℂ :=
  (mixedHermitianWeight nativeXiCompletionFactor w 0 *
        (canonicalC3MixedRadialCoefficient
              (operatorHeightParameter w) (operatorHeightParameter 0) *
            inner ℂ
              (canonicalCompletedC3DirichletGradientPrefixState
                (operatorHeightParameter 0) (3 * M))
              (canonicalCompletedC3DirichletGradientPrefixState
                (reflectedParameter (operatorHeightParameter w)) (3 * M)) +
          canonicalC3FiniteMixedHeightGreenProvenanceChannel M
            (operatorHeightParameter w) (operatorHeightParameter 0) +
          canonicalC3FiniteMixedHeightOffDiagonalChannel M
            (operatorHeightParameter w) (operatorHeightParameter 0) +
          canonicalC3FiniteMixedHeightReadoutResidualChannel M
            (operatorHeightParameter w) (operatorHeightParameter 0) +
          canonicalC3MixedHeightTailCompletionDefect M w 0) +
      canonicalCompletedC3ArchimedeanChartMixedChannel w 0) /
    (mixedHermitianWeight canonicalC3ChartFactorHeight w 0 *
      ((2 : ℂ) *
        conj (completedNativeOperatorCharacteristic 0) *
        completedNativeOperatorCharacteristic w))

/-- Opening the Hilbert ledger state gives exactly the explicit
channel-separated numerator above.  This equality also holds at collision;
it uses neither a separation hypothesis nor a scalar `dslope` cancellation. -/
theorem canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator_eq_ledger
    (M : ℕ) (w : ℂ) :
    canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M w =
      canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M 0 w := by
  unfold canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator
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

/-! ## Collision value and first variation -/

/-- The complete normalized ledger numerator vanishes at the central
collision.  This is cancellation of the total channel ledger, not the
vanishing of its individual coordinates. -/
theorem canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_zero_zero
    (M : ℕ) :
    canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M 0 0 = 0 := by
  rw [canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_response M
    zero_mem_completedNativeHeightDomain
    zero_mem_completedNativeHeightDomain
    completedNativeOperatorCharacteristic_zero_ne_zero
    completedNativeOperatorCharacteristic_zero_ne_zero]
  unfold canonicalCompletedNativePolarizedResponseNumerator
  have hreflection :=
    completedNativeGreenNormalizedResponse_centeredReflection
      (z := (0 : ℂ)) zero_mem_completedNativeHeightDomain
  simpa using sub_eq_zero.mpr hreflection

/-- Consequently the same collision cancellation holds after every channel
has been displayed explicitly. -/
theorem canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator_zero
    (M : ℕ) :
    canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M 0 = 0 := by
  rw [canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator_eq_ledger,
    canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_zero_zero]

/-- Near the center, the fixed-center ledger numerator is exactly the
Hermitian-polarized completed response numerator. -/
theorem
    canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_fixedCenter_eventuallyEq_response
    (M : ℕ) :
    (fun w : ℂ =>
      canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M 0 w) =ᶠ[nhds 0]
      (fun w : ℂ => canonicalCompletedNativePolarizedResponseNumerator 0 w) := by
  have hdomain :
      {w : ℂ | operatorHeightParameter w ∈ genuineCriticalStrip} ∈
        nhds 0 :=
    (hasDerivAt_operatorHeightParameter 0).continuousAt.preimage_mem_nhds
      (isOpen_genuineCriticalStrip.mem_nhds
        zero_mem_completedNativeHeightDomain)
  have hnonzero : ∀ᶠ w : ℂ in nhds 0,
      completedNativeOperatorCharacteristic w ≠ 0 :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero
  filter_upwards [hdomain, hnonzero] with w hw hF
  exact canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_response M
    zero_mem_completedNativeHeightDomain hw
    completedNativeOperatorCharacteristic_zero_ne_zero hF

/-- The first variation of the complete ledger numerator at collision is
exactly `h₀`.  This is the total central-ledger target before any attempt to
assign derivatives to its separate channels. -/
theorem deriv_canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_fixedCenter_zero
    (M : ℕ) :
    deriv
        (fun w : ℂ =>
          canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M 0 w) 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [(canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_fixedCenter_eventuallyEq_response
    M).deriv_eq]
  unfold canonicalCompletedNativePolarizedResponseNumerator
  rw [deriv_sub_const]
  have hmoment := completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical 0
  simpa [completedNativeGreenResponseTaylorCoefficient,
    iteratedDeriv_one] using hmoment

/-- The fully displayed channel sum has the same prescribed first variation
`h₀`. -/
theorem
    deriv_canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator_zero
    (M : ℕ) :
    deriv
        (canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M) 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [show canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M =
      fun w : ℂ =>
        canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M 0 w by
    funext w
    exact canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator_eq_ledger
      M w]
  exact
    deriv_canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_fixedCenter_zero M

/-! ## Exact comparison with the concrete dressed one-point Gram -/

/-- Sewing the central ledger variation to the concrete positive one-point
Gram is exactly vanishing of the concrete dressed central moment defect. -/
theorem
    deriv_fixedCenterChannelSeparatedLedger_eq_dressedGram_re_iff_defect_zero
    (M : ℕ) :
    (deriv
        (canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M) 0).re =
        (canonicalCompletedC3RealAxisPositiveKernel 0 0).re ↔
      canonicalCompletedC3ConcreteDressedCentralMomentDefect = 0 := by
  rw [deriv_canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator_zero]
  unfold canonicalCompletedC3ConcreteDressedCentralMomentDefect
  simp only [Complex.ofReal_re]
  constructor <;> intro h <;> linarith

/-- Final central comparison: the ledger first variation equals the dressed
Gram exactly when the old ordinary/logarithmic defect supplies the negative
square of the retained residual. -/
theorem
    deriv_fixedCenterChannelSeparatedLedger_eq_dressedGram_re_iff_residualBalance
    (M : ℕ) :
    (deriv
        (canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M) 0).re =
        (canonicalCompletedC3RealAxisPositiveKernel 0 0).re ↔
      (inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re -
        canonicalCompletedNativeLogDerivativeMoment 0 =
          -‖canonicalCompletedC3RealAxisResidualState 0‖ ^ 2 := by
  rw [deriv_fixedCenterChannelSeparatedLedger_eq_dressedGram_re_iff_defect_zero,
    canonicalCompletedC3ConcreteDressedCentralMomentDefect_eq_zero_iff]

end

end CarrySelfAdjointOperator
