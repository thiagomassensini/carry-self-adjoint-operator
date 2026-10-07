import CarrySelfAdjointOperator.CompletedC3AdjacentClockCompletion
import CarrySelfAdjointOperator.CompletedNativeChiralReturnPolarizedGreen
import CarrySelfAdjointOperator.CompletedNativeChiralReturnCoisometricSewing

/-!
# Adjacent-clock channels inside the SAME corrected completed ledger

The material-clock terms are synthesized only after both local channels
are retained. Ordered cross, all synthesis residuals, exact tail, Xi and
archimedean/chart completion are the old source-derived channels. This
observation rewrites the existing complete ledger; it supplies no positive
complementary norm or new Hilbert kernel.
-/
namespace CarrySelfAdjointOperator
open CPFormal.Analytic.Cp NativeCarrySpectralWeyl.Boundary
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false

/-- Complete observation built from the independently derived local clock
channels and unchanged full synthesis/completion coordinates. -/
def canonicalCompletedC3AdjacentClockCorrectedReadout (M : ℕ) (z w : ℂ) : ℂ :=
  let sZ := operatorHeightParameter z
  let sW := operatorHeightParameter w
  let x := canonicalC3AllCutoffMixedSourcePrefixState M sZ sW
  mixedHermitianWeight nativeXiCompletionFactor z w *
    (((∑ mr, (canonicalC3AdjacentClockChannelFamily M sZ sW mr).1) +
      (∑ mr, (canonicalC3AdjacentClockChannelFamily M sZ sW mr).2)) +
      x.offDiagonalReadout M + x.heightResidualReadout M +
        canonicalC3MixedHeightTailCompletionDefect M z w) +
    canonicalCompletedC3ArchimedeanChartMixedChannel z w

/-- The input global structured ledger is unchanged. Only its final complete
readout is expanded using the literal local material-clock identity. -/
theorem canonicalCompletedC3AdjacentClockCorrectedReadout_eq_existingLedger
    (M : ℕ) (z w : ℂ) :
    canonicalCompletedC3AdjacentClockCorrectedReadout M z w =
      (canonicalCompletedC3AllCutoffKernelLedgerState M z w).finalReadout := by
  unfold canonicalCompletedC3AdjacentClockCorrectedReadout
  rw [CanonicalCompletedC3AllCutoffKernelLedgerHilbert.finalReadout,
    CanonicalCompletedC3AllCutoffKernelLedgerHilbert.rawReadout,
    canonicalCompletedC3AllCutoffKernelLedgerState_xiWeight,
    canonicalCompletedC3AllCutoffKernelLedgerState_radial_eq_greenForm,
    canonicalCompletedC3AllCutoffKernelLedgerState_structural_eq_sourceReadout,
    canonicalCompletedC3AllCutoffKernelLedgerState_tail,
    canonicalCompletedC3AllCutoffKernelLedgerState_archimedeanChart]
  unfold canonicalC3MixedStructuralScalarReadout
    CanonicalC3AllCutoffMixedSourceHilbert.structuralReadout
  dsimp only
  rw [canonicalC3MixedPrefixGreenProvenance_clockTransport]
  simp only [canonicalC3AllCutoffMixedSourcePrefixState_wSource,
    canonicalC3AllCutoffMixedSourcePrefixState_reflectedZSource,
    canonicalC3AllCutoffGreenPort_prefix_eq, WithLp.toLp_fst, WithLp.toLp_snd]
  ring

/-- Same six-source completed ledger, with no moment coefficient as input. -/
theorem canonicalCompletedC3AdjacentClockCorrectedReadout_eq_sixChannelReadout
    (M : ℕ) (z w : ℂ) :
    canonicalCompletedC3AdjacentClockCorrectedReadout M z w =
      (canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w).finalReadout := by
  rw [canonicalCompletedC3AdjacentClockCorrectedReadout_eq_existingLedger,
    CanonicalCompletedC3AllCutoffKernelLedgerHilbert.finalReadout_eq_mixedChannels_finalReadout,
    canonicalCompletedC3AllCutoffKernelLedgerState_mixedChannels_eq]

/-- Direct completed source identity at EVERY cutoff, with chart/completion
restored. This is a signed Wronskian, not a positive inner product. -/
theorem canonicalCompletedC3AdjacentClockCorrectedReadout_eq_completedWronskian
    (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3AdjacentClockCorrectedReadout M z w =
      mixedHermitianWeight canonicalC3ChartFactorHeight z w *
        completedGreenWronskian completedNativeOperatorCharacteristic
          (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u) z w := by
  rw [canonicalCompletedC3AdjacentClockCorrectedReadout_eq_existingLedger]
  exact canonicalCompletedC3AllCutoffKernelLedgerState_finalReadout_eq_completedWronskian M hz hw

/-- Pointwise equality to the corrected Green numerator already consumed
by the complete independently polarized ChiralReturn synthesis. -/
theorem canonicalCompletedC3AdjacentClockCorrectedReadout_eq_correctedGreenNumerator
    (M : ℕ) (z w : ℂ) :
    let L := canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w
    canonicalCompletedC3AdjacentClockCorrectedReadout M z w =
      mixedHermitianWeight nativeXiCompletionFactor z w *
          canonicalC3BracketTfvdMixedGreenReadout M (operatorHeightParameter z) (operatorHeightParameter w) +
        L.greenProvenance + L.offDiagonal + L.readoutResidual + L.tailCompletion + L.archimedeanChart := by
  dsimp only
  rw [canonicalCompletedC3AdjacentClockCorrectedReadout_eq_sixChannelReadout]
  unfold CanonicalCompletedC3FNegFPrimeMixedChannels.finalReadout
  have hRad : (canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w).radialGreen =
      mixedHermitianWeight nativeXiCompletionFactor z w *
        canonicalC3BracketTfvdMixedGreenReadout M (operatorHeightParameter z) (operatorHeightParameter w) := by
    unfold canonicalCompletedC3FiniteFNegFPrimeMixedChannels
    dsimp only
    rw [canonicalC3BracketTfvdMixedGreenReadout_eq_bracketGreen, Nat.mul_comm M 3]
  rw [hRad]

/-- Empty material head is not empty completed source: its exact tail and
independent completion chart still remain in the readout. -/
theorem canonicalCompletedC3AdjacentClockCorrectedReadout_zero (z w : ℂ) :
    canonicalCompletedC3AdjacentClockCorrectedReadout 0 z w =
      mixedHermitianWeight nativeXiCompletionFactor z w *
        canonicalC3MixedHeightTailCompletionDefect 0 z w +
      canonicalCompletedC3ArchimedeanChartMixedChannel z w := by
  unfold canonicalCompletedC3AdjacentClockCorrectedReadout
  dsimp only
  rw [← canonicalC3MixedPrefixHead_clockTransport]
  simp [CanonicalC3AllCutoffMixedSourceHilbert.valueHeadReadout,
    CanonicalC3AllCutoffMixedSourceHilbert.logJetHeadReadout, mixedScalarBoundaryWedge]

namespace ChiralReturn

/-- Same complete source balance, arbitrary independent coefficient vectors
and internal radii, with all ordered Cauchy cross terms retained. The radial
index k is not a material time or the material cutoff M. -/
theorem polarizedSourceBalance_eq_adjacentClockCorrectedLedger
    (M k : ℕ) {N : ℕ} (c d : Fin N → ℂ) (r s : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    let z := fun i : Fin N => canonicalCompletedC3RadialTiltPoint k i
    let a := fun i : Fin N => c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (z i)
    let b := fun i : Fin N => d i * (s : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (z i)
    polarizedSourceBalance k c d r s = -2 * Complex.I *
      (∑ i : Fin N, ∑ j : Fin N, star (a i) * b j *
        inner ℂ (completedNativeRadialChiralCauchyState k i) (completedNativeRadialChiralCauchyState k j) *
        (canonicalCompletedC3AdjacentClockCorrectedReadout M (z j) (z i) /
          mixedHermitianWeight canonicalC3ChartFactorHeight (z j) (z i))) := by
  rw [polarizedSourceBalance_eq_corrected_green_ledger M k c d r s hstrip]
  dsimp only
  simp_rw [← canonicalCompletedC3AdjacentClockCorrectedReadout_eq_correctedGreenNumerator]

/-- Exact remaining sign as a bound on the PRE-EXISTING geometric correction.
This equivalence proves neither side and introduces no positivity premise. -/
theorem storage_nonnegative_iff_coisometricCorrection_le_energy
    (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hpositive : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    0 ≤ (storage k c r).re ↔
      (coisometricFourChannelBalance k c c r r (fun i => (hstrip i).1)).im ≤
        ‖coisometricSourceSynthesis k c r (fun i => (hstrip i).1)‖ ^ 2 := by
  rw [storage_re_eq_coisometricEnergy_sub_fourChannelBalance 0 k c r hstrip hpositive]
  constructor <;> intro h <;> linarith

end ChiralReturn
end
end CarrySelfAdjointOperator
