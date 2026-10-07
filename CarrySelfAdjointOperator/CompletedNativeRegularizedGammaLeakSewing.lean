import CarrySelfAdjointOperator.CompletedNativeChiralReturnGammaPortTest
import CarrySelfAdjointOperator.CompletedNativeChiralReturnCompletionSplit
import CarrySelfAdjointOperator.CompletedNativeCentralChiralEnergyFlow

/-!
# Regularized four-channel sewing with the same complete vector source

Normalize both resolved source channels by the already canonical sqrt(2)*F.
Their synthesis precedes the pairing. Compare their full Gram expansion with
both parts of the old material/completion Green form, without identifying the
carriers or their metrics. No new target-defined vector or metric is used.
-/
namespace CarrySelfAdjointOperator
open CPFormal.Analytic.Cp NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Boundary
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false

/-- The old Gamma port response with the unchanged characteristic normalization. -/
def canonicalCompletedC3NormalizedGammaPortResponse
    (z : ℂ) (hz : z.im ≠ 0) (hs : 0 < (operatorHeightParameter z).re) :
    CarryGammaComplexNaimark :=
  ((((Real.sqrt 2 : ℝ) : ℂ) * completedNativeOperatorCharacteristic z)⁻¹) •
    canonicalCompletedC3GammaNaimarkView
      (carryGammaSource z hz (canonicalCompletedC3CoisometricCompressedSourceLimit z hs))

/-- The retained leak is resolved and normalized in the same existing Hilbert carrier. -/
def canonicalCompletedC3NormalizedResolvedLeakResponse
    (z : ℂ) (hz : z.im ≠ 0) (hs : 0 < (operatorHeightParameter z).re) :
    CarryGammaComplexNaimark :=
  ((((Real.sqrt 2 : ℝ) : ℂ) * completedNativeOperatorCharacteristic z)⁻¹) •
    canonicalCompletedC3GammaNaimarkView
      (logarithmicResolventBlock z hz (canonicalCompletedC3CoisometricNaimarkLeakLimit z hs))

/-- Exact vector synthesis; not a decomposition inferred from scalar traces. -/
theorem canonicalCompletedC3NormalizedAmbientResponse_eq_gammaPort_add_resolvedLeak
    (z : ℂ) (hz : z.im ≠ 0) (hs : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3NormalizedAmbientResponseState z hs =
      canonicalCompletedC3NormalizedGammaPortResponse z hz hs +
        canonicalCompletedC3NormalizedResolvedLeakResponse z hz hs := by
  unfold canonicalCompletedC3NormalizedAmbientResponseState
    canonicalCompletedC3AmbientResponseState
  rw [canonicalCompletedC3AmbientResponse_eq_gammaPort_add_resolvedLeak,
    canonicalCompletedC3GammaNaimarkView_add, smul_add]
  rfl

/-- All four ordered pairings of geometrically produced resolved channels.
No moment, dslope, desired Gram, or completion coefficient defines this readout. -/
def canonicalCompletedC3NormalizedGammaLeakPairing
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re)
    (ht : 0 < (operatorHeightParameter w).re) : ℂ :=
  let g := canonicalCompletedC3NormalizedGammaPortResponse
  let l := canonicalCompletedC3NormalizedResolvedLeakResponse
  inner ℂ (g z hz hs) (g w hw ht) + inner ℂ (g z hz hs) (l w hw ht) +
    (inner ℂ (l z hz hs) (g w hw ht) + inner ℂ (l z hz hs) (l w hw ht))

/-- The full old normalized Gram, with neither ordered cross term erased. -/
theorem canonicalCompletedC3NormalizedAmbientKernel_eq_gammaLeakPairing
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re)
    (ht : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3NormalizedAmbientResponseKernel z w hs ht =
      canonicalCompletedC3NormalizedGammaLeakPairing z w hz hw hs ht := by
  rw [canonicalCompletedC3NormalizedAmbientResponseKernel_eq_inner,
    canonicalCompletedC3NormalizedAmbientResponse_eq_gammaPort_add_resolvedLeak z hz hs,
    canonicalCompletedC3NormalizedAmbientResponse_eq_gammaPort_add_resolvedLeak w hw ht,
    inner_add_left, inner_add_right, inner_add_right]
  rfl

/-- Separation and characteristic weight are both required. This compares
resolved port/leak vectors with the old material/completion form, not with
an invented complement. -/
theorem canonicalCompletedC3RegularizedFourChannel_eq_gammaLeak_sub_materialCompletion
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (ht : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3CoisometricWronskianFourChannelDefect z w hz hw hs.1 ht.1 /
        (canonicalCompletedC3GammaCharacteristicWeight z w * (w - conj z)) =
      canonicalCompletedC3NormalizedGammaLeakPairing z w hz hw hs.1 ht.1 -
        ((starRingEnd ℂ) (nativeXiCompletionFactor z) * nativeXiCompletionFactor w *
            canonicalNativeUndressedGreenForm z w +
          canonicalArchimedeanBoundaryGreenCorrection z w) /
          (canonicalCompletedC3GammaCharacteristicWeight z w * (w - conj z)) := by
  rw [canonicalCompletedC3CoisometricWronskianFourChannelDefect_eq_sub z w hz hw hs ht,
    ← canonicalCompletedC3AmbientBoundaryReadout_eq_coisometricCompressed,
    canonicalCompletedC3AmbientBoundaryReadout_eq_kernel z w hz hw hs.1 ht.1,
    completedC3Wronskian_eq_scalarBoundaryGreenForm,
    canonicalCompletedC3ScalarGreenForm_eq_scaledNative_add_archimedeanCorrection hs ht,
    sub_div]
  rw [← canonicalCompletedC3NormalizedAmbientKernel_eq_gammaLeakPairing]
  unfold canonicalCompletedC3NormalizedAmbientResponseKernel
    canonicalCompletedC3AmbientResponseKernel canonicalCompletedC3AmbientResponseState
  have hn : w - conj z ≠ 0 := sub_ne_zero.mpr hsep
  congr 1
  rw [mul_comm (canonicalCompletedC3GammaCharacteristicWeight z w) (w - conj z)]
  exact mul_div_mul_left _ _ hn

/-- The dslope comparison is obtained only after the vector Gram is formed,
with both nonzero characteristic values and the exact separated argument order. -/
theorem canonicalCompletedC3RegularizedFourChannel_eq_gammaLeak_sub_dslope
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (ht : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3CoisometricWronskianFourChannelDefect z w hz hw hs.1 ht.1 /
        (canonicalCompletedC3GammaCharacteristicWeight z w * (w - conj z)) =
      canonicalCompletedC3NormalizedGammaLeakPairing z w hz hw hs.1 ht.1 -
        canonicalCompletedNativePolarizedDslopeKernel z w := by
  rw [canonicalCompletedC3CoisometricWronskianFourChannelDefect_eq_sub z w hz hw hs ht,
    ← canonicalCompletedC3AmbientBoundaryReadout_eq_coisometricCompressed,
    canonicalCompletedC3AmbientBoundaryReadout_eq_kernel z w hz hw hs.1 ht.1, sub_div]
  have hW := canonicalC3BracketTfvdCompletedWronskianReadout_div_weight_eq_mul_dslope
    0 hs ht hzF hwF hsep
  rw [canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime 0 ht hs] at hW
  rw [show (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u) =
      completedNativeOperatorBoundaryCompanion by
    funext u; exact (completedNativeOperatorBoundaryCompanion_eq_neg_deriv u).symm] at hW
  have hn : w - conj z ≠ 0 := sub_ne_zero.mpr hsep
  have hWdiv : completedGreenWronskian completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion w z /
        (canonicalCompletedC3GammaCharacteristicWeight z w * (w - conj z)) =
      canonicalCompletedNativePolarizedDslopeKernel z w := by
    rw [← div_div, hW]
    exact mul_div_cancel_left₀ _ hn
  rw [hWdiv, ← canonicalCompletedC3NormalizedAmbientKernel_eq_gammaLeakPairing]
  unfold canonicalCompletedC3NormalizedAmbientResponseKernel
    canonicalCompletedC3AmbientResponseKernel canonicalCompletedC3AmbientResponseState
  congr 1
  rw [mul_comm (canonicalCompletedC3GammaCharacteristicWeight z w) (w - conj z)]
  exact mul_div_mul_left _ _ hn

/-- The existing regularized radial defect is exactly the four resolved
pairings minus the old dslope kernel. This uses the ambient radial grid,
without identifying it with the distinct chiral sampling grid. -/
theorem canonicalCompletedC3RegularizedAmbientDefect_eq_gammaLeak_sub_dslope
    (k N : ℕ) (i j : Fin N) :
    let z := canonicalCompletedC3AmbientRadialTiltPoint k N i
    let w := canonicalCompletedC3AmbientRadialTiltPoint k N j
    canonicalCompletedC3RegularizedAmbientRadialDslopeDefect k N i j =
      canonicalCompletedC3NormalizedGammaLeakPairing z w
        (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k N i)
        (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k N j)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N j) -
      canonicalCompletedNativePolarizedDslopeKernel z w := by
  dsimp only
  rw [canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_eq_kernel_sub,
    canonicalCompletedC3NormalizedAmbientKernel_eq_gammaLeakPairing]

/-- Product-rule Green readout, regularized only after its two source parts
are retained. This is a scalar contraction, not a Hilbert identification. -/
theorem canonicalCompletedC3Dslope_eq_materialCompletion_div
    {z w : ℂ}
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (ht : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedNativePolarizedDslopeKernel z w =
      ((starRingEnd ℂ) (nativeXiCompletionFactor z) * nativeXiCompletionFactor w *
          canonicalNativeUndressedGreenForm z w +
        canonicalArchimedeanBoundaryGreenCorrection z w) /
        (canonicalCompletedC3GammaCharacteristicWeight z w * (w - conj z)) := by
  have hW := canonicalC3BracketTfvdCompletedWronskianReadout_div_weight_eq_mul_dslope
    0 hs ht hzF hwF hsep
  rw [canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime 0 ht hs] at hW
  rw [show (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u) =
      completedNativeOperatorBoundaryCompanion by
    funext u; exact (completedNativeOperatorBoundaryCompanion_eq_neg_deriv u).symm] at hW
  rw [completedC3Wronskian_eq_scalarBoundaryGreenForm,
    canonicalCompletedC3ScalarGreenForm_eq_scaledNative_add_archimedeanCorrection hs ht] at hW
  rw [← div_div, hW]
  exact (mul_div_cancel_left₀ _ (sub_ne_zero.mpr hsep)).symm

/-- Exact radial comparison with the material and completion terms. No
cancellation or sign of this difference is inferred. -/
theorem canonicalCompletedC3RegularizedAmbientDefect_eq_gammaLeak_sub_materialCompletion
    (k N : ℕ) (i j : Fin N)
    (hiF : completedNativeOperatorCharacteristic
      (canonicalCompletedC3AmbientRadialTiltPoint k N i) ≠ 0)
    (hjF : completedNativeOperatorCharacteristic
      (canonicalCompletedC3AmbientRadialTiltPoint k N j) ≠ 0) :
    let z := canonicalCompletedC3AmbientRadialTiltPoint k N i
    let w := canonicalCompletedC3AmbientRadialTiltPoint k N j
    canonicalCompletedC3RegularizedAmbientRadialDslopeDefect k N i j =
      canonicalCompletedC3NormalizedGammaLeakPairing z w
        (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k N i)
        (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k N j)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N j) -
      ((starRingEnd ℂ) (nativeXiCompletionFactor z) * nativeXiCompletionFactor w *
          canonicalNativeUndressedGreenForm z w +
        canonicalArchimedeanBoundaryGreenCorrection z w) /
        (canonicalCompletedC3GammaCharacteristicWeight z w * (w - conj z)) := by
  dsimp only
  rw [canonicalCompletedC3RegularizedAmbientDefect_eq_gammaLeak_sub_dslope]
  rw [canonicalCompletedC3Dslope_eq_materialCompletion_div
    (canonicalCompletedC3AmbientRadialTiltPoint_mem_genuineCriticalStrip k N i)
    (canonicalCompletedC3AmbientRadialTiltPoint_mem_genuineCriticalStrip k N j)
    hiF hjF (sub_ne_zero.mp (canonicalCompletedC3AmbientRadialTilt_separation_ne_zero k N i j))]

/-- The existing complete regularized correction ledger itself is eventually
this resolved four-pairing minus the material/completion contraction. No
new ledger replaces the old one, and no channel is set to zero. -/
theorem canonicalCompletedC3RegularizedLedger_eventually_eq_gammaLeak_sub_materialCompletion
    (M N : ℕ) (i j : Fin N) :
    (fun k => canonicalCompletedC3RegularizedAmbientRadialCorrectionLedger k N i j) =ᶠ[
      Filter.atTop] (fun k =>
      let z := canonicalCompletedC3AmbientRadialTiltPoint k N i
      let w := canonicalCompletedC3AmbientRadialTiltPoint k N j
      canonicalCompletedC3NormalizedGammaLeakPairing z w
        (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k N i)
        (canonicalCompletedC3AmbientRadialTiltPoint_im_ne_zero k N j)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N i)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k N j) -
      ((starRingEnd ℂ) (nativeXiCompletionFactor z) * nativeXiCompletionFactor w *
          canonicalNativeUndressedGreenForm z w +
        canonicalArchimedeanBoundaryGreenCorrection z w) /
        (canonicalCompletedC3GammaCharacteristicWeight z w * (w - conj z))) := by
  filter_upwards
    [canonicalCompletedC3NormalizedAmbientRadialDslopeDefect_eventually_eq_ledger M N i j,
      canonicalCompletedC3AmbientRadialTiltPoint_eventually_characteristic_ne_zero N i,
      canonicalCompletedC3AmbientRadialTiltPoint_eventually_characteristic_ne_zero N j]
      with k hk hiF hjF
  have hreg : canonicalCompletedC3RegularizedAmbientRadialDslopeDefect k N i j =
      canonicalCompletedC3RegularizedAmbientRadialCorrectionLedger k N i j := by
    unfold canonicalCompletedC3RegularizedAmbientRadialDslopeDefect
      canonicalCompletedC3RegularizedAmbientRadialCorrectionLedger
    rw [hk]
  rw [← hreg]
  exact canonicalCompletedC3RegularizedAmbientDefect_eq_gammaLeak_sub_materialCompletion
    k N i j hiF hjF

end
end CarrySelfAdjointOperator
