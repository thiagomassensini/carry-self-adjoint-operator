import CarrySelfAdjointOperator.CompletedGreenHeightChannelBridge
import CarrySelfAdjointOperator.CanonicalCompletedC3GammaLedgerNumerator
import Mathlib.Tactic

/-!
# Reconciliation of the height-channel bridge with the polarized `dslope`

The height-channel bridge (`CompletedGreenHeightChannelBridge`) expresses the
Herglotz/Pick object as the divided difference
`(a z − conj a w)/(z − conj w)` of the coordinate
`a = completedNativeLogDerivativeHerglotzCoordinate = −F'/F`.

The completed-native transport machinery instead uses the polarized `dslope`
of the normalized response `Psi/(2F) = a/2`, with the conjugate-first
separation `w − conj z` (`canonicalCompletedNativePolarizedDslopeKernel`).

This file proves they are the same object.  The build's polarized `dslope`
kernel is exactly the bridge's Herglotz divided difference, halved, in the
conjugate-first separation.  This closes the `z − conj w` factor end to end:
from the finite native/camera Green identity through to the height spectral
kernel, the separation is carried, not re-derived.
-/

open scoped ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The completed-native normalized response is half the bridge's Herglotz
coordinate `a = −F'/F`; this is the `Psi/(2F)` versus `Psi/F` normalization. -/
theorem completedGreenNormalizedResponse_native_eq_half_coordinate (z : ℂ) :
    completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z =
      completedNativeLogDerivativeHerglotzCoordinate z / 2 := by
  unfold completedGreenNormalizedResponse
    completedNativeLogDerivativeHerglotzCoordinate
    completedNativeOperatorBoundaryCompanion
  ring

/-- The Hermitian-polarized response numerator is the coordinate divided
difference numerator, halved. -/
theorem canonicalCompletedNativePolarizedResponseNumerator_eq_coordinate
    (z w : ℂ) :
    canonicalCompletedNativePolarizedResponseNumerator z w =
      (completedNativeLogDerivativeHerglotzCoordinate w -
          conj (completedNativeLogDerivativeHerglotzCoordinate z)) / 2 := by
  simp only [canonicalCompletedNativePolarizedResponseNumerator,
    completedGreenNormalizedResponse_native_eq_half_coordinate,
    map_div₀, map_ofNat]
  ring

/-- **End-to-end reconciliation.**  The transport machinery's polarized
`dslope` kernel is exactly the bridge's Herglotz divided difference of
`a = −F'/F`, halved, in the conjugate-first separation `w − conj z`.  The
`z − conj w` factor from the finite Green identity is carried verbatim to the
height spectral kernel. -/
theorem canonicalCompletedNativePolarizedDslopeKernel_eq_herglotzDividedDifference
    {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hsep : w ≠ conj z) :
    canonicalCompletedNativePolarizedDslopeKernel z w =
      (completedNativeLogDerivativeHerglotzCoordinate w -
          conj (completedNativeLogDerivativeHerglotzCoordinate z)) /
        ((2 : ℂ) * (w - conj z)) := by
  have hsepNe : w - conj z ≠ 0 := sub_ne_zero.mpr hsep
  have hdslope :
      canonicalCompletedNativePolarizedDslopeKernel z w =
        canonicalCompletedNativePolarizedResponseNumerator z w /
          (w - conj z) := by
    rw [canonicalCompletedNativePolarizedResponseNumerator_eq_mul_dslope
      hzStrip hsep, mul_comm, mul_div_assoc, div_self hsepNe, mul_one]
  rw [hdslope, canonicalCompletedNativePolarizedResponseNumerator_eq_coordinate,
    div_div]

end

end CarrySelfAdjointOperator
