import CarrySelfAdjointOperator.NativeScalarGenuineIdentification
import CarrySelfAdjointOperator.CompletedProductJet
import CPFormal.Analytic.CpGenuineRiemannZetaIdentification
import Mathlib.Tactic

/-!
# Classical comparison of the native scalar

The carry-native identification with the canonical Genuine continuation is
proved independently in `NativeScalarGenuineIdentification`.  This module is
only the downstream comparison with the classical scalar.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Consequently, the native scalar is literally Mathlib's Riemann zeta on
the open critical strip. -/
theorem nativeScalar_eq_riemannZeta
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    nativeScalar s = riemannZeta s := by
  rw [nativeScalar_eq_genuineContinuation hs,
    genuineContinuation_eq_riemannZeta hs]

/-- The completed operator characteristic from the native script is the
standard completed zeta expression wherever its height parameter lies in the
open critical strip. -/
theorem completedNativeOperatorCharacteristic_eq_completedRiemannZeta
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedNativeOperatorCharacteristic z =
      nativeXiCompletionFactor z *
        riemannZeta (operatorHeightParameter z) := by
  rw [completedNativeOperatorCharacteristic,
    nativeScalar_eq_riemannZeta hs]

/-- Classical specialization of the native scalar-zero product reduction. -/
theorem completedNativeOperatorGreenWronskian_at_riemannZeta_zero
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : riemannZeta (operatorHeightParameter z) = 0) :
    completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z z =
      nativeXiCompletionFactor z *
          (starRingEnd ℂ) (nativeXiCompletionFactor z) *
        completedGreenWronskian
          nativeHeightScalar nativeHeightScalarBoundaryCompanion z z := by
  apply completedNativeOperatorGreenWronskian_at_nativeScalar_zero hs
  unfold nativeHeightScalar
  rw [nativeScalar_eq_riemannZeta hs, hzero]

/-- Classical specialization of diagonal Wronskian vanishing. -/
theorem completedNativeOperatorGreenWronskian_eq_zero_at_riemannZeta_zero
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : riemannZeta (operatorHeightParameter z) = 0) :
    completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z z = 0 := by
  apply completedNativeOperatorGreenWronskian_eq_zero_at_nativeScalar_zero hs
  unfold nativeHeightScalar
  rw [nativeScalar_eq_riemannZeta hs, hzero]

end

end CarrySelfAdjointOperator
