import CarrySelfAdjointOperator.BR2RealComplexAllOrderBridge
import CarrySelfAdjointOperator.CompletedNativeRealWeylMoments
import NativeCarrySpectralWeyl.Camera.NativeLineFloor
import Mathlib.Tactic

/-!
# All-order camera bridge to the completed native characteristic

The real finite camera, its exact analytic tail, and the completed native
operator characteristic were previously connected through adjacent APIs.
This file records their direct composition.  The final identity remains
cross-multiplied by the explicit camera factor, so it introduces no division
and is valid independently of every zero set.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- The real native line and the centered operator parameter are the same
complex point. -/
theorem operatorHeightParameter_ofReal_eq_nativeLine (t : ℝ) :
    operatorHeightParameter (t : ℂ) = nativeLine t := by
  apply Complex.ext <;> simp [operatorHeightParameter, nativeLine]

/-- Completing the real finite operator by its exact analytic tail gives the
same all-order jet as the head-plus-tail camera characteristic. -/
theorem completedPackagedFiniteNativeOperatorJet_eq_completedNativeCharacteristic
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (cutoff order : ℕ) (time : ℝ) :
    completedPackagedFiniteNativeOperatorJet camera cutoff order time =
      iteratedDeriv order
        (fun u : ℝ ↦
          completedNativeCharacteristic camera cutoff (nativeLine u)) time := by
  calc
    completedPackagedFiniteNativeOperatorJet camera cutoff order time =
        iteratedDeriv order
          (fun u : ℝ ↦ bracketCharacteristic camera (nativeLine u)) time :=
      completedPackagedFiniteNativeOperatorJet_eq_along_nativeLine
        hcamera cutoff order time
    _ = iteratedDeriv order
          (fun u : ℝ ↦
            completedNativeCharacteristic camera cutoff (nativeLine u)) time := by
      congr 1
      funext u
      exact (completedNativeCharacteristic_eq_bracketCharacteristic
        hcamera (by simp [bracketDomain]; norm_num)).symm

/-- Exact cross-multiplied value bridge from every completed camera to the
camera-independent characteristic `F`. -/
theorem nativeXiCompletionFactor_mul_completedNativeCharacteristic_nativeLine
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (cutoff : ℕ) (time : ℝ) :
    nativeXiCompletionFactor (time : ℂ) *
        completedNativeCharacteristic camera cutoff (nativeLine time) =
      factor camera (nativeLine time) *
        completedNativeOperatorCharacteristic (time : ℂ) := by
  have hdomain :
      operatorHeightParameter (time : ℂ) ∈ nativeScalarDomain := by
    rw [operatorHeightParameter_ofReal_eq_nativeLine]
    simp [nativeScalarDomain]
    norm_num
  have h := nativeXiCompletionFactor_mul_completedNativeCharacteristic
    (camera := camera) (cutoff := cutoff) hcamera hdomain
  rwa [operatorHeightParameter_ofReal_eq_nativeLine] at h

/-- Every completed camera has exactly the same real-height zero set as the
camera-independent characteristic.  Both dressings are discharged by their
already-proved nonvanishing theorems. -/
theorem completedNativeCharacteristic_nativeLine_eq_zero_iff
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (cutoff : ℕ) (time : ℝ) :
    completedNativeCharacteristic camera cutoff (nativeLine time) = 0 ↔
      completedNativeOperatorCharacteristic (time : ℂ) = 0 := by
  have hbridge :=
    nativeXiCompletionFactor_mul_completedNativeCharacteristic_nativeLine
      hcamera cutoff time
  have hstrip :
      operatorHeightParameter (time : ℂ) ∈ genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter]
  constructor
  · intro hcameraZero
    have hproduct :
        factor camera (nativeLine time) *
            completedNativeOperatorCharacteristic (time : ℂ) = 0 := by
      rw [← hbridge, hcameraZero, mul_zero]
    exact (mul_eq_zero.mp hproduct).resolve_left
      (factor_nativeLine_ne_zero hcamera time)
  · intro hcompletedZero
    have hproduct :
        nativeXiCompletionFactor (time : ℂ) *
            completedNativeCharacteristic camera cutoff (nativeLine time) = 0 := by
      rw [hbridge, hcompletedZero, mul_zero]
    exact (mul_eq_zero.mp hproduct).resolve_left
      (nativeXiCompletionFactor_ne_zero hstrip)

/-- At order zero, the real finite native operator with its exact tail has
precisely the real-height zeros of the completed operator characteristic. -/
theorem completedPackagedFiniteNativeOperatorJet_zero_eq_zero_iff
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (cutoff : ℕ) (time : ℝ) :
    completedPackagedFiniteNativeOperatorJet camera cutoff 0 time = 0 ↔
      completedNativeOperatorCharacteristic (time : ℂ) = 0 := by
  rw [completedPackagedFiniteNativeOperatorJet_eq_completedNativeCharacteristic
      hcamera]
  simpa using
    completedNativeCharacteristic_nativeLine_eq_zero_iff
      hcamera cutoff time

/-- Exact camera independence of the completed real zero readout.  In
particular, the cameras `2,3,4,5,6,7` require no separate arithmetic cases. -/
theorem completedPackagedFiniteNativeOperatorJet_zero_camera_independent
    {camera₁ camera₂ : ℕ}
    (hcamera₁ : 2 ≤ camera₁) (hcamera₂ : 2 ≤ camera₂)
    (cutoff₁ cutoff₂ : ℕ) (time : ℝ) :
    completedPackagedFiniteNativeOperatorJet
          camera₁ cutoff₁ 0 time = 0 ↔
      completedPackagedFiniteNativeOperatorJet
          camera₂ cutoff₂ 0 time = 0 := by
  rw [completedPackagedFiniteNativeOperatorJet_zero_eq_zero_iff
      hcamera₁,
    completedPackagedFiniteNativeOperatorJet_zero_eq_zero_iff
      hcamera₂]

/-- The cross-multiplied camera-to-`F` identity holds in every derivative
order.  This is the all-order stitching theorem used by the moment tower. -/
theorem iteratedDeriv_nativeXiCompletionFactor_mul_completedNativeCharacteristic_eq
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (cutoff order : ℕ) (time : ℝ) :
    iteratedDeriv order
        (fun u : ℝ ↦
          nativeXiCompletionFactor (u : ℂ) *
            completedNativeCharacteristic camera cutoff (nativeLine u)) time =
      iteratedDeriv order
        (fun u : ℝ ↦
          factor camera (nativeLine u) *
            completedNativeOperatorCharacteristic (u : ℂ)) time := by
  congr 1
  funext u
  exact
    nativeXiCompletionFactor_mul_completedNativeCharacteristic_nativeLine
      hcamera cutoff u

/-- After exact completion, changing the finite cutoff changes neither the
dressed camera function nor any of its real-axis jets. -/
theorem iteratedDeriv_completedXiDressedCamera_cutoff_independent
    {camera : ℕ} (hcamera : 2 ≤ camera)
    (cutoff₁ cutoff₂ order : ℕ) (time : ℝ) :
    iteratedDeriv order
        (fun u : ℝ ↦
          nativeXiCompletionFactor (u : ℂ) *
            completedNativeCharacteristic camera cutoff₁ (nativeLine u)) time =
      iteratedDeriv order
        (fun u : ℝ ↦
          nativeXiCompletionFactor (u : ℂ) *
            completedNativeCharacteristic camera cutoff₂ (nativeLine u)) time := by
  rw [iteratedDeriv_nativeXiCompletionFactor_mul_completedNativeCharacteristic_eq
      hcamera,
    iteratedDeriv_nativeXiCompletionFactor_mul_completedNativeCharacteristic_eq
      hcamera]

end

end CarrySelfAdjointOperator
