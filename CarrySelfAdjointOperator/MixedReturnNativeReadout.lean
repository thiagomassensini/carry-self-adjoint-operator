import CarrySelfAdjointOperator.CameraReturnVarianceDefect
import CarrySelfAdjointOperator.C3ProjectiveHilbertReadoutKernel
import NativeCarrySpectralWeyl.Camera.ModalEnergy

/-!
# The mixed return ray applied to actual completed camera readouts

The return ray is derived from the camera Gram. Here it acts on the actual
head-plus-tail characteristic of each camera. Its source factor is calculated,
including the sign, rather than assigned by the definition of a modal amplitude.
After removing that factor and applying native completion, the readout is the
characteristic whose moments enter the native operator. This scalar identity
leaves the positive response-kernel identification separate.
-/

open scoped BigOperators

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Camera NativeCarrySpectralWeyl.Finite
open PowerSeries

noncomputable section

/-- Apply the Gram-derived mixed ray to six independently completed camera
heads. Each camera retains its own exact whole-center tail. -/
def mixedReturnCompletedCameraReadout (cutoff : Fin 6 → ℕ) (s : ℂ) : ℂ :=
  ∑ i : Fin 6, (sixCameraMixedReturnRay i : ℂ) *
    completedNativeCharacteristic (sixCamera i) (cutoff i) s

/-- The residual direction has support precisely on cameras 2, 3, 4 and 6. -/
theorem mixedReturnCompletedCameraReadout_eq_four_cameras
    (cutoff : Fin 6 → ℕ) (s : ℂ) :
    mixedReturnCompletedCameraReadout cutoff s =
      -6 * completedNativeCharacteristic 2 (cutoff 0) s -
      3 * completedNativeCharacteristic 3 (cutoff 1) s +
      2 * completedNativeCharacteristic 4 (cutoff 2) s +
      3 * completedNativeCharacteristic 6 (cutoff 4) s := by
  simp [mixedReturnCompletedCameraReadout, sixCameraMixedReturnRay,
    sixCamera, Fin.sum_univ_succ]
  ring

/-- Exact factor of the four-camera combination. The minus sign is fixed
by the orientation of the Gram-derived residual ray. -/
theorem mixedReturn_cameraFactor_identity (s : ℂ) :
    -6 * factor 2 s - 3 * factor 3 s + 2 * factor 4 s + 3 * factor 6 s =
      -4 * (binaryDefectFactor s * factor 3 s) := by
  have htwo : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [show 1 - s = 1 + (-s) by ring, Complex.cpow_add]
    · simp
    · norm_num
  have hthree : (3 : ℂ) ^ (1 - s) = 3 * (3 : ℂ) ^ (-s) := by
    rw [show 1 - s = 1 + (-s) by ring, Complex.cpow_add]
    · simp
    · norm_num
  have hfour : (4 : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * (2 : ℂ) ^ (-s) := by
    convert Complex.natCast_mul_natCast_cpow 2 2 (-s) using 1 <;> norm_num
  have hsix : (6 : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * (3 : ℂ) ^ (-s) := by
    convert Complex.natCast_mul_natCast_cpow 2 3 (-s) using 1 <;> norm_num
  norm_num [factor, c2Factor, oddFactor, evenFactor, binaryDefectFactor]
  rw [htwo, hthree, hfour, hsix]
  ring

/-- Source-level identification of the actual return-ray readout, on the
native scalar strip and for arbitrary camera cutoffs. -/
theorem mixedReturnCompletedCameraReadout_eq_nativeScalar
    (cutoff : Fin 6 → ℕ) {s : ℂ} (hs : s ∈ nativeScalarDomain) :
    mixedReturnCompletedCameraReadout cutoff s =
      (-4 * (binaryDefectFactor s * factor 3 s)) * nativeScalar s := by
  rw [mixedReturnCompletedCameraReadout_eq_four_cameras]
  rw [completedNativeCharacteristic_eq_factor_mul_nativeScalar (by norm_num : 2 ≤ 2) hs,
    completedNativeCharacteristic_eq_factor_mul_nativeScalar (by norm_num : 2 ≤ 3) hs,
    completedNativeCharacteristic_eq_factor_mul_nativeScalar (by norm_num : 2 ≤ 4) hs,
    completedNativeCharacteristic_eq_factor_mul_nativeScalar (by norm_num : 2 ≤ 6) hs]
  calc
    _ = (-6 * factor 2 s - 3 * factor 3 s + 2 * factor 4 s + 3 * factor 6 s) *
          nativeScalar s := by ring
    _ = _ := by rw [mixedReturn_cameraFactor_identity]

/-- The previously defined mixed modal amplitude is realized by this actual
camera combination with its derived scale and orientation. -/
theorem mixedReturnCompletedCameraReadout_eq_modalAmplitude
    (cutoff : Fin 6 → ℕ) {s : ℂ} (hs : s ∈ nativeScalarDomain) :
    mixedReturnCompletedCameraReadout cutoff s = -4 * modalAmplitude .mixed s := by
  rw [mixedReturnCompletedCameraReadout_eq_nativeScalar cutoff hs,
    modalAmplitude_mixed_eq_binaryDefectFactor_mul_factor_three_mul_nativeScalar]
  ring

/-- Independent changes of complete camera cutoffs preserve the mixed
readout, with no synchronization of the head lengths required. -/
theorem mixedReturnCompletedCameraReadout_cutoff_independent
    (cutoff₁ cutoff₂ : Fin 6 → ℕ) {s : ℂ} (hs : s ∈ nativeScalarDomain) :
    mixedReturnCompletedCameraReadout cutoff₁ s =
      mixedReturnCompletedCameraReadout cutoff₂ s := by
  rw [mixedReturnCompletedCameraReadout_eq_nativeScalar cutoff₁ hs,
    mixedReturnCompletedCameraReadout_eq_nativeScalar cutoff₂ hs]

/-- The exact Gram normalization of the raw ray recovers the native modal
energy coefficient `16 / 278 = 8 / 139`. -/
theorem mixedReturnCompletedCameraReadout_normalized_energy
    (cutoff : Fin 6 → ℕ) (t : ℝ) :
    Complex.normSq (mixedReturnCompletedCameraReadout cutoff (nativeLine t)) / 278 =
      modalEnergy .mixed t := by
  have hs : nativeLine t ∈ nativeScalarDomain := by
    simp [nativeScalarDomain]
    norm_num
  rw [mixedReturnCompletedCameraReadout_eq_modalAmplitude cutoff hs]
  simp [Complex.normSq_mul, modalEnergy, modalCoefficient]
  ring

/-- Normalize the actual mixed readout by its computed factor, then apply
the same native completion as the operator. -/
def mixedReturnCompletedHeightCharacteristic
    (cutoff : Fin 6 → ℕ) (t : ℝ) : ℂ :=
  nativeXiCompletionFactor (t : ℂ) *
    (mixedReturnCompletedCameraReadout cutoff (nativeLine t) /
      (-4 * (binaryDefectFactor (nativeLine t) * factor 3 (nativeLine t))))

/-- The selected return ray, with its complete camera ledger, recovers the
native characteristic along the entire real height axis. -/
theorem mixedReturnCompletedHeightCharacteristic_eq
    (cutoff : Fin 6 → ℕ) :
    mixedReturnCompletedHeightCharacteristic cutoff =
      fun t : ℝ => completedNativeOperatorCharacteristic (t : ℂ) := by
  funext t
  have hs : nativeLine t ∈ nativeScalarDomain := by
    simp [nativeScalarDomain]
    norm_num
  have hfactor : -4 * (binaryDefectFactor (nativeLine t) * factor 3 (nativeLine t)) ≠ 0 :=
    mul_ne_zero (by norm_num)
      (mul_ne_zero (binaryDefectFactor_nativeLine_ne_zero t)
        (factor_nativeLine_ne_zero (by norm_num : 2 ≤ 3) t))
  unfold mixedReturnCompletedHeightCharacteristic
  rw [mixedReturnCompletedCameraReadout_eq_nativeScalar cutoff hs,
    mul_div_cancel_left₀ _ hfactor]
  rw [completedNativeOperatorCharacteristic, operatorHeightParameter_ofReal_eq_nativeLine]

/-- Every jet is transported by the same exact characteristic identity. -/
theorem iteratedDeriv_mixedReturnCompletedHeightCharacteristic
    (cutoff : Fin 6 → ℕ) (order : ℕ) (t : ℝ) :
    iteratedDeriv order (mixedReturnCompletedHeightCharacteristic cutoff) t =
      iteratedDeriv order completedNativeOperatorCharacteristic (t : ℂ) := by
  rw [mixedReturnCompletedHeightCharacteristic_eq]
  exact iteratedDeriv_completedNativeOperatorCharacteristic_comp_ofReal order t

/-- Even coefficients extracted from the normalized return-ray readout. -/
def mixedReturnEvenCoefficient (cutoff : Fin 6 → ℕ) (n : ℕ) : ℝ :=
  (((Nat.factorial (2*n) : ℂ)⁻¹ •
    iteratedDeriv (2*n) (mixedReturnCompletedHeightCharacteristic cutoff) 0) : ℂ).re

theorem mixedReturnEvenCoefficient_eq_native (cutoff : Fin 6 → ℕ) :
    mixedReturnEvenCoefficient cutoff = completedNativeRealEvenCharacteristicCoefficient := by
  funext n
  unfold mixedReturnEvenCoefficient completedNativeRealEvenCharacteristicCoefficient
    completedNativeEvenCharacteristicCoefficient completedGreenTaylorJet
  rw [iteratedDeriv_mixedReturnCompletedHeightCharacteristic]
  simp only [Complex.ofReal_zero]

/-- Formal mass extracted from this complete return-ray readout. -/
def mixedReturnReciprocalMass (cutoff : Fin 6 → ℕ) : PowerSeries ℝ :=
  (C (mixedReturnEvenCoefficient cutoff 0)⁻¹ * mk (mixedReturnEvenCoefficient cutoff))⁻¹

/-- The scalar mass of the selected return-ray readout is exactly the native
reciprocal characteristic; no Gram identification is assumed. -/
theorem mixedReturnReciprocalMass_eq_native (cutoff : Fin 6 → ℕ) :
    mixedReturnReciprocalMass cutoff = normalizedCompletedNativeEvenFormalSeries⁻¹ := by
  unfold mixedReturnReciprocalMass
  rw [mixedReturnEvenCoefficient_eq_native]
  rfl

end
end CarrySelfAdjointOperator
