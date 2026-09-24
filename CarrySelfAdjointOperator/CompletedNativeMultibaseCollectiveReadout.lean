import CarrySelfAdjointOperator.CompletedNativeCameraUniversality
import CarrySelfAdjointOperator.MixedReturnHeightZeroEquivalenceBridge
import Mathlib.Tactic

/-!
# Collective completed-camera blindness on the real height axis

This module is the smallest finite multibase adapter presently justified by
the repository.  `CompletedNativeCameraUniversality` already proves that every
supported *normalized completed camera coordinate* is literally the canonical
completed-native characteristic on the real height axis.  We package those
coordinates into a family-valued readout and prove that its collective
blindness has exactly the same zero locus.

The construction deliberately does **not** identify this family with a future
whitened finite orbit `Q_N e^{-it L_N} j_N`, nor with a Potapov matrix.  Those
objects and the comparison map from them to these completed scalar camera
coordinates have not been formalized.  Thus the result here is an honest
canonical finite-camera readout seam, not an assertion that the empirical
matrix realization has already been imported.

For a finite family, the companion root-free scalar is four times the sum of
the coordinate norm-squares.  Its zero locus is proved algebraically, before
any positivity, HP, Weyl, or spectral argument is used.
-/

open scoped BigOperators

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite

noncomputable section

/-- The canonical multibase coordinate family assembled from the already
completed and factor-normalized camera readouts.  It remains vector-valued:
the scalar `completedNativeOperatorCharacteristic` is not used to define it.
-/
def completedNativeCameraFamilyReadout
    {ι : Type*} (camera cutoff : ι → ℕ) (time : ℝ) : ι → ℂ :=
  fun i => normalizedCompletedNativeCameraCharacteristic
    (camera i) (cutoff i) time

/-- Gate A: every supported coordinate of the canonical multibase family is
literally the completed-native characteristic.  The coordinate has already
absorbed exactly the completed camera and nonvanishing-factor normalization
proved in `CompletedNativeCameraUniversality`. -/
theorem completedNativeCameraFamilyReadout_apply_eq
    {ι : Type*} (camera cutoff : ι → ℕ)
    (hcamera : ∀ i : ι, 2 ≤ camera i)
    (time : ℝ) (i : ι) :
    completedNativeCameraFamilyReadout camera cutoff time i =
      completedNativeOperatorCharacteristic (time : ℂ) := by
  exact congrFun
    (normalizedCompletedNativeCameraCharacteristic_eq (hcamera i) (cutoff i)) time

/-- A nonempty family of supported normalized completed cameras is collectively
blind exactly at the canonical completed-native zero heights. -/
theorem completedNativeCameraFamilyReadout_eq_zero_iff_nativeZero
    {ι : Type*} [Nonempty ι]
    (camera cutoff : ι → ℕ)
    (hcamera : ∀ i : ι, 2 ≤ camera i)
    (time : ℝ) :
    completedNativeCameraFamilyReadout camera cutoff time = 0 ↔
      completedNativeOperatorCharacteristic (time : ℂ) = 0 := by
  constructor
  · intro hblind
    let i : ι := Classical.choice inferInstance
    have hcoordinate :
        normalizedCompletedNativeCameraCharacteristic (camera i) (cutoff i) time = 0 := by
      have happly := congrFun hblind i
      simpa only [completedNativeCameraFamilyReadout, Pi.zero_apply] using happly
    change completedNativeCameraFamilyReadout camera cutoff time i = 0 at hcoordinate
    rw [completedNativeCameraFamilyReadout_apply_eq camera cutoff hcamera time i] at hcoordinate
    exact hcoordinate
  · intro hzero
    funext i
    rw [completedNativeCameraFamilyReadout_apply_eq camera cutoff hcamera time i]
    exact hzero

/-- The canonical collective completed-camera family is a zero-equivalent
height readout.  This is the precise adapter from multibase collective
blindness to the pre-existing height-spectrum bridge. -/
theorem completedNativeCameraFamilyReadout_isZeroEquivalent
    {ι : Type*} [Nonempty ι]
    (camera cutoff : ι → ℕ)
    (hcamera : ∀ i : ι, 2 ≤ camera i) :
    IsZeroEquivalentCompletedNativeHeightReadout
      (completedNativeCameraFamilyReadout camera cutoff) :=
  fun time =>
    completedNativeCameraFamilyReadout_eq_zero_iff_nativeZero camera cutoff hcamera time

/-- Root-free scalar secular for a finite family of completed camera
coordinates.  The factor four matches the usual `4 |Phi|^2` convention; the
coordinate sum is the finite-dimensional norm-square of this particular
family-valued readout. -/
def completedNativeCameraFamilyRootFreeSecular
    {ι : Type*} [Fintype ι]
    (camera cutoff : ι → ℕ) (time : ℝ) : ℝ :=
  4 * ∑ i, Complex.normSq (completedNativeCameraFamilyReadout camera cutoff time i)

/-- The root-free secular vanishes precisely when every coordinate of the
completed camera family vanishes.  This is a finite algebraic fact; it does
not use a spectral theorem or a positive operator certificate. -/
theorem completedNativeCameraFamilyRootFreeSecular_eq_zero_iff
    {ι : Type*} [Fintype ι]
    (camera cutoff : ι → ℕ) (time : ℝ) :
    completedNativeCameraFamilyRootFreeSecular camera cutoff time = 0 ↔
      completedNativeCameraFamilyReadout camera cutoff time = 0 := by
  constructor
  · intro hsecular
    have hsum :
        ∑ i, Complex.normSq (completedNativeCameraFamilyReadout camera cutoff time i) = 0 := by
      exact (mul_eq_zero.mp hsecular).resolve_left (by norm_num)
    funext i
    apply Complex.normSq_eq_zero.mp
    have hterms : ∀ j ∈ (Finset.univ : Finset ι),
        Complex.normSq (completedNativeCameraFamilyReadout camera cutoff time j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Complex.normSq_nonneg _)).mp hsum
    exact hterms i (by simp)
  · intro hblind
    simp only [completedNativeCameraFamilyRootFreeSecular, hblind,
      Pi.zero_apply, Complex.normSq_zero, Finset.sum_const_zero, mul_zero]

/-- The root-free finite multibase secular has the canonical completed-native
zero locus whenever the selected camera family is nonempty and supported. -/
theorem completedNativeCameraFamilyRootFreeSecular_eq_zero_iff_nativeZero
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (camera cutoff : ι → ℕ)
    (hcamera : ∀ i : ι, 2 ≤ camera i)
    (time : ℝ) :
    completedNativeCameraFamilyRootFreeSecular camera cutoff time = 0 ↔
      completedNativeOperatorCharacteristic (time : ℂ) = 0 := by
  rw [completedNativeCameraFamilyRootFreeSecular_eq_zero_iff,
    completedNativeCameraFamilyReadout_eq_zero_iff_nativeZero camera cutoff hcamera]

/-- The root-free scalar is the scalar zero-equivalent handoff suitable for a
future reduced secular/round-trip realization once that realization is proved
equal to this coordinate energy. -/
theorem completedNativeCameraFamilyRootFreeSecular_isZeroEquivalent
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (camera cutoff : ι → ℕ)
    (hcamera : ∀ i : ι, 2 ≤ camera i) :
    IsZeroEquivalentCompletedNativeHeightReadout
      (completedNativeCameraFamilyRootFreeSecular camera cutoff) :=
  fun time =>
    completedNativeCameraFamilyRootFreeSecular_eq_zero_iff_nativeZero
      camera cutoff hcamera time

/-- The concrete supported camera family `2,3,4,5,6,7`. -/
def completedNativeSixCameraCollectiveReadout
    (cutoff : Fin 6 → ℕ) : ℝ → Fin 6 → ℂ :=
  completedNativeCameraFamilyReadout sixCamera cutoff

/-- The concrete six-camera root-free secular. -/
def completedNativeSixCameraRootFreeSecular
    (cutoff : Fin 6 → ℕ) : ℝ → ℝ :=
  completedNativeCameraFamilyRootFreeSecular sixCamera cutoff

/-- Every historical six-camera slot is supported by the individual camera
universality theorem. -/
theorem two_le_sixCamera (i : Fin 6) : 2 ≤ sixCamera i := by
  simp only [sixCamera]
  omega

/-- Concrete collective six-camera blindness is exactly the native completed
characteristic zero condition. -/
theorem completedNativeSixCameraCollectiveReadout_eq_zero_iff_nativeZero
    (cutoff : Fin 6 → ℕ) (time : ℝ) :
    completedNativeSixCameraCollectiveReadout cutoff time = 0 ↔
      completedNativeOperatorCharacteristic (time : ℂ) = 0 := by
  exact completedNativeCameraFamilyReadout_eq_zero_iff_nativeZero
    sixCamera cutoff two_le_sixCamera time

/-- Concrete zero-equivalent six-camera collective readout. -/
theorem completedNativeSixCameraCollectiveReadout_isZeroEquivalent
    (cutoff : Fin 6 → ℕ) :
    IsZeroEquivalentCompletedNativeHeightReadout
      (completedNativeSixCameraCollectiveReadout cutoff) :=
  completedNativeCameraFamilyReadout_isZeroEquivalent
    sixCamera cutoff two_le_sixCamera

/-- Concrete root-free six-camera secular has the same real-axis zero locus
as the canonical completed-native characteristic. -/
theorem completedNativeSixCameraRootFreeSecular_eq_zero_iff_nativeZero
    (cutoff : Fin 6 → ℕ) (time : ℝ) :
    completedNativeSixCameraRootFreeSecular cutoff time = 0 ↔
      completedNativeOperatorCharacteristic (time : ℂ) = 0 := by
  exact completedNativeCameraFamilyRootFreeSecular_eq_zero_iff_nativeZero
    sixCamera cutoff two_le_sixCamera time

/-- Concrete scalar zero-equivalent handoff for the root-free six-camera
secular. -/
theorem completedNativeSixCameraRootFreeSecular_isZeroEquivalent
    (cutoff : Fin 6 → ℕ) :
    IsZeroEquivalentCompletedNativeHeightReadout
      (completedNativeSixCameraRootFreeSecular cutoff) :=
  completedNativeCameraFamilyRootFreeSecular_isZeroEquivalent
    sixCamera cutoff two_le_sixCamera

namespace CompletedNativeRealHPCarrierCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {jet : (ℕ ⊕ ℕ) → E}

/-- Collective blindness of any nonempty supported completed camera family is
an eigenvalue of the already constructed reduced signed-height operator. -/
theorem completedNativeCameraFamily_collectivelyBlind_hasSignedHeightEigenvalue
    {ι : Type*} [Nonempty ι]
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (camera cutoff : ι → ℕ)
    (hcamera : ∀ i : ι, 2 ≤ camera i)
    {time : ℝ}
    (hblind : completedNativeCameraFamilyReadout camera cutoff time = 0) :
    LinearPMap.HasEigenvalue
      certificate.toReducedMaximalSelfAdjointHeightData.selfAdjointData.complexification
      (time : ℂ) := by
  exact certificate.zeroEquivalentReadout_zero_hasSignedHeightEigenvalue
    (completedNativeCameraFamilyReadout_isZeroEquivalent camera cutoff hcamera) hblind

/-- At nonzero height, collective blindness of any nonempty supported
completed camera family is exactly the reciprocal-square Jacobi point
eigenvalue condition. -/
theorem completedNativeCameraFamily_collectivelyBlind_iff_jacobiEigenvalue_inv_sq
    {ι : Type*} [Nonempty ι]
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (camera cutoff : ι → ℕ)
    (hcamera : ∀ i : ι, 2 ≤ camera i)
    {time : ℝ} (htime : time ≠ 0) :
    completedNativeCameraFamilyReadout camera cutoff time = 0 ↔
      LinearPMap.HasEigenvalue
        certificate.completedJacobiEnergySelfAdjointData.complexification
        ((time : ℂ) ^ 2)⁻¹ := by
  exact certificate.zeroEquivalentReadout_zero_iff_jacobiEigenvalue_inv_sq
    (completedNativeCameraFamilyReadout_isZeroEquivalent camera cutoff hcamera) htime

/-- The concrete root-free six-camera secular inherits the pre-existing
signed-height point-spectrum implication without introducing any operator. -/
theorem completedNativeSixCameraRootFreeSecular_zero_hasSignedHeightEigenvalue
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (cutoff : Fin 6 → ℕ) {time : ℝ}
    (hzero : completedNativeSixCameraRootFreeSecular cutoff time = 0) :
    LinearPMap.HasEigenvalue
      certificate.toReducedMaximalSelfAdjointHeightData.selfAdjointData.complexification
      (time : ℂ) := by
  exact certificate.zeroEquivalentReadout_zero_hasSignedHeightEigenvalue
    (completedNativeSixCameraRootFreeSecular_isZeroEquivalent cutoff) hzero

/-- The concrete root-free six-camera secular is equivalent, away from zero
height, to the pre-existing reciprocal-square Jacobi point spectrum. -/
theorem completedNativeSixCameraRootFreeSecular_zero_iff_jacobiEigenvalue_inv_sq
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (cutoff : Fin 6 → ℕ) {time : ℝ} (htime : time ≠ 0) :
    completedNativeSixCameraRootFreeSecular cutoff time = 0 ↔
      LinearPMap.HasEigenvalue
        certificate.completedJacobiEnergySelfAdjointData.complexification
        ((time : ℂ) ^ 2)⁻¹ := by
  exact certificate.zeroEquivalentReadout_zero_iff_jacobiEigenvalue_inv_sq
    (completedNativeSixCameraRootFreeSecular_isZeroEquivalent cutoff) htime

end CompletedNativeRealHPCarrierCertificate

end
end CarrySelfAdjointOperator
