import CarrySelfAdjointOperator.NativeGammaMixedSource
import CarrySelfAdjointOperator.NativeGammaCauchyIntegral

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators InnerProductSpace ENNReal MeasureTheory
open Set MeasureTheory NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

def nativeSixPeriodicMean : Matrix (Fin 6) (Fin 6) ℝ :=
  !![3/2,0,5/2,0,4/3,0; 0,2,0,0,2,0; 5/2,0,11/2,0,4/3,0;
    0,0,0,4,0,0; 4/3,2,4/3,0,22/3,0; 0,0,0,0,0,6]

theorem nativeSixPeriodicMean_eq_original (i j : Fin 6) :
    periodicMeanKernel (atlasSixCameraIndex i) (atlasSixCameraIndex j) =
      nativeSixPeriodicMean i j := by
  have h := atlasSixCameraGram_entry_eq_gramKernel i j
  unfold gramKernel at h
  fin_cases i <;> fin_cases j <;>
    norm_num [nativeSixPeriodicMean, sixCameraGram, sixCameraGramRat,
      atlasSixCameraIndex, sixCamera, cameraSlope, cameraLabel] at h ⊢ <;> linarith

def nativeCameraFiber (i : Fin 6) (x : ℝ) : KolmogorovSpace :=
  (cameraInterval (atlasSixCameraIndex i)).indicator
    (fun _ => kolmogorovVector (atlasSixCameraIndex i)) x

def nativeMixedFiber (x : ℝ) : KolmogorovSpace :=
  (-6 : ℝ) • nativeCameraFiber 0 x + (-3 : ℝ) • nativeCameraFiber 1 x +
    (2 : ℝ) • nativeCameraFiber 2 x + (3 : ℝ) • nativeCameraFiber 4 x

def nativeMixedDensity (x : ℝ) : ℝ :=
  if 0 < x then if x ≤ 3 then 32 else if x ≤ 4 then 50 else if x ≤ 6 then 66 else 0
  else 0

theorem nativeCameraFiber_inner (i j : Fin 6) (x : ℝ) :
    inner ℝ (nativeCameraFiber i x) (nativeCameraFiber j x) =
      if (0 < x ∧ x ≤ (cameraSlope (cameraLabel (atlasSixCameraIndex i)) : ℝ)) ∧
        (0 < x ∧ x ≤ (cameraSlope (cameraLabel (atlasSixCameraIndex j)) : ℝ))
        then nativeSixPeriodicMean i j else 0 := by
  classical
  by_cases hp : 0 < x <;>
    by_cases hi : x ≤ (cameraSlope (cameraLabel (atlasSixCameraIndex i)) : ℝ) <;>
    by_cases hj : x ≤ (cameraSlope (cameraLabel (atlasSixCameraIndex j)) : ℝ) <;>
    simp only [nativeCameraFiber, Set.indicator_apply, cameraInterval, Set.mem_Ioc] <;>
    simp [hp, hi, hj,
      inner_kolmogorovVector, nativeSixPeriodicMean_eq_original]

theorem nativeMixedFiber_camera_inner (i : Fin 6) (x : ℝ) :
    inner ℝ (nativeMixedFiber x) (nativeCameraFiber i x) =
      if i = 4 then nativeMixedDensity x / 3 else 0 := by
  unfold nativeMixedFiber
  simp only [inner_add_left, real_inner_smul_left, nativeCameraFiber_inner]
  fin_cases i <;>
    norm_num [nativeSixPeriodicMean, cameraInterval, atlasSixCameraIndex,
      sixCamera, cameraSlope, cameraLabel] <;>
    by_cases hp : 0 < x <;> by_cases h3 : x ≤ 3 <;>
    by_cases h4 : x ≤ 4 <;> by_cases h6 : x ≤ 6 <;>
    simp [nativeMixedDensity, hp, h3, h4, h6] <;> linarith

theorem nativeMixedFiber_norm_sq (x : ℝ) :
    ‖nativeMixedFiber x‖ ^ 2 = nativeMixedDensity x := by
  rw [← real_inner_self_eq_norm_sq]
  nth_rw 2 [nativeMixedFiber]
  simp only [inner_add_right, real_inner_smul_right, nativeMixedFiber_camera_inner]
  simp
  ring

theorem nativeMixedFiber_complement_inner (c : Fin 6 → ℝ) (hc : c 4 = 0) (x : ℝ) :
    inner ℝ (nativeMixedFiber x) (∑ i, c i • nativeCameraFiber i x) = 0 := by
  simp only [inner_sum, real_inner_smul_right, nativeMixedFiber_camera_inner]
  simp [hc]

end
end CarrySelfAdjointOperator.GammaMaterialSewing
