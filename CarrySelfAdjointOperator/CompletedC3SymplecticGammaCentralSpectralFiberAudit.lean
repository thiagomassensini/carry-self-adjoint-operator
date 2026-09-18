import CarrySelfAdjointOperator.CompletedC3SymplecticGammaNormalizedKernelZerothAudit
import CarrySelfAdjointOperator.CanonicalC3SymplecticNaimarkBridge
import NativeCarrySpectralWeyl.Infinite.Naimark
import NativeCarrySpectralWeyl.Infinite.LogarithmicMultiplication
import Mathlib.Tactic

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- The six camera slopes attached to the six real C3 coordinates. -/
theorem canonicalC3RealCoordinateCameraSlope_values :
    (List.ofFn fun j : CanonicalC3RealCoordinate =>
      cameraSlope
        (cameraLabel
          (canonicalC3RealCoordinateCameraIndex j))) =
      [4, 3, 4, 5, 6, 7] := by
  simp only [finiteC3GreenBoundarySpace_real_finrank_eq_six]
  decide

def canonicalC3CommonNaimarkInterval : Set ℝ := Set.Ioc 0 3

theorem canonicalC3CommonNaimarkInterval_subset_cameraInterval
    (j : CanonicalC3RealCoordinate) :
    canonicalC3CommonNaimarkInterval ⊆
      cameraInterval (canonicalC3RealCoordinateCameraIndex j) := by
  intro x hx
  have hj : 3 ≤ cameraSlope
      (cameraLabel (canonicalC3RealCoordinateCameraIndex j)) := by
    have hlabel : 2 ≤
        cameraLabel (canonicalC3RealCoordinateCameraIndex j) := by
      have hmem :=
        (Finset.mem_Icc.mp
          (canonicalC3RealCoordinateCameraIndex_val_mem_Icc_two_seven j)).1
      simpa [cameraLabel] using hmem
    by_cases htwo :
        cameraLabel (canonicalC3RealCoordinateCameraIndex j) = 2
    · simp [htwo]
    · rw [cameraSlope_of_ne_two htwo]
      have hlabel3 : 3 ≤ cameraLabel
          (canonicalC3RealCoordinateCameraIndex j) := by omega
      exact hlabel3
  simp only [canonicalC3CommonNaimarkInterval, cameraInterval] at hx ⊢
  exact ⟨hx.1, by
    exact_mod_cast (le_trans hx.2 (by exact_mod_cast hj :
      (3 : ℝ) ≤ (cameraSlope
        (cameraLabel (canonicalC3RealCoordinateCameraIndex j)) : ℝ)))⟩

theorem canonicalC3RawCameraVector_ae_eq_kolmogorov_on_common
    (j : CanonicalC3RealCoordinate) :
    ∀ᵐ x ∂positiveLebesgueMeasure,
      x ∈ canonicalC3CommonNaimarkInterval →
        (naimarkIsometry (canonicalC3RawCameraVector j)) x =
          kolmogorovVector
            (canonicalC3RealCoordinateCameraIndex j) := by
  rw [show canonicalC3RawCameraVector j =
      cameraVector (canonicalC3RealCoordinateCameraIndex j) from rfl]
  rw [naimarkIsometry_cameraVector]
  filter_upwards [naimarkCameraVector_coeFn
      (canonicalC3RealCoordinateCameraIndex j)] with x hx
  intro hxcommon
  rw [hx]
  rw [Set.indicator_of_mem
    (canonicalC3CommonNaimarkInterval_subset_cameraInterval j hxcommon)]

/-- The Gram--Schmidt camera vectors remain in the span of the raw family. -/
theorem canonicalC3OrthonormalCameraVector_mem_span_raw
    (j : CanonicalC3RealCoordinate) :
    canonicalC3OrthonormalCameraVector j ∈
      Submodule.span ℝ (Set.range canonicalC3RawCameraVector) := by
  unfold canonicalC3OrthonormalCameraVector
  apply Submodule.smul_mem
  have hspan := InnerProductSpace.gramSchmidt_mem_span
    ℝ canonicalC3RawCameraVector (le_refl j)
  exact (Submodule.span_mono (show
      canonicalC3RawCameraVector '' Set.Iic j ⊆
        Set.range canonicalC3RawCameraVector by
      rintro x ⟨i, hi, rfl⟩
      exact ⟨i, rfl⟩)) hspan

/-
Outcome C:
the imported infrastructure gives the span-membership theorem above, but it
does not provide canonical finite Gram--Schmidt coefficients for the
orthonormal vectors.  Consequently the two central common fibers are not
classified here without extracting those coefficients explicitly.
-/

#print axioms canonicalC3RealCoordinateCameraSlope_values
#print axioms canonicalC3CommonNaimarkInterval_subset_cameraInterval
#print axioms canonicalC3RawCameraVector_ae_eq_kolmogorov_on_common
#print axioms canonicalC3OrthonormalCameraVector_mem_span_raw

end

end CarrySelfAdjointOperator
