import CarrySelfAdjointOperator.CompletedNativeIndependentReflectedSixSourceLift

/-!
# Dependency audit for the independent-reflected C3 lift

The independent-reflected lift separates the historical reflected coordinate
before six-source TFVD analysis.  This file records, through small source
projection lemmas rather than a wholesale unfolding of reconstruction, which
of the two independent coordinates reaches each Green port.
-/

open scoped BigOperators lp ENNReal NNReal ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary

noncomputable section
set_option autoImplicit false

/-- The `w` pair of six-source analyses is independent of both independent
coordinates: that role is fixed at `operatorHeightParameter 0`. -/
theorem cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis_wSource_independent
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (u₁ v₁ u₂ v₂ : ℂ) (camera : ℕ) :
    (cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis
      M q S u₁ v₁ camera).2.1 =
    (cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis
      M q S u₂ v₂ camera).2.1 := by
  change
    ((cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses
        M q S u₁ v₁ (.w, .ordinary)) camera,
      (cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses
        M q S u₁ v₁ (.w, .logJet)) camera) =
      ((cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses
        M q S u₂ v₂ (.w, .ordinary)) camera,
        (cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses
          M q S u₂ v₂ (.w, .logJet)) camera)
  rfl

/-- The reflected-`z` pair of six-source analyses depends on the independent
reflected coordinate only; changing `u` leaves it unchanged. -/
theorem cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis_reflectedZSource_independent_u
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (u₁ u₂ v : ℂ) (camera : ℕ) :
    (cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis
      M q S u₁ v camera).2.2 =
    (cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis
      M q S u₂ v camera).2.2 := by
  change
    ((cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses
        M q S u₁ v (.reflectedZ, .ordinary)) camera,
      (cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses
        M q S u₁ v (.reflectedZ, .logJet)) camera) =
      ((cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses
        M q S u₂ v (.reflectedZ, .ordinary)) camera,
        (cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses
          M q S u₂ v (.reflectedZ, .logJet)) camera)
  rfl

/-- Reconstructing the `w` source uses only the `w` pair of TFVD analyses. -/
theorem canonicalC3AllCutoffMixedSourceTfvdReconstruction_wSource_congr
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data₁ data₂ : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S)
    (h : data₁.2.1 = data₂.2.1) :
    (canonicalC3AllCutoffMixedSourceTfvdReconstruction q hq0 hq1 S data₁).wSource =
      (canonicalC3AllCutoffMixedSourceTfvdReconstruction q hq0 hq1 S data₂).wSource := by
  unfold canonicalC3AllCutoffMixedSourceTfvdReconstruction
    CanonicalC3AllCutoffMixedSourceHilbert.wSource
  simp only [WithLp.toLp_snd, WithLp.toLp_fst]
  rw [h]

/-- Reconstructing the reflected source uses only the reflected-`z` pair of
TFVD analyses. -/
theorem canonicalC3AllCutoffMixedSourceTfvdReconstruction_reflectedZSource_congr
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data₁ data₂ : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S)
    (h : data₁.2.2 = data₂.2.2) :
    (canonicalC3AllCutoffMixedSourceTfvdReconstruction q hq0 hq1 S data₁).reflectedZSource =
      (canonicalC3AllCutoffMixedSourceTfvdReconstruction q hq0 hq1 S data₂).reflectedZSource := by
  unfold canonicalC3AllCutoffMixedSourceTfvdReconstruction
    CanonicalC3AllCutoffMixedSourceHilbert.reflectedZSource
  simp only [WithLp.toLp_snd]
  rw [h]

/-- The reconstructed `w` source is constant over the independent-reflected
plane.  This is a source-projection theorem, not a full reconstruction unfold. -/
theorem cameraResolvedIndependentReflectedSixSourceReconstruction_wSource_independent
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (u₁ v₁ u₂ v₂ : ℂ) (camera : ℕ) :
    (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
      M q hq0 hq1 S u₁ v₁ camera).wSource =
    (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
      M q hq0 hq1 S u₂ v₂ camera).wSource := by
  apply canonicalC3AllCutoffMixedSourceTfvdReconstruction_wSource_congr
  exact cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis_wSource_independent
    M q S u₁ v₁ u₂ v₂ camera

/-- The reconstructed reflected source is independent of `u` when the
independent reflected coordinate `v` is held fixed. -/
theorem cameraResolvedIndependentReflectedSixSourceReconstruction_reflectedZSource_independent_u
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (u₁ u₂ v : ℂ) (camera : ℕ) :
    (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
      M q hq0 hq1 S u₁ v camera).reflectedZSource =
    (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
      M q hq0 hq1 S u₂ v camera).reflectedZSource := by
  apply canonicalC3AllCutoffMixedSourceTfvdReconstruction_reflectedZSource_congr
  exact cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis_reflectedZSource_independent_u
    M q S u₁ u₂ v camera

/-- The direct Green port is constant in both independent coordinates. -/
theorem cameraResolvedIndependentReflectedDirectGreenPort_independent
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (u₁ v₁ u₂ v₂ : ℂ) (camera : ℕ) :
    cameraResolvedIndependentReflectedDirectGreenPort M q hq0 hq1 S u₁ v₁ camera =
      cameraResolvedIndependentReflectedDirectGreenPort M q hq0 hq1 S u₂ v₂ camera := by
  unfold cameraResolvedIndependentReflectedDirectGreenPort
  rw [cameraResolvedIndependentReflectedSixSourceReconstruction_wSource_independent]

/-- The reflected Green port is independent of `u`; its possible variable
dependence is entirely through the independent reflected coordinate `v`. -/
theorem cameraResolvedIndependentReflectedReflectedGreenPort_independent_u
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (u₁ u₂ v : ℂ) (camera : ℕ) :
    cameraResolvedIndependentReflectedReflectedGreenPort M q hq0 hq1 S u₁ v camera =
      cameraResolvedIndependentReflectedReflectedGreenPort M q hq0 hq1 S u₂ v camera := by
  unfold cameraResolvedIndependentReflectedReflectedGreenPort
  rw [cameraResolvedIndependentReflectedSixSourceReconstruction_reflectedZSource_independent_u]

/-- Each independent-reflected pair Green kernel is independent of `u`.
The conjugate-linear Green slot is the constant direct port. -/
theorem canonicalC3CameraResolvedIndependentReflectedGreenKernel_independent_u
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (u₁ u₂ v : ℂ) (directCamera reflectedCamera : ℕ) :
    canonicalC3CameraResolvedIndependentReflectedGreenKernel M q hq0 hq1 S
      u₁ v directCamera reflectedCamera =
    canonicalC3CameraResolvedIndependentReflectedGreenKernel M q hq0 hq1 S
      u₂ v directCamera reflectedCamera := by
  unfold canonicalC3CameraResolvedIndependentReflectedGreenKernel
  rw [cameraResolvedIndependentReflectedDirectGreenPort_independent,
    cameraResolvedIndependentReflectedReflectedGreenPort_independent_u]

/-! ## The remaining radial obstruction -/

/-- The radial normalization retained by the existing Green-port extractor,
viewed along the independent reflected height coordinate.  This is distinct
from the physical-section conjugation: it is a real-coordinate dependence
already present in `greenPort`. -/
def canonicalC3IndependentReflectedRadialDisplacement (v : ℂ) : ℂ :=
  ((criticalDisplacement (operatorHeightParameter v).re : ℝ) : ℂ)

/-- Along `operatorHeightParameter`, the radial displacement is minus the
imaginary coordinate.  This makes the remaining non-complex-linear dependence
explicit before any attempt to prove analytic regularity of Green ports. -/
theorem canonicalC3IndependentReflectedRadialDisplacement_eq_neg_im
    (v : ℂ) :
    canonicalC3IndependentReflectedRadialDisplacement v = -((v.im : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [canonicalC3IndependentReflectedRadialDisplacement,
      criticalDisplacement, operatorHeightParameter]

/-- The radial coordinate used by the current `greenPort` presentation is not
complex differentiable at the centered height.  The proof reduces it directly
to the already established non-differentiability of complex conjugation. -/
theorem canonicalC3IndependentReflectedRadialDisplacement_not_differentiableAt_zero :
    ¬ DifferentiableAt ℂ canonicalC3IndependentReflectedRadialDisplacement 0 := by
  intro h
  have hscaled := h.const_smul ((2 : ℂ) * Complex.I)
  change DifferentiableAt ℂ
    (fun v : ℂ => ((2 : ℂ) * Complex.I) *
      canonicalC3IndependentReflectedRadialDisplacement v) 0 at hscaled
  have hsum := differentiableAt_id.add hscaled
  change DifferentiableAt ℂ
    (fun v : ℂ => v + ((2 : ℂ) * Complex.I) *
      canonicalC3IndependentReflectedRadialDisplacement v) 0 at hsum
  have hconj :
      (fun v : ℂ => v + ((2 : ℂ) * Complex.I) *
        canonicalC3IndependentReflectedRadialDisplacement v) =
        fun v : ℂ => (starRingEnd ℂ) v := by
    funext v
    rw [canonicalC3IndependentReflectedRadialDisplacement_eq_neg_im]
    apply Complex.ext <;> simp <;> ring
  rw [hconj] at hsum
  exact complexConjugation_not_differentiableAt_zero hsum

/-- Consequently the radial coordinate is not complex analytic at the
center.  This is the earliest concrete analytic obstruction remaining after
the reflected six-source role has been made independent. -/
theorem canonicalC3IndependentReflectedRadialDisplacement_not_analyticAt_zero :
    ¬ AnalyticAt ℂ canonicalC3IndependentReflectedRadialDisplacement 0 := by
  intro h
  exact canonicalC3IndependentReflectedRadialDisplacement_not_differentiableAt_zero
    h.differentiableAt

/-- Coordinate-level exposure of the radial normalization in the reflected
camera port.  It does not assert that an individual port fails to be
analytic—its source coordinate might vanish or cancel—but it records the
precise non-holomorphic factor that blocks a uniform port-wise proof by
composition alone. -/
theorem cameraResolvedIndependentReflectedReflectedGreenPort_fst_apply
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) (camera : ℕ)
    (n : Fin (3 * M)) :
    (cameraResolvedIndependentReflectedReflectedGreenPort
      M q hq0 hq1 S u v camera).1 n =
      (((3 : ℝ) ^
          (-criticalDisplacement (operatorHeightParameter v).re) : ℝ) : ℂ) *
        (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
          M q hq0 hq1 S u v camera).reflectedZSource.1 (n : ℕ) := by
  rfl

/-- The non-holomorphic radial scalar appearing in the first coordinate of
the reflected port is exactly the real-power function of the explicit
displacement audit coordinate. -/
theorem cameraResolvedIndependentReflectedReflectedGreenPort_radialFactor_eq
    (v : ℂ) :
    (((3 : ℝ) ^
        (-criticalDisplacement (operatorHeightParameter v).re) : ℝ) : ℂ) =
      (((3 : ℝ) ^
        (-((canonicalC3IndependentReflectedRadialDisplacement v).re)) : ℝ) : ℂ) := by
  congr 2

end

end CarrySelfAdjointOperator
