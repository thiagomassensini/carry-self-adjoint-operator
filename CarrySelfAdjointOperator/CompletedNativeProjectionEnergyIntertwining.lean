import CarrySelfAdjointOperator.CompletedC3NaimarkCoisometricBlock
import CarrySelfAdjointOperator.CarryTfvdTraceMetricKernel
import CarrySelfAdjointOperator.MultibaseCameraLogTfvdChannelTransport
import Mathlib.Tactic

open scoped InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-! The primary camera identity is the polarized lossless analysis identity.
It is stronger than a finite Gram equality and does not mention Hankel or
Jacobi coordinates. -/
theorem canonicalCompletedC3NaimarkPortEscapeReadout_inner
    (x y : RealifiedNaimarkComplexification) :
    inner ℝ (canonicalCompletedC3NaimarkPortEscapeReadout x)
        (canonicalCompletedC3NaimarkPortEscapeReadout y) =
      inner ℝ (realifiedNaimarkAdjoint x) (realifiedNaimarkAdjoint y) +
        inner ℝ (canonicalCompletedC3AmbientPortEscape x)
          (canonicalCompletedC3AmbientPortEscape y) := by
  change inner ℝ
      ((canonicalCompletedC3NaimarkPortEscapeReadout x).fst)
        ((canonicalCompletedC3NaimarkPortEscapeReadout y).fst) +
      inner ℝ
        ((canonicalCompletedC3NaimarkPortEscapeReadout x).snd)
          ((canonicalCompletedC3NaimarkPortEscapeReadout y).snd) = _
  rw [canonicalCompletedC3NaimarkPortEscapeReadout_fst,
    canonicalCompletedC3NaimarkPortEscapeReadout_fst,
    canonicalCompletedC3NaimarkPortEscapeReadout_snd,
    canonicalCompletedC3NaimarkPortEscapeReadout_snd]
  rfl

/-! Pull the same identity back to the native ambient carrier. -/
theorem canonicalCompletedC3AmbientPortEscape_inner
    (x y : RealifiedNaimarkComplexification) :
    inner ℝ x y =
      inner ℝ (realifiedNaimarkAdjoint x) (realifiedNaimarkAdjoint y) +
        inner ℝ (canonicalCompletedC3AmbientPortEscape x)
          (canonicalCompletedC3AmbientPortEscape y) := by
  rw [← canonicalCompletedC3NaimarkPortEscapeIsometry.inner_map_map x y]
  exact canonicalCompletedC3NaimarkPortEscapeReadout_inner x y

/-! The TFVD side is an exact channel intertwining identity: analysis and
channel synthesis commute before any Gram or moment object is formed. -/
theorem canonicalNativeTfvdCameraAnalysisSynthesis_intertwining
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (x : CameraResolvedCarryVertical) :
    cameraChannelAnalysisSynthesis S
        (cameraChannelTfvdAnalysis q S x) =
      nativeGpreFiniteTfvdAnalysis q S (cameraChannelSynthesis x) := by
  exact cameraChannelAnalysisSynthesis_tfvdAnalysis_commutes q S x

theorem canonicalNativeTfvdCameraReconstruction_after_analysis
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (x : CameraResolvedCarryVertical) :
    cameraChannelSynthesis
        (cameraChannelTfvdReconstruction q hqpos.le hq1 S
          (cameraChannelTfvdAnalysis q S x)) =
      cameraChannelSynthesis x := by
  exact cameraChannelTfvdReconstruction_analysis_synthesis q hqpos hq1 S x

/-! The energy factorization is the native TFVD identity itself. -/
theorem canonicalCarryTfvdEnergy_intertwining
    (q : ℝ) (x y : CarryVerticalL2) :
    inner ℂ (carryTfvdMetricState q x) (carryTfvdMetricState q y) =
      inner ℂ (carryTfvdCausalSecondDifference q x)
        (carryTfvdCausalSecondDifference q y) := by
  exact carryTfvdMetricState_inner q x y

end

end CarrySelfAdjointOperator
