import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration
import NativeCarryC3Crosswalk.GeometricCutoffCompleteness

/-!
# Central calibration at geometrically complete C3 cutoffs

The completed scalar readout has the same central value at every cutoff.
Thus restricting to one or more complete camera centers does not remove
the mismatch of the fixed standard orthogonal-sum metric. Other metric
transports and other Hilbert states remain outside this statement.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- The completed central readout equals the native zeroth moment at every
cutoff, including all geometrically complete ones. -/
theorem canonicalCompletedC3AllCutoffOrientedRealKernelReadout_zero_zero
    (M : ℕ) :
    canonicalCompletedC3AllCutoffOrientedRealKernelReadout M 0 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  simp only [canonicalCompletedC3AllCutoffOrientedRealKernelReadout,
    ↓reduceIte, Complex.ofReal_zero,
    completedNativeGreenNormalizedResponse_hasDerivAt_h0.deriv]

/-- Exact strict comparison at each cutoff; no empty-cutoff specialization
is needed. -/
theorem canonicalCompletedC3AllCutoffCentralReadout_re_lt_fixedKernel
    (M : ℕ) :
    (canonicalCompletedC3AllCutoffOrientedRealKernelReadout M 0 0).re <
      (canonicalCompletedC3RealAxisPositiveKernel 0 0).re := by
  rw [canonicalCompletedC3AllCutoffOrientedRealKernelReadout_zero_zero]
  exact canonicalCompletedC3RealAxisPositiveKernel_zero_zero_re_gt_nativeMoment

/-- In C3 the raw window ends at the last center plus its right leg. -/
theorem canonicalC3_geometricallyCompleteCutoff_iff (M N : ℕ) :
    NativeCarryC3Crosswalk.IsGeometricallyCompleteNativeCutoff 3 M N ↔
      1 ≤ M ∧ 3 * M + 1 ≤ N := by
  simp [NativeCarryC3Crosswalk.IsGeometricallyCompleteNativeCutoff,
    NativeCarryC3Crosswalk.natural_complete_horizon (by norm_num : 3 ≤ (3 : ℕ))]

/-- Even when only cutoffs with at least two complete C3 centers are
allowed, the fixed standard metric cannot equal the completed central
readout. The witness is the full two-center window through index seven. -/
theorem not_canonicalCompletedC3CentralSewing_on_twoCompleteCenters :
    ¬ (∀ M N : ℕ, 2 ≤ M →
      NativeCarryC3Crosswalk.IsGeometricallyCompleteNativeCutoff 3 M N →
      canonicalCompletedC3AllCutoffOrientedRealKernelReadout M 0 0 =
        canonicalCompletedC3RealAxisPositiveKernel 0 0) := by
  intro h
  have hcomplete :
      NativeCarryC3Crosswalk.IsGeometricallyCompleteNativeCutoff 3 2 7 := by
    rw [canonicalC3_geometricallyCompleteCutoff_iff]
    norm_num
  have heq := congrArg Complex.re (h 2 7 (by norm_num) hcomplete)
  exact (ne_of_lt
    (canonicalCompletedC3AllCutoffCentralReadout_re_lt_fixedKernel 2)) heq

end
end CarrySelfAdjointOperator
