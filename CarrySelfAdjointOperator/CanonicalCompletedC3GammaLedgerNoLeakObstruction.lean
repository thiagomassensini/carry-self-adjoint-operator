import CarrySelfAdjointOperator.CanonicalCompletedC3GammaLedgerBoundaryDefect
import CarrySelfAdjointOperator.C3GammaCameraTraceObstruction
import CarrySelfAdjointOperator.CompletedNativeCentralChiralQuotientCurvature

/-!
# Obstruction to the raw completed C3 Gamma--ledger no-leak gate

The completed C3 polarized Gamma state has a positive Gram in its common
Naimark carrier.  This module records that this *particular* unnormalized
Gamma Gram cannot equal the completed-native `dslope` on the central radial
diagonal.  Hence it cannot supply
`CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak`.

This is a local representation obstruction only.  It does not negate the
Green/TFVD geometry, the completed ledger, or another carrier with a proved
non-tautological correction of the Gamma state.
-/

open scoped ComplexConjugate InnerProductSpace
open Filter Topology Set

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- On the central radial diagonal, the unnormalized completed C3 Gamma Gram
is eventually different from the completed-native polarized `dslope`.

The Gamma diagonal is a squared norm and is strictly greater than `1 / 16`;
the `dslope` diagonal tends to the native zeroth moment, strictly below the
same bound.  No characteristic normalization factor is introduced here. -/
theorem canonicalCompletedC3PolarizedGammaKernel_ne_dslope_eventually_radialDiagonal :
    ∀ᶠ k : ℕ in atTop,
      canonicalCompletedC3PolarizedGammaKernel
          (canonicalCompletedC3RadialTiltPoint k 0)
          (canonicalCompletedC3RadialTiltPoint k 0)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0) ≠
        canonicalCompletedNativePolarizedDslopeKernel
          (canonicalCompletedC3RadialTiltPoint k 0)
          (canonicalCompletedC3RadialTiltPoint k 0) := by
  have hpoint := canonicalCompletedC3RadialTiltPoint_tendsto_zero 0
  have hcoord := hpoint.eventually
    (continuousAt_canonicalC3CameraFive_coordinate.tendsto.eventually
      (eventually_gt_nhds canonicalC3CameraFive_central_coordinate_gt_quarter))
  have hunit := hpoint.eventually
    (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1))
  have himTendsto : Tendsto
      (fun k : ℕ => (canonicalCompletedC3RadialTiltPoint k 0).im)
      atTop (nhds 0) :=
    Complex.continuous_im.continuousAt.tendsto.comp hpoint
  have hdslope := himTendsto.eventually
    completedNativePolarizedDslope_imaginaryAxis_eventually_lt_sixteenth
  filter_upwards [hcoord, hunit, hdslope] with k hcoord hunit hdslope
  have hnorm : ‖canonicalCompletedC3RadialTiltPoint k 0‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hunit
  have henergy : (1 / 16 : ℝ) <
      ‖canonicalCompletedC3PolarizedGammaState
        (canonicalCompletedC3RadialTiltPoint k 0)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)‖ ^ 2 :=
    canonicalC3Gamma_energy_gt_sixteenth_of_cameraFive
      (canonicalCompletedC3RadialTiltPoint k 0)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)
      ((Complex.abs_re_le_norm _).trans hnorm.le)
      ((Complex.abs_im_le_norm _).trans hnorm.le)
      hcoord
  rw [← canonicalCompletedC3RadialTiltPoint_eq_I_mul_im k 0] at hdslope
  intro heq
  have hre := congrArg Complex.re heq
  rw [canonicalCompletedC3PolarizedGammaKernel_diagonal_eq_norm_sq,
    ← Complex.ofReal_pow, Complex.ofReal_re] at hre
  linarith

/-- The literal completed C3 Gamma--ledger boundary defect is eventually
nonzero on the same radial diagonal. -/
theorem canonicalCompletedC3GammaLedgerBoundaryDefect_ne_zero_eventually_radialDiagonal :
    ∀ᶠ k : ℕ in atTop,
      canonicalCompletedC3GammaLedgerBoundaryDefect 0
          (canonicalCompletedC3RadialTiltPoint k 0)
          (canonicalCompletedC3RadialTiltPoint k 0)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0) ≠ 0 := by
  filter_upwards [canonicalCompletedC3PolarizedGammaKernel_ne_dslope_eventually_radialDiagonal,
    canonicalCompletedC3RadialTiltPoint_eventually_admissible 0] with k hne hadm
  intro hzero
  apply hne
  exact
    (canonicalCompletedC3GammaLedgerBoundaryDefect_eq_zero_iff_kernel_eq_dslope
      0
      (canonicalCompletedC3RadialTiltPoint k 0)
      (canonicalCompletedC3RadialTiltPoint k 0)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)
      hadm.1 hadm.1 hadm.2 hadm.2
      (sub_ne_zero.mp (canonicalCompletedC3RadialTilt_separation_ne_zero k 0 0))).mp
      hzero

/-- The local radial Gamma-ledger no-leak condition is false for the raw
completed C3 polarized Gamma realization. -/
theorem not_CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak :
    ¬ CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak := by
  intro hnoLeak
  have hdiag : Tendsto (fun k : ℕ => (k, k)) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_id.prodMk tendsto_id
  have hzero : ∀ᶠ k : ℕ in atTop,
      canonicalCompletedC3GammaLedgerBoundaryDefect 0
          (canonicalCompletedC3RadialTiltPoint k 0)
          (canonicalCompletedC3RadialTiltPoint k 0)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0) = 0 := by
    filter_upwards [hdiag.eventually (hnoLeak 0 0)] with k hk
    exact hk 0 (by simp) 0 (by simp)
  rcases
      (hzero.and
        canonicalCompletedC3GammaLedgerBoundaryDefect_ne_zero_eventually_radialDiagonal).exists with
    ⟨k, hzeroK, hneK⟩
  exact hneK hzeroK

end

end CarrySelfAdjointOperator
