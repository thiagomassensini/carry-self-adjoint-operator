import CarrySelfAdjointOperator.CompletedC3CentralChartFreeSewingAudit
import CarrySelfAdjointOperator.CompletedNativeXiThetaMomentBounds
import CarrySelfAdjointOperator.CompletedNativeCentralProductDressingAudit
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Calibration of the fixed ordinary/logarithmic/residual metric

The existing concrete carrier uses the standard orthogonal sum metric. Its
zeroth Gram is already larger than the zeroth native moment. This audit only
addresses that fixed realization: it does not exclude a transported metric
or another native Hilbert state. The moment estimate uses the already proved
cosine representation of the actual completed native characteristic.
-/

open Real Set MeasureTheory
open scoped BigOperators InnerProductSpace lp

namespace CarrySelfAdjointOperator
open CPFormal.Analytic.Cp XiThetaCosine
noncomputable section

private theorem calibration_exp_neg_three_lt : Real.exp (-3) < (1 / 16 : ℝ) := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 5
  have hlarge : (16 : ℝ) < Real.exp 3 := by
    norm_num [Finset.sum_range_succ] at hs
    linarith
  rw [Real.exp_neg]
  simpa only [one_div] using (inv_lt_inv₀ (Real.exp_pos 3) (by norm_num)).mpr hlarge

private theorem calibration_theta_mode_bound {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    thetaTailMode n u ≤
      (1 / 16 : ℝ) * (1 / 4096 : ℝ) ^ n * Real.exp (-5 * u) := by
  have hm : (1 : ℝ) + 3 * n ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
    cases n with
    | zero => norm_num
    | succ n =>
      push_cast
      nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]
  have he : 1 + 2 * u ≤ Real.exp (2 * u) := by simpa only [add_comm] using Real.add_one_le_exp (2 * u)
  have hindex : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hp : 3 * ((n + 1 : ℕ) : ℝ) ^ 2 * (1 + 2 * u) ≤
      Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg _)
    · exact he
    · positivity
    · positivity
  have hexponent : u / 2 - Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) ≤
      -3 - 9 * n - 5 * u := by
    have hprod : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ 2 - 1) * u := mul_nonneg (by linarith) hu
    nlinarith
  have hdecay : Real.exp (-9) ≤ (1 / 4096 : ℝ) := by
    have hc := pow_le_pow_left₀ (Real.exp_nonneg (-3)) calibration_exp_neg_three_lt.le 3
    have heq : Real.exp (-9) = Real.exp (-3) ^ 3 := by
      have he := Real.exp_nat_mul (-3) 3
      norm_num at he
      exact he
    rw [heq]
    norm_num at hc ⊢
    exact hc
  unfold thetaTailMode
  rw [← Real.exp_add]
  calc
    Real.exp (u / 2 + -Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) ≤
        Real.exp (-3 - 9 * n - 5 * u) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hexponent]
    _ = Real.exp (-3) * Real.exp (-9) ^ n * Real.exp (-5 * u) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ (1 / 16 : ℝ) * (1 / 4096 : ℝ) ^ n * Real.exp (-5 * u) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul calibration_exp_neg_three_lt.le
          (pow_le_pow_left₀ (Real.exp_nonneg (-9)) hdecay n)
          (pow_nonneg (Real.exp_nonneg (-9)) n) (by norm_num)) (Real.exp_nonneg _)

/-- A coarse explicit majorant suffices to calibrate the central metric. -/
theorem calibration_thetaTail_le_exp {u : ℝ} (hu : 0 ≤ u) :
    thetaTail u ≤ (1 / 7 : ℝ) * Real.exp (-5 * u) := by
  rw [thetaTail_eq_two_mul_tsum]
  have hgeom : Summable (fun n : ℕ =>
      (1 / 16 : ℝ) * (1 / 4096 : ℝ) ^ n * Real.exp (-5 * u)) :=
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num :
      (1 / 4096 : ℝ) < 1)).mul_left (1 / 16)).mul_right _
  have hs := (summable_thetaTailMode u).tsum_le_tsum
    (calibration_theta_mode_bound hu) hgeom
  have hsum : (∑' n : ℕ,
      (1 / 16 : ℝ) * (1 / 4096 : ℝ) ^ n * Real.exp (-5 * u)) =
      (256 / 4095 : ℝ) * Real.exp (-5 * u) := by
    rw [tsum_mul_right, tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num) (by norm_num :
        (1 / 4096 : ℝ) < 1)]
    ring
  rw [hsum] at hs
  nlinarith [Real.exp_pos (-5 * u)]

/-- The same theta tail appearing in the native cosine representation has
mass at most `1/35`; this is an analytic bound, not a numerical estimate. -/
theorem completedNativeThetaTailMoment_zero_le_calibration :
    completedNativeThetaTailMoment 0 ≤ (1 / 35 : ℝ) := by
  have hm : IntegrableOn (fun u : ℝ => (1 / 7 : ℝ) * Real.exp (-5 * u))
      (Ioi 0) := (integrableOn_exp_mul_Ioi (by norm_num : (-5 : ℝ) < 0) 0).const_mul _
  have hi := integral_mono_ae integrableOn_thetaTail hm (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact calibration_thetaTail_le_exp hu.le)
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-5 : ℝ) < 0) 0] at hi
  norm_num at hi
  simpa [completedNativeThetaTailMoment] using hi

/-- The actual completed native zeroth moment is below the fixed ruler
`1/16`. Only the previously proved native cosine/characteristic identities
and the explicit tail bound above are used. -/
theorem canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth :
    canonicalCompletedNativeLogDerivativeMoment 0 < (1 / 16 : ℝ) := by
  have hc := canonicalCompletedNativeLogDerivativeMoment_real_recurrence 0
  simp only [Finset.range_zero, Finset.sum_empty, add_zero, zero_add,
    Nat.cast_one] at hc
  rw [completedNativeRealEvenCharacteristicCoefficient_zero_eq_xiCosineMoment,
    completedNativeRealEvenCharacteristicCoefficient_one_eq_xiCosineMoment,
    completedNativeXiCosineMoment_zero_eq_thetaTailMoments,
    completedNativeXiCosineMoment_one_eq_thetaTailMoments] at hc
  have hmass := completedNativeThetaTailMoment_zero_le_calibration
  have htwo : 0 ≤ completedNativeThetaTailMoment 2 := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (sq_nonneg _) (by
      rw [thetaTail_eq_two_mul_tsum]
      exact mul_nonneg (by norm_num) (tsum_nonneg (fun n => by
        unfold thetaTailMode
        positivity)))
  have hden : 0 < 1 / 2 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 0 := by
    nlinarith
  nlinarith


/-- The first ordinary-gradient coordinate alone exceeds `1/16` in energy. -/
theorem canonicalCentralCompletedGradient_firstCoordinate_sq_gt_sixteenth :
    (1 / 16 : ℝ) < ‖canonicalCentralCompletedDirichletGradientState 0‖ ^ 2 := by
  let a : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))
  have ha : 0 ≤ a := Real.rpow_nonneg (by norm_num) _
  have haSq : a ^ 2 = (1 / 2 : ℝ) := by
    dsimp [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hcoord : canonicalCentralCompletedDirichletGradientState 0 =
      ((a - 1 : ℝ) : ℂ) := by
    change natDirichletTerm (1 / 2 : ℂ) 2 - natDirichletTerm (1 / 2 : ℂ) 1 = _
    rw [natDirichletTerm_half_eq_realRpow, natDirichletTerm_half_eq_realRpow]
    simp [a]
  rw [hcoord, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg (a - 23 / 32)]

/-- The completed ordinary TFVD energy is already above the native ruler. -/
theorem infiniteReflectedGreenEnergy_half_gt_sixteenth :
    (1 / 16 : ℝ) < infiniteReflectedGreenEnergy (1 / 2 : ℂ) := by
  rw [infiniteReflectedGreenEnergy_half_eq_gradient_norm_sq]
  have hcoord := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    canonicalCentralCompletedDirichletGradientState 0
  have hsq : ‖canonicalCentralCompletedDirichletGradientState 0‖ ^ 2 ≤
      ‖canonicalCentralCompletedDirichletGradientState‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hcoord 2
  exact canonicalCentralCompletedGradient_firstCoordinate_sq_gt_sixteenth.trans_le hsq

/-- Exact central metric mismatch for the fixed three-channel realization.
This compares the full Gram with the actual native moment; it does not infer
non-cancellation from the residual norm alone. -/
theorem canonicalCompletedC3RealAxisPositiveKernel_zero_zero_re_gt_nativeMoment :
    canonicalCompletedNativeLogDerivativeMoment 0 <
      (canonicalCompletedC3RealAxisPositiveKernel 0 0).re := by
  rw [canonicalCompletedC3RealAxisPositiveKernel_zero_zero_re_eq_enriched_add_residual,
    inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet_zero_zero_re_eq_reflectedGreen_add_logJet]
  have hE := infiniteReflectedGreenEnergy_half_gt_sixteenth
  have hh := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  nlinarith [sq_nonneg ‖canonicalCompletedC3LogJetState (1 / 2 : ℂ) (by norm_num)‖,
    sq_nonneg ‖canonicalCompletedC3RealAxisResidualState 0‖]

/-- The explicitly named central defect is strictly positive for this
standard orthogonal-sum metric. -/
theorem canonicalCompletedC3ConcreteDressedCentralMomentDefect_pos :
    0 < canonicalCompletedC3ConcreteDressedCentralMomentDefect := by
  unfold canonicalCompletedC3ConcreteDressedCentralMomentDefect
  exact sub_pos.mpr canonicalCompletedC3RealAxisPositiveKernel_zero_zero_re_gt_nativeMoment


/-- With every existing coordinate opened, the strictly positive difference
is exactly `E + L + E² - h₀`. -/
theorem canonicalCompletedC3ConcreteDressedCentralMomentDefect_eq_calibration :
    canonicalCompletedC3ConcreteDressedCentralMomentDefect =
      infiniteReflectedGreenEnergy (1 / 2 : ℂ) +
        ‖canonicalCompletedC3LogJetState (1 / 2 : ℂ) (by norm_num)‖ ^ 2 +
        infiniteReflectedGreenEnergy (1 / 2 : ℂ) ^ 2 -
        canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [canonicalCompletedC3ConcreteDressedCentralMomentDefect_eq,
    inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet_zero_zero_re_eq_reflectedGreen_add_logJet,
    canonicalCompletedC3RealAxisResidualState_zero_norm_sq_eq_energy_sq]
  ring

/-- The standard metric on this particular three-channel state cannot be the
native kernel metric. This does not exclude a positive metric transport. -/
theorem not_canonicalCompletedC3ConcreteRealAxisPositiveSewing :
    ¬ CanonicalCompletedC3ConcreteRealAxisPositiveSewing := by
  intro hsewing
  have h := hsewing 0 0 0 completedNativeOperatorCharacteristic_zero_ne_zero
    completedNativeOperatorCharacteristic_zero_ne_zero
  rw [canonicalCompletedC3AllCutoffOrientedRealKernelReadout_eq_dslope
    0 0 0 completedNativeOperatorCharacteristic_zero_ne_zero
      completedNativeOperatorCharacteristic_zero_ne_zero] at h
  simp only [Complex.ofReal_zero, dslope_same,
    completedNativeGreenNormalizedResponse_hasDerivAt_h0.deriv] at h
  have hreal := congrArg Complex.re h
  change canonicalCompletedNativeLogDerivativeMoment 0 =
    (canonicalCompletedC3RealAxisPositiveKernel 0 0).re at hreal
  exact (ne_of_gt canonicalCompletedC3RealAxisPositiveKernel_zero_zero_re_gt_nativeMoment)
    hreal.symm

/-- Equivalent spelling for the existing fixed unnormalized state. -/
theorem not_hasCompletedNativeRealAxisNormalizedGreenKernel_concreteC3 :
    ¬ HasCompletedNativeRealAxisNormalizedGreenKernel
      canonicalCompletedC3ConcreteRealAxisGreenState := by
  intro hkernel
  exact not_canonicalCompletedC3ConcreteRealAxisPositiveSewing
    (canonicalCompletedC3ConcreteRealAxisPositiveSewing_iff_realAxisKernel.mpr hkernel)

end
end CarrySelfAdjointOperator
