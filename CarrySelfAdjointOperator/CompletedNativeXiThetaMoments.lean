import CarrySelfAdjointOperator.CompletedNativeXiCosineMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Theta-tail moments behind the completed Xi cosine kernel

Writing `A` for the positive theta tail, the concrete Xi kernel is

`K = A'' - A / 4`.

This file records the polynomial moments of `A`, justifies the two weighted
integrations by parts needed at orders two and four, and transports the Xi
moment inequality to a simpler inequality between the zeroth and second
theta-tail moments.
-/

open Real Set Filter MeasureTheory

namespace CarrySelfAdjointOperator

noncomputable section

open XiThetaCosine

/-- The `power`-th (not necessarily even) moment of the positive theta tail. -/
def completedNativeThetaTailMoment (power : ℕ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), u ^ power * thetaTail u

private theorem integrableOn_pow_mul_of_exp_decay
    (f : ℝ → ℝ) (power : ℕ)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    (hdecay : ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : ℝ}, 0 ≤ u →
      ‖f u‖ ≤ C * Real.exp (-(3 / 2 : ℝ) * u)) :
    IntegrableOn (fun u : ℝ ↦ u ^ power * f u) (Ioi (0 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := hdecay
  have hbaseRpow : IntegrableOn
      (fun u : ℝ ↦
        u ^ (power : ℝ) *
          Real.exp (-(3 / 2 : ℝ) * u ^ (1 : ℝ)))
      (Ioi (0 : ℝ)) := by
    have hpower : -(1 : ℝ) < (power : ℝ) := by
      have hnonneg : 0 ≤ (power : ℝ) := Nat.cast_nonneg power
      linarith
    exact integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (power : ℝ)) (b := (3 / 2 : ℝ))
        hpower (by norm_num) (by norm_num)
  have hbase : IntegrableOn
      (fun u : ℝ ↦ u ^ power * Real.exp (-(3 / 2 : ℝ) * u))
      (Ioi (0 : ℝ)) := by
    apply hbaseRpow.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.rpow_natCast, Real.rpow_one]
  have hmajorant : IntegrableOn
      (fun u : ℝ ↦ C * (u ^ power * Real.exp (-(3 / 2 : ℝ) * u)))
      (Ioi (0 : ℝ)) := hbase.const_mul C
  apply hmajorant.mono'
  · exact (continuous_id.pow power).aestronglyMeasurable.mul hmeas
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hpow : 0 ≤ u ^ power := pow_nonneg hu.le power
    calc
      ‖u ^ power * f u‖ = u ^ power * ‖f u‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hpow]
      _ ≤ u ^ power * (C * Real.exp (-(3 / 2 : ℝ) * u)) :=
        mul_le_mul_of_nonneg_left (hbound hu.le) hpow
      _ = C * (u ^ power * Real.exp (-(3 / 2 : ℝ) * u)) := by ring

/-- Every polynomially weighted theta tail is integrable. -/
theorem integrableOn_pow_mul_thetaTail (power : ℕ) :
    IntegrableOn (fun u : ℝ ↦ u ^ power * thetaTail u) (Ioi (0 : ℝ)) := by
  apply integrableOn_pow_mul_of_exp_decay thetaTail power
  · exact integrableOn_thetaTail.aestronglyMeasurable
  · exact exists_thetaTail_exp_decay

/-- Every polynomially weighted first derivative of the theta tail is
integrable. -/
theorem integrableOn_pow_mul_thetaTailFirst (power : ℕ) :
    IntegrableOn (fun u : ℝ ↦ u ^ power * thetaTailFirst u) (Ioi (0 : ℝ)) := by
  apply integrableOn_pow_mul_of_exp_decay thetaTailFirst power
  · exact integrableOn_thetaTailFirst.aestronglyMeasurable
  · exact exists_thetaTailFirst_exp_decay

/-- Every polynomially weighted second derivative of the theta tail is
integrable. -/
theorem integrableOn_pow_mul_thetaTailSecond (power : ℕ) :
    IntegrableOn (fun u : ℝ ↦ u ^ power * thetaTailSecond u) (Ioi (0 : ℝ)) := by
  have hK := integrableOn_pow_mul_completedNativeXiCosineKernel power
  have hA := (integrableOn_pow_mul_thetaTail power).const_mul (1 / 4 : ℝ)
  have hsum := hK.add hA
  apply hsum.congr
  exact Filter.Eventually.of_forall (fun u ↦ by
    simp only [Pi.add_apply]
    rw [← thetaTailSecond_sub_quarter u]
    ring)

private theorem tendsto_mul_pow_atTop_of_exp_decay
    (f : ℝ → ℝ) (power : ℕ)
    (hdecay : ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : ℝ}, 0 ≤ u →
      ‖f u‖ ≤ C * Real.exp (-(3 / 2 : ℝ) * u)) :
    Tendsto (fun u : ℝ ↦ f u * u ^ power) atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ := hdecay
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun u ↦ norm_nonneg (f u * u ^ power))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    have hpow : 0 ≤ u ^ power := pow_nonneg hu power
    calc
      ‖f u * u ^ power‖ = ‖f u‖ * u ^ power := by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpow]
      _ ≤ (C * Real.exp (-(3 / 2 : ℝ) * u)) * u ^ power :=
        mul_le_mul_of_nonneg_right (hbound hu) hpow
      _ = C * (u ^ power * Real.exp (-(3 / 2 : ℝ) * u)) := by ring
  · have hrpow := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (power : ℝ) (3 / 2 : ℝ) (by norm_num)
    have hnat : Tendsto
        (fun u : ℝ ↦ u ^ power * Real.exp (-(3 / 2 : ℝ) * u))
        atTop (nhds 0) := by
      apply hrpow.congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
      rw [Real.rpow_natCast]
    simpa using hnat.const_mul C

private theorem thetaTailFirst_mul_pow_tendsto_zero (power : ℕ) :
    Tendsto (fun u : ℝ ↦ thetaTailFirst u * u ^ power) atTop (nhds 0) :=
  tendsto_mul_pow_atTop_of_exp_decay thetaTailFirst power
    exists_thetaTailFirst_exp_decay

private theorem thetaTail_mul_pow_tendsto_zero (power : ℕ) :
    Tendsto (fun u : ℝ ↦ thetaTail u * u ^ power) atTop (nhds 0) :=
  tendsto_mul_pow_atTop_of_exp_decay thetaTail power exists_thetaTail_exp_decay

private theorem thetaTailFirst_mul_pow_tendsto_zero_right (power : ℕ)
    (hpower : 0 < power) :
    Tendsto (fun u : ℝ ↦ thetaTailFirst u * u ^ power)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hcont : Tendsto (fun u : ℝ ↦ thetaTailFirst u * u ^ power)
      (nhds 0) (nhds (thetaTailFirst 0 * 0 ^ power)) :=
    (hasDerivAt_thetaTailFirst 0).continuousAt.tendsto.mul
      ((continuousAt_id.pow power).tendsto)
  have hzero : thetaTailFirst 0 * (0 : ℝ) ^ power = 0 := by
    simp [Nat.ne_zero_of_lt hpower]
  rw [hzero] at hcont
  change Tendsto (fun u : ℝ ↦ thetaTailFirst u * u ^ power)
    (nhds 0 ⊓ Filter.principal (Ioi 0)) (nhds 0)
  exact hcont.mono_left inf_le_left

private theorem thetaTail_mul_pow_tendsto_zero_right (power : ℕ)
    (hpower : 0 < power) :
    Tendsto (fun u : ℝ ↦ thetaTail u * u ^ power)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hcont : Tendsto (fun u : ℝ ↦ thetaTail u * u ^ power)
      (nhds 0) (nhds (thetaTail 0 * 0 ^ power)) :=
    (hasDerivAt_thetaTail 0).continuousAt.tendsto.mul
      ((continuousAt_id.pow power).tendsto)
  have hzero : thetaTail 0 * (0 : ℝ) ^ power = 0 := by
    simp [Nat.ne_zero_of_lt hpower]
  rw [hzero] at hcont
  change Tendsto (fun u : ℝ ↦ thetaTail u * u ^ power)
    (nhds 0 ⊓ Filter.principal (Ioi 0)) (nhds 0)
  exact hcont.mono_left inf_le_left

/-- Two integrations by parts identify the quadratic moment of `A''`. -/
theorem integral_pow_two_mul_thetaTailSecond :
    (∫ u in Ioi (0 : ℝ), u ^ 2 * thetaTailSecond u) =
      2 * completedNativeThetaTailMoment 0 := by
  have hfirst := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := thetaTailFirst) (u' := thetaTailSecond)
    (v := fun u : ℝ ↦ u ^ 2) (v' := fun u : ℝ ↦ 2 * u)
    (fun u _hu ↦ hasDerivAt_thetaTailFirst u)
    (fun u _hu ↦ by
      refine (((hasDerivAt_id u).pow 2).congr_of_eventuallyEq ?_).congr_deriv ?_
      · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
      · simp only [id_eq]
        ring)
    (by
      apply (integrableOn_pow_mul_thetaTailFirst 1).const_mul 2 |>.congr
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
    (by
      apply (integrableOn_pow_mul_thetaTailSecond 2).congr
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
    (thetaTailFirst_mul_pow_tendsto_zero_right 2 (by norm_num))
    (thetaTailFirst_mul_pow_tendsto_zero 2)
  have hsecond := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := thetaTail) (u' := thetaTailFirst)
    (v := fun u : ℝ ↦ 2 * u) (v' := fun _u : ℝ ↦ 2)
    (fun u _hu ↦ hasDerivAt_thetaTail u)
    (fun u _hu ↦ by simpa using (hasDerivAt_id u).const_mul 2)
    (by
      apply (integrableOn_pow_mul_thetaTail 0).const_mul 2 |>.congr
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
    (by
      apply (integrableOn_pow_mul_thetaTailFirst 1).const_mul 2 |>.congr
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
    (by
      have h := thetaTail_mul_pow_tendsto_zero_right 1 (by norm_num)
      have hscaled : Tendsto (fun u : ℝ ↦ 2 * (thetaTail u * u))
          (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
        simpa only [pow_one, mul_zero] using h.const_mul 2
      refine hscaled.congr' ?_
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
    (by
      have h := thetaTail_mul_pow_tendsto_zero 1
      have hscaled : Tendsto (fun u : ℝ ↦ 2 * (thetaTail u * u))
          atTop (nhds 0) := by
        simpa only [pow_one, mul_zero] using h.const_mul 2
      refine hscaled.congr' ?_
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
  rw [completedNativeThetaTailMoment]
  rw [show (fun u : ℝ ↦ thetaTailFirst u * (2 * u)) =
      fun u : ℝ ↦ 2 * (u * thetaTailFirst u) by funext u; ring,
    integral_const_mul] at hfirst
  rw [show (fun u : ℝ ↦ thetaTail u * 2) =
      fun u : ℝ ↦ 2 * (u ^ 0 * thetaTail u) by funext u; ring,
    integral_const_mul,
    show (fun u : ℝ ↦ thetaTailFirst u * (2 * u)) =
      fun u : ℝ ↦ 2 * (u * thetaTailFirst u) by funext u; ring,
    integral_const_mul] at hsecond
  calc
    (∫ u in Ioi (0 : ℝ), u ^ 2 * thetaTailSecond u) =
        ∫ u in Ioi (0 : ℝ), thetaTailSecond u * u ^ 2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u ↦ by ring)
    _ = -2 * ∫ u in Ioi (0 : ℝ), u * thetaTailFirst u := by linarith
    _ = 2 * ∫ u in Ioi (0 : ℝ), u ^ 0 * thetaTail u := by linarith
    _ = 2 * completedNativeThetaTailMoment 0 := rfl

/-- Two integrations by parts identify the quartic moment of `A''`. -/
theorem integral_pow_four_mul_thetaTailSecond :
    (∫ u in Ioi (0 : ℝ), u ^ 4 * thetaTailSecond u) =
      12 * completedNativeThetaTailMoment 2 := by
  have hfirst := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := thetaTailFirst) (u' := thetaTailSecond)
    (v := fun u : ℝ ↦ u ^ 4) (v' := fun u : ℝ ↦ 4 * u ^ 3)
    (fun u _hu ↦ hasDerivAt_thetaTailFirst u)
    (fun u _hu ↦ by
      refine (((hasDerivAt_id u).pow 4).congr_of_eventuallyEq ?_).congr_deriv ?_
      · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
      · simp only [id_eq]
        ring)
    (by
      apply (integrableOn_pow_mul_thetaTailFirst 3).const_mul 4 |>.congr
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
    (by
      apply (integrableOn_pow_mul_thetaTailSecond 4).congr
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
    (thetaTailFirst_mul_pow_tendsto_zero_right 4 (by norm_num))
    (thetaTailFirst_mul_pow_tendsto_zero 4)
  have hsecond := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := thetaTail) (u' := thetaTailFirst)
    (v := fun u : ℝ ↦ 4 * u ^ 3) (v' := fun u : ℝ ↦ 12 * u ^ 2)
    (fun u _hu ↦ hasDerivAt_thetaTail u)
    (fun u _hu ↦ by
      refine ((((hasDerivAt_id u).pow 3).const_mul 4).congr_of_eventuallyEq ?_).congr_deriv ?_
      · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
      · simp only [id_eq]
        ring)
    (by
      apply (integrableOn_pow_mul_thetaTail 2).const_mul 12 |>.congr
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
    (by
      apply (integrableOn_pow_mul_thetaTailFirst 3).const_mul 4 |>.congr
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
    (by
      have h := thetaTail_mul_pow_tendsto_zero_right 3 (by norm_num)
      have hscaled : Tendsto (fun u : ℝ ↦ 4 * (thetaTail u * u ^ 3))
          (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
        simpa only [mul_zero] using h.const_mul 4
      refine hscaled.congr' ?_
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
    (by
      have h := thetaTail_mul_pow_tendsto_zero 3
      have hscaled : Tendsto (fun u : ℝ ↦ 4 * (thetaTail u * u ^ 3))
          atTop (nhds 0) := by
        simpa only [mul_zero] using h.const_mul 4
      refine hscaled.congr' ?_
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
  rw [completedNativeThetaTailMoment]
  rw [show (fun u : ℝ ↦ thetaTailFirst u * (4 * u ^ 3)) =
      fun u : ℝ ↦ 4 * (u ^ 3 * thetaTailFirst u) by funext u; ring,
    integral_const_mul] at hfirst
  rw [show (fun u : ℝ ↦ thetaTail u * (12 * u ^ 2)) =
      fun u : ℝ ↦ 12 * (u ^ 2 * thetaTail u) by funext u; ring,
    integral_const_mul,
    show (fun u : ℝ ↦ thetaTailFirst u * (4 * u ^ 3)) =
      fun u : ℝ ↦ 4 * (u ^ 3 * thetaTailFirst u) by funext u; ring,
    integral_const_mul] at hsecond
  calc
    (∫ u in Ioi (0 : ℝ), u ^ 4 * thetaTailSecond u) =
        ∫ u in Ioi (0 : ℝ), thetaTailSecond u * u ^ 4 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u ↦ by ring)
    _ = -4 * ∫ u in Ioi (0 : ℝ), u ^ 3 * thetaTailFirst u := by linarith
    _ = 12 * ∫ u in Ioi (0 : ℝ), u ^ 2 * thetaTail u := by linarith
    _ = 12 * completedNativeThetaTailMoment 2 := rfl

/-- The Xi-kernel mass in terms of the zeroth theta-tail moment. -/
theorem completedNativeXiCosineMoment_zero_eq_thetaTailMoments :
    completedNativeXiCosineMoment 0 =
      1 / 2 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 0 := by
  have h := integral_completedNativeXiCosineKernel_mul_cos 0
  rw [completedNativeXiCosineMoment, completedNativeThetaTailMoment]
  simpa using h

/-- The second Xi-kernel moment in terms of theta-tail moments. -/
theorem completedNativeXiCosineMoment_one_eq_thetaTailMoments :
    completedNativeXiCosineMoment 1 =
      2 * completedNativeThetaTailMoment 0 -
        (1 / 4 : ℝ) * completedNativeThetaTailMoment 2 := by
  unfold completedNativeXiCosineMoment
  have hsplit :
      (∫ u in Ioi (0 : ℝ), u ^ 2 * completedNativeXiCosineKernel u) =
        (∫ u in Ioi (0 : ℝ), u ^ 2 * thetaTailSecond u) -
          (1 / 4 : ℝ) * ∫ u in Ioi (0 : ℝ), u ^ 2 * thetaTail u := by
    rw [← integral_const_mul, ← integral_sub
      (integrableOn_pow_mul_thetaTailSecond 2)
      ((integrableOn_pow_mul_thetaTail 2).const_mul (1 / 4 : ℝ))]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u ↦ by
      change u ^ 2 * completedNativeXiCosineKernel u =
        u ^ 2 * thetaTailSecond u - (1 / 4 : ℝ) * (u ^ 2 * thetaTail u)
      rw [← thetaTailSecond_sub_quarter u]
      ring)
  rw [integral_pow_two_mul_thetaTailSecond] at hsplit
  simpa [completedNativeThetaTailMoment] using hsplit

/-- The fourth Xi-kernel moment in terms of theta-tail moments. -/
theorem completedNativeXiCosineMoment_two_eq_thetaTailMoments :
    completedNativeXiCosineMoment 2 =
      12 * completedNativeThetaTailMoment 2 -
        (1 / 4 : ℝ) * completedNativeThetaTailMoment 4 := by
  unfold completedNativeXiCosineMoment
  have hsplit :
      (∫ u in Ioi (0 : ℝ), u ^ 4 * completedNativeXiCosineKernel u) =
        (∫ u in Ioi (0 : ℝ), u ^ 4 * thetaTailSecond u) -
          (1 / 4 : ℝ) * ∫ u in Ioi (0 : ℝ), u ^ 4 * thetaTail u := by
    rw [← integral_const_mul, ← integral_sub
      (integrableOn_pow_mul_thetaTailSecond 4)
      ((integrableOn_pow_mul_thetaTail 4).const_mul (1 / 4 : ℝ))]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u ↦ by
      change u ^ 4 * completedNativeXiCosineKernel u =
        u ^ 4 * thetaTailSecond u - (1 / 4 : ℝ) * (u ^ 4 * thetaTail u)
      rw [← thetaTailSecond_sub_quarter u]
      ring)
  rw [integral_pow_four_mul_thetaTailSecond] at hsplit
  simpa [completedNativeThetaTailMoment] using hsplit

private theorem thetaTail_nonneg (u : ℝ) : 0 ≤ thetaTail u := by
  rw [thetaTail_eq_two_mul_tsum]
  exact mul_nonneg (by norm_num) (tsum_nonneg (fun n ↦ by
    unfold thetaTailMode
    positivity))

/-- All theta-tail moments are nonnegative. -/
theorem completedNativeThetaTailMoment_nonneg (power : ℕ) :
    0 ≤ completedNativeThetaTailMoment power := by
  rw [completedNativeThetaTailMoment]
  exact integral_nonneg_of_ae (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (pow_nonneg hu.le power) (thetaTail_nonneg u))

/-- A strict theta-tail second-moment bound is sufficient for the desired
strict Xi-kernel fourth-moment inequality.  The cancellation in this lemma is
the key algebraic simplification of the low-order gate. -/
theorem completedNativeXiCosineMoment_inequality_of_thetaTailMoment_two_lt
    (hsmall : completedNativeThetaTailMoment 2 <
      2 * completedNativeThetaTailMoment 0 ^ 2) :
    completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 2 <
      3 * completedNativeXiCosineMoment 1 ^ 2 := by
  rw [completedNativeXiCosineMoment_zero_eq_thetaTailMoments,
    completedNativeXiCosineMoment_one_eq_thetaTailMoments,
    completedNativeXiCosineMoment_two_eq_thetaTailMoments]
  have hA0 := completedNativeThetaTailMoment_nonneg 0
  have hA2 := completedNativeThetaTailMoment_nonneg 2
  have hA4 := completedNativeThetaTailMoment_nonneg 4
  have hA0lt : completedNativeThetaTailMoment 0 < 2 := by
    have hμ0 := completedNativeXiCosineMoment_pos 0
    rw [completedNativeXiCosineMoment_zero_eq_thetaTailMoments] at hμ0
    linarith
  nlinarith

/-! ## The same integration-by-parts mechanism at every higher order -/

/-- Two integrations by parts at an arbitrary polynomial degree. All
boundary limits and integrability estimates are the existing theta ones. -/
theorem integral_pow_add_two_mul_thetaTailSecond (n : ℕ) :
    (∫ u in Ioi (0 : ℝ), u ^ (n+2) * thetaTailSecond u) =
      ((n+2 : ℕ) : ℝ) * ((n+1 : ℕ) : ℝ) * completedNativeThetaTailMoment n := by
  have hfirst := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := thetaTailFirst) (u' := thetaTailSecond)
    (v := fun u : ℝ ↦ u ^ (n+2))
    (v' := fun u : ℝ ↦ ((n+2 : ℕ) : ℝ) * u ^ (n+1))
    (fun u _hu ↦ hasDerivAt_thetaTailFirst u)
    (fun u _hu ↦ by
      refine (((hasDerivAt_id u).pow (n+2)).congr_of_eventuallyEq ?_).congr_deriv ?_
      · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
      · simp only [id_eq, mul_one]
        congr 1)
    (by
      apply (integrableOn_pow_mul_thetaTailFirst (n+1)).const_mul
        ((n+2 : ℕ) : ℝ) |>.congr
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
    (by
      apply (integrableOn_pow_mul_thetaTailSecond (n+2)).congr
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
    (thetaTailFirst_mul_pow_tendsto_zero_right (n+2) (by omega))
    (thetaTailFirst_mul_pow_tendsto_zero (n+2))
  have hsecond := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := thetaTail) (u' := thetaTailFirst)
    (v := fun u : ℝ ↦ ((n+2 : ℕ) : ℝ) * u ^ (n+1))
    (v' := fun u : ℝ ↦ (((n+2 : ℕ) : ℝ) * ((n+1 : ℕ) : ℝ)) * u ^ n)
    (fun u _hu ↦ hasDerivAt_thetaTail u)
    (fun u _hu ↦ by
      convert ((hasDerivAt_id u).pow (n+1)).const_mul ((n+2 : ℕ) : ℝ) using 1 <;> simp [mul_assoc])
    (by
      apply (integrableOn_pow_mul_thetaTail n).const_mul
        (((n+2 : ℕ) : ℝ) * ((n+1 : ℕ) : ℝ)) |>.congr
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
    (by
      apply (integrableOn_pow_mul_thetaTailFirst (n+1)).const_mul
        ((n+2 : ℕ) : ℝ) |>.congr
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
    (by
      have h := thetaTail_mul_pow_tendsto_zero_right (n+1) (by omega)
      have hscaled : Tendsto
          (fun u : ℝ ↦ ((n+2 : ℕ) : ℝ) * (thetaTail u * u ^ (n+1)))
          (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
        simpa only [mul_zero] using h.const_mul ((n+2 : ℕ) : ℝ)
      refine hscaled.congr' ?_
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
    (by
      have h := thetaTail_mul_pow_tendsto_zero (n+1)
      have hscaled : Tendsto
          (fun u : ℝ ↦ ((n+2 : ℕ) : ℝ) * (thetaTail u * u ^ (n+1)))
          atTop (nhds 0) := by
        simpa only [mul_zero] using h.const_mul ((n+2 : ℕ) : ℝ)
      refine hscaled.congr' ?_
      exact Filter.Eventually.of_forall (fun u ↦ by
        simp only [Pi.mul_apply]
        ring))
  rw [show (fun u : ℝ ↦ thetaTailFirst u * (((n+2 : ℕ) : ℝ) * u ^ (n+1))) =
      fun u : ℝ ↦ ((n+2 : ℕ) : ℝ) * (u ^ (n+1) * thetaTailFirst u) by
        funext u; ring, integral_const_mul] at hfirst hsecond
  rw [show (fun u : ℝ ↦ thetaTail u *
      ((((n+2 : ℕ) : ℝ) * ((n+1 : ℕ) : ℝ)) * u ^ n)) =
      fun u : ℝ ↦ (((n+2 : ℕ) : ℝ) * ((n+1 : ℕ) : ℝ)) *
        (u ^ n * thetaTail u) by funext u; ring, integral_const_mul] at hsecond
  unfold completedNativeThetaTailMoment
  rw [show (fun u : ℝ ↦ u ^ (n+2) * thetaTailSecond u) =
      fun u : ℝ ↦ thetaTailSecond u * u ^ (n+2) by funext u; ring]
  linarith

/-- Every positive even Xi order is expressed through the same theta-tail
moments. This generalizes the existing orders one and two without changing
their definitions or their proofs. -/
theorem completedNativeXiCosineMoment_succ_eq_thetaTailMoments (n : ℕ) :
    completedNativeXiCosineMoment (n+1) =
      ((2*n+2 : ℕ) : ℝ) * ((2*n+1 : ℕ) : ℝ) * completedNativeThetaTailMoment (2*n) -
        (1/4 : ℝ) * completedNativeThetaTailMoment (2*n+2) := by
  unfold completedNativeXiCosineMoment
  rw [show 2*(n+1) = 2*n+2 by omega]
  have hsplit :
      (∫ u in Ioi (0 : ℝ), u ^ (2*n+2) * completedNativeXiCosineKernel u) =
        (∫ u in Ioi (0 : ℝ), u ^ (2*n+2) * thetaTailSecond u) -
          (1/4 : ℝ) * ∫ u in Ioi (0 : ℝ), u ^ (2*n+2) * thetaTail u := by
    rw [← integral_const_mul, ← integral_sub
      (integrableOn_pow_mul_thetaTailSecond (2*n+2))
      ((integrableOn_pow_mul_thetaTail (2*n+2)).const_mul (1/4 : ℝ))]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u ↦ by
      change u ^ (2*n+2) * completedNativeXiCosineKernel u =
        u ^ (2*n+2) * thetaTailSecond u - (1/4 : ℝ) * (u ^ (2*n+2) * thetaTail u)
      rw [← thetaTailSecond_sub_quarter u]
      ring)
  rw [integral_pow_add_two_mul_thetaTailSecond] at hsplit
  simpa [completedNativeThetaTailMoment] using hsplit

/-- The new sixth-order term retains the subtraction of the sixth tail
moment, which cannot be dropped in a lower-bound argument. -/
theorem completedNativeXiCosineMoment_three_eq_thetaTailMoments :
    completedNativeXiCosineMoment 3 =
      30 * completedNativeThetaTailMoment 4 -
        (1/4 : ℝ) * completedNativeThetaTailMoment 6 := by
  convert completedNativeXiCosineMoment_succ_eq_thetaTailMoments 2 using 1
  norm_num

end

end CarrySelfAdjointOperator
