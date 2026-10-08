import CarrySelfAdjointOperator.CompletedNativeThetaDecayingTail

/-! Extend the original source integral to 9/8 before enclosing its tail.
This is a quadrature cutoff, not a change of the source or its metric. -/
namespace CarrySelfAdjointOperator
open Real Set Filter MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem theta_exp_neg_1133_bound : exp (-(1133/40:ℝ)) ≤ (51/100000000000000:ℝ) := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 1133/40) 65
  rw [exp_neg]
  apply (inv_le_iff_one_le_mul₀ (exp_pos _)).mpr
  have ht : (1:ℝ) ≤ (51/100000000000000)*∑ i ∈ Finset.range 65,
      (1133/40:ℝ)^i/i.factorial := by norm_num [Finset.sum_range_succ]
  exact ht.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

theorem integral_thetaFirstMode_weighted_tail_le_fourteen (p : ℕ) (hp : p ≤ 14) :
    (∫ u in Ioi (9/8:ℝ), u^p*thetaFirstMode u) ≤ (2/10000000000000:ℝ) := by
  have hu (u : ℝ) (h : 9/8 ≤ u) : u^p*thetaFirstMode u ≤
      (2*(9/8:ℝ)^14*exp (131/20))*exp (-31*u) := by
    have hb : u ≤ (9/8:ℝ)*exp (u-9/8) := by
      have he := Real.add_one_le_exp (u-9/8)
      have hm := mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 9/8)
      nlinarith
    have he : u^p ≤ (9/8:ℝ)^14*exp (14*(u-9/8)) := by
      calc
        _ ≤ u^14 := pow_le_pow_right₀ (by linarith) hp
        _ ≤ ((9/8:ℝ)*exp (u-9/8))^14 := pow_le_pow_left₀ (by linarith) hb 14
        _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]; norm_num
    calc
      _ ≤ ((9/8:ℝ)^14*exp (14*(u-9/8)))*(2*exp ((223/10:ℝ)-45*u)) :=
        mul_le_mul he (thetaFirstMode_tail_le_fortyFive (by linarith))
          (by unfold thetaFirstMode; positivity) (by positivity)
      _ = _ := by
        rw [show ((9/8:ℝ)^14*exp (14*(u-9/8)))*(2*exp ((223/10:ℝ)-45*u)) =
          (2*(9/8:ℝ)^14)*(exp (14*(u-9/8))*exp ((223/10:ℝ)-45*u)) by ring,
          ← exp_add, show 14*(u-9/8)+(223/10-45*u) = 131/20+(-31*u) by ring,
          exp_add]
        ring

  have hi := (integrableOn_pow_mul_thetaFirstMode p).mono_set
    (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 9/8))
  have h := integral_mono_ae hi
    ((integrableOn_exp_mul_Ioi (by norm_num : (-31:ℝ)<0) (9/8)).const_mul
      (2*(9/8:ℝ)^14*exp (131/20))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hmem
      exact hu u hmem.le)
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-31:ℝ)<0) (9/8)] at h
  have he : (2*(9/8:ℝ)^14*exp (131/20))*(-exp ((-31:ℝ)*(9/8))/(-31)) =
      (2*(9/8:ℝ)^14/31)*exp (-(1133/40:ℝ)) := by
    rw [neg_div_neg_eq, ← mul_div_assoc, mul_assoc, ← exp_add]
    norm_num
    ring
  rw [he] at h
  have hnum : (2*(9/8:ℝ)^14/31)*(51/100000000000000) ≤ (2/10000000000000:ℝ) := by norm_num
  exact h.trans ((mul_le_mul_of_nonneg_left theta_exp_neg_1133_bound (by positivity)).trans hnum)

private theorem integrableOn_fourteenth_pow_exp (p : ℕ) :
    IntegrableOn (fun u : ℝ => u^p*exp (-23*u)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1:ℝ))
    (s := (p:ℝ)) (b := (23:ℝ))
    (show -1 < (p:ℝ) by have h := Nat.cast_nonneg (α := ℝ) p; linarith) (by norm_num) (by norm_num)
  simpa only [rpow_natCast, rpow_one] using h

private theorem integral_fourteenth_pow_exp (p : ℕ) :
    (∫ u in Ioi (0:ℝ), u^p*exp (-23*u)) = (p.factorial:ℝ)/23^(p+1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (p:ℝ)+1) (r := (23:ℝ)) (by positivity) (by norm_num)
  simp only [add_sub_cancel_right, rpow_natCast] at h
  rw [Real.Gamma_nat_eq_factorial] at h
  rw [show (p:ℝ)+1 = ((p+1:ℕ):ℝ) by push_cast; rfl, rpow_natCast] at h
  simpa [one_div, inv_pow, div_eq_mul_inv, mul_comm, neg_mul] using h

theorem completedNativeThetaTailMoment_finite_upper_fourteen (p : ℕ) (hp : p ≤ 14) :
    completedNativeThetaTailMoment p ≤
      (∫ u in (0:ℝ)..(9/8), u^p*thetaFirstMode u) + (2/10000000000000:ℝ) +
        (p.factorial:ℝ)/(100000*23^(p+1)) := by
  have hi := integrableOn_pow_mul_thetaFirstMode p
  have ht := hi.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 9/8))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi ht
  have htail := integral_thetaFirstMode_weighted_tail_le_fourteen p hp
  have h := integral_mono_ae (integrableOn_pow_mul_thetaTail p)
    (hi.add ((integrableOn_fourteenth_pow_exp p).const_mul (1/100000:ℝ))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have h := mul_le_mul_of_nonneg_left (thetaTail_le_first_add_decaying hu.le)
        (pow_nonneg hu.le p)
      simpa only [mul_add, mul_left_comm, mul_assoc, Pi.add_apply] using h)
  simp only [Pi.add_apply] at h
  rw [integral_add hi ((integrableOn_fourteenth_pow_exp p).const_mul (1/100000:ℝ)),
    integral_const_mul, integral_fourteenth_pow_exp] at h
  have he : (1/100000:ℝ)*((p.factorial:ℝ)/23^(p+1)) =
      (p.factorial:ℝ)/(100000*23^(p+1)) := by ring
  rw [he] at h
  unfold completedNativeThetaTailMoment
  linarith

theorem completedNativeThetaTailMoment_finite_lower_fourteen (p : ℕ) :
    (∫ u in (0:ℝ)..(9/8), u^p*thetaFirstMode u) ≤ completedNativeThetaTailMoment p := by
  have hi := integrableOn_pow_mul_thetaFirstMode p
  have hit := hi.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 9/8))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi hit
  have htail : 0 ≤ ∫ u in Ioi (9/8:ℝ), u^p*thetaFirstMode u := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (pow_nonneg (by have hh : (9/8:ℝ) < u := hu; linarith) p) (by unfold thetaFirstMode; positivity)
  have hmono := integral_mono_ae hi (integrableOn_pow_mul_thetaTail p) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_le_mul_of_nonneg_left (thetaTail_ge_thetaFirstMode hu.le) (pow_nonneg hu.le p))
  unfold completedNativeThetaTailMoment
  linarith
end
end CarrySelfAdjointOperator
