import CarrySelfAdjointOperator.CompletedNativeThetaRefinedTail
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! Source-only bounds retaining the decay of the higher theta modes.
These are enclosures of the existing theta tail, not new source weights. -/
namespace CarrySelfAdjointOperator
open Real Set Filter MeasureTheory
noncomputable section
set_option autoImplicit false

private theorem exp_neg_constant_bound :
    exp (-(1178097/125000 : ℝ)) ≤ (1/12300 : ℝ) := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 1178097/125000) 30
  rw [exp_neg]
  apply (inv_le_iff_one_le_mul₀ (exp_pos _)).mpr
  have ht : (1:ℝ) ≤ (1/12300)*∑ i ∈ Finset.range 30,
      (1178097/125000:ℝ)^i/i.factorial := by norm_num [Finset.sum_range_succ]
  exact ht.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

private theorem pi_exp_lower {u : ℝ} (hu : 0 ≤ u) :
    (3141592/1000000 : ℝ)+6*u ≤ Real.pi*exp (2*u) := by
  have he := Real.add_one_le_exp (2*u)
  have hm := mul_nonneg Real.pi_pos.le (show 0 ≤ exp (2*u)-(2*u+1) by linarith)
  have hp := mul_nonneg (show 0 ≤ Real.pi-3 by linarith [Real.pi_gt_three]) hu
  nlinarith [Real.pi_gt_d6]

/-- Higher modes keep their native u-dependent decay before summation. -/
theorem thetaTailMode_le_decaying_geometric {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    XiThetaCosine.thetaTailMode n u ≤ XiThetaCosine.thetaTailMode 0 u *
      ((1/12300 : ℝ)*exp (-18*u))^n := by
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hi : 3*(n:ℝ) ≤ (((n+1:ℕ):ℝ)^2)-1 := by
    cases n with
    | zero => norm_num
    | succ n =>
        norm_num [Nat.cast_add, Nat.cast_one]
        have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
        have hh := mul_nonneg hn0 hn0
        nlinarith
  have hprod : ((1178097/125000:ℝ)+18*u)*(n:ℝ) ≤
      (Real.pi*exp (2*u))*((((n+1:ℕ):ℝ)^2)-1) := by
    have h := mul_le_mul (pi_exp_lower hu) hi (by positivity) (by positivity)
    nlinarith
  have hdecay : exp (-Real.pi*((((n+1:ℕ):ℝ)^2)-1)*exp (2*u)) ≤
      ((1/12300:ℝ)*exp (-18*u))^n := by
    calc
      _ ≤ exp (-((1178097/125000:ℝ)+18*u)*(n:ℝ)) := by
        apply exp_le_exp.mpr
        nlinarith
      _ = (exp (-(1178097/125000:ℝ))*exp (-18*u))^n := by
        rw [← exp_add, ← exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_right exp_neg_constant_bound (exp_nonneg _)) n
  have hsplit : exp (-Real.pi*(((n+1:ℕ):ℝ)^2)*exp (2*u)) =
      exp (-Real.pi*exp (2*u))*
        exp (-Real.pi*((((n+1:ℕ):ℝ)^2)-1)*exp (2*u)) := by
    rw [← exp_add]
    congr 1
    ring
  unfold XiThetaCosine.thetaTailMode
  rw [hsplit]
  simp only [Nat.cast_one, zero_add, one_pow, mul_one]
  calc
    _ = (exp (u/2)*exp (-Real.pi*exp (2*u)))*
      exp (-Real.pi*((((n+1:ℕ):ℝ)^2)-1)*exp (2*u)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)

/-- The discarded higher modes have an explicit exponentially decaying
majorant. The first mode itself is retained unchanged. -/
theorem thetaTail_le_first_add_decaying {u : ℝ} (hu : 0 ≤ u) :
    XiThetaCosine.thetaTail u ≤ thetaFirstMode u + (1/100000:ℝ)*exp (-23*u) := by
  let β := exp (-18*u)
  let α := (1/12300:ℝ)*β
  have hβ : 0 ≤ β := exp_nonneg _
  have hβ1 : β ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hα1 : α < 1 := by dsimp [α]; nlinarith
  have hs := (XiThetaCosine.summable_thetaTailMode u).tsum_le_tsum
    (thetaTailMode_le_decaying_geometric hu)
    ((summable_geometric_of_lt_one hα hα1).mul_left (XiThetaCosine.thetaTailMode 0 u))
  have ht : XiThetaCosine.thetaTail u ≤ thetaFirstMode u/(1-α) := by
    rw [XiThetaCosine.thetaTail_eq_two_mul_tsum]
    have h := mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 2)
    rw [tsum_mul_left, tsum_geometric_of_lt_one hα hα1] at h
    simpa [thetaFirstMode, XiThetaCosine.thetaTailMode, α, β, div_eq_mul_inv, mul_assoc] using h
  have hf0 : 0 ≤ thetaFirstMode u := by unfold thetaFirstMode; positivity
  have hd : 0 < 1-α := by linarith
  have h1 : thetaFirstMode u/(1-α) ≤ thetaFirstMode u +
      (1/12299:ℝ)*thetaFirstMode u*β := by
    apply (div_le_iff₀ hd).mpr
    dsimp [α]
    have hp := mul_nonneg (mul_nonneg hf0 hβ) (sub_nonneg.mpr hβ1)
    nlinarith
  have hfirst : thetaFirstMode u ≤ 2*exp (-3)*exp (-(11/2:ℝ)*u) := by
    unfold thetaFirstMode
    rw [mul_assoc, ← exp_add, mul_assoc, ← exp_add]
    apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
    have h := pi_exp_lower hu
    linarith
  have he3 : (200000/12299:ℝ) ≤ exp 3 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3) 5
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hc : (2/12299:ℝ)*exp (-3) ≤ 1/100000 := by
    rw [exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (exp_pos 3)).mpr
    linarith
  have h2 : (1/12299:ℝ)*thetaFirstMode u*β ≤ (1/100000:ℝ)*exp (-23*u) := by
    calc
      _ ≤ (1/12299:ℝ)*(2*exp (-3)*exp (-(11/2:ℝ)*u))*β := by gcongr
      _ = ((2/12299:ℝ)*exp (-3))*exp (-(47/2:ℝ)*u) := by
        have he : exp (-(11/2:ℝ)*u)*β = exp (-(47/2:ℝ)*u) := by
          dsimp [β]
          rw [← exp_add]
          congr 1
          ring
        calc
          _ = ((2/12299:ℝ)*exp (-3))*(exp (-(11/2:ℝ)*u)*β) := by ring
          _ = _ := by rw [he]
      _ ≤ (1/100000:ℝ)*exp (-23*u) := by
        apply mul_le_mul hc (exp_le_exp.mpr (by linarith)) (by positivity) (by norm_num)
  exact ht.trans (h1.trans (add_le_add le_rfl h2))

private theorem exp_neg_twentyTwo_bound : exp (-22) ≤ (3/10000000000:ℝ) := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 22) 30
  rw [exp_neg]
  apply (inv_le_iff_one_le_mul₀ (exp_pos _)).mpr
  have ht : (1:ℝ) ≤ (3/10000000000)*∑ i ∈ Finset.range 30,
      (22:ℝ)^i/i.factorial := by norm_num [Finset.sum_range_succ]
  exact ht.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

private theorem thetaFirstMode_tail_le_twentyTwo {u : ℝ} (hu : 1 ≤ u) :
    thetaFirstMode u ≤ 2*exp (-22*u) := by
  have he : (369/50:ℝ) ≤ exp 2 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 2) 10
    norm_num [Finset.sum_range_succ] at h
    linarith
  have he' := Real.add_one_le_exp (2*(u-1))
  have hprod := mul_le_mul_of_nonneg_left he' (exp_pos 2).le
  rw [← exp_add] at hprod
  have heq : 2+2*(u-1)=2*u := by ring
  rw [heq] at hprod
  have hprod' : exp 2*(2*u-1) ≤ exp (2*u) := by
    nlinarith [hprod]
  have hmul := mul_le_mul_of_nonneg_right he (show 0 ≤ 2*u-1 by linarith)
  have hpi := mul_le_mul_of_nonneg_left (hmul.trans hprod')
    (show 0 ≤ (3141592/1000000:ℝ) by norm_num)
  have hpi' := mul_le_mul_of_nonneg_right
    (show (3141592/1000000:ℝ) ≤ Real.pi by linarith [Real.pi_gt_d6]) (exp_pos (2*u)).le
  unfold thetaFirstMode
  rw [mul_assoc, ← exp_add]
  apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
  nlinarith

/-- A single tail bound through order ten, independent of the finite cells. -/
theorem integral_thetaFirstMode_weighted_tail_le_ten (p : ℕ) (hp : p ≤ 10) :
    (∫ u in Ioi (1:ℝ), u^p*thetaFirstMode u) ≤ (1/20000000000:ℝ) := by
  have hu (u : ℝ) (h : 1 ≤ u) : u^p*thetaFirstMode u ≤
      (2*exp (-10))*exp (-12*u) := by
    have hb : u ≤ exp (u-1) := by linarith [Real.add_one_le_exp (u-1)]
    have he : u^p ≤ exp (10*(u-1)) := by
      calc
        _ ≤ u^10 := pow_le_pow_right₀ h hp
        _ ≤ (exp (u-1))^10 := pow_le_pow_left₀ (by linarith) hb 10
        _ = _ := (Real.exp_nat_mul (u-1) 10).symm
    calc
      _ ≤ exp (10*(u-1))*(2*exp (-22*u)) :=
        mul_le_mul he (thetaFirstMode_tail_le_twentyTwo h)
          (by unfold thetaFirstMode; positivity) (by positivity)
      _ = _ := by
        rw [mul_comm (exp (10*(u-1))), mul_assoc, ← exp_add, mul_assoc, ← exp_add]
        congr 2
        ring
  have hi := (integrableOn_pow_mul_thetaFirstMode p).mono_set
    (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have h := integral_mono_ae hi
    ((integrableOn_exp_mul_Ioi (by norm_num : (-12:ℝ)<0) 1).const_mul (2*exp (-10))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hmem
      exact hu u hmem.le)
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-12:ℝ)<0) 1] at h
  have he : (2*exp (-10))*(-exp ((-12:ℝ)*1)/(-12)) = exp (-22)/6 := by
    norm_num
    rw [← mul_div_assoc, mul_assoc, ← exp_add]
    norm_num
    ring_nf
  rw [he] at h
  linarith [exp_neg_twentyTwo_bound]

private theorem integrableOn_pow_exp (p : ℕ) :
    IntegrableOn (fun u : ℝ => u^p*exp (-23*u)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1:ℝ))
    (s := (p:ℝ)) (b := (23:ℝ))
    (show -1 < (p:ℝ) by have h := Nat.cast_nonneg (α := ℝ) p; linarith) (by norm_num) (by norm_num)
  simpa only [rpow_natCast, rpow_one] using h

private theorem integral_pow_exp (p : ℕ) :
    (∫ u : ℝ in Ioi 0, u^p*exp (-23*u)) = (p.factorial:ℝ)/23^(p+1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (p:ℝ)+1) (r := (23:ℝ)) (by positivity) (by norm_num)
  simp only [add_sub_cancel_right, rpow_natCast] at h
  rw [Real.Gamma_nat_eq_factorial] at h
  rw [show (p:ℝ)+1 = ((p+1:ℕ):ℝ) by push_cast; rfl, rpow_natCast] at h
  simpa [one_div, inv_pow, div_eq_mul_inv, mul_comm, neg_mul] using h

/-- Full theta integral enclosure: first-mode cells, first-mode tail, and
ALL higher modes. Cross-order dependence is retained by later substitution. -/
theorem completedNativeThetaTailMoment_finite_upper_decaying (p : ℕ) (hp : p ≤ 10) :
    completedNativeThetaTailMoment p ≤
      (∫ u in (0:ℝ)..1, u^p*thetaFirstMode u) + (1/20000000000:ℝ) +
        (p.factorial:ℝ)/(100000*23^(p+1)) := by
  have hi := integrableOn_pow_mul_thetaFirstMode p
  have ht := hi.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi ht
  have htail := integral_thetaFirstMode_weighted_tail_le_ten p hp
  have h := integral_mono_ae (integrableOn_pow_mul_thetaTail p)
    (hi.add ((integrableOn_pow_exp p).const_mul (1/100000:ℝ))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have h := mul_le_mul_of_nonneg_left (thetaTail_le_first_add_decaying hu.le)
        (pow_nonneg hu.le p)
      simpa only [mul_add, mul_left_comm, mul_assoc, Pi.add_apply] using h)
  simp only [Pi.add_apply] at h
  rw [integral_add hi ((integrableOn_pow_exp p).const_mul (1/100000:ℝ)),
    integral_const_mul, integral_pow_exp] at h
  have he : (1/100000:ℝ)*((p.factorial:ℝ)/23^(p+1)) =
      (p.factorial:ℝ)/(100000*23^(p+1)) := by ring
  rw [he] at h
  unfold completedNativeThetaTailMoment
  linarith

/-- Sharper first-mode tail in the unchanged source coordinate. -/
theorem thetaFirstMode_tail_le_fortyFive {u : ℝ} (hu : 1 ≤ u) :
    thetaFirstMode u ≤ 2*exp ((223/10:ℝ)-45*u) := by
  have he : (7389/1000:ℝ) ≤ exp 2 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 2) 16
    norm_num [Finset.sum_range_succ] at h
    linarith
  have he' := Real.add_one_le_exp (2*(u-1))
  have hprod := mul_le_mul_of_nonneg_left he' (exp_pos 2).le
  rw [← exp_add, show 2+2*(u-1)=2*u by ring] at hprod
  have hmul := mul_le_mul_of_nonneg_right he (show 0 ≤ 2*u-1 by linarith)
  have hprod' : exp 2*(2*u-1) ≤ exp (2*u) := by nlinarith [hprod]
  have hpi := mul_le_mul_of_nonneg_left (hmul.trans hprod')
    (show 0 ≤ (3141592/1000000:ℝ) by norm_num)
  have hpi' := mul_le_mul_of_nonneg_right
    (show (3141592/1000000:ℝ) ≤ Real.pi by linarith [Real.pi_gt_d6]) (exp_pos (2*u)).le
  unfold thetaFirstMode
  rw [mul_assoc, ← exp_add]
  apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
  nlinarith

private theorem exp_neg_227_bound : exp (-(227/10:ℝ)) ≤ (14/100000000000:ℝ) := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 227/10) 40
  rw [exp_neg]
  apply (inv_le_iff_one_le_mul₀ (exp_pos _)).mpr
  have ht : (1:ℝ) ≤ (14/100000000000)*∑ i ∈ Finset.range 40,
      (227/10:ℝ)^i/i.factorial := by norm_num [Finset.sum_range_succ]
  exact ht.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

/-- A uniform tail enclosure through power twelve. -/
theorem integral_thetaFirstMode_weighted_tail_le_twelve (p : ℕ) (hp : p ≤ 12) :
    (∫ u in Ioi (1:ℝ), u^p*thetaFirstMode u) ≤ (9/1000000000000:ℝ) := by
  have hu (u : ℝ) (h : 1 ≤ u) : u^p*thetaFirstMode u ≤
      (2*exp (103/10))*exp (-33*u) := by
    have hb : u ≤ exp (u-1) := by linarith [Real.add_one_le_exp (u-1)]
    have he : u^p ≤ exp (12*(u-1)) := by
      calc
        _ ≤ u^12 := pow_le_pow_right₀ h hp
        _ ≤ (exp (u-1))^12 := pow_le_pow_left₀ (by linarith) hb 12
        _ = _ := (Real.exp_nat_mul (u-1) 12).symm
    calc
      _ ≤ exp (12*(u-1))*(2*exp ((223/10:ℝ)-45*u)) :=
        mul_le_mul he (thetaFirstMode_tail_le_fortyFive h)
          (by unfold thetaFirstMode; positivity) (by positivity)
      _ = _ := by
        rw [mul_comm (exp (12*(u-1))), mul_assoc, ← exp_add, mul_assoc, ← exp_add]
        congr 2
        ring
  have hi := (integrableOn_pow_mul_thetaFirstMode p).mono_set
    (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have h := integral_mono_ae hi
    ((integrableOn_exp_mul_Ioi (by norm_num : (-33:ℝ)<0) 1).const_mul (2*exp (103/10))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hmem
      exact hu u hmem.le)
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-33:ℝ)<0) 1] at h
  have he : (2*exp (103/10))*(-exp ((-33:ℝ)*1)/(-33)) = 2*exp (-(227/10:ℝ))/33 := by
    norm_num
    rw [← mul_div_assoc, mul_assoc, ← exp_add]
    norm_num
  rw [he] at h
  linarith [exp_neg_227_bound]

/-- All higher modes are included, with the sharper first-mode tail. -/
theorem completedNativeThetaTailMoment_finite_upper_twelve (p : ℕ) (hp : p ≤ 12) :
    completedNativeThetaTailMoment p ≤
      (∫ u in (0:ℝ)..1, u^p*thetaFirstMode u) + (9/1000000000000:ℝ) +
        (p.factorial:ℝ)/(100000*23^(p+1)) := by
  have hi := integrableOn_pow_mul_thetaFirstMode p
  have ht := hi.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi ht
  have htail := integral_thetaFirstMode_weighted_tail_le_twelve p hp
  have h := integral_mono_ae (integrableOn_pow_mul_thetaTail p)
    (hi.add ((integrableOn_pow_exp p).const_mul (1/100000:ℝ))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have h := mul_le_mul_of_nonneg_left (thetaTail_le_first_add_decaying hu.le)
        (pow_nonneg hu.le p)
      simpa only [mul_add, mul_left_comm, mul_assoc, Pi.add_apply] using h)
  simp only [Pi.add_apply] at h
  rw [integral_add hi ((integrableOn_pow_exp p).const_mul (1/100000:ℝ)),
    integral_const_mul, integral_pow_exp] at h
  have he : (1/100000:ℝ)*((p.factorial:ℝ)/23^(p+1)) =
      (p.factorial:ℝ)/(100000*23^(p+1)) := by ring
  rw [he] at h
  unfold completedNativeThetaTailMoment
  linarith

/-- A positive source tail is retained, rather than replaced by zero. -/
theorem integral_thetaFirstMode_weighted_tail_ge_two (p : ℕ) :
    (2/1000000000000:ℝ) ≤ ∫ u in Ioi (1:ℝ), u^p*thetaFirstMode u := by
  have hE : exp (2*(65/64:ℝ)) ≤ (762361/100000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(65/64))
      (by norm_num : 2*(65/64:ℝ) ≤ 32)).2
    have hc : thetaExpUpper (2*(65/64:ℝ)) ≤ 762361/100000 := by
      norm_num [thetaExpUpper, Finset.sum_range_succ]
    exact h.trans hc
  have hU : Real.pi*exp (2*(65/64:ℝ))-1/2 ≤ (234503/10000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hE (exp_nonneg _) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    linarith
  have hcert : (13/100000000000:ℝ)*exp (234503/10000) ≤ 2 := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 234503/10000)
      (by norm_num : (234503/10000:ℝ) ≤ 32)).2
    have hc : (13/100000000000:ℝ)*thetaExpUpper (234503/10000) ≤ 2 := by
      norm_num [thetaExpUpper, Finset.sum_range_succ]
    exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans hc
  have hpoint (u : ℝ) (hu : u ∈ Icc (1:ℝ) (65/64)) :
      (13/100000000000:ℝ) ≤ u^p*thetaFirstMode u := by
    have hx : u/2-Real.pi*exp (2*u) ≥ -(234503/10000:ℝ) := by
      have he : exp (2*u) ≤ exp (2*(65/64:ℝ)) := exp_le_exp.mpr (by linarith [hu.2])
      have h := mul_le_mul_of_nonneg_left he Real.pi_pos.le
      linarith [hu.1]
    have hlow : (13/100000000000:ℝ) ≤ thetaFirstMode u := by
      unfold thetaFirstMode
      rw [mul_assoc, ← exp_add]
      have hb : (13/100000000000:ℝ) ≤ 2*exp (-(234503/10000:ℝ)) := by
        rw [exp_neg, ← div_eq_mul_inv]
        exact (le_div_iff₀ (exp_pos _)).mpr hcert
      exact hb.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) (by norm_num))
    have hp : 1 ≤ u^p := one_le_pow₀ hu.1
    nlinarith
  have hc := intervalIntegral.integral_mono_on (by norm_num : (1:ℝ) ≤ 65/64)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (13/100000000000:ℝ)) volume 1 (65/64))
    (by apply Continuous.intervalIntegrable; unfold thetaFirstMode; fun_prop :
      IntervalIntegrable (fun u : ℝ => u^p*thetaFirstMode u) volume 1 (65/64)) hpoint
  have hi := (integrableOn_pow_mul_thetaFirstMode p).mono_set
    (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have ht := intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Ioi_subset_Ioi (by norm_num : (1:ℝ) ≤ 65/64)))
  have hn : 0 ≤ ∫ u in Ioi (65/64:ℝ), u^p*thetaFirstMode u := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hut : (65/64:ℝ) < u := hu
    have hu0 : 0 ≤ u := by linarith
    unfold thetaFirstMode
    positivity
  norm_num [intervalIntegral.integral_const, smul_eq_mul] at hc
  linarith

/-- Lower enclosure retaining a certified positive piece of the SAME source tail. -/
theorem completedNativeThetaTailMoment_finite_lower_twelve (p : ℕ) :
    (∫ u in (0:ℝ)..1, u^p*thetaFirstMode u) + (2/1000000000000:ℝ) ≤
      completedNativeThetaTailMoment p := by
  have hi := integrableOn_pow_mul_thetaFirstMode p
  have hit := hi.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi hit
  have htail := integral_thetaFirstMode_weighted_tail_ge_two p
  have hmono := integral_mono_ae hi (integrableOn_pow_mul_thetaTail p) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_le_mul_of_nonneg_left (thetaTail_ge_thetaFirstMode hu.le) (pow_nonneg hu.le p))
  unfold completedNativeThetaTailMoment
  linarith
end
end CarrySelfAdjointOperator
