import CarrySelfAdjointOperator.CompletedNativeThetaFirstModeQuadrature

open Real Set Filter MeasureTheory

namespace CarrySelfAdjointOperator

noncomputable section

private theorem exp_neg_1178097_div_125000_lt :
    Real.exp (-(1178097 / 125000 : ℝ)) < (1 / 12300 : ℝ) := by
  have hseries := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 1178097 / 125000) 30
  rw [Real.exp_neg, inv_lt_iff_one_lt_mul₀
    (Real.exp_pos (1178097 / 125000 : ℝ))]
  have hfinite : (1 : ℝ) < (1 / 12300 : ℝ) *
      ∑ i ∈ Finset.range 30, (1178097 / 125000 : ℝ) ^ i / i.factorial := by
    norm_num [Finset.sum_range_succ]
  exact hfinite.trans_le (mul_le_mul_of_nonneg_left hseries (by norm_num))

theorem thetaTailMode_le_geometric_refined {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    XiThetaCosine.thetaTailMode n u ≤ XiThetaCosine.thetaTailMode 0 u *
      (1 / 12300 : ℝ) ^ n := by
  have hindex :
      (1 : ℝ) + 3 * (n : ℝ) ≤ (((n + 1 : ℕ) : ℝ) ^ 2) := by
    cases n with
    | zero => norm_num
    | succ k =>
        norm_num [Nat.cast_add, Nat.cast_one]
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hkprod : 0 ≤ (k : ℝ) * ((k : ℝ) + 1) := by positivity
        nlinarith
  have hexpOne : (1 : ℝ) ≤ Real.exp (2 * u) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num) hu)
  have hpiExp : (3141592 / 1000000 : ℝ) ≤ Real.pi * Real.exp (2 * u) := by
    calc
      (3141592 / 1000000 : ℝ) ≤ (3141592 / 1000000 : ℝ) * Real.exp (2 * u) := by
        nlinarith
      _ ≤ Real.pi * Real.exp (2 * u) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_d6]) (Real.exp_pos _).le
  have hdiff :
      3 * (n : ℝ) ≤ (((n + 1 : ℕ) : ℝ) ^ 2) - 1 := by
    linarith
  have hproduct :
      (1178097 / 125000 : ℝ) * (n : ℝ) ≤
        (Real.pi * Real.exp (2 * u)) *
          ((((n + 1 : ℕ) : ℝ) ^ 2) - 1) := by
    have hmul := mul_le_mul hpiExp hdiff
      (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
      (mul_nonneg Real.pi_pos.le (Real.exp_pos _).le)
    nlinarith
  have hdecay :
      Real.exp
          (-Real.pi * ((((n + 1 : ℕ) : ℝ) ^ 2) - 1) *
            Real.exp (2 * u)) ≤
        (1 / 12300 : ℝ) ^ n := by
    calc
      Real.exp
          (-Real.pi * ((((n + 1 : ℕ) : ℝ) ^ 2) - 1) *
            Real.exp (2 * u)) ≤
          Real.exp (-(1178097 / 125000 : ℝ) * (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = Real.exp (-(1178097 / 125000 : ℝ)) ^ n := by
        convert Real.exp_nat_mul (-(1178097 / 125000 : ℝ)) n using 1
        all_goals ring_nf
      _ ≤ (1 / 12300 : ℝ) ^ n :=
        pow_le_pow_left₀ (Real.exp_nonneg _) exp_neg_1178097_div_125000_lt.le n
  have hsplit :
      Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * u)) =
        Real.exp (-Real.pi * Real.exp (2 * u)) *
          Real.exp
            (-Real.pi * ((((n + 1 : ℕ) : ℝ) ^ 2) - 1) *
              Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  unfold XiThetaCosine.thetaTailMode
  rw [hsplit]
  have hfactor :
      0 ≤ Real.exp (u / 2) * Real.exp (-Real.pi * Real.exp (2 * u)) := by
    positivity
  calc
    Real.exp (u / 2) *
        (Real.exp (-Real.pi * Real.exp (2 * u)) *
          Real.exp
            (-Real.pi * ((((n + 1 : ℕ) : ℝ) ^ 2) - 1) *
              Real.exp (2 * u))) =
        (Real.exp (u / 2) * Real.exp (-Real.pi * Real.exp (2 * u))) *
          Real.exp
            (-Real.pi * ((((n + 1 : ℕ) : ℝ) ^ 2) - 1) *
              Real.exp (2 * u)) := by ring_nf
    _ ≤ (Real.exp (u / 2) * Real.exp (-Real.pi * Real.exp (2 * u))) *
        (1 / 12300 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left hdecay hfactor
    _ = Real.exp (u / 2) *
        Real.exp (-Real.pi * (((0 + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * u)) *
          (1 / 12300 : ℝ) ^ n := by norm_num

theorem thetaTail_le_geometric_first_refined {u : ℝ} (hu : 0 ≤ u) :
    XiThetaCosine.thetaTail u ≤ (12300 / 12299 : ℝ) * thetaFirstMode u := by
  rw [XiThetaCosine.thetaTail_eq_two_mul_tsum]
  have hgeom : Summable (fun n : ℕ ↦
      XiThetaCosine.thetaTailMode 0 u * (1 / 12300 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num :
      (1 / 12300 : ℝ) < 1)).mul_left _
  have hsum := (XiThetaCosine.summable_thetaTailMode u).tsum_le_tsum
    (thetaTailMode_le_geometric_refined hu) hgeom
  calc
    2 * ∑' n : ℕ, XiThetaCosine.thetaTailMode n u ≤
        2 * ∑' n : ℕ, XiThetaCosine.thetaTailMode 0 u * (1 / 12300 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (12300 / 12299 : ℝ) * thetaFirstMode u := by
      rw [tsum_mul_left,
        tsum_geometric_of_lt_one (by norm_num) (by norm_num :
          (1 / 12300 : ℝ) < 1)]
      unfold thetaFirstMode XiThetaCosine.thetaTailMode
      norm_num
      ring_nf

theorem thetaFirstMode_weighted_tail_pointwise_eight (p : ℕ) (hp : p ≤ 8)
    {u : ℝ} (hu : 1 ≤ u) :
    u^p*thetaFirstMode u ≤ (2*exp (-8))*exp (-12*u) := by
  have hp8 : u^p ≤ u^8 := pow_le_pow_right₀ hu hp
  have hb : u ≤ exp (u-1) := by linarith [Real.add_one_le_exp (u-1)]
  have he : u^p ≤ exp (8*(u-1)) := by
    calc
      u^p ≤ u^8 := hp8
      _ ≤ (exp (u-1))^8 := pow_le_pow_left₀ (by linarith) hb 8
      _ = exp (8*(u-1)) := by simpa using (Real.exp_nat_mul (u-1) 8).symm
  calc
    u^p*thetaFirstMode u ≤ exp (8*(u-1))*(2*exp (-20*u)) :=
      mul_le_mul he (thetaFirstMode_le_exp_tail hu)
        (by unfold thetaFirstMode; positivity) (exp_nonneg _)
    _ = (2*exp (-8))*exp (-12*u) := by
      rw [mul_comm (exp (8*(u-1))), mul_assoc, ← exp_add, mul_assoc, ← exp_add]
      congr 2
      ring_nf

private theorem exp_neg_twenty_le_three_div_billion :
    exp (-20) ≤ (3 / 1000000000 : ℝ) := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 20) 23
  rw [exp_neg]
  apply (inv_le_iff_one_le_mul₀ (exp_pos 20)).2
  have hf : (1:ℝ) ≤ (3 / 1000000000) *
      ∑ i ∈ Finset.range 23, (20:ℝ)^i/i.factorial := by
    norm_num [Finset.sum_range_succ]
  exact hf.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

theorem integral_thetaFirstMode_weighted_tail_le_eight (p : ℕ) (hp : p ≤ 8) :
    (∫ u in Ioi (1:ℝ), u^p*thetaFirstMode u) ≤ (1/2000000000:ℝ) := by
  have hi : IntegrableOn (fun u : ℝ ↦ u^p*thetaFirstMode u) (Ioi 1) :=
    (integrableOn_pow_mul_thetaFirstMode p).mono_set (Ioi_subset_Ioi (by norm_num))
  have h := integral_mono_ae hi
    ((integrableOn_exp_mul_Ioi (by norm_num : (-12:ℝ)<0) 1).const_mul (2*exp (-8)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact thetaFirstMode_weighted_tail_pointwise_eight p hp hu.le)
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-12:ℝ)<0) 1] at h
  have he : (2*exp (-8))*(-exp ((-12:ℝ)*1)/(-12)) = exp (-20)/6 := by
    norm_num
    rw [← mul_div_assoc, mul_assoc, ← exp_add]
    norm_num
    ring_nf
  rw [he] at h
  nlinarith [exp_neg_twenty_le_three_div_billion]

theorem completedNativeThetaTailMoment_finite_upper_refined (p : ℕ) (hp : p ≤ 8) :
    completedNativeThetaTailMoment p ≤ (12300/12299:ℝ)*
      ((∫ u in (0:ℝ)..1, u^p*thetaFirstMode u)+1/2000000000) := by
  have hi := integrableOn_pow_mul_thetaFirstMode p
  have hit := hi.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi hit
  have htail := integral_thetaFirstMode_weighted_tail_le_eight p hp
  have hmono := integral_mono_ae (integrableOn_pow_mul_thetaTail p)
    (hi.const_mul (12300/12299:ℝ)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have h := mul_le_mul_of_nonneg_left (thetaTail_le_geometric_first_refined hu.le)
        (pow_nonneg hu.le p)
      simpa only [mul_assoc, mul_left_comm] using h)
  rw [integral_const_mul] at hmono
  unfold completedNativeThetaTailMoment
  linarith

end

end CarrySelfAdjointOperator
