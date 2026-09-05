import CarrySelfAdjointOperator.CompletedNativeThetaExponentialBounds

open Real Set Filter MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false

def thetaFirstModeFirst (u : ℝ) : ℝ :=
  (1/2-2*Real.pi*exp (2*u))*thetaFirstMode u

def thetaFirstModeSecond (u : ℝ) : ℝ :=
  (1/4-6*Real.pi*exp (2*u)+4*(Real.pi*exp (2*u))^2)*thetaFirstMode u

theorem hasDerivAt_thetaFirstMode (u : ℝ) :
    HasDerivAt thetaFirstMode (thetaFirstModeFirst u) u := by
  have h := (((hasDerivAt_id u).div_const 2).exp.const_mul 2).mul
    ((((hasDerivAt_id u).const_mul 2).exp.const_mul (-Real.pi)).exp)
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
  · simp only [id_eq, thetaFirstModeFirst, thetaFirstMode]
    ring

theorem hasDerivAt_thetaFirstModeFirst (u : ℝ) :
    HasDerivAt thetaFirstModeFirst (thetaFirstModeSecond u) u := by
  have hf := (hasDerivAt_const u (1/2:ℝ)).sub
    (((hasDerivAt_id u).const_mul 2).exp.const_mul (2*Real.pi))
  have h := hf.mul (hasDerivAt_thetaFirstMode u)
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
  · simp only [id_eq, thetaFirstModeFirst, thetaFirstModeSecond, Pi.sub_apply]
    ring

theorem convexOn_thetaFirstMode : ConvexOn ℝ (Ici 0) thetaFirstMode := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
    (f' := thetaFirstModeFirst) (f'' := thetaFirstModeSecond)
  · exact (by unfold thetaFirstMode; fun_prop : Continuous thetaFirstMode).continuousOn
  · intro u _; exact (hasDerivAt_thetaFirstMode u).hasDerivWithinAt
  · intro u _; exact (hasDerivAt_thetaFirstModeFirst u).hasDerivWithinAt
  · intro u hu
    have hu0 : 0 ≤ u := (interior_subset hu)
    have he : 1 ≤ exp (2*u) := one_le_exp_iff.mpr (by positivity)
    have ht : 3 ≤ Real.pi*exp (2*u) := by nlinarith [Real.pi_gt_three]
    unfold thetaFirstModeSecond
    apply mul_nonneg _ (by unfold thetaFirstMode; positivity)
    nlinarith [sq_nonneg (Real.pi*exp (2*u)-3)]

theorem thetaFirstMode_tangent_le {m x : ℝ} (hm : 0 ≤ m) (hx : 0 ≤ x) :
    thetaFirstMode m + thetaFirstModeFirst m*(x-m) ≤ thetaFirstMode x := by
  rcases lt_trichotomy m x with h | h | h
  · have hs := convexOn_thetaFirstMode.le_slope_of_hasDerivAt hm hx h
      (hasDerivAt_thetaFirstMode m)
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hs
    linarith
  · simp [h]
  · have hs := convexOn_thetaFirstMode.slope_le_of_hasDerivAt hx hm h
      (hasDerivAt_thetaFirstMode m)
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hs
    nlinarith

theorem thetaFirstMode_le_chord {a b x : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    thetaFirstMode x ≤
      (b-x)/(b-a)*thetaFirstMode a+(x-a)/(b-a)*thetaFirstMode b := by
  have hd : 0 < b-a := sub_pos.mpr hab
  have hw : (b-x)/(b-a)+(x-a)/(b-a) = 1 := by field_simp; ring
  have h := convexOn_thetaFirstMode.2 ha (ha.trans hab.le)
    (div_nonneg (sub_nonneg.mpr hxb) hd.le)
    (div_nonneg (sub_nonneg.mpr hax) hd.le) hw
  have he : (b-x)/(b-a)*a+(x-a)/(b-a)*b = x := by field_simp; ring
  simpa only [smul_eq_mul, he] using h

def thetaPowerMass (p : ℕ) (a b : ℝ) : ℝ :=
  (b^(p+1)-a^(p+1))/(p+1)

theorem integral_thetaPowerMass (p : ℕ) (a b : ℝ) :
    (∫ x in a..b, x^p) = thetaPowerMass p a b := by
  simp [thetaPowerMass, integral_pow]

theorem integral_thetaPower_affine (p : ℕ) (a b A B : ℝ) :
    (∫ x in a..b, x^p*(A+B*x)) =
      A*thetaPowerMass p a b+B*thetaPowerMass (p+1) a b := by
  have he : (fun x : ℝ ↦ x^p*(A+B*x)) = fun x ↦ A*x^p+B*x^(p+1) := by
    funext x; ring
  rw [he, intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop : IntervalIntegrable (fun x : ℝ ↦ A*x^p) volume a b)
    (by apply Continuous.intervalIntegrable; fun_prop : IntervalIntegrable (fun x : ℝ ↦ B*x^(p+1)) volume a b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_thetaPowerMass, integral_thetaPowerMass]

theorem thetaFirstMode_weighted_cell_lower (p : ℕ) (a b m l : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hm : 0 ≤ m)
    (hw : 0 ≤ thetaPowerMass p a b)
    (hmean : thetaPowerMass (p+1) a b = m*thetaPowerMass p a b)
    (hl : l ≤ thetaFirstMode m) :
    l*thetaPowerMass p a b ≤ ∫ x in a..b, x^p*thetaFirstMode x := by
  have h := intervalIntegral.integral_mono_on hab
    (by apply Continuous.intervalIntegrable; unfold thetaFirstModeFirst thetaFirstMode; fun_prop :
      IntervalIntegrable (fun x : ℝ ↦ x^p*(thetaFirstMode m+thetaFirstModeFirst m*(x-m))) volume a b)
    (by apply Continuous.intervalIntegrable; unfold thetaFirstMode; fun_prop :
      IntervalIntegrable (fun x : ℝ ↦ x^p*thetaFirstMode x) volume a b)
    (fun x hx ↦ mul_le_mul_of_nonneg_left (thetaFirstMode_tangent_le hm (ha.trans hx.1))
      (pow_nonneg (ha.trans hx.1) p))
  have he : (fun x : ℝ ↦ x^p*(thetaFirstMode m+thetaFirstModeFirst m*(x-m))) =
      fun x ↦ x^p*((thetaFirstMode m-thetaFirstModeFirst m*m)+thetaFirstModeFirst m*x) := by
    funext x; ring
  rw [he, integral_thetaPower_affine, hmean] at h
  nlinarith [mul_le_mul_of_nonneg_right hl hw]

theorem thetaFirstMode_weighted_cell_upper (p : ℕ) (a b A B : ℝ)
    (ha : 0 ≤ a) (hab : a < b)
    (hA : thetaFirstMode a ≤ A) (hB : thetaFirstMode b ≤ B) :
    (∫ x in a..b, x^p*thetaFirstMode x) ≤
      ((b*A-a*B)*thetaPowerMass p a b+(B-A)*thetaPowerMass (p+1) a b)/(b-a) := by
  have hd : 0 < b-a := sub_pos.mpr hab
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) :
      thetaFirstMode x ≤ (b*A-a*B)/(b-a)+(B-A)/(b-a)*x := by
    calc
      thetaFirstMode x ≤ (b-x)/(b-a)*thetaFirstMode a+(x-a)/(b-a)*thetaFirstMode b :=
        thetaFirstMode_le_chord ha hab hx.1 hx.2
      _ ≤ (b-x)/(b-a)*A+(x-a)/(b-a)*B := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hA (div_nonneg (sub_nonneg.mpr hx.2) hd.le))
          (mul_le_mul_of_nonneg_left hB (div_nonneg (sub_nonneg.mpr hx.1) hd.le))
      _ = _ := by ring
  have h := intervalIntegral.integral_mono_on hab.le
    (by apply Continuous.intervalIntegrable; unfold thetaFirstMode; fun_prop : IntervalIntegrable (fun x : ℝ ↦ x^p*thetaFirstMode x) volume a b)
    (by apply Continuous.intervalIntegrable; fun_prop : IntervalIntegrable (fun x : ℝ ↦ x^p*((b*A-a*B)/(b-a)+(B-A)/(b-a)*x)) volume a b)
    (fun x hx ↦ mul_le_mul_of_nonneg_left (hpoint x hx) (pow_nonneg (ha.trans hx.1) p))
  rw [integral_thetaPower_affine] at h
  convert h using 1
  ring

theorem integrableOn_pow_mul_thetaFirstMode (p : ℕ) :
    IntegrableOn (fun u : ℝ ↦ u^p*thetaFirstMode u) (Ioi 0) := by
  apply (integrableOn_pow_mul_thetaTail p).mono'
  · exact (by unfold thetaFirstMode; fun_prop :
      Continuous (fun u : ℝ ↦ u^p*thetaFirstMode u)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := hu.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold thetaFirstMode; positivity)]
    exact mul_le_mul_of_nonneg_left (thetaTail_ge_thetaFirstMode hu.le)
      (pow_nonneg hu.le p)

/-- The first mode decays faster than this elementary exponential beyond one. -/
theorem thetaFirstMode_le_exp_tail {u : ℝ} (hu : 1 ≤ u) :
    thetaFirstMode u ≤ 2*exp (-20*u) := by
  have he2 : (7:ℝ) ≤ exp 2 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 2) 5
    norm_num [Finset.sum_range_succ] at h
    exact h
  have hlin := Real.add_one_le_exp (2*u-2)
  have he : 7*u ≤ exp (2*u) := by
    have h := mul_le_mul he2 hlin (by linarith) (exp_nonneg 2)
    rw [← exp_add] at h
    have hh : (2:ℝ)+(2*u-2) = 2*u := by ring
    rw [hh] at h
    nlinarith
  have hpi : 21*u ≤ Real.pi*exp (2*u) := by
    have h := mul_le_mul Real.pi_gt_three.le he (by positivity) Real.pi_pos.le
    nlinarith
  unfold thetaFirstMode
  rw [mul_assoc, ← exp_add]
  apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr _) (by norm_num)
  linarith

theorem thetaFirstMode_weighted_tail_pointwise (p : ℕ) (hp : p ≤ 6)
    {u : ℝ} (hu : 1 ≤ u) :
    u^p*thetaFirstMode u ≤ (2*exp (-6))*exp (-14*u) := by
  have hp6 : u^p ≤ u^6 := pow_le_pow_right₀ hu hp
  have hb : u ≤ exp (u-1) := by linarith [Real.add_one_le_exp (u-1)]
  have he : u^p ≤ exp (6*(u-1)) := by
    calc
      u^p ≤ u^6 := hp6
      _ ≤ (exp (u-1))^6 := pow_le_pow_left₀ (by linarith) hb 6
      _ = exp (6*(u-1)) := by simpa using (Real.exp_nat_mul (u-1) 6).symm
  calc
    u^p*thetaFirstMode u ≤ exp (6*(u-1))*(2*exp (-20*u)) :=
      mul_le_mul he (thetaFirstMode_le_exp_tail hu)
        (by unfold thetaFirstMode; positivity) (exp_nonneg _)
    _ = (2*exp (-6))*exp (-14*u) := by
      rw [mul_comm (exp (6*(u-1))), mul_assoc, ← exp_add, mul_assoc, ← exp_add]
      congr 2
      ring

theorem integral_thetaFirstMode_weighted_tail_le (p : ℕ) (hp : p ≤ 6) :
    (∫ u in Ioi (1:ℝ), u^p*thetaFirstMode u) ≤ (1/100000000:ℝ) := by
  have hi : IntegrableOn (fun u : ℝ ↦ u^p*thetaFirstMode u) (Ioi 1) :=
    (integrableOn_pow_mul_thetaFirstMode p).mono_set (Ioi_subset_Ioi (by norm_num))
  have h := integral_mono_ae hi
    ((integrableOn_exp_mul_Ioi (by norm_num : (-14:ℝ)<0) 1).const_mul (2*exp (-6)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact thetaFirstMode_weighted_tail_pointwise p hp hu.le)
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-14:ℝ)<0) 1] at h
  have he : (2*exp (-6))*(-exp ((-14:ℝ)*1)/(-14)) = exp (-20)/7 := by
    norm_num
    rw [← mul_div_assoc, mul_assoc, ← exp_add]
    norm_num
    ring
  rw [he] at h
  have he20 : exp (-20) ≤ (7/100000000:ℝ) := by
    have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 20) 16
    rw [exp_neg]
    apply (inv_le_iff_one_le_mul₀ (exp_pos 20)).2
    have hf : (1:ℝ) ≤ (7/100000000)*∑ i ∈ Finset.range 16, (20:ℝ)^i/i.factorial := by
      norm_num [Finset.sum_range_succ]
    exact hf.trans (mul_le_mul_of_nonneg_left hs (by norm_num))
  linarith

theorem completedNativeThetaTailMoment_finite_lower (p : ℕ) :
    (∫ u in (0:ℝ)..1, u^p*thetaFirstMode u) ≤ completedNativeThetaTailMoment p := by
  have hi := integrableOn_pow_mul_thetaFirstMode p
  have hit := hi.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi hit
  have htail : 0 ≤ ∫ u in Ioi (1:ℝ), u^p*thetaFirstMode u := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_trans (by norm_num) hu.le
    unfold thetaFirstMode
    positivity
  have hmono := integral_mono_ae hi (integrableOn_pow_mul_thetaTail p) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_le_mul_of_nonneg_left (thetaTail_ge_thetaFirstMode hu.le) (pow_nonneg hu.le p))
  unfold completedNativeThetaTailMoment
  linarith

theorem completedNativeThetaTailMoment_finite_upper (p : ℕ) (hp : p ≤ 6) :
    completedNativeThetaTailMoment p ≤ (8000/7999:ℝ)*
      ((∫ u in (0:ℝ)..1, u^p*thetaFirstMode u)+1/100000000) := by
  have hi := integrableOn_pow_mul_thetaFirstMode p
  have hit := hi.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi hit
  have htail := integral_thetaFirstMode_weighted_tail_le p hp
  have hmono := integral_mono_ae (integrableOn_pow_mul_thetaTail p)
    (hi.const_mul (8000/7999:ℝ)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have h := mul_le_mul_of_nonneg_left (thetaTail_le_geometric_first hu.le)
        (pow_nonneg hu.le p)
      simpa only [mul_assoc, mul_left_comm] using h)
  rw [integral_const_mul] at hmono
  unfold completedNativeThetaTailMoment
  linarith

end
end CarrySelfAdjointOperator
