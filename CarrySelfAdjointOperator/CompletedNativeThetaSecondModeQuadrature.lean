import CarrySelfAdjointOperator.CompletedNativeThetaTenthSupport

open Real Set Filter MeasureTheory

namespace CarrySelfAdjointOperator
noncomputable section

/- The first and second logarithmic derivatives of the explicitly retained
second positive theta mode. -/
def thetaSecondModeFirst (u : ℝ) : ℝ :=
  2 * XiThetaCosine.thetaTailModeFirst 1 u

def thetaSecondModeSecond (u : ℝ) : ℝ :=
  2 * XiThetaCosine.thetaTailModeSecond 1 u

theorem hasDerivAt_thetaSecondMode (u : ℝ) :
    HasDerivAt thetaSecondMode (thetaSecondModeFirst u) u := by
  have h := (XiThetaCosine.hasDerivAt_thetaTailMode 1 u).const_mul 2
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun x ↦
      thetaSecondMode_eq_two_thetaTailMode_one x)
  · rfl

theorem hasDerivAt_thetaSecondModeFirst (u : ℝ) :
    HasDerivAt thetaSecondModeFirst (thetaSecondModeSecond u) u := by
  exact (XiThetaCosine.hasDerivAt_thetaTailModeFirst 1 u).const_mul 2

theorem thetaSecondModeSecond_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ thetaSecondModeSecond u := by
  unfold thetaSecondModeSecond XiThetaCosine.thetaTailModeSecond
  have he4 : Real.exp (4 * u) = Real.exp (2 * u) ^ 2 := by
    rw [show 4 * u = 2 * u + 2 * u by ring, Real.exp_add, pow_two]
  have hexp : (1 : ℝ) ≤ Real.exp (2 * u) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hpi : (3 : ℝ) ≤ Real.pi * Real.exp (2 * u) := by
    have h := mul_le_mul_of_nonneg_right (Real.pi_gt_three.le)
      (Real.exp_pos (2 * u)).le
    nlinarith
  have hfactor : 0 ≤
      (1 / 4 : ℝ) - 6 * Real.pi * ((1 + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) +
        4 * Real.pi ^ 2 * ((1 + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u) := by
    rw [he4]
    let t : ℝ := Real.pi * Real.exp (2 * u)
    have ht : (3 : ℝ) ≤ t := by exact hpi
    have hq : 0 ≤ (8 * t) * (8 * t - 3) := by
      apply mul_nonneg
      · nlinarith
      · nlinarith
    dsimp [t] at hq ⊢
    nlinarith [hq]
  have hmode : 0 ≤ XiThetaCosine.thetaTailMode 1 u := by
    unfold XiThetaCosine.thetaTailMode
    positivity
  norm_num at hfactor ⊢
  apply mul_nonneg
  · exact hfactor
  · exact hmode

theorem convexOn_thetaSecondMode : ConvexOn ℝ (Ici 0) thetaSecondMode := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
    (f' := thetaSecondModeFirst) (f'' := thetaSecondModeSecond)
  · exact (continuous_iff_continuousAt.2 (fun u ↦
      (hasDerivAt_thetaSecondMode u).continuousAt)).continuousOn
  · intro u _
    exact (hasDerivAt_thetaSecondMode u).hasDerivWithinAt
  · intro u _
    exact (hasDerivAt_thetaSecondModeFirst u).hasDerivWithinAt
  · intro u hu
    exact thetaSecondModeSecond_nonneg (interior_subset hu)

theorem thetaSecondMode_tangent_le {m x : ℝ} (hm : 0 ≤ m) (hx : 0 ≤ x) :
    thetaSecondMode m + thetaSecondModeFirst m * (x-m) ≤ thetaSecondMode x := by
  rcases lt_trichotomy m x with h | h | h
  · have hs := convexOn_thetaSecondMode.le_slope_of_hasDerivAt hm hx h
      (hasDerivAt_thetaSecondMode m)
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hs
    linarith
  · simp [h]
  · have hs := convexOn_thetaSecondMode.slope_le_of_hasDerivAt hx hm h
      (hasDerivAt_thetaSecondMode m)
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hs
    nlinarith

theorem thetaSecondMode_le_chord {a b x : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    thetaSecondMode x ≤
      (b-x)/(b-a)*thetaSecondMode a+(x-a)/(b-a)*thetaSecondMode b := by
  have hd : 0 < b-a := sub_pos.mpr hab
  have hw : (b-x)/(b-a)+(x-a)/(b-a) = 1 := by field_simp; ring
  have h := convexOn_thetaSecondMode.2 ha (ha.trans hab.le)
    (div_nonneg (sub_nonneg.mpr hxb) hd.le)
    (div_nonneg (sub_nonneg.mpr hax) hd.le) hw
  have he : (b-x)/(b-a)*a+(x-a)/(b-a)*b = x := by field_simp; ring
  simpa only [smul_eq_mul, he] using h

theorem thetaSecondMode_weighted_cell_lower (p : ℕ) (a b m l : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hm : 0 ≤ m)
    (hw : 0 ≤ thetaPowerMass p a b)
    (hmean : thetaPowerMass (p+1) a b = m*thetaPowerMass p a b)
    (hl : l ≤ thetaSecondMode m) :
    l*thetaPowerMass p a b ≤ ∫ x in a..b, x^p*thetaSecondMode x := by
  have h := intervalIntegral.integral_mono_on hab
    (by
      apply Continuous.intervalIntegrable
      unfold thetaSecondModeFirst thetaSecondMode
        XiThetaCosine.thetaTailModeFirst XiThetaCosine.thetaTailMode
      fun_prop : IntervalIntegrable
        (fun x : ℝ ↦ x^p*(thetaSecondMode m +
          thetaSecondModeFirst m*(x-m))) volume a b)
    (by
      apply Continuous.intervalIntegrable
      unfold thetaSecondMode
      fun_prop : IntervalIntegrable
        (fun x : ℝ ↦ x^p*thetaSecondMode x) volume a b)
    (fun x hx ↦ mul_le_mul_of_nonneg_left
      (thetaSecondMode_tangent_le hm (ha.trans hx.1))
      (pow_nonneg (ha.trans hx.1) p))
  have he : (fun x : ℝ ↦ x^p*(thetaSecondMode m+
      thetaSecondModeFirst m*(x-m))) =
      fun x ↦ x^p*((thetaSecondMode m-thetaSecondModeFirst m*m)+
        thetaSecondModeFirst m*x) := by
    funext x
    ring
  rw [he, integral_thetaPower_affine, hmean] at h
  nlinarith [mul_le_mul_of_nonneg_right hl hw]

theorem thetaSecondMode_weighted_cell_upper (p : ℕ) (a b A B : ℝ)
    (ha : 0 ≤ a) (hab : a < b)
    (hA : thetaSecondMode a ≤ A) (hB : thetaSecondMode b ≤ B) :
    (∫ x in a..b, x^p*thetaSecondMode x) ≤
      ((b*A-a*B)*thetaPowerMass p a b+(B-A)*thetaPowerMass (p+1) a b)/(b-a) := by
  have hd : 0 < b-a := sub_pos.mpr hab
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) :
      thetaSecondMode x ≤ (b-x)/(b-a)*thetaSecondMode a+
        (x-a)/(b-a)*thetaSecondMode b :=
    thetaSecondMode_le_chord ha hab hx.1 hx.2
  have hpoint' (x : ℝ) (hx : x ∈ Icc a b) :
      thetaSecondMode x ≤
        (b*A-a*B)/(b-a)+(B-A)/(b-a)*x := by
    calc
      thetaSecondMode x ≤ (b-x)/(b-a)*thetaSecondMode a+
          (x-a)/(b-a)*thetaSecondMode b := hpoint x hx
      _ ≤ (b-x)/(b-a)*A+(x-a)/(b-a)*B := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hA
            (div_nonneg (sub_nonneg.mpr hx.2) hd.le))
          (mul_le_mul_of_nonneg_left hB
            (div_nonneg (sub_nonneg.mpr hx.1) hd.le))
      _ = _ := by ring
  have h := intervalIntegral.integral_mono_on hab.le
    (by
      apply Continuous.intervalIntegrable
      unfold thetaSecondMode
      fun_prop : IntervalIntegrable
        (fun x : ℝ ↦ x^p*thetaSecondMode x) volume a b)
    (by
      apply Continuous.intervalIntegrable
      fun_prop : IntervalIntegrable
        (fun x : ℝ ↦ x^p*((b*A-a*B)/(b-a)+(B-A)/(b-a)*x)) volume a b)
    (fun x hx ↦ mul_le_mul_of_nonneg_left (hpoint' x hx)
      (pow_nonneg (ha.trans hx.1) p))
  rw [integral_thetaPower_affine] at h
  convert h using 1
  ring

end
end CarrySelfAdjointOperator
