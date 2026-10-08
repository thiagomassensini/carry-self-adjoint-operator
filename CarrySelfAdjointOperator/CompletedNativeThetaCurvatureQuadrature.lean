import CarrySelfAdjointOperator.CompletedNativeThetaFirstModeQuadrature

/-! Curvature-corrected enclosures of the SAME first theta-mode integrals.
The correction is a certified lower bound for its second derivative; no
source, coefficient, metric or target moment is modified. -/
namespace CarrySelfAdjointOperator
open Real Set Filter MeasureTheory
noncomputable section
set_option autoImplicit false

private theorem thetaFirstMode_antitone : AntitoneOn thetaFirstMode (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (by unfold thetaFirstMode; fun_prop : Continuous thetaFirstMode).continuousOn
  · intro u _
    exact (hasDerivAt_thetaFirstMode u).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu0 : 0 ≤ u := interior_subset hu
    rw [(hasDerivAt_thetaFirstMode u).deriv]
    unfold thetaFirstModeFirst
    have he := one_le_exp_iff.mpr (show 0 ≤ 2*u by positivity)
    have hp : 3 ≤ Real.pi*exp (2*u) := by nlinarith [Real.pi_gt_three]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (by unfold thetaFirstMode; positivity)

/-- A concrete endpoint-based lower bound of curvature, uniform on the cell. -/
theorem thetaFirstModeSecond_cell_lower (a b Q l : ℝ)
    (ha : 0 ≤ a) (hQ : 3 ≤ Q) (hQa : Q ≤ Real.pi*exp (2*a))
    (hl : 0 ≤ l) (hlb : l ≤ thetaFirstMode b) :
    ∀ u ∈ Icc a b,
      (1/4-6*Q+4*Q^2)*l ≤ thetaFirstModeSecond u := by
  intro u hu
  have hqu : Q ≤ Real.pi*exp (2*u) := hQa.trans
    (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith [hu.1])) Real.pi_pos.le)
  have hpoly : 1/4-6*Q+4*Q^2 ≤
      1/4-6*(Real.pi*exp (2*u))+4*(Real.pi*exp (2*u))^2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hqu)
      (show 0 ≤ 4*(Real.pi*exp (2*u)+Q)-6 by linarith)
    nlinarith
  have hnonneg : 0 ≤ 1/4-6*Q+4*Q^2 := by nlinarith [sq_nonneg (Q-3)]
  have hfu : l ≤ thetaFirstMode u := hlb.trans
    (thetaFirstMode_antitone (ha.trans hu.1) (ha.trans (hu.1.trans hu.2)) hu.2)
  unfold thetaFirstModeSecond
  simpa only [mul_assoc] using mul_le_mul hpoly hfu hl (hnonneg.trans hpoly)

private theorem correctedTheta_convex (a b γ : ℝ)
    (hg : ∀ u ∈ Icc a b, γ ≤ thetaFirstModeSecond u) :
    ConvexOn ℝ (Icc a b) (fun u => thetaFirstMode u - γ/2*u^2) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
    (f' := fun u => thetaFirstModeFirst u - γ*u)
    (f'' := fun u => thetaFirstModeSecond u - γ)
  · exact (by unfold thetaFirstMode; fun_prop :
      Continuous (fun u => thetaFirstMode u - γ/2*u^2)).continuousOn
  · intro u _
    have hp : HasDerivAt (fun x : ℝ => γ/2*x^2) (γ*u) u :=
      (((hasDerivAt_id u).pow 2).const_mul (γ/2)).congr_deriv (by simp only [id_eq]; ring)
    exact ((hasDerivAt_thetaFirstMode u).sub hp).hasDerivWithinAt
  · intro u _
    convert ((hasDerivAt_thetaFirstModeFirst u).sub
      ((hasDerivAt_id u).const_mul γ)).hasDerivWithinAt using 1 <;> (first | rfl | simp)
  · intro u hu
    exact sub_nonneg.mpr (hg u (interior_subset hu))

/-- Tangent plus certified curvature, with every correction term retained. -/
theorem thetaFirstMode_curvature_tangent (a b γ m x : ℝ)
    (hg : ∀ u ∈ Icc a b, γ ≤ thetaFirstModeSecond u)
    (hm : m ∈ Icc a b) (hx : x ∈ Icc a b) :
    thetaFirstMode m + thetaFirstModeFirst m*(x-m) + γ/2*(x-m)^2 ≤
      thetaFirstMode x := by
  have hcv := correctedTheta_convex a b γ hg
  have hd : HasDerivAt (fun u => thetaFirstMode u-γ/2*u^2)
      (thetaFirstModeFirst m-γ*m) m := by
    have hp : HasDerivAt (fun x : ℝ => γ/2*x^2) (γ*m) m :=
      (((hasDerivAt_id m).pow 2).const_mul (γ/2)).congr_deriv (by simp only [id_eq]; ring)
    exact (hasDerivAt_thetaFirstMode m).sub hp
  rcases lt_trichotomy m x with h | h | h
  · have hs := hcv.le_slope_of_hasDerivAt hm hx h hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hs
    nlinarith
  · simp [h]
  · have hs := hcv.slope_le_of_hasDerivAt hx hm h hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hs
    nlinarith

/-- Chord minus certified curvature, in the original theta coordinate. -/
theorem thetaFirstMode_curvature_chord (a b γ x : ℝ)
    (hg : ∀ u ∈ Icc a b, γ ≤ thetaFirstModeSecond u)
    (hab : a < b) (hx : x ∈ Icc a b) :
    thetaFirstMode x ≤ (b-x)/(b-a)*thetaFirstMode a +
      (x-a)/(b-a)*thetaFirstMode b - γ/2*(b-x)*(x-a) := by
  have hcv := correctedTheta_convex a b γ hg
  have hd := sub_pos.mpr hab
  have hw : (b-x)/(b-a)+(x-a)/(b-a) = 1 := by field_simp; ring
  have h := hcv.2 ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩
    (div_nonneg (sub_nonneg.mpr hx.2) hd.le)
    (div_nonneg (sub_nonneg.mpr hx.1) hd.le) hw
  have he : (b-x)/(b-a)*a+(x-a)/(b-a)*b = x := by field_simp; ring
  simp only [smul_eq_mul, he] at h
  have ht : (b-x)/(b-a)*(thetaFirstMode a-γ/2*a^2)+
      (x-a)/(b-a)*(thetaFirstMode b-γ/2*b^2) =
      (b-x)/(b-a)*thetaFirstMode a+(x-a)/(b-a)*thetaFirstMode b -
        γ/2*(b-x)*(x-a)-γ/2*x^2 := by field_simp; ring
  rw [ht] at h
  linarith

private theorem integral_quadratic (p : ℕ) (a b A B C : ℝ) :
    (∫ x in a..b, x^p*(A+B*x+C*x^2)) =
      A*thetaPowerMass p a b+B*thetaPowerMass (p+1) a b+C*thetaPowerMass (p+2) a b := by
  have he : (fun x : ℝ => x^p*(A+B*x+C*x^2)) =
      fun x => A*x^p+B*x^(p+1)+C*x^(p+2) := by funext x; ring
  rw [he, intervalIntegral.integral_add, intervalIntegral.integral_add]
  · simp only [intervalIntegral.integral_const_mul, integral_thetaPowerMass]
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- Improved lower cell integral by integrating the same source tangent. -/
theorem thetaFirstMode_weighted_curvature_cell_lower
    (p : ℕ) (a b m l γ : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hm : m ∈ Icc a b)
    (hg : ∀ u ∈ Icc a b, γ ≤ thetaFirstModeSecond u)
    (hw : 0 ≤ thetaPowerMass p a b)
    (hmean : thetaPowerMass (p+1) a b = m*thetaPowerMass p a b)
    (hl : l ≤ thetaFirstMode m) :
    l*thetaPowerMass p a b + γ/2*(thetaPowerMass (p+2) a b-m^2*thetaPowerMass p a b) ≤
      ∫ x in a..b, x^p*thetaFirstMode x := by
  have h := intervalIntegral.integral_mono_on hab
    (by apply Continuous.intervalIntegrable; unfold thetaFirstModeFirst thetaFirstMode; fun_prop :
      IntervalIntegrable (fun x : ℝ => x^p*(thetaFirstMode m+thetaFirstModeFirst m*(x-m)+γ/2*(x-m)^2)) volume a b)
    (by apply Continuous.intervalIntegrable; unfold thetaFirstMode; fun_prop :
      IntervalIntegrable (fun x : ℝ => x^p*thetaFirstMode x) volume a b)
    (fun x hx => mul_le_mul_of_nonneg_left
      (thetaFirstMode_curvature_tangent a b γ m x hg hm hx) (pow_nonneg (ha.trans hx.1) p))
  have he : (fun x : ℝ => x^p*(thetaFirstMode m+thetaFirstModeFirst m*(x-m)+γ/2*(x-m)^2)) =
      fun x => x^p*((thetaFirstMode m-thetaFirstModeFirst m*m+γ/2*m^2)+
        (thetaFirstModeFirst m-γ*m)*x+(γ/2)*x^2) := by funext x; ring
  rw [he, integral_quadratic, hmean] at h
  nlinarith [mul_le_mul_of_nonneg_right hl hw]

/-- Improved upper cell integral by integrating the corrected source chord. -/
theorem thetaFirstMode_weighted_curvature_cell_upper
    (p : ℕ) (a b A B γ : ℝ)
    (ha : 0 ≤ a) (hab : a < b)
    (hg : ∀ u ∈ Icc a b, γ ≤ thetaFirstModeSecond u)
    (hA : thetaFirstMode a ≤ A) (hB : thetaFirstMode b ≤ B) :
    (∫ x in a..b, x^p*thetaFirstMode x) ≤
      ((b*A-a*B)*thetaPowerMass p a b+(B-A)*thetaPowerMass (p+1) a b)/(b-a) -
        γ/2*(-thetaPowerMass (p+2) a b+(a+b)*thetaPowerMass (p+1) a b-a*b*thetaPowerMass p a b) := by
  have hd := sub_pos.mpr hab
  have ht (x : ℝ) (hx : x ∈ Icc a b) : thetaFirstMode x ≤
      ((b*A-a*B)/(b-a)+γ/2*a*b)+
        ((B-A)/(b-a)-γ/2*(a+b))*x+(γ/2)*x^2 := by
    have h := thetaFirstMode_curvature_chord a b γ x hg hab hx
    have hmono := add_le_add
      (mul_le_mul_of_nonneg_left hA (div_nonneg (sub_nonneg.mpr hx.2) hd.le))
      (mul_le_mul_of_nonneg_left hB (div_nonneg (sub_nonneg.mpr hx.1) hd.le))
    have he : (b-x)/(b-a)*A+(x-a)/(b-a)*B-γ/2*(b-x)*(x-a) =
      ((b*A-a*B)/(b-a)+γ/2*a*b)+((B-A)/(b-a)-γ/2*(a+b))*x+(γ/2)*x^2 := by ring
    rw [← he]
    linarith
  have h := intervalIntegral.integral_mono_on hab.le
    (by apply Continuous.intervalIntegrable; unfold thetaFirstMode; fun_prop :
      IntervalIntegrable (fun x : ℝ => x^p*thetaFirstMode x) volume a b)
    (by apply Continuous.intervalIntegrable; fun_prop :
      IntervalIntegrable (fun x : ℝ => x^p*(((b*A-a*B)/(b-a)+γ/2*a*b)+
        ((B-A)/(b-a)-γ/2*(a+b))*x+(γ/2)*x^2)) volume a b)
    (fun x hx => mul_le_mul_of_nonneg_left (ht x hx) (pow_nonneg (ha.trans hx.1) p))
  rw [integral_quadratic] at h
  convert h using 1
  ring
end
end CarrySelfAdjointOperator
