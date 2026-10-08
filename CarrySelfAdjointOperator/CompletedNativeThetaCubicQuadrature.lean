import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
import Mathlib.Analysis.Calculus.Taylor

/-! Cubic cell enclosures of the unchanged first theta mode. The fourth
source derivative controls the remainder; no moment or metric enters. -/
namespace CarrySelfAdjointOperator
open Real Set Filter MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

def thetaFirstModeThird (u : ℝ) : ℝ :=
  (1/8-31/2*(Real.pi*exp (2*u))+30*(Real.pi*exp (2*u))^2-
    8*(Real.pi*exp (2*u))^3)*thetaFirstMode u

def thetaFirstModeFourth (u : ℝ) : ℝ :=
  (1/16-39*(Real.pi*exp (2*u))+166*(Real.pi*exp (2*u))^2-
    112*(Real.pi*exp (2*u))^3+16*(Real.pi*exp (2*u))^4)*thetaFirstMode u

theorem hasDerivAt_thetaFirstModeSecond_cubic (u : ℝ) :
    HasDerivAt thetaFirstModeSecond (thetaFirstModeThird u) u := by
  have hq := (((hasDerivAt_id u).const_mul 2).exp.const_mul Real.pi)
  have hp := ((hasDerivAt_const u (1/4:ℝ)).sub (hq.const_mul 6)).add
    ((hq.pow 2).const_mul 4)
  have h := hp.mul (hasDerivAt_thetaFirstMode u)
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun x => by
      simp only [thetaFirstModeSecond, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
      ring)
  · simp only [id_eq, thetaFirstModeFirst, thetaFirstModeThird, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
    ring

theorem hasDerivAt_thetaFirstModeThird (u : ℝ) :
    HasDerivAt thetaFirstModeThird (thetaFirstModeFourth u) u := by
  have hq := (((hasDerivAt_id u).const_mul 2).exp.const_mul Real.pi)
  have hp := (((hasDerivAt_const u (1/8:ℝ)).sub (hq.const_mul (31/2))).add
    ((hq.pow 2).const_mul 30)).sub ((hq.pow 3).const_mul 8)
  have h := hp.mul (hasDerivAt_thetaFirstMode u)
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun x => by
      simp only [thetaFirstModeThird, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq])
  · simp only [id_eq, thetaFirstModeFirst, thetaFirstModeFourth, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
    ring

theorem thetaFirstMode_cubic_derivatives :
    iteratedDeriv 1 thetaFirstMode = thetaFirstModeFirst ∧
    iteratedDeriv 2 thetaFirstMode = thetaFirstModeSecond ∧
    iteratedDeriv 3 thetaFirstMode = thetaFirstModeThird ∧
    iteratedDeriv 4 thetaFirstMode = thetaFirstModeFourth := by
  have h1 : iteratedDeriv 1 thetaFirstMode = thetaFirstModeFirst := by
    funext u; simpa using (hasDerivAt_thetaFirstMode u).deriv
  have h2 : iteratedDeriv 2 thetaFirstMode = thetaFirstModeSecond := by
    rw [show 2=1+1 from rfl, iteratedDeriv_succ, h1]
    funext u; exact (hasDerivAt_thetaFirstModeFirst u).deriv
  have h3 : iteratedDeriv 3 thetaFirstMode = thetaFirstModeThird := by
    rw [show 3=2+1 from rfl, iteratedDeriv_succ, h2]
    funext u; exact (hasDerivAt_thetaFirstModeSecond_cubic u).deriv
  have h4 : iteratedDeriv 4 thetaFirstMode = thetaFirstModeFourth := by
    rw [show 4=3+1 from rfl, iteratedDeriv_succ, h3]
    funext u; exact (hasDerivAt_thetaFirstModeThird u).deriv
  exact ⟨h1,h2,h3,h4⟩

theorem thetaFirstMode_cubic_remainder (a b C x : ℝ)
    (hab : a < b) (hx : x ∈ Icc a b)
    (hC : ∀ y ∈ Icc a b, |thetaFirstModeFourth y| ≤ C) :
    |thetaFirstMode x - (thetaFirstMode a + thetaFirstModeFirst a*(x-a) +
      thetaFirstModeSecond a/2*(x-a)^2 + thetaFirstModeThird a/6*(x-a)^3)| ≤
      C*(x-a)^4/6 := by
  have hf : ContDiff ℝ 4 thetaFirstMode := by unfold thetaFirstMode; fun_prop
  have hd := thetaFirstMode_cubic_derivatives
  have he (j : ℕ) (hj : j ≤ 4) (y : ℝ) (hy : y ∈ Icc a b) :
      iteratedDerivWithin j thetaFirstMode (Icc a b) y = iteratedDeriv j thetaFirstMode y :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
      (hf.of_le (by exact_mod_cast hj)).contDiffAt hy
  have h := taylor_mean_remainder_bound (n:=3) hab.le hf.contDiffOn hx (by
    intro y hy
    rw [he 4 (by omega) y hy, hd.2.2.2, Real.norm_eq_abs]
    exact hC y hy)
  rw [taylorWithinEval_succ, taylorWithinEval_succ, taylorWithinEval_succ,
    taylor_within_zero_eval, he 1 (by omega) a ⟨le_rfl,hab.le⟩,
    he 2 (by omega) a ⟨le_rfl,hab.le⟩, he 3 (by omega) a ⟨le_rfl,hab.le⟩,
    hd.1, hd.2.1, hd.2.2.1] at h
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat, Real.norm_eq_abs,
    smul_eq_mul, one_mul, inv_one] at h
  convert h using 1
  congr 1
  ring

/-- More precise pi input for the SAME exponential node enclosure. -/
theorem thetaFirstMode_precise_node_bounds (q el eu l r : ℝ)
    (hq : 0 ≤ q) (hq2 : 2*q ≤ 32)
    (hel : 0 ≤ el) (_heu : 0 ≤ eu)
    (hinnerL : el ≤ thetaExpLower (2*q))
    (hinnerU : thetaExpUpper (2*q) ≤ eu)
    (hargL : 0 ≤ (314159265358979323846/100000000000000000000 : ℝ)*el-q/2)
    (hargU : (314159265358979323847/100000000000000000000 : ℝ)*eu-q/2 ≤ 32)
    (hl : 0 ≤ l) (hr : 0 ≤ r)
    (hlcert : l * thetaExpUpper ((314159265358979323847/100000000000000000000 : ℝ)*eu-q/2) ≤ 2)
    (hrcert : 2 ≤ r * thetaExpLower ((314159265358979323846/100000000000000000000 : ℝ)*el-q/2)) :
    l ≤ thetaFirstMode q ∧ thetaFirstMode q ≤ r := by
  have hi := thetaExp_bounds (x := 2*q) (by positivity) hq2
  have heL : el ≤ exp (2*q) := hinnerL.trans hi.1
  have heU : exp (2*q) ≤ eu := hi.2.trans hinnerU
  have hpiL : (314159265358979323846/100000000000000000000 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
  have hpiU : Real.pi ≤ (314159265358979323847/100000000000000000000 : ℝ) := by linarith [Real.pi_lt_d20]
  have hlo : (314159265358979323846/100000000000000000000 : ℝ)*el-q/2 ≤ Real.pi*exp (2*q)-q/2 := by gcongr
  have hhi : Real.pi*exp (2*q)-q/2 ≤ (314159265358979323847/100000000000000000000 : ℝ)*eu-q/2 := by gcongr
  have hlow := thetaExp_bounds hargL (hlo.trans hhi |>.trans hargU)
  have hupp := thetaExp_bounds (hargL.trans (hlo.trans hhi)) hargU
  have hEq : thetaFirstMode q = 2 / exp (Real.pi*exp (2*q)-q/2) := by
    unfold thetaFirstMode
    rw [mul_assoc, ← exp_add]
    rw [show q/2 + -Real.pi*exp (2*q) = -(Real.pi*exp (2*q)-q/2) by ring, exp_neg]
    exact (div_eq_mul_inv _ _).symm
  rw [hEq]
  constructor
  · apply (le_div_iff₀ (exp_pos _)).2
    exact (mul_le_mul_of_nonneg_left ((exp_le_exp.mpr hhi).trans hupp.2) hl).trans hlcert
  · apply (div_le_iff₀ (exp_pos _)).2
    exact hrcert.trans (mul_le_mul_of_nonneg_left (hlow.1.trans (exp_le_exp.mpr hlo)) hr)

/-- Existing source decreases, permitting endpoint bounds without new sampling weights. -/
theorem thetaFirstMode_antitone_cubic : AntitoneOn thetaFirstMode (Ici 0) := by
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

/-- Fourth derivative control from geometric endpoint bounds. -/
theorem thetaFirstModeFourth_cell_bound (a b Q U : ℝ)
    (ha : 0 ≤ a) (hQ : Real.pi*exp (2*b) ≤ Q)
    (hU : thetaFirstMode a ≤ U) :
    ∀ x ∈ Icc a b, |thetaFirstModeFourth x| ≤
      (16*Q^4+112*Q^3+166*Q^2+39*Q+1/16)*U := by
  intro x hx
  let q := Real.pi*exp (2*x)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqx : q ≤ Q := by
    exact (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith [hx.2])) Real.pi_pos.le).trans hQ
  have hQ0 : 0 ≤ Q := hq0.trans hqx
  have hf : thetaFirstMode x ≤ U := (thetaFirstMode_antitone_cubic
    ha (ha.trans hx.1) hx.1).trans hU
  have hf0 : 0 ≤ thetaFirstMode x := by unfold thetaFirstMode; positivity
  have hp : |1/16-39*q+166*q^2-112*q^3+16*q^4| ≤
      16*Q^4+112*Q^3+166*Q^2+39*Q+1/16 := by
    apply abs_le.mpr
    have h2 := pow_le_pow_left₀ hq0 hqx 2
    have h3 := pow_le_pow_left₀ hq0 hqx 3
    have h4 := pow_le_pow_left₀ hq0 hqx 4
    have hp2 := pow_nonneg hq0 2
    have hp3 := pow_nonneg hq0 3
    have hp4 := pow_nonneg hq0 4
    constructor <;> nlinarith
  unfold thetaFirstModeFourth
  change |(1/16-39*q+166*q^2-112*q^3+16*q^4)*thetaFirstMode x| ≤ _
  rw [abs_mul, abs_of_nonneg hf0]
  exact mul_le_mul hp hf hf0 (by positivity)

/-- Integrals of the retained cubic and its explicit fourth-power error. -/
def thetaCubicCellMass (p : ℕ) (a b f0 f1 f2 f3 f4 : ℝ) : ℝ :=
  f0*thetaPowerMass p a b +
  f1*(thetaPowerMass (p+1) a b-a*thetaPowerMass p a b) +
  f2/2*(thetaPowerMass (p+2) a b-2*a*thetaPowerMass (p+1) a b+a^2*thetaPowerMass p a b) +
  f3/6*(thetaPowerMass (p+3) a b-3*a*thetaPowerMass (p+2) a b+3*a^2*thetaPowerMass (p+1) a b-a^3*thetaPowerMass p a b) +
  f4/6*(thetaPowerMass (p+4) a b-4*a*thetaPowerMass (p+3) a b+6*a^2*thetaPowerMass (p+2) a b-4*a^3*thetaPowerMass (p+1) a b+a^4*thetaPowerMass p a b)

private theorem thetaCubicCellMass_eq_integral (p : ℕ) (a b f0 f1 f2 f3 f4 : ℝ) :
    thetaCubicCellMass p a b f0 f1 f2 f3 f4 =
      ∫ x in a..b, x^p*(f0+f1*(x-a)+f2/2*(x-a)^2+f3/6*(x-a)^3+f4/6*(x-a)^4) := by
  have he : (fun x : ℝ => x^p*(f0+f1*(x-a)+f2/2*(x-a)^2+f3/6*(x-a)^3+f4/6*(x-a)^4)) =
      fun x => (f0-a*f1+a^2*f2/2-a^3*f3/6+a^4*f4/6)*x^p +
        (f1-a*f2+a^2*f3/2-2*a^3*f4/3)*x^(p+1) +
        (f2/2-a*f3/2+a^2*f4)*x^(p+2) +
        (f3/6-2*a*f4/3)*x^(p+3) + f4/6*x^(p+4) := by funext x; ring
  rw [he]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_add, intervalIntegral.integral_add]
  · simp only [intervalIntegral.integral_const_mul, integral_thetaPowerMass]
    unfold thetaCubicCellMass
    ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- Source enclosure BEFORE any coefficient or discriminant readout. -/
theorem thetaFirstMode_weighted_cubic_cell_bounds (p : ℕ)
    (a b l0 l1 l2 l3 u0 u1 u2 u3 C : ℝ)
    (ha : 0 ≤ a) (hab : a < b)
    (h0 : l0 ≤ thetaFirstMode a ∧ thetaFirstMode a ≤ u0)
    (h1 : l1 ≤ thetaFirstModeFirst a ∧ thetaFirstModeFirst a ≤ u1)
    (h2 : l2 ≤ thetaFirstModeSecond a ∧ thetaFirstModeSecond a ≤ u2)
    (h3 : l3 ≤ thetaFirstModeThird a ∧ thetaFirstModeThird a ≤ u3)
    (hC : ∀ x ∈ Icc a b, |thetaFirstModeFourth x| ≤ C) :
    thetaCubicCellMass p a b l0 l1 l2 l3 (-C) ≤ (∫ x in a..b, x^p*thetaFirstMode x) ∧
      (∫ x in a..b, x^p*thetaFirstMode x) ≤ thetaCubicCellMass p a b u0 u1 u2 u3 C := by
  rw [thetaCubicCellMass_eq_integral, thetaCubicCellMass_eq_integral]
  have hc0 (x : ℝ) (hx : x ∈ Icc a b) : 0 ≤ x-a := sub_nonneg.mpr hx.1
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) :=
    abs_le.mp (thetaFirstMode_cubic_remainder a b C x hab hx hC)
  constructor
  · apply intervalIntegral.integral_mono_on hab.le
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; unfold thetaFirstMode; fun_prop)
    intro x hx
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (ha.trans hx.1) p)
    have hn := hc0 x hx
    have h1l := mul_le_mul_of_nonneg_right h1.1 hn
    have h2l := mul_le_mul_of_nonneg_right h2.1 (pow_nonneg hn 2)
    have h3l := mul_le_mul_of_nonneg_right h3.1 (pow_nonneg hn 3)
    nlinarith [hpoint x hx]
  · apply intervalIntegral.integral_mono_on hab.le
      (by apply Continuous.intervalIntegrable; unfold thetaFirstMode; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
    intro x hx
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (ha.trans hx.1) p)
    have hn := hc0 x hx
    have h1u := mul_le_mul_of_nonneg_right h1.2 hn
    have h2u := mul_le_mul_of_nonneg_right h2.2 (pow_nonneg hn 2)
    have h3u := mul_le_mul_of_nonneg_right h3.2 (pow_nonneg hn 3)
    nlinarith [hpoint x hx]

/-- Retain the source derivative signs while bounding each monomial, with
no assumption that the third derivative is positive. -/
theorem thetaFirstMode_cubic_node_derivative_bounds (m QL QU L U : ℝ)
    (hQL : 0 ≤ QL) (hL : 0 ≤ L)
    (hqL : QL ≤ Real.pi*exp (2*m)) (hqU : Real.pi*exp (2*m) ≤ QU)
    (hfL : L ≤ thetaFirstMode m) (hfU : thetaFirstMode m ≤ U) :
    ((1/2)*L-2*QU*U ≤ thetaFirstModeFirst m ∧
      thetaFirstModeFirst m ≤ (1/2)*U-2*QL*L) ∧
    ((1/4)*L-6*QU*U+4*QL^2*L ≤ thetaFirstModeSecond m ∧
      thetaFirstModeSecond m ≤ (1/4)*U-6*QL*L+4*QU^2*U) ∧
    ((1/8)*L-(31/2)*QU*U+30*QL^2*L-8*QU^3*U ≤ thetaFirstModeThird m ∧
      thetaFirstModeThird m ≤ (1/8)*U-(31/2)*QL*L+30*QU^2*U-8*QL^3*L) := by
  let q := Real.pi*exp (2*m)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hQU : 0 ≤ QU := hq0.trans hqU
  have hf0 : 0 ≤ thetaFirstMode m := hL.trans hfL
  have ht1 := And.intro (mul_le_mul hqL hfL hL hq0)
    (mul_le_mul hqU hfU hf0 hQU)
  have ht2 := And.intro (mul_le_mul (pow_le_pow_left₀ hQL hqL 2) hfL hL (pow_nonneg hq0 2))
    (mul_le_mul (pow_le_pow_left₀ hq0 hqU 2) hfU hf0 (pow_nonneg hQU 2))
  have ht3 := And.intro (mul_le_mul (pow_le_pow_left₀ hQL hqL 3) hfL hL (pow_nonneg hq0 3))
    (mul_le_mul (pow_le_pow_left₀ hq0 hqU 3) hfU hf0 (pow_nonneg hQU 3))
  change QL*L ≤ q*thetaFirstMode m ∧ q*thetaFirstMode m ≤ QU*U at ht1
  change QL^2*L ≤ q^2*thetaFirstMode m ∧ q^2*thetaFirstMode m ≤ QU^2*U at ht2
  change QL^3*L ≤ q^3*thetaFirstMode m ∧ q^3*thetaFirstMode m ≤ QU^3*U at ht3
  rw [show thetaFirstModeFirst m = (1/2-2*q)*thetaFirstMode m from by
    dsimp [thetaFirstModeFirst,q]; ring]
  rw [show thetaFirstModeSecond m = (1/4-6*q+4*q^2)*thetaFirstMode m from by
    dsimp [thetaFirstModeSecond,q]; ring,
    show thetaFirstModeThird m = (1/8-31/2*q+30*q^2-8*q^3)*thetaFirstMode m from by
    dsimp [thetaFirstModeThird,q]]
  change (_ ≤ (1/2-2*q)*thetaFirstMode m ∧ (1/2-2*q)*thetaFirstMode m ≤ _) ∧
    (_ ≤ (1/4-6*q+4*q^2)*thetaFirstMode m ∧ (1/4-6*q+4*q^2)*thetaFirstMode m ≤ _) ∧
    (_ ≤ (1/8-31/2*q+30*q^2-8*q^3)*thetaFirstMode m ∧
      (1/8-31/2*q+30*q^2-8*q^3)*thetaFirstMode m ≤ _)
  constructor
  · constructor <;> nlinarith only [hfL,hfU,ht1.1,ht1.2]
  · constructor
    · constructor <;> nlinarith only [hfL,hfU,ht1.1,ht1.2,ht2.1,ht2.2]
    · constructor <;> nlinarith only [hfL,hfU,ht1.1,ht1.2,ht2.1,ht2.2,ht3.1,ht3.2]

end
end CarrySelfAdjointOperator
