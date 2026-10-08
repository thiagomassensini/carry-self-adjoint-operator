import CarrySelfAdjointOperator.CompletedNativeThetaCurvatureQuadrature

/-! Source-only refinement of the existing curvature quadrature.
The first-mode second derivative decreases on the nonnegative half-line.
All cells and weights remain in the original theta coordinate. -/
namespace CarrySelfAdjointOperator
open Real Set Filter MeasureTheory
noncomputable section
set_option autoImplicit false

private theorem hasDerivAt_thetaFirstModeSecond (u : ℝ) :
    HasDerivAt thetaFirstModeSecond
      ((1/8-31/2*(Real.pi*exp (2*u))+30*(Real.pi*exp (2*u))^2-
        8*(Real.pi*exp (2*u))^3)*thetaFirstMode u) u := by
  have hq := (((hasDerivAt_id u).const_mul 2).exp.const_mul Real.pi)
  have hp := ((hasDerivAt_const u (1/4:ℝ)).sub (hq.const_mul 6)).add
    ((hq.pow 2).const_mul 4)
  have h := hp.mul (hasDerivAt_thetaFirstMode u)
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun x => by
      simp only [thetaFirstModeSecond, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
      ring)
  · simp only [id_eq, thetaFirstModeFirst, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
    ring

/-- Endpoint curvature is the minimum curvature on every source cell. -/
theorem thetaFirstModeSecond_antitone : AntitoneOn thetaFirstModeSecond (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (by unfold thetaFirstModeSecond thetaFirstMode; fun_prop : Continuous thetaFirstModeSecond).continuousOn
  · intro u _
    exact (hasDerivAt_thetaFirstModeSecond u).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu0 : 0 ≤ u := interior_subset hu
    rw [(hasDerivAt_thetaFirstModeSecond u).deriv]
    have hq : 157/50 ≤ Real.pi*exp (2*u) := by
      have he := one_le_exp_iff.mpr (show 0 ≤ 2*u by positivity)
      nlinarith [Real.pi_gt_d6]
    let x := Real.pi*exp (2*u)-157/50
    have hx : 0 ≤ x := sub_nonneg.mpr hq
    have he : 1/8-31/2*(Real.pi*exp (2*u))+30*(Real.pi*exp (2*u))^2-
        8*(Real.pi*exp (2*u))^3 =
        -8*x^3-1134/25*x^2-79663/1250*x-53769/125000 := by dsimp [x]; ring
    rw [he]
    apply mul_nonpos_of_nonpos_of_nonneg
    · have hc : 0 ≤ x^3 := pow_nonneg hx 3
      nlinarith [sq_nonneg x]
    · unfold thetaFirstMode; positivity

/-- Sharper source-cell curvature bound using its right endpoint. -/
theorem thetaFirstModeSecond_endpoint_cell_lower (a b Q l : ℝ)
    (ha : 0 ≤ a) (hQ : 3 ≤ Q) (hQb : Q ≤ Real.pi*exp (2*b))
    (hl : 0 ≤ l) (hlb : l ≤ thetaFirstMode b) :
    ∀ u ∈ Icc a b, (1/4-6*Q+4*Q^2)*l ≤ thetaFirstModeSecond u := by
  intro u hu
  have hp : 1/4-6*Q+4*Q^2 ≤
      1/4-6*(Real.pi*exp (2*b))+4*(Real.pi*exp (2*b))^2 := by
    have h := mul_nonneg (sub_nonneg.mpr hQb)
      (show 0 ≤ 4*(Real.pi*exp (2*b)+Q)-6 by linarith)
    nlinarith
  have hn : 0 ≤ 1/4-6*Q+4*Q^2 := by nlinarith [sq_nonneg (Q-3)]
  have he : (1/4-6*Q+4*Q^2)*l ≤ thetaFirstModeSecond b := by
    unfold thetaFirstModeSecond
    simpa only [mul_assoc] using mul_le_mul hp hlb hl (hn.trans hp)
  exact he.trans (thetaFirstModeSecond_antitone (ha.trans hu.1)
    (ha.trans (hu.1.trans hu.2)) hu.2)

/-- Integrate a tangent at any certified node; retain the nonzero first-moment term. -/
theorem thetaFirstMode_weighted_curvature_node_lower
    (p : ℕ) (a b m l d γ : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hm : m ∈ Icc a b)
    (hg : ∀ u ∈ Icc a b, γ ≤ thetaFirstModeSecond u)
    (hw : 0 ≤ thetaPowerMass p a b)
    (hl : l ≤ thetaFirstMode m)
    (hd : d*(thetaPowerMass (p+1) a b-m*thetaPowerMass p a b) ≤
      thetaFirstModeFirst m*(thetaPowerMass (p+1) a b-m*thetaPowerMass p a b)) :
    l*thetaPowerMass p a b + d*(thetaPowerMass (p+1) a b-m*thetaPowerMass p a b) +
      γ/2*(thetaPowerMass (p+2) a b-2*m*thetaPowerMass (p+1) a b+m^2*thetaPowerMass p a b) ≤
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
  rw [he] at h
  have he' : (∫ x in a..b, x^p*((thetaFirstMode m-thetaFirstModeFirst m*m+γ/2*m^2)+
        (thetaFirstModeFirst m-γ*m)*x+(γ/2)*x^2)) =
      (thetaFirstMode m-thetaFirstModeFirst m*m+γ/2*m^2)*thetaPowerMass p a b+
        (thetaFirstModeFirst m-γ*m)*thetaPowerMass (p+1) a b+
        γ/2*thetaPowerMass (p+2) a b := by
    have hex : (fun x : ℝ => x^p*((thetaFirstMode m-thetaFirstModeFirst m*m+γ/2*m^2)+
        (thetaFirstModeFirst m-γ*m)*x+(γ/2)*x^2)) =
        fun x => (thetaFirstMode m-thetaFirstModeFirst m*m+γ/2*m^2)*x^p+
          (thetaFirstModeFirst m-γ*m)*x^(p+1)+(γ/2)*x^(p+2) := by funext x; ring
    rw [hex, intervalIntegral.integral_add, intervalIntegral.integral_add]
    · simp only [intervalIntegral.integral_const_mul, integral_thetaPowerMass]
    all_goals apply Continuous.intervalIntegrable; fun_prop
  rw [he'] at h
  nlinarith [mul_le_mul_of_nonneg_right hl hw]

/-- First derivative interval derived from the same source node interval. -/
theorem thetaFirstModeFirst_node_bounds (m Qlo Qhi l u : ℝ)
    (hQlo : 3 ≤ Qlo) (hlo : Qlo ≤ Real.pi*exp (2*m))
    (hhi : Real.pi*exp (2*m) ≤ Qhi)
    (hl0 : 0 ≤ l) (hl : l ≤ thetaFirstMode m) (hu : thetaFirstMode m ≤ u) :
    (1/2-2*Qhi)*u ≤ thetaFirstModeFirst m ∧
      thetaFirstModeFirst m ≤ (1/2-2*Qlo)*l := by
  have hq : 3 ≤ Real.pi*exp (2*m) := hQlo.trans hlo
  have hu0 : 0 ≤ u := hl0.trans (hl.trans hu)
  have hleft : (1/2-2*Qhi)*u ≤ (1/2-2*(Real.pi*exp (2*m)))*thetaFirstMode m := by
    calc
      _ ≤ (1/2-2*(Real.pi*exp (2*m)))*u :=
        mul_le_mul_of_nonneg_right (by linarith) hu0
      _ ≤ _ := mul_le_mul_of_nonpos_left hu (by linarith)
  have hright : (1/2-2*(Real.pi*exp (2*m)))*thetaFirstMode m ≤ (1/2-2*Qlo)*l := by
    calc
      _ ≤ (1/2-2*(Real.pi*exp (2*m)))*l := mul_le_mul_of_nonpos_left hl (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hl0
  simpa only [thetaFirstModeFirst, mul_assoc] using And.intro hleft hright
end
end CarrySelfAdjointOperator
