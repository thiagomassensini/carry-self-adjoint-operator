import CarrySelfAdjointOperator.CompletedNativeXiThetaMoments
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Explicit rational bounds for the low theta-tail moments

This module supplies certified rational estimates for the two theta-tail
moments isolated in `CompletedNativeXiThetaMoments`.  All transcendental
comparisons are reduced to finite Taylor bounds for the real exponential and
Mathlib's rational bounds for `π`.
-/

open Real Set Filter MeasureTheory
open scoped Interval

namespace CarrySelfAdjointOperator

noncomputable section

open XiThetaCosine

private theorem exp_neg_lt_of_partial_sum (x q : ℝ) (n : ℕ)
    (hx : 0 ≤ x) (hq : 0 ≤ q)
    (hfinite : 1 < q * ∑ i ∈ Finset.range n, x ^ i / i.factorial) :
    Real.exp (-x) < q := by
  have hseries := Real.sum_le_exp_of_nonneg hx n
  rw [Real.exp_neg, inv_lt_iff_one_lt_mul₀ (Real.exp_pos x)]
  exact hfinite.trans_le (mul_le_mul_of_nonneg_left hseries hq)

private theorem exp_neg_6283_div_2000_lt :
    Real.exp (-(6283 / 2000 : ℝ)) < 43218 / 1000000 := by
  apply exp_neg_lt_of_partial_sum (6283 / 2000 : ℝ) (43218 / 1000000 : ℝ) 15
  · norm_num
  · norm_num
  · norm_num [Finset.sum_range_succ]

private theorem exp_upper_bound_fifth {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤
      (∑ m ∈ Finset.range 5, x ^ m / m.factorial) +
        x ^ 5 * 6 / (Nat.factorial 5 * 5) :=
  by
    convert Real.exp_bound' hx0 hx1 (n := 5) (by norm_num) using 1 <;> norm_num

private theorem exp_neg_22_div_7_gt :
    (431 / 10000 : ℝ) < Real.exp (-(22 / 7 : ℝ)) := by
  let z : ℝ := 11 / 14
  let U : ℝ :=
    (∑ m ∈ Finset.range 5, z ^ m / m.factorial) +
      z ^ 5 * 6 / (Nat.factorial 5 * 5)
  have hz : Real.exp z ≤ U := by
    apply exp_upper_bound_fifth
    · dsimp [z]; norm_num
    · dsimp [z]; norm_num
  have hexp : Real.exp (22 / 7 : ℝ) ≤ U ^ 4 := by
    have hrewrite : (22 / 7 : ℝ) = z * 4 := by
      dsimp [z]
      ring
    rw [hrewrite]
    calc
      Real.exp (z * 4) = Real.exp z ^ 4 := by
        simpa [mul_comm] using Real.exp_nat_mul z 4
      _ ≤ U ^ 4 := pow_le_pow_left₀ (Real.exp_nonneg z) hz 4
  have hU : U ^ 4 < (10000 / 431 : ℝ) := by
    dsimp [U, z]
    norm_num [Finset.sum_range_succ]
  rw [Real.exp_neg, ← one_div]
  apply (lt_div_iff₀ (Real.exp_pos (22 / 7 : ℝ))).2
  have hpos : (0 : ℝ) < 431 / 10000 := by norm_num
  calc
    (431 / 10000 : ℝ) * Real.exp (22 / 7 : ℝ) ≤
        (431 / 10000 : ℝ) * U ^ 4 :=
      mul_le_mul_of_nonneg_left hexp hpos.le
    _ < 1 := by
      norm_num at hU ⊢

private def thetaMassSecondTangentSwitch : ℝ :=
  3322053 / 2685817

private theorem exp_neg_thetaMassSecondTangentSwitch_gt :
    (1 / 49 : ℝ) <
      Real.exp (-(22 / 7 : ℝ) * thetaMassSecondTangentSwitch) := by
  let x : ℝ := (22 / 7 : ℝ) * thetaMassSecondTangentSwitch
  let z : ℝ := x / 4
  let U : ℝ :=
    (∑ m ∈ Finset.range 5, z ^ m / m.factorial) +
      z ^ 5 * 6 / (Nat.factorial 5 * 5)
  have hz0 : 0 ≤ z := by
    dsimp [z, x, thetaMassSecondTangentSwitch]
    norm_num
  have hz1 : z ≤ 1 := by
    dsimp [z, x, thetaMassSecondTangentSwitch]
    norm_num
  have hz : Real.exp z ≤ U := exp_upper_bound_fifth hz0 hz1
  have hexp : Real.exp x ≤ U ^ 4 := by
    have hrewrite : x = z * 4 := by
      dsimp [z]
      ring
    rw [hrewrite]
    calc
      Real.exp (z * 4) = Real.exp z ^ 4 := by
        simpa [mul_comm] using Real.exp_nat_mul z 4
      _ ≤ U ^ 4 := pow_le_pow_left₀ (Real.exp_nonneg z) hz 4
  have hU : U ^ 4 < (49 : ℝ) := by
    dsimp [U, z, x, thetaMassSecondTangentSwitch]
    norm_num [Finset.sum_range_succ]
  have harg : -(22 / 7 : ℝ) * thetaMassSecondTangentSwitch = -x := by
    dsimp [x]
    ring
  rw [harg, Real.exp_neg, ← one_div]
  apply (lt_div_iff₀ (Real.exp_pos x)).2
  calc
    (1 / 49 : ℝ) * Real.exp x ≤ (1 / 49 : ℝ) * U ^ 4 :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ < 1 := by nlinarith

/-- Algebraic form of `x⁻³ᐟ⁴` using only nested square roots. -/
private def thetaMassWeight (x : ℝ) : ℝ :=
  (Real.sqrt x * Real.sqrt (Real.sqrt x))⁻¹

private theorem thetaMassWeight_eq_inv_pow {x : ℝ} (hx : 0 < x) :
    thetaMassWeight x = (Real.sqrt (Real.sqrt x) ^ 3)⁻¹ := by
  let t := Real.sqrt (Real.sqrt x)
  have hsqrt : Real.sqrt x = t ^ 2 := by
    dsimp [t]
    rw [sq_sqrt (Real.sqrt_nonneg x)]
  change (Real.sqrt x * t)⁻¹ = (t ^ 3)⁻¹
  congr 1
  rw [hsqrt]
  ring

/-- The tangent line to `x ↦ x⁻³ᐟ⁴` at the fourth power `q⁴` lies below
the function.  Choosing fourth powers keeps every tangent coefficient
rational. -/
private theorem thetaMass_tangent_le (q x : ℝ) (hq : 0 < q) (hx : 0 < x) :
    (7 / (4 * q ^ 3) - 3 * x / (4 * q ^ 7)) ≤ thetaMassWeight x := by
  let t : ℝ := Real.sqrt (Real.sqrt x)
  have ht : 0 < t := by
    dsimp [t]
    exact Real.sqrt_pos.2 (Real.sqrt_pos.2 hx)
  have ht2 : t ^ 2 = Real.sqrt x := by
    dsimp [t]
    exact sq_sqrt (Real.sqrt_nonneg x)
  have ht4 : t ^ 4 = x := by
    rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, ht2, sq_sqrt hx.le]
  let z : ℝ := t / q
  have hz : 0 < z := div_pos ht hq
  have hpoly :
      0 ≤ (z - 1) ^ 2 *
        (3 * z ^ 5 + 6 * z ^ 4 + 9 * z ^ 3 + 12 * z ^ 2 + 8 * z + 4) := by
    positivity
  have hmain : 7 * z ^ 3 - 3 * z ^ 7 ≤ 4 := by
    nlinarith [show
      (z - 1) ^ 2 *
          (3 * z ^ 5 + 6 * z ^ 4 + 9 * z ^ 3 + 12 * z ^ 2 + 8 * z + 4) =
        3 * z ^ 7 - 7 * z ^ 3 + 4 by ring]
  rw [thetaMassWeight_eq_inv_pow hx]
  change (7 / (4 * q ^ 3) - 3 * x / (4 * q ^ 7)) ≤ (t ^ 3)⁻¹
  rw [← ht4]
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (pow_pos ht 3)).2
  dsimp [z] at hmain
  field_simp [hq.ne'] at hmain ⊢
  nlinarith

private def thetaFirstMode (u : ℝ) : ℝ :=
  2 * Real.exp (u / 2) * Real.exp (-Real.pi * Real.exp (2 * u))

private def thetaMassIntegrand (x : ℝ) : ℝ :=
  thetaMassWeight x * Real.exp (-Real.pi * x)

private theorem continuousAt_thetaMassWeight {x : ℝ} (hx : 0 < x) :
    ContinuousAt thetaMassWeight x := by
  unfold thetaMassWeight
  have hleft : ContinuousAt (fun y : ℝ ↦ Real.sqrt y) x :=
    Real.continuous_sqrt.continuousAt
  have hright : ContinuousAt (fun y : ℝ ↦ Real.sqrt (Real.sqrt y)) x :=
    Real.continuous_sqrt.continuousAt.comp hleft
  apply (hleft.mul hright).inv₀
  exact mul_ne_zero (Real.sqrt_pos.2 hx).ne'
    (Real.sqrt_pos.2 (Real.sqrt_pos.2 hx)).ne'

private theorem continuousOn_thetaMassIntegrand :
    ContinuousOn thetaMassIntegrand (Ioi (0 : ℝ)) := by
  intro x hx
  exact (continuousAt_thetaMassWeight hx).mul (by fun_prop) |>.continuousWithinAt

private theorem thetaMassWeight_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ thetaMassWeight x := by
  unfold thetaMassWeight
  positivity

private theorem thetaMassWeight_le_one {x : ℝ} (hx : 1 ≤ x) :
    thetaMassWeight x ≤ 1 := by
  have hsqrt : 1 ≤ Real.sqrt x := one_le_sqrt.mpr hx
  have hsqrtsqrt : 1 ≤ Real.sqrt (Real.sqrt x) := one_le_sqrt.mpr hsqrt
  have hmul : 1 ≤ Real.sqrt x * Real.sqrt (Real.sqrt x) := by
    have := mul_le_mul hsqrt hsqrtsqrt (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : 0 ≤ Real.sqrt x)
    simpa using this
  unfold thetaMassWeight
  exact inv_le_one_of_one_le₀ hmul

private theorem integrableOn_thetaMassIntegrand_Ici :
    IntegrableOn thetaMassIntegrand (Ici (1 : ℝ)) := by
  have hbaseIoi : IntegrableOn (fun x : ℝ ↦ Real.exp (-3 * x)) (Ioi (1 : ℝ)) := by
    simpa using integrableOn_exp_mul_Ioi (a := (-3 : ℝ)) (by norm_num) 1
  have hbase : IntegrableOn (fun x : ℝ ↦ Real.exp (-3 * x)) (Ici (1 : ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact hbaseIoi
  apply hbase.mono'
  · exact (continuousOn_thetaMassIntegrand.mono (by
      show Ici (1 : ℝ) ⊆ Ioi 0
      intro x hx
      change 1 ≤ x at hx
      exact zero_lt_one.trans_le hx)).aestronglyMeasurable measurableSet_Ici
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    have hxpos : 0 < x := zero_lt_one.trans_le hx
    have hweight0 := thetaMassWeight_nonneg hxpos
    have hweight1 := thetaMassWeight_le_one hx
    have hexp : Real.exp (-Real.pi * x) ≤ Real.exp (-3 * x) := by
      apply Real.exp_le_exp.mpr
      have hpi := Real.pi_gt_three
      nlinarith [mul_le_mul_of_nonneg_right hpi.le hxpos.le]
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      unfold thetaMassIntegrand
      positivity)]
    unfold thetaMassIntegrand
    calc
      thetaMassWeight x * Real.exp (-Real.pi * x) ≤
          1 * Real.exp (-Real.pi * x) :=
        mul_le_mul_of_nonneg_right hweight1 (Real.exp_pos _).le
      _ ≤ Real.exp (-3 * x) := by simpa using hexp

private theorem thetaTail_ge_thetaFirstMode {u : ℝ} (hu : 0 ≤ u) :
    thetaFirstMode u ≤ thetaTail u := by
  rw [thetaTail_eq_two_mul_tsum]
  have hmode : thetaTailMode 0 u ≤ ∑' n : ℕ, thetaTailMode n u :=
    (summable_thetaTailMode u).le_tsum 0 (fun n _hn ↦ by
      unfold thetaTailMode
      positivity)
  have hscaled' :
      2 * thetaTailMode 0 u ≤ 2 * ∑' n : ℕ, thetaTailMode n u :=
    mul_le_mul_of_nonneg_left hmode (by norm_num)
  unfold thetaFirstMode thetaTailMode at hscaled' ⊢
  convert hscaled' using 1 <;> ring

private theorem integrableOn_thetaFirstMode :
    IntegrableOn thetaFirstMode (Ioi (0 : ℝ)) := by
  apply integrableOn_thetaTail.mono'
  · exact (by
      unfold thetaFirstMode
      fun_prop : Continuous thetaFirstMode).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hnonneg : 0 ≤ thetaFirstMode u := by
      unfold thetaFirstMode
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact thetaTail_ge_thetaFirstMode hu.le

private theorem thetaMassIntegrand_comp_exp (u : ℝ) :
    thetaMassIntegrand (Real.exp (2 * u)) * (2 * Real.exp (2 * u)) =
      thetaFirstMode u := by
  have hexpdouble : Real.exp (2 * u) = Real.exp u ^ 2 := by
    calc
      Real.exp (2 * u) = Real.exp (u + u) := by congr 1 <;> ring
      _ = Real.exp u * Real.exp u := Real.exp_add u u
      _ = Real.exp u ^ 2 := by ring
  have hsqrt : Real.sqrt (Real.exp (2 * u)) = Real.exp u := by
    rw [hexpdouble,
      Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos u)]
  have hexphalf : Real.exp u = Real.exp (u / 2) ^ 2 := by
    calc
      Real.exp u = Real.exp (u / 2 + u / 2) := by congr 1 <;> ring
      _ = Real.exp (u / 2) * Real.exp (u / 2) := Real.exp_add _ _
      _ = Real.exp (u / 2) ^ 2 := by ring
  have hhalf : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
    rw [hexphalf,
      Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos (u / 2))]
  unfold thetaMassIntegrand thetaMassWeight thetaFirstMode
  rw [hsqrt, hhalf]
  field_simp [Real.exp_ne_zero]
  rw [show Real.exp (u * 2) = Real.exp (2 * u) by congr 1 <;> ring,
    hexpdouble, hexphalf]
  ring

private theorem thetaFirstMode_integral_eq_thetaMassIntegrand :
    (∫ u in Ioi (0 : ℝ), thetaFirstMode u) =
      ∫ x in Ioi (1 : ℝ), thetaMassIntegrand x := by
  let f : ℝ → ℝ := fun u ↦ Real.exp (2 * u)
  let f' : ℝ → ℝ := fun u ↦ 2 * Real.exp (2 * u)
  have hf : ContinuousOn f (Ici (0 : ℝ)) := by
    unfold f
    fun_prop
  have hft : Tendsto f atTop atTop := by
    unfold f
    exact Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hff' : ∀ u ∈ Ioi (0 : ℝ),
      HasDerivWithinAt f (f' u) (Ioi u) u := by
    intro u _hu
    apply HasDerivAt.hasDerivWithinAt
    unfold f f'
    have hlinear : HasDerivAt (fun y : ℝ ↦ 2 * y) 2 u := by
      simpa using (hasDerivAt_id u).const_mul 2
    refine (((Real.hasDerivAt_exp (2 * u)).comp u hlinear).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
    · ring
  have hgcont : ContinuousOn thetaMassIntegrand (f '' Ioi (0 : ℝ)) := by
    apply continuousOn_thetaMassIntegrand.mono
    intro x hx
    rcases hx with ⟨u, _hu, rfl⟩
    unfold f
    exact Real.exp_pos _
  have hgint : IntegrableOn thetaMassIntegrand (f '' Ici (0 : ℝ)) := by
    apply integrableOn_thetaMassIntegrand_Ici.mono_set
    intro x hx
    rcases hx with ⟨u, hu, rfl⟩
    unfold f
    change 0 ≤ u at hu
    exact Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num) hu)
  have hcompint : IntegrableOn
      (fun u : ℝ ↦ (thetaMassIntegrand ∘ f) u * f' u)
      (Ici (0 : ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    apply integrableOn_thetaFirstMode.congr
    exact Filter.Eventually.of_forall (fun u ↦ by
      simp only [Function.comp_apply]
      unfold f f'
      exact (thetaMassIntegrand_comp_exp u).symm)
  have hchange := integral_comp_mul_deriv_Ioi hf hft hff' hgcont hgint hcompint
  have hfzero : f 0 = 1 := by simp [f]
  rw [hfzero] at hchange
  rw [← hchange]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u ↦ by
    simp only [Function.comp_apply]
    unfold f f'
    exact (thetaMassIntegrand_comp_exp u).symm)

private def affineExpPrimitive (rate A B x : ℝ) : ℝ :=
  Real.exp (-rate * x) * (-(A + B * x) / rate - B / rate ^ 2)

private theorem hasDerivAt_affineExpPrimitive
    (rate A B x : ℝ) (hrate : rate ≠ 0) :
    HasDerivAt (affineExpPrimitive rate A B)
      ((A + B * x) * Real.exp (-rate * x)) x := by
  have hinner : HasDerivAt (fun y : ℝ ↦ -rate * y) (-rate) x := by
    simpa using (hasDerivAt_id x).const_mul (-rate)
  have hexp := (Real.hasDerivAt_exp (-rate * x)).comp x hinner
  have haffine : HasDerivAt
      (fun y : ℝ ↦ -(A + B * y) / rate - B / rate ^ 2)
      (-B / rate) x := by
    have hbase := (((hasDerivAt_const x A).add
      ((hasDerivAt_id x).const_mul B)).neg.div_const rate).add_const
        (-B / rate ^ 2)
    refine (hbase.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun y ↦ by
        simp only [id_eq]
        field_simp [hrate]
        dsimp
        ring)
    · ring
  have hprod := hexp.mul haffine
  refine (hprod.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _y ↦ rfl)
  · simp only [Function.comp_apply, Pi.mul_apply]
    field_simp [hrate]
    ring

private theorem integral_affine_mul_exp (rate A B a b : ℝ)
    (hrate : rate ≠ 0) :
    (∫ x in a..b, (A + B * x) * Real.exp (-rate * x)) =
      affineExpPrimitive rate A B b - affineExpPrimitive rate A B a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _hx
    exact hasDerivAt_affineExpPrimitive rate A B x hrate
  · exact (by fun_prop : Continuous (fun x : ℝ ↦
      (A + B * x) * Real.exp (-rate * x))).intervalIntegrable a b

private def thetaMassFirstLine (x : ℝ) : ℝ :=
  7 / 4 - 3 * x / 4

private def thetaMassSecondLine (x : ℝ) : ℝ :=
  896 / 729 - (524288 / 1594323) * x

private def thetaMassSecondLineRoot : ℝ :=
  15309 / 4096

private theorem thetaMassFirstLine_nonneg {x : ℝ}
    (hx1 : 1 ≤ x) (hxswitch : x ≤ thetaMassSecondTangentSwitch) :
    0 ≤ thetaMassFirstLine x := by
  dsimp [thetaMassFirstLine, thetaMassSecondTangentSwitch] at *
  norm_num at *
  linarith

private theorem thetaMassSecondLine_nonneg {x : ℝ}
    (hxswitch : thetaMassSecondTangentSwitch ≤ x)
    (hxroot : x ≤ thetaMassSecondLineRoot) :
    0 ≤ thetaMassSecondLine x := by
  dsimp [thetaMassSecondLine, thetaMassSecondLineRoot] at *
  norm_num at *
  linarith

private theorem thetaMassFirstLine_le_integrand {x : ℝ}
    (hx1 : 1 ≤ x) (hxswitch : x ≤ thetaMassSecondTangentSwitch) :
    thetaMassFirstLine x * Real.exp (-(22 / 7 : ℝ) * x) ≤
      thetaMassIntegrand x := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx1
  have htangent := thetaMass_tangent_le 1 x (by norm_num) hxpos
  have hline : thetaMassFirstLine x ≤ thetaMassWeight x := by
    simpa [thetaMassFirstLine] using htangent
  have hline0 := thetaMassFirstLine_nonneg hx1 hxswitch
  have hexp : Real.exp (-(22 / 7 : ℝ) * x) ≤
      Real.exp (-Real.pi * x) := by
    apply Real.exp_le_exp.mpr
    have hpi := Real.pi_lt_d4
    nlinarith [mul_le_mul_of_nonneg_right hpi.le hxpos.le]
  unfold thetaMassIntegrand
  calc
    thetaMassFirstLine x * Real.exp (-(22 / 7 : ℝ) * x) ≤
        thetaMassFirstLine x * Real.exp (-Real.pi * x) :=
      mul_le_mul_of_nonneg_left hexp hline0
    _ ≤ thetaMassWeight x * Real.exp (-Real.pi * x) :=
      mul_le_mul_of_nonneg_right hline (Real.exp_pos _).le

private theorem thetaMassSecondLine_le_integrand {x : ℝ}
    (hxswitch : thetaMassSecondTangentSwitch ≤ x)
    (hxroot : x ≤ thetaMassSecondLineRoot) :
    thetaMassSecondLine x * Real.exp (-(22 / 7 : ℝ) * x) ≤
      thetaMassIntegrand x := by
  have hxpos : 0 < x := by
    have hswitch : (0 : ℝ) < thetaMassSecondTangentSwitch := by
      dsimp [thetaMassSecondTangentSwitch]
      norm_num
    exact hswitch.trans_le hxswitch
  have htangent := thetaMass_tangent_le (9 / 8 : ℝ) x (by norm_num) hxpos
  have hline : thetaMassSecondLine x ≤ thetaMassWeight x := by
    convert htangent using 1
    · norm_num [thetaMassSecondLine]
      ring
  have hline0 := thetaMassSecondLine_nonneg hxswitch hxroot
  have hexp : Real.exp (-(22 / 7 : ℝ) * x) ≤
      Real.exp (-Real.pi * x) := by
    apply Real.exp_le_exp.mpr
    have hpi := Real.pi_lt_d4
    nlinarith [mul_le_mul_of_nonneg_right hpi.le hxpos.le]
  unfold thetaMassIntegrand
  calc
    thetaMassSecondLine x * Real.exp (-(22 / 7 : ℝ) * x) ≤
        thetaMassSecondLine x * Real.exp (-Real.pi * x) :=
      mul_le_mul_of_nonneg_left hexp hline0
    _ ≤ thetaMassWeight x * Real.exp (-Real.pi * x) :=
      mul_le_mul_of_nonneg_right hline (Real.exp_pos _).le

/-- A two-tangent rational lower certificate for the theta-tail mass. -/
theorem completedNativeThetaTailMoment_zero_gt :
    (113 / 10000 : ℝ) < completedNativeThetaTailMoment 0 := by
  have hmoment :
      (∫ u in Ioi (0 : ℝ), thetaFirstMode u) ≤
        completedNativeThetaTailMoment 0 := by
    rw [completedNativeThetaTailMoment]
    have htheta : IntegrableOn thetaTail (Ioi (0 : ℝ)) := integrableOn_thetaTail
    have hmono := integral_mono_ae integrableOn_thetaFirstMode htheta (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact thetaTail_ge_thetaFirstMode hu.le)
    simpa using hmono
  rw [thetaFirstMode_integral_eq_thetaMassIntegrand] at hmoment
  have hmassIoi : IntegrableOn thetaMassIntegrand (Ioi (1 : ℝ)) := by
    rw [← integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_thetaMassIntegrand_Ici
  have htail : IntegrableOn thetaMassIntegrand (Ioi thetaMassSecondLineRoot) :=
    hmassIoi.mono_set (Ioi_subset_Ioi (by
      dsimp [thetaMassSecondLineRoot]
      norm_num : (1 : ℝ) ≤ thetaMassSecondLineRoot))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hmassIoi htail
  have htailNonneg :
      0 ≤ ∫ x in Ioi thetaMassSecondLineRoot, thetaMassIntegrand x := by
    exact integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      unfold thetaMassIntegrand
      exact mul_nonneg (thetaMassWeight_nonneg (lt_trans (by
        dsimp [thetaMassSecondLineRoot]
        norm_num) hx)) (Real.exp_pos _).le)
  have hroot : (1 : ℝ) ≤ thetaMassSecondLineRoot := by
    dsimp [thetaMassSecondLineRoot]
    norm_num
  have hswitchBounds :
      (1 : ℝ) ≤ thetaMassSecondTangentSwitch ∧
        thetaMassSecondTangentSwitch ≤ thetaMassSecondLineRoot := by
    dsimp [thetaMassSecondTangentSwitch, thetaMassSecondLineRoot]
    norm_num
  have hfirstInt : IntervalIntegrable thetaMassIntegrand volume 1
      thetaMassSecondTangentSwitch := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hswitchBounds.1]
    exact hmassIoi.mono_set Ioc_subset_Ioi_self
  have hsecondInt : IntervalIntegrable thetaMassIntegrand volume
      thetaMassSecondTangentSwitch thetaMassSecondLineRoot := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hswitchBounds.2]
    apply hmassIoi.mono_set
    intro x hx
    exact lt_of_le_of_lt hswitchBounds.1 hx.1
  have hfirstMajorant : IntervalIntegrable
      (fun x : ℝ ↦ thetaMassFirstLine x * Real.exp (-(22 / 7 : ℝ) * x))
      volume 1 thetaMassSecondTangentSwitch :=
    (by
      unfold thetaMassFirstLine
      fun_prop : Continuous (fun x : ℝ ↦
        thetaMassFirstLine x * Real.exp (-(22 / 7 : ℝ) * x))).intervalIntegrable _ _
  have hsecondMajorant : IntervalIntegrable
      (fun x : ℝ ↦ thetaMassSecondLine x * Real.exp (-(22 / 7 : ℝ) * x))
      volume thetaMassSecondTangentSwitch thetaMassSecondLineRoot :=
    (by
      unfold thetaMassSecondLine
      fun_prop : Continuous (fun x : ℝ ↦
        thetaMassSecondLine x * Real.exp (-(22 / 7 : ℝ) * x))).intervalIntegrable _ _
  have hfirstLower := intervalIntegral.integral_mono_on
    hswitchBounds.1 hfirstMajorant hfirstInt (fun x hx ↦
      thetaMassFirstLine_le_integrand hx.1 hx.2)
  have hsecondLower := intervalIntegral.integral_mono_on
    hswitchBounds.2 hsecondMajorant hsecondInt (fun x hx ↦
      thetaMassSecondLine_le_integrand hx.1 hx.2)
  have hlineSplit := intervalIntegral.integral_add_adjacent_intervals
    (f := thetaMassIntegrand) (a := (1 : ℝ))
    (b := thetaMassSecondTangentSwitch) (c := thetaMassSecondLineRoot)
    hfirstInt hsecondInt
  rw [show (fun x : ℝ ↦
      thetaMassFirstLine x * Real.exp (-(22 / 7 : ℝ) * x)) =
      fun x : ℝ ↦ ((7 / 4 : ℝ) + (-3 / 4 : ℝ) * x) *
        Real.exp (-(22 / 7 : ℝ) * x) by
      funext x
      unfold thetaMassFirstLine
      ring,
    integral_affine_mul_exp (22 / 7 : ℝ) (7 / 4 : ℝ) (-3 / 4 : ℝ)
      1 thetaMassSecondTangentSwitch (by norm_num)] at hfirstLower
  rw [show (fun x : ℝ ↦
      thetaMassSecondLine x * Real.exp (-(22 / 7 : ℝ) * x)) =
      fun x : ℝ ↦ ((896 / 729 : ℝ) + (-524288 / 1594323 : ℝ) * x) *
        Real.exp (-(22 / 7 : ℝ) * x) by
      funext x
      unfold thetaMassSecondLine
      ring,
    integral_affine_mul_exp (22 / 7 : ℝ) (896 / 729 : ℝ)
      (-524288 / 1594323 : ℝ) thetaMassSecondTangentSwitch
      thetaMassSecondLineRoot (by norm_num)] at hsecondLower
  have hfiniteLower :
      (113 / 10000 : ℝ) <
        (469 / 1936 : ℝ) * Real.exp (-(22 / 7 : ℝ)) +
          (131605033 / 3086609328 : ℝ) *
            Real.exp (-(22 / 7 : ℝ) * thetaMassSecondTangentSwitch) := by
    nlinarith [exp_neg_22_div_7_gt,
      exp_neg_thetaMassSecondTangentSwitch_gt]
  have hprimitiveSum :
      affineExpPrimitive (22 / 7 : ℝ) (7 / 4 : ℝ) (-3 / 4 : ℝ)
          thetaMassSecondTangentSwitch -
        affineExpPrimitive (22 / 7 : ℝ) (7 / 4 : ℝ) (-3 / 4 : ℝ) 1 +
      (affineExpPrimitive (22 / 7 : ℝ) (896 / 729 : ℝ)
          (-524288 / 1594323 : ℝ) thetaMassSecondLineRoot -
        affineExpPrimitive (22 / 7 : ℝ) (896 / 729 : ℝ)
          (-524288 / 1594323 : ℝ) thetaMassSecondTangentSwitch) =
        (469 / 1936 : ℝ) * Real.exp (-(22 / 7 : ℝ)) +
          (131605033 / 3086609328 : ℝ) *
            Real.exp (-(22 / 7 : ℝ) * thetaMassSecondTangentSwitch) +
          (6422528 / 192913083 : ℝ) *
            Real.exp (-(22 / 7 : ℝ) * thetaMassSecondLineRoot) := by
    unfold affineExpPrimitive thetaMassSecondTangentSwitch thetaMassSecondLineRoot
    ring
  have hrootTerm :
      0 < (6422528 / 192913083 : ℝ) *
        Real.exp (-(22 / 7 : ℝ) * thetaMassSecondLineRoot) := by positivity
  have hlineTotal :
      (113 / 10000 : ℝ) <
        (affineExpPrimitive (22 / 7 : ℝ) (7 / 4 : ℝ) (-3 / 4 : ℝ)
            thetaMassSecondTangentSwitch -
          affineExpPrimitive (22 / 7 : ℝ) (7 / 4 : ℝ) (-3 / 4 : ℝ) 1) +
        (affineExpPrimitive (22 / 7 : ℝ) (896 / 729 : ℝ)
            (-524288 / 1594323 : ℝ) thetaMassSecondLineRoot -
          affineExpPrimitive (22 / 7 : ℝ) (896 / 729 : ℝ)
            (-524288 / 1594323 : ℝ) thetaMassSecondTangentSwitch) := by
    rw [hprimitiveSum]
    nlinarith
  nlinarith [hlineSplit, hsplit]

private theorem exp_neg_nine_lt :
    Real.exp (-9) < (1 / 8000 : ℝ) := by
  apply exp_neg_lt_of_partial_sum 9 (1 / 8000 : ℝ) 30
  · norm_num
  · norm_num
  · norm_num [Finset.sum_range_succ]

private theorem thetaTailMode_le_geometric {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    thetaTailMode n u ≤ thetaTailMode 0 u * (1 / 8000 : ℝ) ^ n := by
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
  have hpiExp : (3 : ℝ) ≤ Real.pi * Real.exp (2 * u) := by
    calc
      (3 : ℝ) ≤ 3 * Real.exp (2 * u) := by nlinarith
      _ ≤ Real.pi * Real.exp (2 * u) :=
        mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_pos _).le
  have hdiff :
      3 * (n : ℝ) ≤ (((n + 1 : ℕ) : ℝ) ^ 2) - 1 := by
    linarith
  have hproduct :
      9 * (n : ℝ) ≤
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
        (1 / 8000 : ℝ) ^ n := by
    calc
      Real.exp
          (-Real.pi * ((((n + 1 : ℕ) : ℝ) ^ 2) - 1) *
            Real.exp (2 * u)) ≤
          Real.exp (-9 * (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = Real.exp (-9) ^ n := by
        convert Real.exp_nat_mul (-9) n using 1 <;> ring
      _ ≤ (1 / 8000 : ℝ) ^ n :=
        pow_le_pow_left₀ (Real.exp_nonneg _) exp_neg_nine_lt.le n
  have hsplit :
      Real.exp
          (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * u)) =
        Real.exp (-Real.pi * Real.exp (2 * u)) *
          Real.exp
            (-Real.pi * ((((n + 1 : ℕ) : ℝ) ^ 2) - 1) *
              Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold thetaTailMode
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
              Real.exp (2 * u)) := by ring
    _ ≤ (Real.exp (u / 2) * Real.exp (-Real.pi * Real.exp (2 * u))) *
        (1 / 8000 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left hdecay hfactor
    _ = Real.exp (u / 2) *
        Real.exp (-Real.pi * (((0 + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * u)) *
          (1 / 8000 : ℝ) ^ n := by norm_num

private theorem thetaTail_le_geometric_first {u : ℝ} (hu : 0 ≤ u) :
    thetaTail u ≤ (8000 / 7999 : ℝ) * thetaFirstMode u := by
  rw [thetaTail_eq_two_mul_tsum]
  have hgeom : Summable (fun n : ℕ ↦
      thetaTailMode 0 u * (1 / 8000 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num :
      (1 / 8000 : ℝ) < 1)).mul_left _
  have hsum := (summable_thetaTailMode u).tsum_le_tsum
    (thetaTailMode_le_geometric hu) hgeom
  calc
    2 * ∑' n : ℕ, thetaTailMode n u ≤
        2 * ∑' n : ℕ, thetaTailMode 0 u * (1 / 8000 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (8000 / 7999 : ℝ) * thetaFirstMode u := by
      rw [tsum_mul_left,
        tsum_geometric_of_lt_one (by norm_num) (by norm_num :
          (1 / 8000 : ℝ) < 1)]
      unfold thetaFirstMode thetaTailMode
      norm_num
      ring

private theorem integrableOn_pow_two_mul_thetaFirstMode :
    IntegrableOn (fun u : ℝ ↦ u ^ 2 * thetaFirstMode u) (Ioi (0 : ℝ)) := by
  apply (integrableOn_pow_mul_thetaTail 2).mono'
  · exact (by
      unfold thetaFirstMode
      fun_prop : Continuous (fun u : ℝ ↦ u ^ 2 * thetaFirstMode u)
      ).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hfirst0 : 0 ≤ thetaFirstMode u := by
      unfold thetaFirstMode
      positivity
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg u) hfirst0)]
    exact mul_le_mul_of_nonneg_left (thetaTail_ge_thetaFirstMode hu.le)
      (sq_nonneg u)

private theorem completedNativeThetaTailMoment_two_le_firstMode :
    completedNativeThetaTailMoment 2 ≤
      (8000 / 7999 : ℝ) *
        ∫ u in Ioi (0 : ℝ), u ^ 2 * thetaFirstMode u := by
  rw [completedNativeThetaTailMoment]
  have hright : IntegrableOn
      (fun u : ℝ ↦ (8000 / 7999 : ℝ) *
        (u ^ 2 * thetaFirstMode u)) (Ioi (0 : ℝ)) :=
    integrableOn_pow_two_mul_thetaFirstMode.const_mul _
  have hmono := integral_mono_ae (integrableOn_pow_mul_thetaTail 2)
    hright (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hpow : 0 ≤ u ^ 2 := sq_nonneg u
      have h := mul_le_mul_of_nonneg_left
        (thetaTail_le_geometric_first hu.le) hpow
      nlinarith)
  simpa [MeasureTheory.integral_const_mul] using hmono

end

end CarrySelfAdjointOperator
