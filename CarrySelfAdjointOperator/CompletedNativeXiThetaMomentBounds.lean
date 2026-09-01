import CarrySelfAdjointOperator.CompletedNativeXiThetaMoments
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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

/-- The elementary weight obtained after the substitution `x = exp (2u)`
and the inequality `u ≤ exp (u/2) - exp (-u/2)`. -/
private def thetaSecondMomentWeight (x : ℝ) : ℝ :=
  (Real.sqrt x - 1) ^ 2 / (x * Real.sqrt (Real.sqrt x))

private def thetaRationalProfile (y : ℝ) : ℝ :=
  (y / (1 + (17 / 20 : ℝ) * y)) ^ 2

private theorem thetaSecondMomentPolynomial {t : ℝ} (ht : 1 ≤ t) :
    (3 + 17 * t ^ 4) ^ 2 ≤
      100 * t ^ 5 * (t ^ 2 + 1) ^ 2 := by
  let s : ℝ := t - 1
  have hs0 : 0 ≤ s := by
    dsimp [s]
    linarith
  let Q : ℝ :=
    100 * s ^ 8 + 611 * s ^ 7 + 1488 * s ^ 6 + 1708 * s ^ 5 +
      716 * s ^ 4 - 232 * s ^ 3 - 192 * s ^ 2 + 96 * s + 80
  have hQ : 0 ≤ Q := by
    by_cases hs1 : s ≤ 1
    · have hbernstein : 0 ≤
          (80 : ℝ) * (1 - s) ^ 8 +
          8 * 92 * s * (1 - s) ^ 7 +
          28 * (680 / 7 : ℝ) * s ^ 2 * (1 - s) ^ 6 +
          56 * (639 / 7 : ℝ) * s ^ 3 * (1 - s) ^ 5 +
          70 * (2818 / 35 : ℝ) * s ^ 4 * (1 - s) ^ 4 +
          56 * (1563 / 14 : ℝ) * s ^ 5 * (1 - s) ^ 3 +
          28 * (2491 / 7 : ℝ) * s ^ 6 * (1 - s) ^ 2 +
          8 * (10575 / 8 : ℝ) * s ^ 7 * (1 - s) +
          4375 * s ^ 8 := by positivity
      have hbernsteinEq : Q =
          (80 : ℝ) * (1 - s) ^ 8 +
          8 * 92 * s * (1 - s) ^ 7 +
          28 * (680 / 7 : ℝ) * s ^ 2 * (1 - s) ^ 6 +
          56 * (639 / 7 : ℝ) * s ^ 3 * (1 - s) ^ 5 +
          70 * (2818 / 35 : ℝ) * s ^ 4 * (1 - s) ^ 4 +
          56 * (1563 / 14 : ℝ) * s ^ 5 * (1 - s) ^ 3 +
          28 * (2491 / 7 : ℝ) * s ^ 6 * (1 - s) ^ 2 +
          8 * (10575 / 8 : ℝ) * s ^ 7 * (1 - s) +
          4375 * s ^ 8 := by
        dsimp [Q]
        ring
      rw [hbernsteinEq]
      exact hbernstein
    · have hs1' : 1 ≤ s := le_of_not_ge hs1
      have hs23 : s ^ 2 ≤ s ^ 3 := by
        nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs1')]
      have hs34 : s ^ 3 ≤ s ^ 4 := by
        nlinarith [mul_nonneg (pow_nonneg hs0 3) (sub_nonneg.mpr hs1')]
      have hcore :
          0 ≤ 716 * s ^ 4 - 232 * s ^ 3 - 192 * s ^ 2 := by
        nlinarith
      dsimp [Q]
      nlinarith [pow_nonneg hs0 5, pow_nonneg hs0 6,
        pow_nonneg hs0 7, pow_nonneg hs0 8]
  have hfactor :
      100 * t ^ 5 * (t ^ 2 + 1) ^ 2 - (3 + 17 * t ^ 4) ^ 2 =
        (t - 1) * Q := by
    dsimp [Q, s]
    ring
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) hQ]

private theorem thetaSecondMomentWeight_le_envelope {y : ℝ} (hy : 0 ≤ y) :
    thetaSecondMomentWeight (1 + y) ≤
      (1 / 4 : ℝ) * thetaRationalProfile y := by
  let t : ℝ := Real.sqrt (Real.sqrt (1 + y))
  have hx : 0 < 1 + y := by linarith
  have ht : 0 < t := by
    dsimp [t]
    exact Real.sqrt_pos.2 (Real.sqrt_pos.2 hx)
  have ht2 : t ^ 2 = Real.sqrt (1 + y) := by
    dsimp [t]
    exact sq_sqrt (Real.sqrt_nonneg (1 + y))
  have ht4 : t ^ 4 = 1 + y := by
    rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, ht2, sq_sqrt hx.le]
  have ht1 : 1 ≤ t := by
    dsimp [t]
    exact one_le_sqrt.mpr (one_le_sqrt.mpr (by linarith))
  have hyform : y = t ^ 4 - 1 := by linarith
  have hmain := thetaSecondMomentPolynomial ht1
  have hleftDen : 0 < t ^ 4 * t := mul_pos (pow_pos ht 4) ht
  have hrightBase : 0 < 1 + (17 / 20 : ℝ) * (t ^ 4 - 1) := by
    nlinarith [pow_pos ht 4]
  have hrightDen : 0 < 4 * (1 + (17 / 20 : ℝ) * (t ^ 4 - 1)) ^ 2 := by
    positivity
  unfold thetaSecondMomentWeight thetaRationalProfile
  rw [← ht2, ← ht4, hyform]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos ht]
  rw [div_pow]
  have hrearrange : (1 / 4 : ℝ) *
      ((t ^ 4 - 1) ^ 2 /
        (1 + (17 / 20 : ℝ) * (t ^ 4 - 1)) ^ 2) =
      (t ^ 4 - 1) ^ 2 /
        (4 * (1 + (17 / 20 : ℝ) * (t ^ 4 - 1)) ^ 2) := by
    field_simp [hrightBase.ne']
  rw [hrearrange]
  apply (div_le_div_iff₀ hleftDen hrightDen).2
  have hscaled := mul_le_mul_of_nonneg_left hmain
    (by positivity : 0 ≤ (t ^ 2 - 1) ^ 2 / 100)
  nlinarith [show
    ((t ^ 2 - 1) ^ 2 / 100) * (3 + 17 * t ^ 4) ^ 2 =
      (t ^ 2 - 1) ^ 2 *
        (4 * (1 + (17 / 20 : ℝ) * (t ^ 4 - 1)) ^ 2) by ring,
    show
      ((t ^ 2 - 1) ^ 2 / 100) *
          (100 * t ^ 5 * (t ^ 2 + 1) ^ 2) =
        (t ^ 4 - 1) ^ 2 * (t ^ 4 * t) by ring]

private def thetaSecondMomentMajorant (y : ℝ) : ℝ :=
  thetaSecondMomentWeight (1 + y) *
    Real.exp (-Real.pi * (1 + y))

private def thetaRationalMomentMajorant (y : ℝ) : ℝ :=
  (1 / 4 : ℝ) * thetaRationalProfile y *
    Real.exp (-(6283 / 2000 : ℝ) * (1 + y))

private theorem thetaRationalProfile_le {y : ℝ} (hy : 0 ≤ y) :
    thetaRationalProfile y ≤ (400 / 289 : ℝ) := by
  have hden : 0 < 1 + (17 / 20 : ℝ) * y := by positivity
  have hratio0 : 0 ≤ y / (1 + (17 / 20 : ℝ) * y) :=
    div_nonneg hy hden.le
  have hratio : y / (1 + (17 / 20 : ℝ) * y) ≤ 20 / 17 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  unfold thetaRationalProfile
  nlinarith [mul_nonneg hratio0 (sub_nonneg.mpr hratio)]

private theorem continuousOn_thetaSecondMomentMajorant :
    ContinuousOn thetaSecondMomentMajorant (Ici (0 : ℝ)) := by
  intro y hy
  change 0 ≤ y at hy
  have hxy : 0 < 1 + y := by linarith
  unfold thetaSecondMomentMajorant thetaSecondMomentWeight
  apply ContinuousAt.continuousWithinAt
  have hroot : ContinuousAt (fun z : ℝ ↦ Real.sqrt (1 + z)) y := by
    fun_prop
  have hrootroot :
      ContinuousAt (fun z : ℝ ↦ Real.sqrt (Real.sqrt (1 + z))) y := by
    fun_prop
  have hnum : ContinuousAt (fun z : ℝ ↦ (Real.sqrt (1 + z) - 1) ^ 2) y := by
    fun_prop
  have hden : ContinuousAt
      (fun z : ℝ ↦ (1 + z) * Real.sqrt (Real.sqrt (1 + z))) y := by
    fun_prop
  have hdenne : (1 + y) * Real.sqrt (Real.sqrt (1 + y)) ≠ 0 :=
    mul_ne_zero hxy.ne' (Real.sqrt_pos.2 (Real.sqrt_pos.2 hxy)).ne'
  exact (hnum.div₀ hden hdenne).mul (by fun_prop)

private theorem continuousOn_thetaRationalMomentMajorant :
    ContinuousOn thetaRationalMomentMajorant (Ici (0 : ℝ)) := by
  intro y hy
  change 0 ≤ y at hy
  have hden : 0 < 1 + (17 / 20 : ℝ) * y := by positivity
  unfold thetaRationalMomentMajorant thetaRationalProfile
  apply ContinuousAt.continuousWithinAt
  have hquot : ContinuousAt
      (fun z : ℝ ↦ z / (1 + (17 / 20 : ℝ) * z)) y := by
    apply continuousAt_id.div₀ (by fun_prop)
    exact hden.ne'
  exact (((hquot.pow 2).const_mul (1 / 4 : ℝ)).mul (by fun_prop))

private theorem thetaSecondMomentMajorant_le_rational {y : ℝ} (hy : 0 ≤ y) :
    thetaSecondMomentMajorant y ≤ thetaRationalMomentMajorant y := by
  have hweight := thetaSecondMomentWeight_le_envelope hy
  have hweight0 : 0 ≤ thetaSecondMomentWeight (1 + y) := by
    unfold thetaSecondMomentWeight
    positivity
  have henv0 : 0 ≤ (1 / 4 : ℝ) * thetaRationalProfile y := by
    unfold thetaRationalProfile
    positivity
  have hexp : Real.exp (-Real.pi * (1 + y)) ≤
      Real.exp (-(6283 / 2000 : ℝ) * (1 + y)) := by
    apply Real.exp_le_exp.mpr
    have hpi := Real.pi_gt_d4
    nlinarith
  unfold thetaSecondMomentMajorant thetaRationalMomentMajorant
  calc
    thetaSecondMomentWeight (1 + y) * Real.exp (-Real.pi * (1 + y)) ≤
        thetaSecondMomentWeight (1 + y) *
          Real.exp (-(6283 / 2000 : ℝ) * (1 + y)) :=
      mul_le_mul_of_nonneg_left hexp hweight0
    _ ≤ ((1 / 4 : ℝ) * thetaRationalProfile y) *
          Real.exp (-(6283 / 2000 : ℝ) * (1 + y)) :=
      mul_le_mul_of_nonneg_right hweight (Real.exp_pos _).le

private theorem integrableOn_thetaRationalMomentMajorant :
    IntegrableOn thetaRationalMomentMajorant (Ici (0 : ℝ)) := by
  have hbaseIoi : IntegrableOn
      (fun y : ℝ ↦ Real.exp (-(6283 / 2000 : ℝ) * y))
      (Ioi (0 : ℝ)) := by
    simpa using integrableOn_exp_mul_Ioi
      (a := (-(6283 / 2000 : ℝ))) (by norm_num) 0
  have hbase : IntegrableOn
      (fun y : ℝ ↦ (100 / 289 : ℝ) *
        Real.exp (-(6283 / 2000 : ℝ) * y))
      (Ici (0 : ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact hbaseIoi.const_mul _
  apply hbase.mono'
  · exact continuousOn_thetaRationalMomentMajorant.aestronglyMeasurable
      measurableSet_Ici
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
    change 0 ≤ y at hy
    have hprofile := thetaRationalProfile_le hy
    have hprofile0 : 0 ≤ thetaRationalProfile y := by
      unfold thetaRationalProfile
      positivity
    have hexp : Real.exp (-(6283 / 2000 : ℝ) * (1 + y)) ≤
        Real.exp (-(6283 / 2000 : ℝ) * y) := by
      apply Real.exp_le_exp.mpr
      norm_num
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      unfold thetaRationalMomentMajorant
      positivity)]
    unfold thetaRationalMomentMajorant
    calc
      (1 / 4 : ℝ) * thetaRationalProfile y *
          Real.exp (-(6283 / 2000 : ℝ) * (1 + y)) ≤
        (1 / 4 : ℝ) * (400 / 289 : ℝ) *
          Real.exp (-(6283 / 2000 : ℝ) * (1 + y)) := by
            gcongr
      _ ≤ (100 / 289 : ℝ) *
          Real.exp (-(6283 / 2000 : ℝ) * y) := by
        nlinarith [mul_le_mul_of_nonneg_left hexp
          (by norm_num : (0 : ℝ) ≤ 100 / 289)]

private theorem integrableOn_thetaSecondMomentMajorant :
    IntegrableOn thetaSecondMomentMajorant (Ici (0 : ℝ)) := by
  apply integrableOn_thetaRationalMomentMajorant.mono'
  · exact continuousOn_thetaSecondMomentMajorant.aestronglyMeasurable
      measurableSet_Ici
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
    change 0 ≤ y at hy
    have hxy : 0 < 1 + y := by linarith
    have hmajorant0 : 0 ≤ thetaSecondMomentMajorant y := by
      unfold thetaSecondMomentMajorant thetaSecondMomentWeight
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hmajorant0]
    exact thetaSecondMomentMajorant_le_rational hy

private theorem thetaSecondMomentMajorant_comp_exp (u : ℝ) :
    thetaSecondMomentMajorant (Real.exp (2 * u) - 1) *
        (2 * Real.exp (2 * u)) =
      thetaFirstMode u *
        (Real.exp (u / 2) - Real.exp (-u / 2)) ^ 2 := by
  have htwo : Real.exp (2 * u) = Real.exp u ^ 2 := by
    rw [show 2 * u = u + u by ring, Real.exp_add, pow_two]
  have hhalf : Real.exp u = Real.exp (u / 2) ^ 2 := by
    calc
      Real.exp u = Real.exp (u / 2 + u / 2) := by congr 1 <;> ring
      _ = Real.exp (u / 2) * Real.exp (u / 2) := Real.exp_add _ _
      _ = Real.exp (u / 2) ^ 2 := by ring
  have hsqrt : Real.sqrt (Real.exp (2 * u)) = Real.exp u := by
    rw [htwo, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos u)]
  have hsqrtexpu : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
    rw [hhalf, Real.sqrt_sq_eq_abs,
      abs_of_pos (Real.exp_pos (u / 2))]
  have hneg : Real.exp (-u / 2) = (Real.exp (u / 2))⁻¹ := by
    rw [show -u / 2 = -(u / 2) by ring, Real.exp_neg]
  unfold thetaSecondMomentMajorant thetaSecondMomentWeight thetaFirstMode
  rw [show 1 + (Real.exp (2 * u) - 1) = Real.exp (2 * u) by ring,
    hsqrt, hsqrtexpu, hneg]
  rw [htwo, hhalf]
  field_simp [Real.exp_ne_zero]

private theorem self_le_exp_half_sub_exp_neg_half {u : ℝ} (hu : 0 ≤ u) :
    u ≤ Real.exp (u / 2) - Real.exp (-u / 2) := by
  have hsinh : u / 2 ≤ Real.sinh (u / 2) :=
    (Real.self_le_sinh_iff).2 (by linarith)
  rw [Real.sinh_eq] at hsinh
  rw [show -(u / 2) = -u / 2 by ring] at hsinh
  nlinarith

private theorem integrableOn_thetaSecondMomentComposite :
    IntegrableOn
      (fun u : ℝ ↦
        thetaSecondMomentMajorant (Real.exp (2 * u) - 1) *
          (2 * Real.exp (2 * u))) (Ici (0 : ℝ)) := by
  have hbaseIoi : IntegrableOn (fun u : ℝ ↦ 2 * Real.exp (-u))
      (Ioi (0 : ℝ)) := (integrableOn_exp_neg_Ioi 0).const_mul _
  have hbase : IntegrableOn (fun u : ℝ ↦ 2 * Real.exp (-u))
      (Ici (0 : ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact hbaseIoi
  have hrhs : IntegrableOn
      (fun u : ℝ ↦ thetaFirstMode u *
        (Real.exp (u / 2) - Real.exp (-u / 2)) ^ 2)
      (Ici (0 : ℝ)) := by
    apply hbase.mono'
    · exact (by
        unfold thetaFirstMode
        fun_prop : Continuous (fun u : ℝ ↦ thetaFirstMode u *
          (Real.exp (u / 2) - Real.exp (-u / 2)) ^ 2)
        ).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
      change 0 ≤ u at hu
      let d : ℝ := Real.exp (u / 2) - Real.exp (-u / 2)
      have hd0 : 0 ≤ d := by
        dsimp [d]
        exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
      have hdle : d ≤ Real.exp (u / 2) := by
        dsimp [d]
        linarith [Real.exp_pos (-u / 2)]
      have hdsq : d ^ 2 ≤ Real.exp u := by
        have hmul := mul_le_mul hdle hdle hd0 (Real.exp_pos _).le
        rw [← pow_two, ← pow_two] at hmul
        rw [show Real.exp u = Real.exp (u / 2) ^ 2 by
          calc
            Real.exp u = Real.exp (u / 2 + u / 2) := by congr 1 <;> ring
            _ = Real.exp (u / 2) * Real.exp (u / 2) := Real.exp_add _ _
            _ = Real.exp (u / 2) ^ 2 := by ring]
        exact hmul
      have hexpLower : 1 + 2 * u ≤ Real.exp (2 * u) :=
        by simpa [add_comm] using Real.add_one_le_exp (2 * u)
      have hpiLower : 3 * (1 + 2 * u) ≤
          Real.pi * Real.exp (2 * u) := by
        calc
          3 * (1 + 2 * u) ≤ 3 * Real.exp (2 * u) := by nlinarith
          _ ≤ Real.pi * Real.exp (2 * u) :=
            mul_le_mul_of_nonneg_right Real.pi_gt_three.le
              (Real.exp_pos _).le
      have hexponent :
          u / 2 + (-Real.pi * Real.exp (2 * u)) + u ≤ -u := by
        nlinarith
      have hexpBound :
          Real.exp (u / 2 + (-Real.pi * Real.exp (2 * u)) + u) ≤
            Real.exp (-u) := Real.exp_le_exp.mpr hexponent
      have hfactor0 : 0 ≤
          2 * Real.exp (u / 2) *
            Real.exp (-Real.pi * Real.exp (2 * u)) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        unfold thetaFirstMode
        positivity)]
      unfold thetaFirstMode
      calc
        2 * Real.exp (u / 2) * Real.exp (-Real.pi * Real.exp (2 * u)) *
            d ^ 2 ≤
          2 * Real.exp (u / 2) * Real.exp (-Real.pi * Real.exp (2 * u)) *
            Real.exp u := mul_le_mul_of_nonneg_left hdsq hfactor0
        _ = 2 * Real.exp
            (u / 2 + (-Real.pi * Real.exp (2 * u)) + u) := by
          rw [Real.exp_add, Real.exp_add]
          ring
        _ ≤ 2 * Real.exp (-u) :=
          mul_le_mul_of_nonneg_left hexpBound (by norm_num)
  apply hrhs.congr
  exact Filter.Eventually.of_forall (fun u ↦
    (thetaSecondMomentMajorant_comp_exp u).symm)

private theorem firstModeSecondMoment_le_rationalMajorant :
    (∫ u in Ioi (0 : ℝ), u ^ 2 * thetaFirstMode u) ≤
      ∫ y in Ioi (0 : ℝ), thetaRationalMomentMajorant y := by
  let f : ℝ → ℝ := fun u ↦ Real.exp (2 * u) - 1
  let f' : ℝ → ℝ := fun u ↦ 2 * Real.exp (2 * u)
  have hf : ContinuousOn f (Ici (0 : ℝ)) := by
    unfold f
    fun_prop
  have hft : Tendsto f atTop atTop := by
    have hbase : Tendsto (fun u : ℝ ↦ Real.exp (2 * u)) atTop atTop :=
      Real.tendsto_exp_atTop.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    simpa [f, sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ) hbase
  have hff' : ∀ u ∈ Ioi (0 : ℝ),
      HasDerivWithinAt f (f' u) (Ioi u) u := by
    intro u _hu
    apply HasDerivAt.hasDerivWithinAt
    unfold f f'
    have hlinear : HasDerivAt (fun x : ℝ ↦ 2 * x) 2 u := by
      simpa using (hasDerivAt_id u).const_mul 2
    have hexpBase := (Real.hasDerivAt_exp (2 * u)).comp u hlinear
    have hexp : HasDerivAt (fun x : ℝ ↦ Real.exp (2 * x))
        (2 * Real.exp (2 * u)) u := by
      refine (hexpBase.congr_of_eventuallyEq ?_).congr_deriv ?_
      · exact Filter.Eventually.of_forall (fun _x ↦ rfl)
      · ring
    exact hexp.sub_const 1
  have hgcont : ContinuousOn thetaSecondMomentMajorant (f '' Ioi (0 : ℝ)) := by
    apply continuousOn_thetaSecondMomentMajorant.mono
    intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    change 0 < u at hu
    change 0 ≤ f u
    unfold f
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by linarith [hu]))
  have hgint : IntegrableOn thetaSecondMomentMajorant (f '' Ici (0 : ℝ)) := by
    apply integrableOn_thetaSecondMomentMajorant.mono_set
    intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    change 0 ≤ f u
    unfold f
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr
      (mul_nonneg (by norm_num) hu))
  have hcomp : IntegrableOn
      (fun u : ℝ ↦ (thetaSecondMomentMajorant ∘ f) u * f' u)
      (Ici (0 : ℝ)) := by
    apply integrableOn_thetaSecondMomentComposite.congr
    exact Filter.Eventually.of_forall (fun u ↦ by
      simp only [Function.comp_apply]
      rfl)
  have hchange := integral_comp_mul_deriv_Ioi hf hft hff' hgcont hgint hcomp
  have hfzero : f 0 = 0 := by simp [f]
  rw [hfzero] at hchange
  have hmono :
      (∫ u in Ioi (0 : ℝ), u ^ 2 * thetaFirstMode u) ≤
        ∫ u in Ioi (0 : ℝ),
          (thetaSecondMomentMajorant ∘ f) u * f' u := by
    apply integral_mono_ae integrableOn_pow_two_mul_thetaFirstMode
      (hcomp.mono_set Ioi_subset_Ici_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0 < u at hu
    have hudiff := self_le_exp_half_sub_exp_neg_half hu.le
    have hdiff0 : 0 ≤ Real.exp (u / 2) - Real.exp (-u / 2) := by
      linarith
    have husq : u ^ 2 ≤
        (Real.exp (u / 2) - Real.exp (-u / 2)) ^ 2 := by
      nlinarith [mul_nonneg hu.le
        (sub_nonneg.mpr hudiff)]
    have hfirst0 : 0 ≤ thetaFirstMode u := by
      unfold thetaFirstMode
      positivity
    simp only [Function.comp_apply]
    unfold f f'
    rw [thetaSecondMomentMajorant_comp_exp]
    simpa [mul_comm] using mul_le_mul_of_nonneg_right husq hfirst0
  calc
    (∫ u in Ioi (0 : ℝ), u ^ 2 * thetaFirstMode u) ≤
        ∫ u in Ioi (0 : ℝ),
          (thetaSecondMomentMajorant ∘ f) u * f' u := hmono
    _ = ∫ y in Ioi (0 : ℝ), thetaSecondMomentMajorant y := hchange
    _ ≤ ∫ y in Ioi (0 : ℝ), thetaRationalMomentMajorant y := by
      apply integral_mono_ae
        (integrableOn_thetaSecondMomentMajorant.mono_set Ioi_subset_Ici_self)
        (integrableOn_thetaRationalMomentMajorant.mono_set Ioi_subset_Ici_self)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact thetaSecondMomentMajorant_le_rational hy.le

end

end CarrySelfAdjointOperator
