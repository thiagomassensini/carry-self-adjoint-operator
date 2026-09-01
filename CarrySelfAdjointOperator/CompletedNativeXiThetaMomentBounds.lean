import CarrySelfAdjointOperator.CompletedNativeXiThetaMoments
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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

private def thetaRationalProfileFirst (y : ℝ) : ℝ :=
  2 * y / (1 + (17 / 20 : ℝ) * y) ^ 3

private def thetaRationalProfileSecond (y : ℝ) : ℝ :=
  2 * (1 - 2 * (17 / 20 : ℝ) * y) /
    (1 + (17 / 20 : ℝ) * y) ^ 4

private theorem hasDerivAt_thetaRationalDenominator (y : ℝ) :
    HasDerivAt (fun z : ℝ ↦ 1 + (17 / 20 : ℝ) * z)
      (17 / 20 : ℝ) y := by
  have hbase := ((hasDerivAt_id y).const_mul (17 / 20 : ℝ)).const_add 1
  refine (hbase.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _z ↦ by
      simp only [id_eq])
  · ring

private theorem hasDerivAt_thetaRationalProfile (y : ℝ)
    (hden : 1 + (17 / 20 : ℝ) * y ≠ 0) :
    HasDerivAt thetaRationalProfile (thetaRationalProfileFirst y) y := by
  have hquot := (hasDerivAt_id y).div
    (hasDerivAt_thetaRationalDenominator y) hden
  have hpow := hquot.pow 2
  refine (hpow.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _z ↦ by
      simp only [thetaRationalProfile, id_eq, Pi.div_apply, Pi.pow_apply])
  · have halg :
        (2 : ℝ) * (y / (1 + (17 / 20 : ℝ) * y)) ^ (2 - 1) *
            ((1 * (1 + (17 / 20 : ℝ) * y) - y * (17 / 20 : ℝ)) /
              (1 + (17 / 20 : ℝ) * y) ^ 2) =
          2 * y / (1 + (17 / 20 : ℝ) * y) ^ 3 := by
      norm_num
      field_simp [hden]
      ring
    unfold thetaRationalProfileFirst
    simpa only [id_eq, Pi.div_apply, Pi.pow_apply, Nat.cast_ofNat] using halg

private theorem hasDerivAt_thetaRationalProfileFirst (y : ℝ)
    (hden : 1 + (17 / 20 : ℝ) * y ≠ 0) :
    HasDerivAt thetaRationalProfileFirst (thetaRationalProfileSecond y) y := by
  have hnum : HasDerivAt (fun z : ℝ ↦ 2 * z) 2 y := by
    simpa using (hasDerivAt_id y).const_mul 2
  have hdenpow := (hasDerivAt_thetaRationalDenominator y).pow 3
  have hquot := hnum.div hdenpow (pow_ne_zero 3 hden)
  refine (hquot.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _z ↦ by
      simp only [thetaRationalProfileFirst, Pi.div_apply, Pi.pow_apply])
  · simp only [Pi.pow_apply]
    unfold thetaRationalProfileSecond
    have hden20 : 20 + 17 * y ≠ 0 := by
      intro hzero
      apply hden
      norm_num at hzero ⊢
      linarith
    field_simp [hden, hden20]
    ring

private theorem continuousOn_thetaRationalProfile_Ici :
    ContinuousOn thetaRationalProfile (Ici (0 : ℝ)) := by
  intro y hy
  change 0 ≤ y at hy
  have hden : 0 < 1 + (17 / 20 : ℝ) * y := by positivity
  exact (hasDerivAt_thetaRationalProfile y hden.ne').continuousAt.continuousWithinAt

private def thetaRationalInflection : ℝ := 10 / 17

private theorem convexOn_thetaRationalProfile :
    ConvexOn ℝ (Icc (0 : ℝ) thetaRationalInflection)
      thetaRationalProfile := by
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (convex_Icc (0 : ℝ) thetaRationalInflection)
  · exact continuousOn_thetaRationalProfile_Ici.mono Icc_subset_Ici_self
  · intro y hy
    have hyIoo : y ∈ Ioo (0 : ℝ) thetaRationalInflection := by
      simpa only [interior_Icc] using hy
    have hy0 : 0 < y := hyIoo.1
    have hden : 1 + (17 / 20 : ℝ) * y ≠ 0 := by positivity
    exact (hasDerivAt_thetaRationalProfile y hden).hasDerivWithinAt
  · intro y hy
    have hyIoo : y ∈ Ioo (0 : ℝ) thetaRationalInflection := by
      simpa only [interior_Icc] using hy
    have hy0 : 0 < y := hyIoo.1
    have hden : 1 + (17 / 20 : ℝ) * y ≠ 0 := by positivity
    exact (hasDerivAt_thetaRationalProfileFirst y hden).hasDerivWithinAt
  · intro y hy
    have hyIoo : y ∈ Ioo (0 : ℝ) thetaRationalInflection := by
      simpa only [interior_Icc] using hy
    have hy' : y < thetaRationalInflection := hyIoo.2
    unfold thetaRationalProfileSecond
    unfold thetaRationalInflection at hy'
    have hden : 0 < (1 + (17 / 20 : ℝ) * y) ^ 4 := by
      have hy0 : 0 < y := hyIoo.1
      positivity
    apply div_nonneg
    · norm_num at hy' ⊢
      linarith
    · exact hden.le

private def thetaRationalChordSlope (a b : ℝ) : ℝ :=
  (thetaRationalProfile b - thetaRationalProfile a) / (b - a)

private def thetaRationalChordIntercept (a b : ℝ) : ℝ :=
  thetaRationalProfile a - thetaRationalChordSlope a b * a

private theorem thetaRationalProfile_le_chord {a b y : ℝ}
    (ha0 : 0 ≤ a) (hab : a < b) (hbR : b ≤ thetaRationalInflection)
    (hay : a ≤ y) (hyb : y ≤ b) :
    thetaRationalProfile y ≤
      thetaRationalChordIntercept a b + thetaRationalChordSlope a b * y := by
  let leftWeight : ℝ := (b - y) / (b - a)
  let rightWeight : ℝ := (y - a) / (b - a)
  have hden : 0 < b - a := sub_pos.mpr hab
  have hleft0 : 0 ≤ leftWeight := div_nonneg (sub_nonneg.mpr hyb) hden.le
  have hright0 : 0 ≤ rightWeight := div_nonneg (sub_nonneg.mpr hay) hden.le
  have hweights : leftWeight + rightWeight = 1 := by
    dsimp [leftWeight, rightWeight]
    field_simp [hden.ne']
    ring
  have haMem : a ∈ Icc (0 : ℝ) thetaRationalInflection :=
    ⟨ha0, hab.le.trans hbR⟩
  have hbMem : b ∈ Icc (0 : ℝ) thetaRationalInflection :=
    ⟨ha0.trans hab.le, hbR⟩
  have hconvex := convexOn_thetaRationalProfile.2 haMem hbMem
    hleft0 hright0 hweights
  change thetaRationalProfile
      (leftWeight * a + rightWeight * b) ≤
        leftWeight * thetaRationalProfile a +
          rightWeight * thetaRationalProfile b at hconvex
  have hpoint : leftWeight * a + rightWeight * b = y := by
    dsimp [leftWeight, rightWeight]
    field_simp [hden.ne']
    ring
  rw [hpoint] at hconvex
  calc
    thetaRationalProfile y ≤
        leftWeight * thetaRationalProfile a +
          rightWeight * thetaRationalProfile b := hconvex
    _ = thetaRationalChordIntercept a b +
        thetaRationalChordSlope a b * y := by
      unfold thetaRationalChordIntercept thetaRationalChordSlope
      dsimp [leftWeight, rightWeight]
      field_simp [hden.ne']
      ring

private def thetaRationalTangentSlope (q : ℝ) : ℝ :=
  thetaRationalProfileFirst q

private def thetaRationalTangentIntercept (q : ℝ) : ℝ :=
  thetaRationalProfile q - thetaRationalTangentSlope q * q

private theorem thetaRationalProfile_le_tangent {q y : ℝ}
    (hqDen : 0 < 1 + (17 / 20 : ℝ) * q)
    (hyDen : 0 < 1 + (17 / 20 : ℝ) * y)
    (hlinear : 0 ≤
      2 * q * (17 / 20 : ℝ) ^ 2 * y + (17 / 20 : ℝ) * q - 1) :
    thetaRationalProfile y ≤
      thetaRationalTangentIntercept q + thetaRationalTangentSlope q * y := by
  have hfactor :
      thetaRationalTangentIntercept q + thetaRationalTangentSlope q * y -
          thetaRationalProfile y =
        (y - q) ^ 2 *
          (2 * q * (17 / 20 : ℝ) ^ 2 * y +
            (17 / 20 : ℝ) * q - 1) /
          ((1 + (17 / 20 : ℝ) * q) ^ 3 *
            (1 + (17 / 20 : ℝ) * y) ^ 2) := by
    have hqDen20 : 20 + 17 * q ≠ 0 := by
      intro hzero
      norm_num at hqDen hzero
      nlinarith
    have hyDen20 : 20 + 17 * y ≠ 0 := by
      intro hzero
      norm_num at hyDen hzero
      nlinarith
    have hqDenCube :
        8000 + q * 20400 + q ^ 2 * 17340 + q ^ 3 * 4913 ≠ 0 := by
      rw [show 8000 + q * 20400 + q ^ 2 * 17340 + q ^ 3 * 4913 =
          (20 + 17 * q) ^ 3 by ring]
      exact pow_ne_zero 3 hqDen20
    have hqDen20Comm : 20 + q * 17 ≠ 0 := by
      simpa only [mul_comm] using hqDen20
    unfold thetaRationalTangentIntercept thetaRationalTangentSlope
      thetaRationalProfileFirst thetaRationalProfile
    rw [div_pow, div_pow]
    field_simp [hqDen.ne', hyDen.ne', hqDen20, hyDen20, hqDenCube]
    try field_simp [hqDen20Comm]
    ring
  have hnonneg : 0 ≤
      thetaRationalTangentIntercept q + thetaRationalTangentSlope q * y -
        thetaRationalProfile y := by
    rw [hfactor]
    positivity
  linarith

private theorem thetaRationalProfile_le_inflectionTangent {y : ℝ}
    (hy : thetaRationalInflection ≤ y) :
    thetaRationalProfile y ≤
      thetaRationalTangentIntercept thetaRationalInflection +
        thetaRationalTangentSlope thetaRationalInflection * y := by
  apply thetaRationalProfile_le_tangent
  · unfold thetaRationalInflection
    norm_num
  · unfold thetaRationalInflection at hy
    positivity
  · unfold thetaRationalInflection at hy ⊢
    norm_num at hy ⊢
    nlinarith

private theorem thetaRationalProfile_le_threeHalvesTangent {y : ℝ}
    (hy : 0 ≤ y) :
    thetaRationalProfile y ≤
      thetaRationalTangentIntercept (3 / 2 : ℝ) +
        thetaRationalTangentSlope (3 / 2 : ℝ) * y := by
  apply thetaRationalProfile_le_tangent
  · norm_num
  · positivity
  · norm_num at hy ⊢
    linarith

private def thetaRationalTangentSwitch : ℝ :=
  3970 / 3587

private theorem exp_neg_thetaRationalKnot_one_lt :
    Real.exp (-(6283 / 2000 : ℝ) * (1 + 9 / 200 : ℝ)) <
      37521 / 1000000 := by
  rw [show -(6283 / 2000 : ℝ) * (1 + 9 / 200 : ℝ) =
      -((6283 / 2000 : ℝ) * (1 + 9 / 200 : ℝ)) by ring]
  apply exp_neg_lt_of_partial_sum
    ((6283 / 2000 : ℝ) * (1 + 9 / 200 : ℝ))
    (37521 / 1000000 : ℝ) 16
  · norm_num
  · norm_num
  · norm_num [Finset.sum_range_succ]

private theorem exp_neg_thetaRationalKnot_two_lt :
    Real.exp (-(6283 / 2000 : ℝ) * (1 + 2 / 25 : ℝ)) <
      33614 / 1000000 := by
  rw [show -(6283 / 2000 : ℝ) * (1 + 2 / 25 : ℝ) =
      -((6283 / 2000 : ℝ) * (1 + 2 / 25 : ℝ)) by ring]
  apply exp_neg_lt_of_partial_sum
    ((6283 / 2000 : ℝ) * (1 + 2 / 25 : ℝ))
    (33614 / 1000000 : ℝ) 16
  · norm_num
  · norm_num
  · norm_num [Finset.sum_range_succ]

private theorem exp_neg_thetaRationalKnot_three_lt :
    Real.exp (-(6283 / 2000 : ℝ) * (1 + 1 / 8 : ℝ)) <
      29183 / 1000000 := by
  rw [show -(6283 / 2000 : ℝ) * (1 + 1 / 8 : ℝ) =
      -((6283 / 2000 : ℝ) * (1 + 1 / 8 : ℝ)) by ring]
  apply exp_neg_lt_of_partial_sum
    ((6283 / 2000 : ℝ) * (1 + 1 / 8 : ℝ))
    (29183 / 1000000 : ℝ) 16
  · norm_num
  · norm_num
  · norm_num [Finset.sum_range_succ]

private theorem exp_neg_thetaRationalKnot_four_lt :
    Real.exp (-(6283 / 2000 : ℝ) * (1 + 9 / 50 : ℝ)) <
      24552 / 1000000 := by
  rw [show -(6283 / 2000 : ℝ) * (1 + 9 / 50 : ℝ) =
      -((6283 / 2000 : ℝ) * (1 + 9 / 50 : ℝ)) by ring]
  apply exp_neg_lt_of_partial_sum
    ((6283 / 2000 : ℝ) * (1 + 9 / 50 : ℝ))
    (24552 / 1000000 : ℝ) 16
  · norm_num
  · norm_num
  · norm_num [Finset.sum_range_succ]

private theorem exp_neg_thetaRationalKnot_five_lt :
    Real.exp (-(6283 / 2000 : ℝ) * (1 + 13 / 50 : ℝ)) <
      19096 / 1000000 := by
  rw [show -(6283 / 2000 : ℝ) * (1 + 13 / 50 : ℝ) =
      -((6283 / 2000 : ℝ) * (1 + 13 / 50 : ℝ)) by ring]
  apply exp_neg_lt_of_partial_sum
    ((6283 / 2000 : ℝ) * (1 + 13 / 50 : ℝ))
    (19096 / 1000000 : ℝ) 16
  · norm_num
  · norm_num
  · norm_num [Finset.sum_range_succ]

private theorem exp_neg_thetaRationalKnot_six_lt :
    Real.exp (-(6283 / 2000 : ℝ) * (1 + 7 / 20 : ℝ)) <
      14393 / 1000000 := by
  rw [show -(6283 / 2000 : ℝ) * (1 + 7 / 20 : ℝ) =
      -((6283 / 2000 : ℝ) * (1 + 7 / 20 : ℝ)) by ring]
  apply exp_neg_lt_of_partial_sum
    ((6283 / 2000 : ℝ) * (1 + 7 / 20 : ℝ))
    (14393 / 1000000 : ℝ) 16
  · norm_num
  · norm_num
  · norm_num [Finset.sum_range_succ]

private theorem exp_neg_thetaRationalKnot_seven_lt :
    Real.exp (-(6283 / 2000 : ℝ) * (1 + 43 / 100 : ℝ)) <
      11195 / 1000000 := by
  rw [show -(6283 / 2000 : ℝ) * (1 + 43 / 100 : ℝ) =
      -((6283 / 2000 : ℝ) * (1 + 43 / 100 : ℝ)) by ring]
  apply exp_neg_lt_of_partial_sum
    ((6283 / 2000 : ℝ) * (1 + 43 / 100 : ℝ))
    (11195 / 1000000 : ℝ) 16
  · norm_num
  · norm_num
  · norm_num [Finset.sum_range_succ]

private theorem exp_neg_thetaRationalInflection_lt :
    Real.exp (-(6283 / 2000 : ℝ) * (1 + thetaRationalInflection)) <
      6810 / 1000000 := by
  rw [show -(6283 / 2000 : ℝ) * (1 + thetaRationalInflection) =
      -((6283 / 2000 : ℝ) * (1 + thetaRationalInflection)) by ring]
  apply exp_neg_lt_of_partial_sum
    ((6283 / 2000 : ℝ) * (1 + thetaRationalInflection))
    (6810 / 1000000 : ℝ) 16
  · unfold thetaRationalInflection
    norm_num
  · norm_num
  · unfold thetaRationalInflection
    norm_num [Finset.sum_range_succ]

private theorem exp_upper_bound_sixth {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤
      (∑ m ∈ Finset.range 6, x ^ m / m.factorial) +
        x ^ 6 * 7 / (Nat.factorial 6 * 6) :=
  by
    convert Real.exp_bound' hx0 hx1 (n := 6) (by norm_num) using 1 <;> norm_num

private theorem exp_neg_thetaRationalTangentSwitch_gt :
    (1335 / 1000000 : ℝ) <
      Real.exp (-(6283 / 2000 : ℝ) * (1 + thetaRationalTangentSwitch)) := by
  let x : ℝ :=
    (6283 / 2000 : ℝ) * (1 + thetaRationalTangentSwitch)
  let z : ℝ := x / 8
  let U : ℝ :=
    (∑ m ∈ Finset.range 6, z ^ m / m.factorial) +
      z ^ 6 * 7 / (Nat.factorial 6 * 6)
  have hz0 : 0 ≤ z := by
    dsimp [z, x, thetaRationalTangentSwitch]
    norm_num
  have hz1 : z ≤ 1 := by
    dsimp [z, x, thetaRationalTangentSwitch]
    norm_num
  have hz : Real.exp z ≤ U := exp_upper_bound_sixth hz0 hz1
  have hexp : Real.exp x ≤ U ^ 8 := by
    have hrewrite : x = z * 8 := by
      dsimp [z]
      ring
    rw [hrewrite]
    calc
      Real.exp (z * 8) = Real.exp z ^ 8 := by
        simpa [mul_comm] using Real.exp_nat_mul z 8
      _ ≤ U ^ 8 := pow_le_pow_left₀ (Real.exp_nonneg z) hz 8
  have hU : U ^ 8 < (1000000 / 1335 : ℝ) := by
    dsimp [U, z, x, thetaRationalTangentSwitch]
    norm_num [Finset.sum_range_succ]
  have harg :
      -(6283 / 2000 : ℝ) * (1 + thetaRationalTangentSwitch) = -x := by
    dsimp [x]
    ring
  rw [harg, Real.exp_neg, ← one_div]
  apply (lt_div_iff₀ (Real.exp_pos x)).2
  calc
    (1335 / 1000000 : ℝ) * Real.exp x ≤
        (1335 / 1000000 : ℝ) * U ^ 8 :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ < (1335 / 1000000 : ℝ) * (1000000 / 1335 : ℝ) :=
      mul_lt_mul_of_pos_left hU (by norm_num)
    _ = 1 := by norm_num

private def thetaRationalAffinePrimitive (A B y : ℝ) : ℝ :=
  (1 / 4 : ℝ) * Real.exp (-(6283 / 2000 : ℝ) * (1 + y)) *
    (-(A + B * y) / (6283 / 2000 : ℝ) -
      B / (6283 / 2000 : ℝ) ^ 2)

private theorem hasDerivAt_thetaRationalAffinePrimitive (A B y : ℝ) :
    HasDerivAt (thetaRationalAffinePrimitive A B)
      ((1 / 4 : ℝ) * (A + B * y) *
        Real.exp (-(6283 / 2000 : ℝ) * (1 + y))) y := by
  have hbase := hasDerivAt_affineExpPrimitive
    (6283 / 2000 : ℝ) A B y (by norm_num)
  have hscaled := hbase.const_mul
    ((1 / 4 : ℝ) * Real.exp (-(6283 / 2000 : ℝ)))
  refine (hscaled.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun z ↦ by
      have hexp :
          Real.exp (-(6283 / 2000 : ℝ)) *
              Real.exp (-(6283 / 2000 : ℝ) * z) =
            Real.exp (-(6283 / 2000 : ℝ) * (1 + z)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      unfold thetaRationalAffinePrimitive affineExpPrimitive
      rw [← hexp]
      ring)
  · have hexp :
        Real.exp (-(6283 / 2000 : ℝ)) *
            Real.exp (-(6283 / 2000 : ℝ) * y) =
          Real.exp (-(6283 / 2000 : ℝ) * (1 + y)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hexp]
    ring

private theorem integral_thetaRationalAffine (A B a b : ℝ) :
    (∫ y in a..b, (1 / 4 : ℝ) * (A + B * y) *
      Real.exp (-(6283 / 2000 : ℝ) * (1 + y))) =
        thetaRationalAffinePrimitive A B b -
          thetaRationalAffinePrimitive A B a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y _hy
    exact hasDerivAt_thetaRationalAffinePrimitive A B y
  · exact (by fun_prop : Continuous (fun y : ℝ ↦
      (1 / 4 : ℝ) * (A + B * y) *
        Real.exp (-(6283 / 2000 : ℝ) * (1 + y)))).intervalIntegrable a b

private theorem integral_thetaRationalMomentMajorant_le_affine
    {a b A B : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hprofile : ∀ y ∈ Icc a b, thetaRationalProfile y ≤ A + B * y) :
    (∫ y in a..b, thetaRationalMomentMajorant y) ≤
      thetaRationalAffinePrimitive A B b -
        thetaRationalAffinePrimitive A B a := by
  have hleft : IntervalIntegrable thetaRationalMomentMajorant volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    apply integrableOn_thetaRationalMomentMajorant.mono_set
    intro y hy
    exact ha0.trans hy.1.le
  have hright : IntervalIntegrable
      (fun y : ℝ ↦ (1 / 4 : ℝ) * (A + B * y) *
        Real.exp (-(6283 / 2000 : ℝ) * (1 + y))) volume a b :=
    (by fun_prop : Continuous (fun y : ℝ ↦
      (1 / 4 : ℝ) * (A + B * y) *
        Real.exp (-(6283 / 2000 : ℝ) * (1 + y)))).intervalIntegrable a b
  have hmono := intervalIntegral.integral_mono_on hab hleft hright
    (fun y hy ↦ by
      have hp := hprofile y hy
      unfold thetaRationalMomentMajorant
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (by norm_num)) (Real.exp_pos _).le)
  rw [integral_thetaRationalAffine] at hmono
  exact hmono

private theorem integral_thetaRationalMomentMajorant_le_chord
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b)
    (hbR : b ≤ thetaRationalInflection) :
    (∫ y in a..b, thetaRationalMomentMajorant y) ≤
      thetaRationalAffinePrimitive (thetaRationalChordIntercept a b)
          (thetaRationalChordSlope a b) b -
        thetaRationalAffinePrimitive (thetaRationalChordIntercept a b)
          (thetaRationalChordSlope a b) a := by
  apply integral_thetaRationalMomentMajorant_le_affine ha0 hab.le
  intro y hy
  exact thetaRationalProfile_le_chord ha0 hab hbR hy.1 hy.2

private theorem tendsto_thetaRationalAffinePrimitive_atTop (A B : ℝ) :
    Tendsto (thetaRationalAffinePrimitive A B) atTop (nhds 0) := by
  have hp : (0 : ℝ) < 6283 / 2000 := by norm_num
  have hexp : Tendsto
      (fun y : ℝ ↦ Real.exp (-(6283 / 2000 : ℝ) * y)) atTop (nhds 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (0 : ℝ) (6283 / 2000 : ℝ) hp
  have hyexp : Tendsto
      (fun y : ℝ ↦ y * Real.exp (-(6283 / 2000 : ℝ) * y)) atTop (nhds 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (1 : ℝ) (6283 / 2000 : ℝ) hp
  let C : ℝ := (1 / 4 : ℝ) * Real.exp (-(6283 / 2000 : ℝ)) *
    (-A / (6283 / 2000 : ℝ) - B / (6283 / 2000 : ℝ) ^ 2)
  let D : ℝ := (1 / 4 : ℝ) * Real.exp (-(6283 / 2000 : ℝ)) *
    (-B / (6283 / 2000 : ℝ))
  have hlim := (hexp.const_mul C).add (hyexp.const_mul D)
  have hzero : C * 0 + D * 0 = 0 := by ring
  rw [hzero] at hlim
  apply hlim.congr'
  filter_upwards with y
  have hexpShift :
      Real.exp (-(6283 / 2000 : ℝ) * (1 + y)) =
        Real.exp (-(6283 / 2000 : ℝ)) *
          Real.exp (-(6283 / 2000 : ℝ) * y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold thetaRationalAffinePrimitive
  dsimp [C, D]
  rw [hexpShift]
  ring

private theorem integral_Ioi_thetaRationalAffine
    (A B a : ℝ) (hline0 : ∀ y ∈ Ioi a, 0 ≤ A + B * y) :
    (∫ y in Ioi a, (1 / 4 : ℝ) * (A + B * y) *
      Real.exp (-(6283 / 2000 : ℝ) * (1 + y))) =
        -thetaRationalAffinePrimitive A B a := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := thetaRationalAffinePrimitive A B)
    (g' := fun y : ℝ ↦ (1 / 4 : ℝ) * (A + B * y) *
      Real.exp (-(6283 / 2000 : ℝ) * (1 + y)))
    (a := a) (l := 0)
    (fun y _hy ↦ hasDerivAt_thetaRationalAffinePrimitive A B y)
    (fun y hy ↦ mul_nonneg
      (mul_nonneg (by norm_num) (hline0 y hy)) (Real.exp_pos _).le)
    (tendsto_thetaRationalAffinePrimitive_atTop A B)
  simpa using h

private theorem integral_Ioi_thetaRationalMomentMajorant_le_affine
    {a A B : ℝ} (ha0 : 0 ≤ a)
    (hprofile : ∀ y ∈ Ioi a, thetaRationalProfile y ≤ A + B * y)
    (hline0 : ∀ y ∈ Ioi a, 0 ≤ A + B * y) :
    (∫ y in Ioi a, thetaRationalMomentMajorant y) ≤
      -thetaRationalAffinePrimitive A B a := by
  have hleft : IntegrableOn thetaRationalMomentMajorant (Ioi a) :=
    integrableOn_thetaRationalMomentMajorant.mono_set (by
      intro y hy
      exact ha0.trans hy.le)
  have hright : IntegrableOn
      (fun y : ℝ ↦ (1 / 4 : ℝ) * (A + B * y) *
        Real.exp (-(6283 / 2000 : ℝ) * (1 + y))) (Ioi a) :=
    integrableOn_Ioi_deriv_of_nonneg'
      (g := thetaRationalAffinePrimitive A B)
      (fun y _hy ↦ hasDerivAt_thetaRationalAffinePrimitive A B y)
      (fun y hy ↦ mul_nonneg
        (mul_nonneg (by norm_num) (hline0 y hy)) (Real.exp_pos _).le)
      (tendsto_thetaRationalAffinePrimitive_atTop A B)
  have hmono := integral_mono_ae hleft hright (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    unfold thetaRationalMomentMajorant
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hprofile y hy) (by norm_num))
      (Real.exp_pos _).le)
  rw [integral_Ioi_thetaRationalAffine A B a hline0] at hmono
  exact hmono

private theorem thetaRationalInflectionTangent_eq (y : ℝ) :
    thetaRationalTangentIntercept thetaRationalInflection +
        thetaRationalTangentSlope thetaRationalInflection * y =
      (-400 / 7803 : ℝ) + (160 / 459 : ℝ) * y := by
  unfold thetaRationalTangentIntercept thetaRationalTangentSlope
    thetaRationalProfileFirst thetaRationalProfile thetaRationalInflection
  norm_num

private theorem thetaRationalThreeHalvesTangent_eq (y : ℝ) :
    thetaRationalTangentIntercept (3 / 2 : ℝ) +
        thetaRationalTangentSlope (3 / 2 : ℝ) * y =
      (39600 / 753571 : ℝ) + (192000 / 753571 : ℝ) * y := by
  unfold thetaRationalTangentIntercept thetaRationalTangentSlope
    thetaRationalProfileFirst thetaRationalProfile
  norm_num

private theorem integral_thetaRationalMomentMajorant_le_exactChord
    {a b A B : ℝ} (ha0 : 0 ≤ a) (hab : a < b)
    (hbR : b ≤ thetaRationalInflection)
    (hline : ∀ y : ℝ,
      thetaRationalChordIntercept a b + thetaRationalChordSlope a b * y =
        A + B * y) :
    (∫ y in a..b, thetaRationalMomentMajorant y) ≤
      thetaRationalAffinePrimitive A B b -
        thetaRationalAffinePrimitive A B a := by
  apply integral_thetaRationalMomentMajorant_le_affine ha0 hab.le
  intro y hy
  calc
    thetaRationalProfile y ≤
        thetaRationalChordIntercept a b + thetaRationalChordSlope a b * y :=
      thetaRationalProfile_le_chord ha0 hab hbR hy.1 hy.2
    _ = A + B * y := hline y

private theorem integral_thetaRationalMomentMajorant_lt :
    (∫ y in Ioi (0 : ℝ), thetaRationalMomentMajorant y) <
      254 / 1000000 := by
  have h0 :
      (∫ y in (0 : ℝ)..(9 / 200 : ℝ), thetaRationalMomentMajorant y) ≤
        thetaRationalAffinePrimitive (0 : ℝ)
            (720000 / 17247409 : ℝ) (9 / 200 : ℝ) -
          thetaRationalAffinePrimitive (0 : ℝ)
            (720000 / 17247409 : ℝ) 0 := by
    apply integral_thetaRationalMomentMajorant_le_exactChord
    · norm_num
    · norm_num
    · unfold thetaRationalInflection
      norm_num
    · intro y
      norm_num [thetaRationalChordIntercept, thetaRationalChordSlope,
        thetaRationalProfile]
  have h1 :
      (∫ y in (9 / 200 : ℝ)..(2 / 25 : ℝ), thetaRationalMomentMajorant y) ≤
        thetaRationalAffinePrimitive (-398959600 / 136616726689 : ℝ)
            (131120000000 / 1229550540201 : ℝ) (2 / 25 : ℝ) -
          thetaRationalAffinePrimitive (-398959600 / 136616726689 : ℝ)
            (131120000000 / 1229550540201 : ℝ) (9 / 200 : ℝ) := by
    apply integral_thetaRationalMomentMajorant_le_exactChord
    · norm_num
    · norm_num
    · unfold thetaRationalInflection
      norm_num
    · intro y
      norm_num [thetaRationalChordIntercept, thetaRationalChordSlope,
        thetaRationalProfile]
  have h2 :
      (∫ y in (2 / 25 : ℝ)..(1 / 8 : ℝ), thetaRationalMomentMajorant y) ≤
        thetaRationalAffinePrimitive (-5294800 / 744471027 : ℝ)
            (118400000 / 744471027 : ℝ) (1 / 8 : ℝ) -
          thetaRationalAffinePrimitive (-5294800 / 744471027 : ℝ)
            (118400000 / 744471027 : ℝ) (2 / 25 : ℝ) := by
    apply integral_thetaRationalMomentMajorant_le_exactChord
    · norm_num
    · norm_num
    · unfold thetaRationalInflection
      norm_num
    · intro y
      norm_num [thetaRationalChordIntercept, thetaRationalChordSlope,
        thetaRationalProfile]
  have h3 :
      (∫ y in (1 / 8 : ℝ)..(9 / 50 : ℝ), thetaRationalMomentMajorant y) ≤
        thetaRationalAffinePrimitive (-62959600 / 4627672729 : ℝ)
            (8787200000 / 41649054561 : ℝ) (9 / 50 : ℝ) -
          thetaRationalAffinePrimitive (-62959600 / 4627672729 : ℝ)
            (8787200000 / 41649054561 : ℝ) (1 / 8 : ℝ) := by
    apply integral_thetaRationalMomentMajorant_le_exactChord
    · norm_num
    · norm_num
    · unfold thetaRationalInflection
      norm_num
    · intro y
      norm_num [thetaRationalChordIntercept, thetaRationalChordSlope,
        thetaRationalProfile]
  have h4 :
      (∫ y in (9 / 50 : ℝ)..(13 / 50 : ℝ), thetaRationalMomentMajorant y) ≤
        thetaRationalAffinePrimitive (-5024172400 / 220215271441 : ℝ)
            (519560000000 / 1981937442969 : ℝ) (13 / 50 : ℝ) -
          thetaRationalAffinePrimitive (-5024172400 / 220215271441 : ℝ)
            (519560000000 / 1981937442969 : ℝ) (9 / 50 : ℝ) := by
    apply integral_thetaRationalMomentMajorant_le_exactChord
    · norm_num
    · norm_num
    · unfold thetaRationalInflection
      norm_num
    · intro y
      norm_num [thetaRationalChordIntercept, thetaRationalChordSlope,
        thetaRationalProfile]
  have h5 :
      (∫ y in (13 / 50 : ℝ)..(7 / 20 : ℝ), thetaRationalMomentMajorant y) ≤
        thetaRationalAffinePrimitive (-4534238800 / 133858140867 : ℝ)
            (40784000000 / 133858140867 : ℝ) (7 / 20 : ℝ) -
          thetaRationalAffinePrimitive (-4534238800 / 133858140867 : ℝ)
            (40784000000 / 133858140867 : ℝ) (13 / 50 : ℝ) := by
    apply integral_thetaRationalMomentMajorant_le_exactChord
    · norm_num
    · norm_num
    · unfold thetaRationalInflection
      norm_num
    · intro y
      norm_num [thetaRationalChordIntercept, thetaRationalChordSlope,
        thetaRationalProfile]
  have h6 :
      (∫ y in (7 / 20 : ℝ)..(43 / 100 : ℝ), thetaRationalMomentMajorant y) ≤
        thetaRationalAffinePrimitive (-85846524400 / 2008991577321 : ℝ)
            (662944000000 / 2008991577321 : ℝ) (43 / 100 : ℝ) -
          thetaRationalAffinePrimitive (-85846524400 / 2008991577321 : ℝ)
            (662944000000 / 2008991577321 : ℝ) (7 / 20 : ℝ) := by
    apply integral_thetaRationalMomentMajorant_le_exactChord
    · norm_num
    · norm_num
    · unfold thetaRationalInflection
      norm_num
    · intro y
      norm_num [thetaRationalChordIntercept, thetaRationalChordSlope,
        thetaRationalProfile]
  have h7 :
      (∫ y in (43 / 100 : ℝ)..thetaRationalInflection,
        thetaRationalMomentMajorant y) ≤
        thetaRationalAffinePrimitive (-56226800 / 1141129233 : ℝ)
            (393920000 / 1141129233 : ℝ) thetaRationalInflection -
          thetaRationalAffinePrimitive (-56226800 / 1141129233 : ℝ)
            (393920000 / 1141129233 : ℝ) (43 / 100 : ℝ) := by
    apply integral_thetaRationalMomentMajorant_le_exactChord
    · norm_num
    · unfold thetaRationalInflection
      norm_num
    · exact le_rfl
    · intro y
      norm_num [thetaRationalChordIntercept, thetaRationalChordSlope,
        thetaRationalProfile, thetaRationalInflection]
  have h8 :
      (∫ y in thetaRationalInflection..thetaRationalTangentSwitch,
        thetaRationalMomentMajorant y) ≤
        thetaRationalAffinePrimitive (-400 / 7803 : ℝ) (160 / 459 : ℝ)
            thetaRationalTangentSwitch -
          thetaRationalAffinePrimitive (-400 / 7803 : ℝ) (160 / 459 : ℝ)
            thetaRationalInflection := by
    apply integral_thetaRationalMomentMajorant_le_affine
    · unfold thetaRationalInflection
      norm_num
    · unfold thetaRationalInflection thetaRationalTangentSwitch
      norm_num
    · intro y hy
      calc
        thetaRationalProfile y ≤
            thetaRationalTangentIntercept thetaRationalInflection +
              thetaRationalTangentSlope thetaRationalInflection * y :=
          thetaRationalProfile_le_inflectionTangent hy.1
        _ = (-400 / 7803 : ℝ) + (160 / 459 : ℝ) * y :=
          thetaRationalInflectionTangent_eq y
  have h9 :
      (∫ y in Ioi thetaRationalTangentSwitch,
        thetaRationalMomentMajorant y) ≤
        -thetaRationalAffinePrimitive (39600 / 753571 : ℝ)
          (192000 / 753571 : ℝ) thetaRationalTangentSwitch := by
    apply integral_Ioi_thetaRationalMomentMajorant_le_affine
    · unfold thetaRationalTangentSwitch
      norm_num
    · intro y hy
      have hy0 : 0 ≤ y := by
        change thetaRationalTangentSwitch < y at hy
        unfold thetaRationalTangentSwitch at hy
        norm_num at hy
        linarith
      calc
        thetaRationalProfile y ≤
            thetaRationalTangentIntercept (3 / 2 : ℝ) +
              thetaRationalTangentSlope (3 / 2 : ℝ) * y :=
          thetaRationalProfile_le_threeHalvesTangent hy0
        _ = (39600 / 753571 : ℝ) + (192000 / 753571 : ℝ) * y :=
          thetaRationalThreeHalvesTangent_eq y
    · intro y hy
      change thetaRationalTangentSwitch < y at hy
      unfold thetaRationalTangentSwitch at hy
      norm_num at hy ⊢
      linarith
  have hIoi : ∀ a : ℝ, 0 ≤ a →
      IntegrableOn thetaRationalMomentMajorant (Ioi a) := by
    intro a ha
    apply integrableOn_thetaRationalMomentMajorant.mono_set
    intro y hy
    exact ha.trans hy.le
  have hs0 := intervalIntegral.integral_interval_add_Ioi
    (hIoi 0 (by norm_num)) (hIoi (9 / 200 : ℝ) (by norm_num))
  have hs1 := intervalIntegral.integral_interval_add_Ioi
    (hIoi (9 / 200 : ℝ) (by norm_num))
    (hIoi (2 / 25 : ℝ) (by norm_num))
  have hs2 := intervalIntegral.integral_interval_add_Ioi
    (hIoi (2 / 25 : ℝ) (by norm_num))
    (hIoi (1 / 8 : ℝ) (by norm_num))
  have hs3 := intervalIntegral.integral_interval_add_Ioi
    (hIoi (1 / 8 : ℝ) (by norm_num))
    (hIoi (9 / 50 : ℝ) (by norm_num))
  have hs4 := intervalIntegral.integral_interval_add_Ioi
    (hIoi (9 / 50 : ℝ) (by norm_num))
    (hIoi (13 / 50 : ℝ) (by norm_num))
  have hs5 := intervalIntegral.integral_interval_add_Ioi
    (hIoi (13 / 50 : ℝ) (by norm_num))
    (hIoi (7 / 20 : ℝ) (by norm_num))
  have hs6 := intervalIntegral.integral_interval_add_Ioi
    (hIoi (7 / 20 : ℝ) (by norm_num))
    (hIoi (43 / 100 : ℝ) (by norm_num))
  have hs7 := intervalIntegral.integral_interval_add_Ioi
    (hIoi (43 / 100 : ℝ) (by norm_num))
    (hIoi thetaRationalInflection (by
      unfold thetaRationalInflection
      norm_num))
  have hs8 := intervalIntegral.integral_interval_add_Ioi
    (hIoi thetaRationalInflection (by
      unfold thetaRationalInflection
      norm_num))
    (hIoi thetaRationalTangentSwitch (by
      unfold thetaRationalTangentSwitch
      norm_num))
  let totalUpper : ℝ :=
    (thetaRationalAffinePrimitive (0 : ℝ) (720000 / 17247409 : ℝ)
          (9 / 200 : ℝ) -
        thetaRationalAffinePrimitive (0 : ℝ) (720000 / 17247409 : ℝ) 0) +
    (thetaRationalAffinePrimitive (-398959600 / 136616726689 : ℝ)
          (131120000000 / 1229550540201 : ℝ) (2 / 25 : ℝ) -
        thetaRationalAffinePrimitive (-398959600 / 136616726689 : ℝ)
          (131120000000 / 1229550540201 : ℝ) (9 / 200 : ℝ)) +
    (thetaRationalAffinePrimitive (-5294800 / 744471027 : ℝ)
          (118400000 / 744471027 : ℝ) (1 / 8 : ℝ) -
        thetaRationalAffinePrimitive (-5294800 / 744471027 : ℝ)
          (118400000 / 744471027 : ℝ) (2 / 25 : ℝ)) +
    (thetaRationalAffinePrimitive (-62959600 / 4627672729 : ℝ)
          (8787200000 / 41649054561 : ℝ) (9 / 50 : ℝ) -
        thetaRationalAffinePrimitive (-62959600 / 4627672729 : ℝ)
          (8787200000 / 41649054561 : ℝ) (1 / 8 : ℝ)) +
    (thetaRationalAffinePrimitive (-5024172400 / 220215271441 : ℝ)
          (519560000000 / 1981937442969 : ℝ) (13 / 50 : ℝ) -
        thetaRationalAffinePrimitive (-5024172400 / 220215271441 : ℝ)
          (519560000000 / 1981937442969 : ℝ) (9 / 50 : ℝ)) +
    (thetaRationalAffinePrimitive (-4534238800 / 133858140867 : ℝ)
          (40784000000 / 133858140867 : ℝ) (7 / 20 : ℝ) -
        thetaRationalAffinePrimitive (-4534238800 / 133858140867 : ℝ)
          (40784000000 / 133858140867 : ℝ) (13 / 50 : ℝ)) +
    (thetaRationalAffinePrimitive (-85846524400 / 2008991577321 : ℝ)
          (662944000000 / 2008991577321 : ℝ) (43 / 100 : ℝ) -
        thetaRationalAffinePrimitive (-85846524400 / 2008991577321 : ℝ)
          (662944000000 / 2008991577321 : ℝ) (7 / 20 : ℝ)) +
    (thetaRationalAffinePrimitive (-56226800 / 1141129233 : ℝ)
          (393920000 / 1141129233 : ℝ) thetaRationalInflection -
        thetaRationalAffinePrimitive (-56226800 / 1141129233 : ℝ)
          (393920000 / 1141129233 : ℝ) (43 / 100 : ℝ)) +
    (thetaRationalAffinePrimitive (-400 / 7803 : ℝ) (160 / 459 : ℝ)
          thetaRationalTangentSwitch -
        thetaRationalAffinePrimitive (-400 / 7803 : ℝ) (160 / 459 : ℝ)
          thetaRationalInflection) -
    thetaRationalAffinePrimitive (39600 / 753571 : ℝ)
      (192000 / 753571 : ℝ) thetaRationalTangentSwitch
  have htotal :
      (∫ y in Ioi (0 : ℝ), thetaRationalMomentMajorant y) ≤ totalUpper := by
    dsimp [totalUpper]
    linarith [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8,
      h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  let certifiedUpper : ℝ :=
    (720000000000 / 680860252703401 : ℝ) *
        Real.exp (-(6283 / 2000 : ℝ)) +
    (79791920000000000 / 48537846554972753889 : ℝ) *
        Real.exp (-(6283 / 2000 : ℝ) * (1 + 9 / 200 : ℝ)) +
    (672807065600000000000 / 506880731573580468862827 : ℝ) *
        Real.exp (-(6283 / 2000 : ℝ) * (1 + 2 / 25 : ℝ)) +
    (51408208000000000000 / 39069741227827439908827 : ℝ) *
        Real.exp (-(6283 / 2000 : ℝ) * (1 + 1 / 8 : ℝ)) +
    (39221940800000000000 / 30261160275537542460769 : ℝ) *
        Real.exp (-(6283 / 2000 : ℝ) * (1 + 9 / 50 : ℝ)) +
    (7568882936000000000000 / 7024857563613100811354667 : ℝ) *
        Real.exp (-(6283 / 2000 : ℝ) * (1 + 13 / 50 : ℝ)) +
    (25266236944000000000000 / 39411440484461117820381843 : ℝ) *
        Real.exp (-(6283 / 2000 : ℝ) * (1 + 7 / 20 : ℝ)) +
    (57731520000000000 / 149802357245751224297 : ℝ) *
        Real.exp (-(6283 / 2000 : ℝ) * (1 + 43 / 100 : ℝ)) +
    (11577760000000 / 135141957487229211 : ℝ) *
        Real.exp (-(6283 / 2000 : ℝ) * (1 + thetaRationalInflection)) -
    (32443360000000 / 13654348461492921 : ℝ) *
        Real.exp (-(6283 / 2000 : ℝ) * (1 + thetaRationalTangentSwitch))
  have haggregate : totalUpper = certifiedUpper := by
    dsimp [totalUpper, certifiedUpper]
    unfold thetaRationalAffinePrimitive thetaRationalInflection
      thetaRationalTangentSwitch
    norm_num
    <;> ring
  rw [haggregate] at htotal
  have hcertified : certifiedUpper < (254 / 1000000 : ℝ) := by
    dsimp [certifiedUpper]
    linarith [exp_neg_6283_div_2000_lt,
      exp_neg_thetaRationalKnot_one_lt,
      exp_neg_thetaRationalKnot_two_lt,
      exp_neg_thetaRationalKnot_three_lt,
      exp_neg_thetaRationalKnot_four_lt,
      exp_neg_thetaRationalKnot_five_lt,
      exp_neg_thetaRationalKnot_six_lt,
      exp_neg_thetaRationalKnot_seven_lt,
      exp_neg_thetaRationalInflection_lt,
      exp_neg_thetaRationalTangentSwitch_gt]
  exact htotal.trans_lt hcertified

/-- Certified upper bound for the quadratic theta-tail moment. -/
theorem completedNativeThetaTailMoment_two_lt :
    completedNativeThetaTailMoment 2 < (51 / 200000 : ℝ) := by
  have hfirst :
      (∫ u in Ioi (0 : ℝ), u ^ 2 * thetaFirstMode u) <
        (254 / 1000000 : ℝ) :=
    firstModeSecondMoment_le_rationalMajorant.trans_lt
      integral_thetaRationalMomentMajorant_lt
  have htail := completedNativeThetaTailMoment_two_le_firstMode
  nlinarith

/-- The concrete completed-Xi cosine kernel has strict sub-Gaussian
fourth moment: `μ₀ μ₄ < 3 μ₂²`. -/
theorem completedNativeXiCosineMoment_strict_kurtosis :
    completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 2 <
      3 * completedNativeXiCosineMoment 1 ^ 2 := by
  apply completedNativeXiCosineMoment_inequality_of_thetaTailMoment_two_lt
  have hzero := completedNativeThetaTailMoment_zero_gt
  have htwo := completedNativeThetaTailMoment_two_lt
  nlinarith [sq_nonneg
    (completedNativeThetaTailMoment 0 - (113 / 10000 : ℝ))]

end

end CarrySelfAdjointOperator
