import CarrySelfAdjointOperator.CompletedNativeThetaExponentialBounds
import CarrySelfAdjointOperator.CompletedNativeThetaRefinedTail

/-!
# High-precision node support for the tenth theta/Hankel gate

The eighth-order certificate deliberately used the convenient six-decimal
bounds on `π`.  That precision is adequate for its determinant, but not for
the strongly cancelling tenth-order numerator.  This module changes no
theta, xi, or native-moment definition: it exposes the same rational
exponential enclosure with the existing twenty-decimal bounds on `π` from
Mathlib, so that a separately generated order-ten certificate can use a
tighter node box.
-/

open Real Set Filter MeasureTheory

namespace CarrySelfAdjointOperator

noncomputable section

set_option autoImplicit false

/-- A high-precision counterpart of `thetaFirstMode_node_bounds`.

It has the same proof shape and the same rational exponential enclosures as
the eighth-order node lemma.  Only the certified enclosure for `π` is made
tighter; keeping it separate prevents any change to the existing order-eight
certificate footprint. -/
theorem thetaFirstMode_node_bounds_d20 (q el eu l r : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hel : 0 ≤ el) (_heu : 0 ≤ eu)
    (hinnerL : el ≤ thetaExpLower (2*q))
    (hinnerU : thetaExpUpper (2*q) ≤ eu)
    (hargL : 0 ≤ (314159265358979323846 / 100000000000000000000 : ℝ) * el - q / 2)
    (hargU :
      (314159265358979323847 / 100000000000000000000 : ℝ) * eu - q / 2 ≤ 32)
    (hl : 0 ≤ l) (hr : 0 ≤ r)
    (hlcert :
      l * thetaExpUpper
        ((314159265358979323847 / 100000000000000000000 : ℝ) * eu - q / 2) ≤ 2)
    (hrcert :
      2 ≤ r * thetaExpLower
        ((314159265358979323846 / 100000000000000000000 : ℝ) * el - q / 2)) :
    l ≤ thetaFirstMode q ∧ thetaFirstMode q ≤ r := by
  have hi := thetaExp_bounds (x := 2*q) (by positivity) (by linarith)
  have heL : el ≤ exp (2*q) := hinnerL.trans hi.1
  have heU : exp (2*q) ≤ eu := hi.2.trans hinnerU
  have hpiL : (314159265358979323846 / 100000000000000000000 : ℝ) ≤ Real.pi := by
    linarith [Real.pi_gt_d20]
  have hpiU : Real.pi ≤ (314159265358979323847 / 100000000000000000000 : ℝ) := by
    linarith [Real.pi_lt_d20]
  have hlo :
      (314159265358979323846 / 100000000000000000000 : ℝ) * el - q / 2 ≤
        Real.pi * exp (2*q) - q / 2 := by
    gcongr
  have hhi : Real.pi * exp (2*q) - q / 2 ≤
      (314159265358979323847 / 100000000000000000000 : ℝ) * eu - q / 2 := by
    gcongr
  have hlow := thetaExp_bounds hargL (hlo.trans hhi |>.trans hargU)
  have hupp := thetaExp_bounds (hargL.trans (hlo.trans hhi)) hargU
  have hEq : thetaFirstMode q = 2 / exp (Real.pi * exp (2*q) - q / 2) := by
    unfold thetaFirstMode
    rw [mul_assoc, ← exp_add]
    rw [show q / 2 + -Real.pi * exp (2*q) = -(Real.pi * exp (2*q) - q / 2) by ring,
      exp_neg]
    exact (div_eq_mul_inv _ _).symm
  rw [hEq]
  constructor
  · apply (le_div_iff₀ (exp_pos _)).2
    exact (mul_le_mul_of_nonneg_left
      ((exp_le_exp.mpr hhi).trans hupp.2) hl).trans hlcert
  · apply (div_le_iff₀ (exp_pos _)).2
    exact hrcert.trans (mul_le_mul_of_nonneg_left
      (hlow.1.trans (exp_le_exp.mpr hlo)) hr)

/-- A larger-range version of the rational exponential enclosure.  The second
theta mode reaches an exponent below `128` on the unit interval, whereas the
first-mode certificate only needs the smaller range `32`. -/
def thetaExpLower128 (x : ℝ) : ℝ :=
  (∑ i ∈ Finset.range 12, (x / 128) ^ i / i.factorial) ^ 128

/-- Upper companion to `thetaExpLower128`. -/
def thetaExpUpper128 (x : ℝ) : ℝ :=
  ((∑ i ∈ Finset.range 12, (x / 128) ^ i / i.factorial) +
    (x / 128) ^ 12 * 13 / (Nat.factorial 12 * 12)) ^ 128

theorem thetaExp128_bounds {x : ℝ} (hx : 0 ≤ x) (hx128 : x ≤ 128) :
    thetaExpLower128 x ≤ exp x ∧ exp x ≤ thetaExpUpper128 x := by
  have hy : 0 ≤ x / 128 := by positivity
  have hy1 : x / 128 ≤ 1 := by linarith
  have hl := Real.sum_le_exp_of_nonneg hy 12
  have hu := Real.exp_bound' hy hy1 (n := 12) (by norm_num)
  have hu' : exp (x / 128) ≤
      (∑ i ∈ Finset.range 12, (x / 128) ^ i / i.factorial) +
        (x / 128) ^ 12 * 13 / (Nat.factorial 12 * 12) := by
    convert hu using 1
    norm_num
  have he : exp x = (exp (x / 128)) ^ 128 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  constructor
  · apply pow_le_pow_left₀ _ hl
    exact Finset.sum_nonneg (fun i _ ↦ by positivity)
  · exact pow_le_pow_left₀ (Real.exp_nonneg _) hu' 128

/-- The explicitly retained second positive theta mode.  It is deliberately
kept separate from the geometric remainder so that the tenth-order box does
not inherit the coarse global factor used in the eighth gate. -/
def thetaSecondMode (u : ℝ) : ℝ :=
  2 * exp (u / 2) * exp (-4 * Real.pi * exp (2 * u))

theorem thetaSecondMode_eq_two_thetaTailMode_one (u : ℝ) :
    thetaSecondMode u = 2 * XiThetaCosine.thetaTailMode 1 u := by
  simp only [thetaSecondMode, XiThetaCosine.thetaTailMode]
  norm_num
  ring_nf

/-- Twenty-decimal node enclosure for the explicitly retained second theta
mode on `[0,1]`. -/
theorem thetaSecondMode_node_bounds_d20 (q el eu l r : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hel : 0 ≤ el) (_heu : 0 ≤ eu)
    (hinnerL : el ≤ thetaExpLower (2 * q))
    (hinnerU : thetaExpUpper (2 * q) ≤ eu)
    (hargL :
      0 ≤ 4 * (314159265358979323846 / 100000000000000000000 : ℝ) * el - q / 2)
    (hargU :
      4 * (314159265358979323847 / 100000000000000000000 : ℝ) * eu - q / 2 ≤ 128)
    (hl : 0 ≤ l) (hr : 0 ≤ r)
    (hlcert :
      l * thetaExpUpper128
        (4 * (314159265358979323847 / 100000000000000000000 : ℝ) * eu - q / 2) ≤ 2)
    (hrcert :
      2 ≤ r * thetaExpLower128
        (4 * (314159265358979323846 / 100000000000000000000 : ℝ) * el - q / 2)) :
    l ≤ thetaSecondMode q ∧ thetaSecondMode q ≤ r := by
  have hi := thetaExp_bounds (x := 2 * q) (by positivity) (by linarith)
  have heL : el ≤ exp (2 * q) := hinnerL.trans hi.1
  have heU : exp (2 * q) ≤ eu := hi.2.trans hinnerU
  have hpiL : (314159265358979323846 / 100000000000000000000 : ℝ) ≤ Real.pi := by
    linarith [Real.pi_gt_d20]
  have hpiU : Real.pi ≤ (314159265358979323847 / 100000000000000000000 : ℝ) := by
    linarith [Real.pi_lt_d20]
  have hlo :
      4 * (314159265358979323846 / 100000000000000000000 : ℝ) * el - q / 2 ≤
        4 * Real.pi * exp (2 * q) - q / 2 := by
    gcongr
  have hhi : 4 * Real.pi * exp (2 * q) - q / 2 ≤
      4 * (314159265358979323847 / 100000000000000000000 : ℝ) * eu - q / 2 := by
    gcongr
  have hlow := thetaExp128_bounds hargL (hlo.trans hhi |>.trans hargU)
  have hupp := thetaExp128_bounds (hargL.trans (hlo.trans hhi)) hargU
  have hEq : thetaSecondMode q = 2 / exp (4 * Real.pi * exp (2 * q) - q / 2) := by
    unfold thetaSecondMode
    rw [mul_assoc, ← exp_add]
    rw [show q / 2 + -4 * Real.pi * exp (2 * q) =
      -(4 * Real.pi * exp (2 * q) - q / 2) by ring, exp_neg]
    exact (div_eq_mul_inv _ _).symm
  rw [hEq]
  constructor
  · apply (le_div_iff₀ (exp_pos _)).2
    exact (mul_le_mul_of_nonneg_left
      ((exp_le_exp.mpr hhi).trans hupp.2) hl).trans hlcert
  · apply (div_le_iff₀ (exp_pos _)).2
    exact hrcert.trans (mul_le_mul_of_nonneg_left
      (hlow.1.trans (exp_le_exp.mpr hlo)) hr)

/-- Retaining the first two positive theta modes is an exact lower
decomposition of the full positive tail. -/
theorem thetaFirstMode_add_secondMode_le_thetaTail {u : ℝ} (_hu : 0 ≤ u) :
    thetaFirstMode u + thetaSecondMode u ≤ XiThetaCosine.thetaTail u := by
  rw [XiThetaCosine.thetaTail_eq_two_mul_tsum]
  have hf := XiThetaCosine.summable_thetaTailMode u
  have hs0 := hf.tsum_eq_add_tsum_ite 0
  have hg : Summable (fun n : ℕ =>
      if n = 0 then 0 else XiThetaCosine.thetaTailMode n u) := by
    simpa only [show (fun n : ℕ => if n = 0 then 0 else
        XiThetaCosine.thetaTailMode n u) =
        Function.update (fun n : ℕ => XiThetaCosine.thetaTailMode n u) 0 0 by
          funext n
          by_cases hn : n = 0 <;> simp [hn]] using hf.update 0 0
  have hs1 := hg.tsum_eq_add_tsum_ite 1
  rw [hs0, hs1]
  simp only [if_false, Nat.one_ne_zero]
  unfold thetaFirstMode thetaSecondMode XiThetaCosine.thetaTailMode
  have hR : 0 ≤ ∑' (n : ℕ), if n = 1 then 0 else if n = 0 then 0 else
      Real.exp (u / 2) * Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (2 * u)) := by
    exact tsum_nonneg (fun n ↦ by positivity)
  have hR2 : 0 ≤ 2 * ∑' (n : ℕ), if n = 1 then 0 else if n = 0 then 0 else
      Real.exp (u / 2) * Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (2 * u)) := mul_nonneg (by norm_num) hR
  have hsum_eq :
      (∑' (n : ℕ), if n = 1 then 0 else if n = 0 then 0 else
        Real.exp (u / 2) * Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2) *
          Real.exp (2 * u))) =
      (∑' (n : ℕ), if n = 1 then 0 else if n = 0 then 0 else
        Real.exp (u * (1 / 2)) * Real.exp
          (-(Real.pi * Real.exp (u * 2) * (((1 + n : ℕ) : ℝ) ^ 2)))) := by
    apply tsum_congr
    intro n
    by_cases h1 : n = 1 <;> by_cases h0 : n = 0
    all_goals simp [h1, h0]
    all_goals congr 2 <;> congr 1 <;> ring
  rw [hsum_eq] at hR2
  ring_nf at hR2 ⊢
  nlinarith only [hR2]

/-- The geometric estimate is reserved for the modes starting at index two;
the first and second modes are kept exact. -/
theorem thetaTail_le_first_add_secondMode_plus_remainder {u : ℝ} (hu : 0 ≤ u) :
    XiThetaCosine.thetaTail u ≤ thetaFirstMode u + thetaSecondMode u +
      (1 / (12300 * 12299 : ℝ)) * thetaFirstMode u := by
  rw [XiThetaCosine.thetaTail_eq_two_mul_tsum]
  have hf := XiThetaCosine.summable_thetaTailMode u
  have hs0 := hf.tsum_eq_add_tsum_ite 0
  have hg : Summable (fun n : ℕ =>
      if n = 0 then 0 else XiThetaCosine.thetaTailMode n u) := by
    simpa only [show (fun n : ℕ => if n = 0 then 0 else
        XiThetaCosine.thetaTailMode n u) =
        Function.update (fun n : ℕ => XiThetaCosine.thetaTailMode n u) 0 0 by
          funext n
          by_cases hn : n = 0 <;> simp [hn]] using hf.update 0 0
  have hs1 := hg.tsum_eq_add_tsum_ite 1
  have hrem : Summable (fun n : ℕ =>
      if n = 1 then 0 else if n = 0 then 0 else
        XiThetaCosine.thetaTailMode n u) := by
    simpa only [show (fun n : ℕ => if n = 1 then 0 else if n = 0 then 0 else
        XiThetaCosine.thetaTailMode n u) = Function.update
          (fun n : ℕ => if n = 0 then 0 else XiThetaCosine.thetaTailMode n u) 1 0 by
            funext n
            by_cases h1 : n = 1 <;> by_cases h0 : n = 0 <;> simp [h1, h0]] using
      hg.update 1 0
  have hgeom : Summable (fun n : ℕ =>
      if n = 1 then 0 else if n = 0 then 0 else
        XiThetaCosine.thetaTailMode 0 u * (1 / 12300 : ℝ) ^ n) := by
    have hgeo : Summable (fun n : ℕ =>
        XiThetaCosine.thetaTailMode 0 u * (1 / 12300 : ℝ) ^ n) :=
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 12300)
        (by norm_num : (1 / 12300 : ℝ) < 1)).mul_left
        (XiThetaCosine.thetaTailMode 0 u)
    have hgeo0 : Summable (fun n : ℕ => if n = 0 then 0 else
        XiThetaCosine.thetaTailMode 0 u * (1 / 12300 : ℝ) ^ n) := by
      simpa only [show (fun n : ℕ => if n = 0 then 0 else
          XiThetaCosine.thetaTailMode 0 u * (1 / 12300 : ℝ) ^ n) =
          Function.update (fun n : ℕ => XiThetaCosine.thetaTailMode 0 u *
            (1 / 12300 : ℝ) ^ n) 0 0 by
            funext n
            by_cases hn : n = 0 <;> simp [hn]] using hgeo.update 0 0
    simpa only [show (fun n : ℕ => if n = 1 then 0 else if n = 0 then 0 else
        XiThetaCosine.thetaTailMode 0 u * (1 / 12300 : ℝ) ^ n) = Function.update
          (fun n : ℕ => if n = 0 then 0 else XiThetaCosine.thetaTailMode 0 u *
            (1 / 12300 : ℝ) ^ n) 1 0 by
          funext n
          by_cases h1 : n = 1 <;> by_cases h0 : n = 0 <;> simp [h1, h0]] using
      hgeo0.update 1 0
  have hsum := hrem.tsum_le_tsum (fun n ↦ by
    by_cases h1 : n = 1
    · simp [h1]
    · by_cases h0 : n = 0
      · simp [h0]
      · simpa [h1, h0] using thetaTailMode_le_geometric_refined hu n) hgeom
  rw [hs0, hs1]
  simp only [if_false, Nat.one_ne_zero]
  have hgeom_sum :
      (∑' (n : ℕ), if n = 1 then 0 else if n = 0 then 0 else
        XiThetaCosine.thetaTailMode 0 u * (1 / 12300 : ℝ) ^ n) =
      XiThetaCosine.thetaTailMode 0 u *
        ((1 / 12300 : ℝ) ^ 2 / (1 - (1 / 12300 : ℝ))) := by
    have hgeomPow : Summable (fun n : ℕ => (1 / 12300 : ℝ) ^ n) :=
      summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 12300)
        (by norm_num : (1 / 12300 : ℝ) < 1)
    have hpow := tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 12300)
      (by norm_num : (1 / 12300 : ℝ) < 1)
    have hpow0 : (1 / 12300 : ℝ) ^ 0 = 1 := by norm_num
    have hpow1 : (1 / 12300 : ℝ) ^ 1 = 1 / 12300 := by norm_num
    have hite : (∑' (n : ℕ), if n = 1 then 0 else if n = 0 then 0 else
        (1 / 12300 : ℝ) ^ n) =
        (1 / (1 - (1 / 12300 : ℝ))) - 1 - 1 / 12300 := by
      rw [show (fun n : ℕ => if n = 1 then 0 else if n = 0 then 0 else
          (1 / 12300 : ℝ) ^ n) =
          (fun n : ℕ => (1 / 12300 : ℝ) ^ n -
            (if n = 0 then (1 : ℝ) else 0) -
            (if n = 1 then (1 / 12300 : ℝ) else 0)) by
          funext n
          by_cases h1 : n = 1 <;> by_cases h0 : n = 0 <;> simp [h1, h0]]
      have hone : Summable (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) :=
        (hasSum_ite_eq 0 (1 : ℝ)).summable
      have htwo : Summable (fun n : ℕ =>
          if n = 1 then (1 / 12300 : ℝ) else 0) :=
        (hasSum_ite_eq 1 (1 / 12300 : ℝ)).summable
      calc
        (∑' (n : ℕ), (((1 / 12300 : ℝ) ^ n -
            (if n = 0 then (1 : ℝ) else 0)) -
              (if n = 1 then (1 / 12300 : ℝ) else 0))) =
            (∑' (n : ℕ), ((1 / 12300 : ℝ) ^ n -
              (if n = 0 then (1 : ℝ) else 0))) -
              ∑' (n : ℕ), if n = 1 then (1 / 12300 : ℝ) else 0 :=
          (hgeomPow.sub hone).tsum_sub htwo
        _ = ((∑' (n : ℕ), (1 / 12300 : ℝ) ^ n) -
              ∑' (n : ℕ), if n = 0 then (1 : ℝ) else 0) -
              ∑' (n : ℕ), if n = 1 then (1 / 12300 : ℝ) else 0 := by
          rw [hgeomPow.tsum_sub hone]
        _ = (1 / (1 - (1 / 12300 : ℝ))) - 1 - 1 / 12300 := by
          rw [hpow, (hasSum_ite_eq 0 (1 : ℝ)).tsum_eq,
            (hasSum_ite_eq 1 (1 / 12300 : ℝ)).tsum_eq]
          norm_num
    have hsum_factor :
        (∑' (n : ℕ), if n = 1 then 0 else if n = 0 then 0 else
          XiThetaCosine.thetaTailMode 0 u * (1 / 12300 : ℝ) ^ n) =
        XiThetaCosine.thetaTailMode 0 u *
          (∑' (n : ℕ), if n = 1 then 0 else if n = 0 then 0 else
            (1 / 12300 : ℝ) ^ n) := by
      calc
        (∑' (n : ℕ), if n = 1 then 0 else if n = 0 then 0 else
            XiThetaCosine.thetaTailMode 0 u * (1 / 12300 : ℝ) ^ n) =
            ∑' (n : ℕ), XiThetaCosine.thetaTailMode 0 u *
              (if n = 1 then 0 else if n = 0 then 0 else
                (1 / 12300 : ℝ) ^ n) := by
          apply tsum_congr
          intro n
          by_cases h1 : n = 1 <;> by_cases h0 : n = 0 <;> simp [h1, h0]
        _ = XiThetaCosine.thetaTailMode 0 u *
            (∑' (n : ℕ), if n = 1 then 0 else if n = 0 then 0 else
              (1 / 12300 : ℝ) ^ n) := tsum_mul_left
    rw [hsum_factor, hite]
    ring
  rw [hgeom_sum] at hsum
  have hfactor :
      2 * XiThetaCosine.thetaTailMode 0 u *
          ((1 / 12300 : ℝ) ^ 2 / (1 - (1 / 12300 : ℝ))) =
        (1 / (12300 * 12299 : ℝ)) * thetaFirstMode u := by
    unfold thetaFirstMode XiThetaCosine.thetaTailMode
    norm_num
    ring
  have hsum2 : 2 *
      (∑' (i : ℕ), if i = 1 then 0 else if i = 0 then 0 else
        XiThetaCosine.thetaTailMode i u) ≤
      2 * XiThetaCosine.thetaTailMode 0 u *
        ((1 / 12300 : ℝ) ^ 2 / (1 - (1 / 12300 : ℝ))) := by
    nlinarith only [hsum]
  rw [hfactor] at hsum2
  have hfirst : thetaFirstMode u = 2 * XiThetaCosine.thetaTailMode 0 u := by
    unfold thetaFirstMode XiThetaCosine.thetaTailMode
    ring
  have hsecond : thetaSecondMode u =
      2 * XiThetaCosine.thetaTailMode 1 u :=
    thetaSecondMode_eq_two_thetaTailMode_one u
  rw [hfirst] at hsum2
  rw [hfirst, hsecond]
  nlinarith only [hsum2]

private theorem exp_neg_twenty_le_21_div_ten_billion :
    exp (-20) ≤ (21 / 10000000000 : ℝ) := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 20) 32
  rw [exp_neg]
  apply (inv_le_iff_one_le_mul₀ (exp_pos 20)).2
  have hf : (1 : ℝ) ≤ (21 / 10000000000) *
      ∑ i ∈ Finset.range 32, (20 : ℝ)^i / i.factorial := by
    norm_num [Finset.sum_range_succ]
  exact hf.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

theorem thetaFirstMode_weighted_tail_pointwise_ten (p : ℕ) (hp : p ≤ 10)
    {u : ℝ} (hu : 1 ≤ u) :
    u^p*thetaFirstMode u ≤ (2*exp (-10))*exp (-10*u) := by
  have hp10 : u^p ≤ u^10 := pow_le_pow_right₀ hu hp
  have hb : u ≤ exp (u-1) := by linarith [Real.add_one_le_exp (u-1)]
  have he : u^p ≤ exp (10*(u-1)) := by
    calc
      u^p ≤ u^10 := hp10
      _ ≤ (exp (u-1))^10 := pow_le_pow_left₀ (by linarith) hb 10
      _ = exp (10*(u-1)) := by simpa using (Real.exp_nat_mul (u-1) 10).symm
  calc
    u^p*thetaFirstMode u ≤ exp (10*(u-1))*(2*exp (-20*u)) :=
      mul_le_mul he (thetaFirstMode_le_exp_tail hu)
        (by unfold thetaFirstMode; positivity) (exp_nonneg _)
    _ = (2*exp (-10))*exp (-10*u) := by
      rw [mul_comm (exp (10*(u-1))), mul_assoc, ← exp_add, mul_assoc, ← exp_add]
      congr 2
      ring_nf

theorem integral_thetaFirstMode_weighted_tail_le_ten (p : ℕ) (hp : p ≤ 10) :
    (∫ u in Ioi (1:ℝ), u^p*thetaFirstMode u) ≤ (1/2000000000:ℝ) := by
  have hi : IntegrableOn (fun u : ℝ ↦ u^p*thetaFirstMode u) (Ioi 1) :=
    (integrableOn_pow_mul_thetaFirstMode p).mono_set (Ioi_subset_Ioi (by norm_num))
  have h := integral_mono_ae hi
    ((integrableOn_exp_mul_Ioi (by norm_num : (-10:ℝ)<0) 1).const_mul (2*exp (-10)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact thetaFirstMode_weighted_tail_pointwise_ten p hp hu.le)
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-10:ℝ)<0) 1] at h
  have he : (2*exp (-10))*(-exp ((-10:ℝ)*1)/(-10)) = exp (-20)/5 := by
    norm_num
    rw [← mul_div_assoc, mul_assoc, ← exp_add]
    norm_num
    ring_nf
  rw [he] at h
  nlinarith [exp_neg_twenty_le_21_div_ten_billion]

theorem completedNativeThetaTailMoment_finite_upper_refined_ten (p : ℕ) (hp : p ≤ 10) :
    completedNativeThetaTailMoment p ≤ (12300/12299:ℝ)*
      ((∫ u in (0:ℝ)..1, u^p*thetaFirstMode u)+1/2000000000) := by
  have hi := integrableOn_pow_mul_thetaFirstMode p
  have hit := hi.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi hit
  have htail := integral_thetaFirstMode_weighted_tail_le_ten p hp
  have hmono := integral_mono_ae (integrableOn_pow_mul_thetaTail p)
    (hi.const_mul (12300/12299:ℝ)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have h := mul_le_mul_of_nonneg_left (thetaTail_le_geometric_first_refined hu.le)
        (pow_nonneg hu.le p)
      simpa only [mul_assoc, mul_left_comm] using h)
  rw [integral_const_mul] at hmono
  unfold completedNativeThetaTailMoment
  linarith

private theorem exp_two_ge_733_div_100 :
    (733 / 100 : ℝ) ≤ exp 2 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 7
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem thetaFirstMode_le_exp_tail_sharp {u : ℝ} (hu : 1 ≤ u) :
    thetaFirstMode u ≤ 2 * exp (23 - (91 / 2 : ℝ) * u) := by
  have hshift : 2 * u - 1 ≤ exp (2 * (u - 1)) := by
    have h := Real.add_one_le_exp (2 * (u - 1))
    linarith
  have hpi2 : (23 : ℝ) ≤ Real.pi * exp 2 := by
    have hpi : (3141592 / 1000000 : ℝ) ≤ Real.pi := by
      linarith [Real.pi_gt_d6]
    have hp := mul_le_mul hpi exp_two_ge_733_div_100
      (by norm_num : (0 : ℝ) ≤ 733 / 100) Real.pi_pos.le
    nlinarith
  have hsplit : Real.pi * exp (2 * u) =
      (Real.pi * exp 2) * exp (2 * (u - 1)) := by
    rw [show 2 * u = 2 + 2 * (u - 1) by ring, Real.exp_add]
    ring
  have hprod : 23 * (2 * u - 1) ≤ Real.pi * exp (2 * u) := by
    calc
      23 * (2 * u - 1) ≤ (Real.pi * exp 2) * (2 * u - 1) := by
        exact mul_le_mul_of_nonneg_right hpi2 (by linarith)
      _ ≤ (Real.pi * exp 2) * exp (2 * (u - 1)) := by
        exact mul_le_mul_of_nonneg_left hshift (by positivity)
      _ = Real.pi * exp (2 * u) := hsplit.symm
  unfold thetaFirstMode
  rw [mul_assoc, ← exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
  linarith

private theorem exp_neg_45_div_2_le_17_div_100_billion :
    exp (-(45 / 2 : ℝ)) ≤ (17 / 100000000000 : ℝ) := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 45 / 2) 38
  rw [exp_neg]
  apply (inv_le_iff_one_le_mul₀ (exp_pos (45 / 2 : ℝ))).2
  have hf : (1 : ℝ) ≤ (17 / 100000000000) *
      ∑ i ∈ Finset.range 38, (45 / 2 : ℝ)^i / i.factorial := by
    norm_num [Finset.sum_range_succ]
  exact hf.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

theorem thetaFirstMode_weighted_tail_pointwise_ten_sharp
    (p : ℕ) (hp : p ≤ 10) {u : ℝ} (hu : 1 ≤ u) :
    u^p*thetaFirstMode u ≤ 2*exp 13*exp (-(71 / 2 : ℝ) * u) := by
  have hp10 : u^p ≤ u^10 := pow_le_pow_right₀ hu hp
  have hb : u ≤ exp (u-1) := by linarith [Real.add_one_le_exp (u-1)]
  have he : u^p ≤ exp (10*(u-1)) := by
    calc
      u^p ≤ u^10 := hp10
      _ ≤ (exp (u-1))^10 := pow_le_pow_left₀ (by linarith) hb 10
      _ = exp (10*(u-1)) := by simpa using (Real.exp_nat_mul (u-1) 10).symm
  calc
    u^p*thetaFirstMode u ≤ exp (10*(u-1)) *
        (2 * exp (23 - (91 / 2 : ℝ) * u)) :=
      mul_le_mul he (thetaFirstMode_le_exp_tail_sharp hu)
        (by unfold thetaFirstMode; positivity) (exp_nonneg _)
    _ = 2*exp 13*exp (-(71 / 2 : ℝ) * u) := by
      calc
        exp (10*(u-1)) * (2 * exp (23 - (91 / 2 : ℝ) * u)) =
            2 * (exp (10*(u-1)) * exp (23 - (91 / 2 : ℝ) * u)) := by ring
        _ = 2 * exp (10*(u-1) + (23 - (91 / 2 : ℝ) * u)) := by
          rw [← Real.exp_add]
        _ = 2*exp 13*exp (-(71 / 2 : ℝ) * u) := by
          rw [show 10*(u-1) + (23 - (91 / 2 : ℝ) * u) =
            13 + (-(71 / 2 : ℝ) * u) by ring, Real.exp_add]
          ring

theorem integral_thetaFirstMode_weighted_tail_le_ten_sharp
    (p : ℕ) (hp : p ≤ 10) :
    (∫ u in Ioi (1:ℝ), u^p*thetaFirstMode u) ≤ (1/100000000000:ℝ) := by
  have hi : IntegrableOn (fun u : ℝ ↦ u^p*thetaFirstMode u) (Ioi 1) :=
    (integrableOn_pow_mul_thetaFirstMode p).mono_set (Ioi_subset_Ioi (by norm_num))
  have h := integral_mono_ae hi
    ((integrableOn_exp_mul_Ioi (by norm_num : (-(71 / 2 : ℝ))<0) 1).const_mul (2*exp 13))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact thetaFirstMode_weighted_tail_pointwise_ten_sharp p hp hu.le)
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-(71 / 2 : ℝ))<0) 1] at h
  have he : (2*exp 13)*(-exp ((-(71 / 2 : ℝ))*1)/(-(71 / 2 : ℝ))) =
      (4 / 71 : ℝ) * exp (-(45 / 2 : ℝ)) := by
    norm_num
    rw [← mul_div_assoc, mul_assoc, ← exp_add]
    norm_num
    ring_nf
  rw [he] at h
  nlinarith [exp_neg_45_div_2_le_17_div_100_billion]

/- The second positive mode is retained explicitly on the compact part of
the logarithmic half-line.  This is the support lemma needed by the order-ten
screen: the geometric estimate is used only for the residual modes and for
the exterior tail. -/
theorem thetaSecondMode_le_thetaTail {u : ℝ} (_hu : 0 ≤ u) :
    thetaSecondMode u ≤ XiThetaCosine.thetaTail u := by
  rw [thetaSecondMode_eq_two_thetaTailMode_one,
    XiThetaCosine.thetaTail_eq_two_mul_tsum]
  have hf := XiThetaCosine.summable_thetaTailMode u
  have hmode : XiThetaCosine.thetaTailMode 1 u ≤
      ∑' n : ℕ, XiThetaCosine.thetaTailMode n u :=
    hf.le_tsum 1 (fun n _hn ↦ by
      unfold XiThetaCosine.thetaTailMode
      positivity)
  exact mul_le_mul_of_nonneg_left hmode (by norm_num)

theorem integrableOn_pow_mul_thetaSecondMode (p : ℕ) :
    IntegrableOn (fun u : ℝ ↦ u^p*thetaSecondMode u) (Ioi (0:ℝ)) := by
  apply (integrableOn_pow_mul_thetaTail p).mono'
  · exact (by unfold thetaSecondMode; fun_prop :
      Continuous (fun u : ℝ ↦ u^p*thetaSecondMode u)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hnonneg : 0 ≤ thetaSecondMode u := by
      unfold thetaSecondMode
      exact mul_nonneg (mul_nonneg (by norm_num) (exp_pos _).le) (exp_pos _).le
    have hprod : 0 ≤ u^p * thetaSecondMode u :=
      mul_nonneg (pow_nonneg hu.le p) hnonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hprod]
    exact mul_le_mul_of_nonneg_left (thetaSecondMode_le_thetaTail hu.le)
      (pow_nonneg hu.le p)

/- A two-mode upper enclosure for every moment needed by the tenth-order
Hankel numerator.  It keeps the first and second modes exact on `[0,1]` and
uses the sharp certified exterior estimate on `(1,∞)`. -/
theorem completedNativeThetaTailMoment_finite_upper_refined_two_mode
    (p : ℕ) (hp : p ≤ 10) :
    completedNativeThetaTailMoment p ≤
      (∫ u in (0:ℝ)..1, u^p*thetaFirstMode u) +
        (∫ u in (0:ℝ)..1, u^p*thetaSecondMode u) +
        (1 / (12300 * 12299 : ℝ)) *
          (∫ u in (0:ℝ)..1, u^p*thetaFirstMode u) +
        (12300 / 12299 : ℝ) * (1 / 100000000000 : ℝ) := by
  have hiTail := integrableOn_pow_mul_thetaTail p
  have hiFirst := integrableOn_pow_mul_thetaFirstMode p
  have hiSecond := integrableOn_pow_mul_thetaSecondMode p
  have hcontTail : Continuous XiThetaCosine.thetaTail := by
    exact continuous_iff_continuousAt.2 (fun u ↦
      (XiThetaCosine.hasDerivAt_thetaTail u).continuousAt)
  have hcontFirst : Continuous thetaFirstMode := by
    unfold thetaFirstMode
    fun_prop
  have hcontSecond : Continuous thetaSecondMode := by
    unfold thetaSecondMode
    fun_prop
  have hcontPower : Continuous (fun u : ℝ ↦ u^p) := by
    fun_prop
  have hcontRemainder : Continuous (fun u : ℝ ↦
      (1 / (12300 * 12299 : ℝ)) * thetaFirstMode u) :=
    hcontFirst.const_mul _
  have hcontUpper : Continuous (fun u : ℝ ↦
      thetaFirstMode u + thetaSecondMode u +
        (1 / (12300 * 12299 : ℝ)) * thetaFirstMode u) :=
    (hcontFirst.add hcontSecond).add hcontRemainder
  have hinner :
      (∫ u in (0:ℝ)..1, u^p*XiThetaCosine.thetaTail u) ≤
        (∫ u in (0:ℝ)..1, u^p*thetaFirstMode u) +
          (∫ u in (0:ℝ)..1, u^p*thetaSecondMode u) +
          (1 / (12300 * 12299 : ℝ)) *
            (∫ u in (0:ℝ)..1, u^p*thetaFirstMode u) := by
    have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      ((hcontPower.mul hcontTail).intervalIntegrable (μ := volume) 0 1)
      ((hcontPower.mul hcontUpper).intervalIntegrable (μ := volume) 0 1)
      (fun u hu ↦ by
        have hu0 : 0 ≤ u := hu.1
        have h := thetaTail_le_first_add_secondMode_plus_remainder hu0
        have hp0 : 0 ≤ u^p := pow_nonneg hu0 p
        have h' := mul_le_mul_of_nonneg_left h hp0
        simpa [mul_add, mul_assoc, mul_left_comm, add_assoc] using h')
    have hif : IntervalIntegrable (fun u : ℝ ↦ u^p*thetaFirstMode u)
        volume 0 1 := by
      convert (hcontPower.mul hcontFirst).intervalIntegrable (μ := volume) 0 1 using 1
      ext u
      simp only [Pi.mul_apply]
    have his : IntervalIntegrable (fun u : ℝ ↦ u^p*thetaSecondMode u)
        volume 0 1 := by
      convert (hcontPower.mul hcontSecond).intervalIntegrable (μ := volume) 0 1 using 1
      ext u
      simp only [Pi.mul_apply]
    have hic : IntervalIntegrable (fun u : ℝ ↦
        (1 / (12300 * 12299 : ℝ)) * (u^p*thetaFirstMode u)) volume 0 1 :=
      hif.const_mul _
    have h' :
        (∫ u in (0:ℝ)..1, u^p*XiThetaCosine.thetaTail u) ≤
          ∫ u in (0:ℝ)..1, u^p * (thetaFirstMode u + thetaSecondMode u +
            (1 / (12300 * 12299 : ℝ)) * thetaFirstMode u) := by
      simpa only [Pi.mul_apply] using h
    rw [show (fun u : ℝ ↦
        u^p * (thetaFirstMode u + thetaSecondMode u +
          (1 / (12300 * 12299 : ℝ)) * thetaFirstMode u)) =
        (fun u : ℝ ↦ u^p*thetaFirstMode u + u^p*thetaSecondMode u +
          (1 / (12300 * 12299 : ℝ)) * (u^p*thetaFirstMode u)) by
          funext u; ring] at h'
    rw [intervalIntegral.integral_add (hif.add his) hic,
      intervalIntegral.integral_add hif his,
      intervalIntegral.integral_const_mul] at h'
    simpa [mul_add, mul_assoc, mul_left_comm, add_assoc] using h'
  have hsplit := intervalIntegral.integral_interval_add_Ioi hiTail
    (hiTail.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1)))
  have hiTailOuter := hiTail.mono_set
    (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have hiFirstOuter := hiFirst.mono_set
    (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have houter := integral_mono_ae hiTailOuter
    (hiFirstOuter.const_mul (12300 / 12299 : ℝ))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 ≤ u := le_trans (by norm_num) hu.le
      have h := mul_le_mul_of_nonneg_left
        (thetaTail_le_geometric_first_refined hu0) (pow_nonneg hu0 p)
      simpa only [mul_assoc, mul_left_comm] using h)
  rw [integral_const_mul] at houter
  have htail := integral_thetaFirstMode_weighted_tail_le_ten_sharp p hp
  unfold completedNativeThetaTailMoment
  linarith

end

end CarrySelfAdjointOperator
