import CarrySelfAdjointOperator.CompletedNativeXiThetaMomentBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Rational exponential bounds for the existing first theta mode

Convexity supplies weighted cell bounds. The other theta modes retain their
previous geometric majorant. All numerical certificates below are rational
inequalities checked by the kernel.
-/

open Real Set Filter MeasureTheory

namespace CarrySelfAdjointOperator

noncomputable section
set_option autoImplicit false

def thetaExpLower (x : ℝ) : ℝ :=
  (∑ i ∈ Finset.range 12, (x/32)^i / i.factorial)^32

def thetaExpUpper (x : ℝ) : ℝ :=
  ((∑ i ∈ Finset.range 12, (x/32)^i / i.factorial) +
    (x/32)^12*13/(Nat.factorial 12*12))^32

theorem thetaExp_bounds {x : ℝ} (hx : 0 ≤ x) (hx32 : x ≤ 32) :
    thetaExpLower x ≤ exp x ∧ exp x ≤ thetaExpUpper x := by
  have hy : 0 ≤ x/32 := by positivity
  have hy1 : x/32 ≤ 1 := by linarith
  have hl := Real.sum_le_exp_of_nonneg hy 12
  have hu := Real.exp_bound' hy hy1 (n := 12) (by norm_num)
  have hu' : exp (x/32) ≤
      (∑ i ∈ Finset.range 12, (x/32)^i / i.factorial) +
        (x/32)^12*13/(Nat.factorial 12*12) := by
    convert hu using 1
    norm_num
  have he : exp x = (exp (x/32))^32 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  constructor
  · apply pow_le_pow_left₀ _ hl
    exact Finset.sum_nonneg (fun i _ ↦ by positivity)
  · exact pow_le_pow_left₀ (Real.exp_nonneg _) hu' 32

/-- A node enclosure whose inputs are exclusively rational inequalities.
The bounds on Real.pi are existing mathlib theorems. -/
theorem thetaFirstMode_node_bounds (q el eu l r : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hel : 0 ≤ el) (_heu : 0 ≤ eu)
    (hinnerL : el ≤ thetaExpLower (2*q))
    (hinnerU : thetaExpUpper (2*q) ≤ eu)
    (hargL : 0 ≤ (3141592/1000000 : ℝ)*el-q/2)
    (hargU : (3141593/1000000 : ℝ)*eu-q/2 ≤ 32)
    (hl : 0 ≤ l) (hr : 0 ≤ r)
    (hlcert : l * thetaExpUpper ((3141593/1000000 : ℝ)*eu-q/2) ≤ 2)
    (hrcert : 2 ≤ r * thetaExpLower ((3141592/1000000 : ℝ)*el-q/2)) :
    l ≤ thetaFirstMode q ∧ thetaFirstMode q ≤ r := by
  have hi := thetaExp_bounds (x := 2*q) (by positivity) (by linarith)
  have heL : el ≤ exp (2*q) := hinnerL.trans hi.1
  have heU : exp (2*q) ≤ eu := hi.2.trans hinnerU
  have hpiL : (3141592/1000000 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d6]
  have hpiU : Real.pi ≤ (3141593/1000000 : ℝ) := by linarith [Real.pi_lt_d6]
  have hlo : (3141592/1000000 : ℝ)*el-q/2 ≤ Real.pi*exp (2*q)-q/2 := by
    gcongr
  have hhi : Real.pi*exp (2*q)-q/2 ≤ (3141593/1000000 : ℝ)*eu-q/2 := by
    gcongr
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
    exact (mul_le_mul_of_nonneg_left
      ((exp_le_exp.mpr hhi).trans hupp.2) hl).trans hlcert
  · apply (div_le_iff₀ (exp_pos _)).2
    exact hrcert.trans (mul_le_mul_of_nonneg_left
      (hlow.1.trans (exp_le_exp.mpr hlo)) hr)

end
end CarrySelfAdjointOperator
