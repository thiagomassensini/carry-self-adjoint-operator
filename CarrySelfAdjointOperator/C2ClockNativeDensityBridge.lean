import CarrySelfAdjointOperator.C2ClockAllOrderDerivative
import CarrySelfAdjointOperator.C2MellinInfiniteLimit
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The common clock density in the original C2 cells

The two summands are the common clock and its dyadic translate before
the camera factor is divided out.
-/

namespace CarrySelfAdjointOperator

open Set MeasureTheory

theorem nativeC2MellinGeometricDensity_eq_clock_add_dyadic {x : ℝ}
    (hx : 0 < x) :
    nativeC2MellinGeometricDensity x = c2ClockDensity x + c2ClockDensity (2 * x) := by
  let q := Real.exp (-x)
  have hq : 0 < q := Real.exp_pos _
  have he₁ : Real.exp x = q⁻¹ := by simp [q, Real.exp_neg]
  have he₂ : Real.exp (2 * x) = (q ^ 2)⁻¹ := by
    rw [show 2 * x = x + x by ring, Real.exp_add, he₁, pow_two, mul_inv]
  have h₁ : 1 + q ≠ 0 := by positivity
  have h₂ : 1 + q ^ 2 ≠ 0 := by positivity
  unfold nativeC2MellinGeometricDensity c2ClockDensity
  rw [nativeC2MellinGeometricOmega0_eq_q_form hx, he₁, he₂]
  change q + q ^ 3 * (1 - q) / ((1 + q) * (1 + q ^ 2)) =
    (1 + q⁻¹)⁻¹ + (1 + (q ^ 2)⁻¹)⁻¹
  rw [show 1 + q⁻¹ = (1 + q) / q by field_simp [hq.ne']; ring,
    show 1 + (q ^ 2)⁻¹ = (1 + q ^ 2) / q ^ 2 by
      field_simp [hq.ne']; ring]
  rw [inv_div, inv_div]
  field_simp [h₁, h₂]
  ring

/-- The shifted density contributes exactly the dyadic camera multiplier. -/
theorem nativeC2MellinGeometricIntegral_eq_clock_mul {s : ℝ}
    (hs : s ∈ Ioo (3 / 8 : ℝ) (5 / 8)) :
    (∫ x in Ioi (0 : ℝ), x ^ (s - 1) * nativeC2MellinGeometricDensity x) =
      (1 + (2 : ℝ) ^ (-s)) * c2ClockLogMoment 0 s := by
  let v := c2ClockLogIntegrand 0 s
  have hv : IntegrableOn v (Ioi 0) := c2ClockLogIntegrand_integrableOn 0 hs
  have hw : IntegrableOn (fun x => v (2 * x)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff v 0 (by norm_num : (0 : ℝ) < 2)).2
      (by simpa using hv)
  have hfun : Set.EqOn (fun x : ℝ => x ^ (s - 1) * nativeC2MellinGeometricDensity x)
      (fun x => v x + (2 : ℝ) ^ (1 - s) * v (2 * x)) (Ioi 0) := by
    intro x hx
    have hx₀ : 0 < x := hx
    change x ^ (s - 1) * nativeC2MellinGeometricDensity x =
      v x + (2 : ℝ) ^ (1 - s) * v (2 * x)
    rw [nativeC2MellinGeometricDensity_eq_clock_add_dyadic hx₀]
    simp only [v, c2ClockLogIntegrand, pow_zero, mul_one,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx₀.le]
    rw [← mul_assoc ((2 : ℝ) ^ (1 - s)), ← mul_assoc ((2 : ℝ) ^ (1 - s)),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      show 1 - s + (s - 1) = 0 by ring, Real.rpow_zero, one_mul]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_add hv (hw.const_mul _),
    integral_const_mul, integral_comp_mul_left_Ioi v 0 (by norm_num : (0 : ℝ) < 2),
    mul_zero, smul_eq_mul, ← mul_assoc, ← Real.rpow_neg_one (2 : ℝ),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), show 1 - s + (-1) = -s by ring]
  change c2ClockLogMoment 0 s + (2 : ℝ) ^ (-s) * c2ClockLogMoment 0 s =
    (1 + (2 : ℝ) ^ (-s)) * c2ClockLogMoment 0 s
  ring

end CarrySelfAdjointOperator
