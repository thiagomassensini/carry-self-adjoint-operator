import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-!
# A fixed-strip majorant for the logarithmic Mellin jets

Every fixed logarithmic order can use the same two integrable powers of
the Mellin variable. The constant depends on the order.
-/

namespace CarrySelfAdjointOperator

open Set MeasureTheory

noncomputable section

theorem nativeC2Mellin_logPower_le (r : ℕ) (x : ℝ) :
    |Real.log x| ^ r ≤ (8 : ℝ) ^ r * r.factorial * Real.exp (|Real.log x| / 8) := by
  have h := Real.pow_div_factorial_le_exp (|Real.log x| / 8)
    (div_nonneg (abs_nonneg (Real.log x)) (by norm_num : (0 : ℝ) ≤ 8)) r
  rw [div_pow, div_div] at h
  exact (div_le_iff₀ (by positivity)).mp h
    |> fun ht => by simpa [mul_comm] using ht

def nativeC2MellinAllOrderMajorant (r : ℕ) (x : ℝ) : ℝ :=
  (2 * (8 : ℝ) ^ r * r.factorial) *
    (Real.exp (-x) * (x ^ (-(3 / 4 : ℝ)) + x ^ (-(1 / 4 : ℝ))))

theorem nativeC2MellinAllOrderMajorant_integrable (r : ℕ) :
    IntegrableOn (nativeC2MellinAllOrderMajorant r) (Ioi 0) := by
  have h₁ := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 4)
  have h₂ := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 3 / 4)
  have h₁' : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (-(3 / 4 : ℝ))) (Ioi 0) := by
    simpa only [show (1 / 4 : ℝ) - 1 = -(3 / 4 : ℝ) by norm_num] using h₁
  have h₂' : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (-(1 / 4 : ℝ))) (Ioi 0) := by
    simpa only [show (3 / 4 : ℝ) - 1 = -(1 / 4 : ℝ) by norm_num] using h₂
  have hsum : IntegrableOn
      (fun x : ℝ => Real.exp (-x) *
        (x ^ (-(3 / 4 : ℝ)) + x ^ (-(1 / 4 : ℝ)))) (Ioi 0) := by
    exact (h₁'.add h₂').congr_fun (fun x _ => by dsimp; ring) measurableSet_Ioi
  exact hsum.const_mul (2 * (8 : ℝ) ^ r * r.factorial)

private theorem nativeC2Mellin_rpow_expLog_bound (s x : ℝ) (hx : 0 < x)
    (hs : s ∈ Ioo (3 / 8 : ℝ) (5 / 8)) :
    x ^ (s - 1) * Real.exp (|Real.log x| / 8) ≤
      x ^ (-(3 / 4 : ℝ)) + x ^ (-(1 / 4 : ℝ)) := by
  rcases le_total x 1 with hsmall | hlarge
  · rw [abs_of_nonpos (Real.log_nonpos hx.le hsmall),
      show -Real.log x / 8 = Real.log x * (-(1 / 8 : ℝ)) by ring,
      ← Real.rpow_def_of_pos hx, ← Real.rpow_add hx]
    apply le_add_of_le_of_nonneg _ (Real.rpow_nonneg hx.le _)
    exact Real.rpow_le_rpow_of_exponent_ge hx hsmall (by linarith [hs.1])
  · rw [abs_of_nonneg (Real.log_nonneg hlarge),
      show Real.log x / 8 = Real.log x * (1 / 8 : ℝ) by ring,
      ← Real.rpow_def_of_pos hx, ← Real.rpow_add hx]
    apply le_add_of_nonneg_of_le (Real.rpow_nonneg hx.le _) _
    exact Real.rpow_le_rpow_of_exponent_le hlarge (by linarith [hs.2])

/-- The density can be instantiated with the original C2 density or with
another density having the same pointwise bound. -/
theorem nativeC2MellinAllOrderMajorant_bound (r : ℕ) (s x ρ : ℝ) (hx : 0 < x)
    (hs : s ∈ Ioo (3 / 8 : ℝ) (5 / 8)) (hρ₀ : 0 ≤ ρ)
    (hρ : ρ ≤ 2 * Real.exp (-x)) :
    |x ^ (s - 1) * (Real.log x) ^ r * ρ| ≤ nativeC2MellinAllOrderMajorant r x := by
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _),
    abs_pow, abs_of_nonneg hρ₀]
  calc
    _ ≤ x ^ (s - 1) * ((8 : ℝ) ^ r * r.factorial *
        Real.exp (|Real.log x| / 8)) * (2 * Real.exp (-x)) := by
      gcongr
      exact nativeC2Mellin_logPower_le r x
    _ = (2 * (8 : ℝ) ^ r * r.factorial) *
        (Real.exp (-x) * (x ^ (s - 1) * Real.exp (|Real.log x| / 8))) := by ring
    _ ≤ _ := by
      unfold nativeC2MellinAllOrderMajorant
      gcongr
      exact nativeC2Mellin_rpow_expLog_bound s x hx hs

end

end CarrySelfAdjointOperator
