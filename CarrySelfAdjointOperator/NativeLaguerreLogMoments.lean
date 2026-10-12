import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Actual Lebesgue logarithmic moments on the physical unit interval.
The endpoint zero is harmless in the measurable class; no continuous
extension of a nonconstant logarithmic Laguerre mode is asserted. -/
namespace CarrySelfAdjointOperator.NativeLaguerre
open MeasureTheory Set
noncomputable section
set_option autoImplicit false

private theorem exp_neg_image : (fun t : ℝ => Real.exp (-t)) '' Ioi 0 = Ioo 0 1 := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)⟩
  · intro hu
    refine ⟨-Real.log u, neg_pos.mpr (Real.log_neg hu.1 hu.2), ?_⟩
    simp [Real.exp_log hu.1]

private theorem exp_neg_deriv (t : ℝ) :
    HasDerivWithinAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) (Ioi 0) t := by
  simpa using ((hasDerivAt_id t).neg.exp).hasDerivWithinAt

private theorem exp_neg_antitone : AntitoneOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
  intro x _ y _ hxy
  exact Real.exp_le_exp.mpr (neg_le_neg hxy)

/-- Integrability of the exponential moment, with its physical decay rate. -/
theorem integrable_exponential_moment (n : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t^n * Real.exp (-(a*t))) (Ioi 0) := by
  have hg := Real.GammaIntegral_convergent (show 0 < (n : ℝ)+1 by positivity)
  simp only [add_sub_cancel_right, Real.rpow_natCast] at hg
  have hc := (integrableOn_Ioi_comp_mul_left_iff
    (fun t : ℝ => Real.exp (-t)*t^n) 0 ha).mpr (by simpa using hg)
  have hd := hc.const_mul ((a^n)⁻¹)
  refine hd.congr (Filter.Eventually.of_forall (fun t => ?_))
  dsimp
  rw [mul_pow]
  field_simp

/-- All logarithmic moments, obtained by the genuine substitution u=exp(-t). -/
theorem integral_logarithmic_moment (n : ℕ) {a : ℝ} (ha : -1 < a) :
    (∫ u in Icc (0 : ℝ) 1, u^a * (-Real.log u)^n) =
      (n.factorial : ℝ) / (a+1)^(n+1) := by
  have ht (t : ℝ) :
      (-(-Real.exp (-t))) • ((Real.exp (-t))^a * (-Real.log (Real.exp (-t)))^n) =
        t^n * Real.exp (-((a+1)*t)) := by
    simp only [neg_neg, Real.log_exp, smul_eq_mul, ← Real.exp_mul]
    rw [← mul_assoc, ← Real.exp_add, mul_comm]
    congr 1
    congr 1
    ring
  have hchange := integral_image_eq_integral_deriv_smul_of_antitoneOn
    measurableSet_Ioi (fun t _ => exp_neg_deriv t) exp_neg_antitone
    (fun u : ℝ => u^a * (-Real.log u)^n)
  rw [exp_neg_image] at hchange
  rw [setIntegral_congr_set Ioo_ae_eq_Icc.symm]
  rw [hchange]
  simp_rw [ht]
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (show 0 < (n : ℝ)+1 by positivity) (show 0 < a+1 by linarith)
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at hg
  rw [show (n : ℝ)+1 = ((n+1 : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast] at hg
  rw [hg]
  simp [div_eq_mul_inv, mul_comm]

/-- The same substitution certifies integrability, independently of the value. -/
theorem integrable_logarithmic_moment (n : ℕ) {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun u : ℝ => u^a * (-Real.log u)^n) (Icc 0 1) := by
  rw [integrableOn_congr_set_ae Ioo_ae_eq_Icc.symm]
  rw [← exp_neg_image]
  apply (integrableOn_image_iff_integrableOn_deriv_smul_of_antitoneOn
    measurableSet_Ioi (fun t _ => exp_neg_deriv t) exp_neg_antitone _).mpr
  refine (integrable_exponential_moment n (show 0 < a+1 by linarith)).congr_fun
    (fun t _ => ?_) measurableSet_Ioi
  simp only [neg_neg, Real.log_exp, smul_eq_mul, ← Real.exp_mul]
  rw [← mul_assoc, ← Real.exp_add, mul_comm]
  congr 1
  congr 1
  ring

end
end CarrySelfAdjointOperator.NativeLaguerre
