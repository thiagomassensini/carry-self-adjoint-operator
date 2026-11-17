import CarrySelfAdjointOperator.C2MellinInfiniteLimit
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open Set MeasureTheory Filter
open scoped Topology

namespace CarrySelfAdjointOperator

noncomputable section
set_option autoImplicit false

def nativeC2MellinGeometricLogIntegrand (r : ℕ) (s x : ℝ) : ℝ :=
  x ^ (s - 1) * (Real.log x) ^ r * nativeC2MellinGeometricDensity x

def nativeC2MellinGeometricLogMoment (r : ℕ) (s : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), nativeC2MellinGeometricLogIntegrand r s x

def nativeC2MellinGeometricSourceIntegral (s : ℝ) : ℝ :=
  nativeC2MellinGeometricLogMoment 0 s

/-- A concrete logarithmic envelope useful for Mellin differentiation near
`s = 1/2`. -/
theorem nativeC2Mellin_abs_log_le_eighth_roots {x : ℝ} (hx : 0 < x) :
    |Real.log x| ≤ 8 * (x ^ (1 / 8 : ℝ) + x ^ (-(1 / 8 : ℝ))) := by
  rcases le_total 1 x with hx1 | hx1
  · have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
    rw [abs_of_nonneg hlog]
    have heq : Real.log x = 8 * Real.log (x ^ (1 / 8 : ℝ)) := by
      rw [Real.log_rpow hx]
      ring
    calc
      Real.log x = 8 * Real.log (x ^ (1 / 8 : ℝ)) := heq
      _ ≤ 8 * x ^ (1 / 8 : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_self (Real.rpow_nonneg hx.le _)) (by norm_num)
      _ ≤ 8 * (x ^ (1 / 8 : ℝ) + x ^ (-(1 / 8 : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _)) (by norm_num)
  · have hlog : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
    rw [abs_of_nonpos hlog]
    have heq : -Real.log x = 8 * Real.log (x ^ (-(1 / 8 : ℝ))) := by
      rw [Real.log_rpow hx]
      ring
    calc
      -Real.log x = 8 * Real.log (x ^ (-(1 / 8 : ℝ))) := heq
      _ ≤ 8 * x ^ (-(1 / 8 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_self (Real.rpow_nonneg hx.le _)) (by norm_num)
      _ ≤ 8 * (x ^ (1 / 8 : ℝ) + x ^ (-(1 / 8 : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _)) (by norm_num)

private theorem nativeC2MellinGeometricDensity_pos {x : ℝ} (hx : 0 < x) :
    0 < nativeC2MellinGeometricDensity x := by
  unfold nativeC2MellinGeometricDensity
  exact add_pos (Real.exp_pos _) (nativeC2MellinGeometricOmega0_pos hx)

private theorem nativeC2MellinGeometricDensity_continuousOn :
    ContinuousOn nativeC2MellinGeometricDensity (Ioi 0) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  have hx0 : 0 < x := hx
  have hden : 1 - Real.exp (-4 * x) ≠ 0 := by
    have hexp : Real.exp (-4 * x) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith)
    linarith
  unfold nativeC2MellinGeometricDensity nativeC2MellinGeometricOmega0
  fun_prop (disch := assumption)

private theorem nativeC2MellinGeometricLogIntegrand_aestronglyMeasurable
    (r : ℕ) (s : ℝ) :
    AEStronglyMeasurable (nativeC2MellinGeometricLogIntegrand r s)
      (volume.restrict (Ioi 0)) := by
  have hpow : ContinuousOn (fun x : ℝ => x ^ (s - 1)) (Ioi 0) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    exact Real.continuousAt_rpow_const x (s - 1) (Or.inl hx.ne')
  have hlog : ContinuousOn Real.log (Ioi 0) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    exact Real.continuousAt_log hx.ne'
  have hcont : ContinuousOn (nativeC2MellinGeometricLogIntegrand r s) (Ioi 0) := by
    unfold nativeC2MellinGeometricLogIntegrand
    exact (hpow.mul (hlog.pow r)).mul nativeC2MellinGeometricDensity_continuousOn
  exact hcont.aestronglyMeasurable measurableSet_Ioi

private theorem nativeC2MellinGeometricLogIntegrand_hasDerivAt
    (r : ℕ) {s x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => nativeC2MellinGeometricLogIntegrand r t x)
      (nativeC2MellinGeometricLogIntegrand (r + 1) s x) s := by
  have hpow : HasDerivAt (fun t : ℝ => x ^ (t - 1))
      (x ^ (s - 1) * Real.log x) s := by
    have hinner : HasDerivAt (fun t : ℝ => t - 1) 1 s :=
      (hasDerivAt_id s).sub_const 1
    have h := hinner.hasFDerivAt.const_rpow hx
    simpa [mul_assoc, smul_eq_mul] using h.hasDerivAt
  have h := hpow.mul_const ((Real.log x) ^ r * nativeC2MellinGeometricDensity x)
  simpa [nativeC2MellinGeometricLogIntegrand, pow_succ, mul_assoc,
    mul_left_comm, mul_comm] using h

private theorem nativeC2Mellin_log_majorant_integrable :
    IntegrableOn
      (fun x : ℝ => 16 * (Real.exp (-x) *
        (x ^ (-(3 / 4 : ℝ)) + x ^ (-(1 / 4 : ℝ)) +
          x ^ (-(1 / 2 : ℝ)) + 1))) (Ioi 0) := by
  have h1 := Real.GammaIntegral_convergent (by norm_num : 0 < (1 / 4 : ℝ))
  have h2 := Real.GammaIntegral_convergent (by norm_num : 0 < (3 / 4 : ℝ))
  have h3 := Real.GammaIntegral_convergent (by norm_num : 0 < (1 / 2 : ℝ))
  have h4 := Real.GammaIntegral_convergent (by norm_num : 0 < (1 : ℝ))
  have h1' : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (-(3 / 4 : ℝ)))
      (Ioi 0) := by
    have heq : (1 / 4 : ℝ) - 1 = -(3 / 4 : ℝ) := by norm_num
    simpa only [heq] using h1
  have h2' : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (-(1 / 4 : ℝ)))
      (Ioi 0) := by
    have heq : (3 / 4 : ℝ) - 1 = -(1 / 4 : ℝ) := by norm_num
    simpa only [heq] using h2
  have h3' : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (-(1 / 2 : ℝ)))
      (Ioi 0) := by
    have heq : (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) := by norm_num
    simpa only [heq] using h3
  have h4' : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
    have heq : (1 : ℝ) - 1 = 0 := by norm_num
    simpa only [heq, Real.rpow_zero, mul_one] using h4
  have hsum0 := (((h1'.add h2').add h3').add h4')
  have hsum : IntegrableOn
      (fun x : ℝ => Real.exp (-x) *
        (x ^ (-(3 / 4 : ℝ)) + x ^ (-(1 / 4 : ℝ)) +
          x ^ (-(1 / 2 : ℝ)) + 1)) (Ioi 0) := by
    apply hsum0.congr_fun
      (fun x hx => by dsimp; ring)
      measurableSet_Ioi
  exact hsum.const_mul 16

private theorem nativeC2MellinGeometricLogIntegrand_norm_bound
    {s x : ℝ} (hx : 0 < x)
    (hs : s ∈ Set.Ioo (3 / 8 : ℝ) (5 / 8)) :
    |nativeC2MellinGeometricLogIntegrand 1 s x| ≤
      16 * (Real.exp (-x) *
        (x ^ (-(3 / 4 : ℝ)) + x ^ (-(1 / 4 : ℝ)) +
          x ^ (-(1 / 2 : ℝ)) + 1)) := by
  have hdensity0 : 0 ≤ nativeC2MellinGeometricDensity x :=
    (nativeC2MellinGeometricDensity_pos hx).le
  have hdensityle : nativeC2MellinGeometricDensity x ≤ 2 * Real.exp (-x) :=
    nativeC2MellinGeometricDensity_le_two_exp_neg hx
  have hlog := nativeC2Mellin_abs_log_le_eighth_roots hx
  rcases le_total x 1 with hx1 | hx1
  · have hpow : x ^ (s - 1) ≤ x ^ (-(5 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (by norm_num; linarith [hs.1])
    have hraw : x ^ (s - 1) * |Real.log x| *
        nativeC2MellinGeometricDensity x ≤
        16 * Real.exp (-x) *
          (x ^ (-(1 / 2 : ℝ)) + x ^ (-(3 / 4 : ℝ))) := by
      calc
        _ ≤ x ^ (-(5 / 8 : ℝ)) *
            (8 * (x ^ (1 / 8 : ℝ) + x ^ (-(1 / 8 : ℝ)))) *
              (2 * Real.exp (-x)) := by
                gcongr
        _ = 16 * Real.exp (-x) *
            (x ^ (-(1 / 2 : ℝ)) + x ^ (-(3 / 4 : ℝ))) := by
              have he1 : x ^ (-(5 / 8 : ℝ)) * x ^ (1 / 8 : ℝ) =
                  x ^ (-(1 / 2 : ℝ)) := by
                rw [← Real.rpow_add hx]
                congr 1; norm_num
              have he2 : x ^ (-(5 / 8 : ℝ)) * x ^ (-(1 / 8 : ℝ)) =
                  x ^ (-(3 / 4 : ℝ)) := by
                rw [← Real.rpow_add hx]
                congr 1; norm_num
              calc
                _ = 16 * Real.exp (-x) *
                    (x ^ (-(5 / 8 : ℝ)) * x ^ (1 / 8 : ℝ) +
                      x ^ (-(5 / 8 : ℝ)) * x ^ (-(1 / 8 : ℝ))) := by ring
                _ = _ := by rw [he1, he2]
    have hpow0 : 0 ≤ x ^ (s - 1) := Real.rpow_nonneg hx.le _
    rw [nativeC2MellinGeometricLogIntegrand, abs_mul, abs_mul,
      abs_of_nonneg hpow0, abs_of_nonneg hdensity0]
    simp only [pow_one]
    calc
      x ^ (s - 1) * |Real.log x| * nativeC2MellinGeometricDensity x ≤
          16 * Real.exp (-x) * (x ^ (-(1 / 2 : ℝ)) + x ^ (-(3 / 4 : ℝ))) := hraw
      _ = 16 * (Real.exp (-x) *
          (x ^ (-(1 / 2 : ℝ)) + x ^ (-(3 / 4 : ℝ)))) := by ring
      _ ≤ 16 * (Real.exp (-x) *
          (x ^ (-(3 / 4 : ℝ)) + x ^ (-(1 / 4 : ℝ)) +
            x ^ (-(1 / 2 : ℝ)) + 1)) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left
          · have h1 : 0 ≤ x ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hx.le _
            have h2 : 0 ≤ (1 : ℝ) := by norm_num
            linarith
          · exact (Real.exp_pos (-x)).le
        · norm_num

  · have hpow : x ^ (s - 1) ≤ x ^ (-(3 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num; linarith [hs.2])
    have hraw : x ^ (s - 1) * |Real.log x| *
        nativeC2MellinGeometricDensity x ≤
        16 * Real.exp (-x) *
          (x ^ (-(1 / 4 : ℝ)) + x ^ (-(1 / 2 : ℝ))) := by
      calc
        _ ≤ x ^ (-(3 / 8 : ℝ)) *
            (8 * (x ^ (1 / 8 : ℝ) + x ^ (-(1 / 8 : ℝ)))) *
              (2 * Real.exp (-x)) := by
                gcongr
        _ = 16 * Real.exp (-x) *
            (x ^ (-(1 / 4 : ℝ)) + x ^ (-(1 / 2 : ℝ))) := by
              have he1 : x ^ (-(3 / 8 : ℝ)) * x ^ (1 / 8 : ℝ) =
                  x ^ (-(1 / 4 : ℝ)) := by
                rw [← Real.rpow_add hx]
                congr 1; norm_num
              have he2 : x ^ (-(3 / 8 : ℝ)) * x ^ (-(1 / 8 : ℝ)) =
                  x ^ (-(1 / 2 : ℝ)) := by
                rw [← Real.rpow_add hx]
                congr 1; norm_num
              calc
                _ = 16 * Real.exp (-x) *
                    (x ^ (-(3 / 8 : ℝ)) * x ^ (1 / 8 : ℝ) +
                      x ^ (-(3 / 8 : ℝ)) * x ^ (-(1 / 8 : ℝ))) := by ring
                _ = _ := by rw [he1, he2]
    have hpow0 : 0 ≤ x ^ (s - 1) := Real.rpow_nonneg hx.le _
    rw [nativeC2MellinGeometricLogIntegrand, abs_mul, abs_mul,
      abs_of_nonneg hpow0, abs_of_nonneg hdensity0]
    simp only [pow_one]
    calc
      x ^ (s - 1) * |Real.log x| * nativeC2MellinGeometricDensity x ≤
          16 * Real.exp (-x) * (x ^ (-(1 / 4 : ℝ)) + x ^ (-(1 / 2 : ℝ))) := hraw
      _ = 16 * (Real.exp (-x) *
          (x ^ (-(1 / 4 : ℝ)) + x ^ (-(1 / 2 : ℝ)))) := by ring
      _ ≤ 16 * (Real.exp (-x) *
          (x ^ (-(3 / 4 : ℝ)) + x ^ (-(1 / 4 : ℝ)) +
            x ^ (-(1 / 2 : ℝ)) + 1)) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left
          · have h1 : 0 ≤ x ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hx.le _
            have h2 : 0 ≤ (1 : ℝ) := by norm_num
            linarith
          · exact (Real.exp_pos (-x)).le
        · norm_num

private theorem nativeC2Mellin_log2_majorant_integrable :
    IntegrableOn
      (fun x : ℝ => 512 * (Real.exp (-x) *
        (x ^ (-(7 / 8 : ℝ)) + x ^ (-(1 / 8 : ℝ))))) (Ioi 0) := by
  have h1 := Real.GammaIntegral_convergent (by norm_num : 0 < (1 / 8 : ℝ))
  have h2 := Real.GammaIntegral_convergent (by norm_num : 0 < (7 / 8 : ℝ))
  have h1' : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (-(7 / 8 : ℝ)))
      (Ioi 0) := by
    have heq : (1 / 8 : ℝ) - 1 = -(7 / 8 : ℝ) := by norm_num
    simpa only [heq] using h1
  have h2' : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (-(1 / 8 : ℝ)))
      (Ioi 0) := by
    have heq : (7 / 8 : ℝ) - 1 = -(1 / 8 : ℝ) := by norm_num
    simpa only [heq] using h2
  have hsum0 := h1'.add h2'
  have hsum : IntegrableOn
      (fun x : ℝ => Real.exp (-x) *
        (x ^ (-(7 / 8 : ℝ)) + x ^ (-(1 / 8 : ℝ)))) (Ioi 0) := by
    apply hsum0.congr_fun
      (fun x hx => by dsimp; ring)
      measurableSet_Ioi
  exact hsum.const_mul 512

private theorem nativeC2MellinGeometricLogIntegrand_two_norm_bound
    {s x : ℝ} (hx : 0 < x)
    (hs : s ∈ Set.Ioo (3 / 8 : ℝ) (5 / 8)) :
    |nativeC2MellinGeometricLogIntegrand 2 s x| ≤
      512 * (Real.exp (-x) *
        (x ^ (-(7 / 8 : ℝ)) + x ^ (-(1 / 8 : ℝ)))) := by
  have hdensity0 : 0 ≤ nativeC2MellinGeometricDensity x :=
    (nativeC2MellinGeometricDensity_pos hx).le
  have hdensityle : nativeC2MellinGeometricDensity x ≤ 2 * Real.exp (-x) :=
    nativeC2MellinGeometricDensity_le_two_exp_neg hx
  have hlog := nativeC2Mellin_abs_log_le_eighth_roots hx
  have hpow0 : 0 ≤ x ^ (s - 1) := Real.rpow_nonneg hx.le _
  rcases le_total x 1 with hx1 | hx1
  · have hpow : x ^ (s - 1) ≤ x ^ (-(5 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (by norm_num; linarith [hs.1])
    have hroot : x ^ (1 / 8 : ℝ) ≤ x ^ (-(1 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (by norm_num)
    have hlog' : |Real.log x| ≤ 16 * x ^ (-(1 / 8 : ℝ)) := by
      calc
        |Real.log x| ≤ 8 * (x ^ (1 / 8 : ℝ) + x ^ (-(1 / 8 : ℝ))) := hlog
        _ ≤ 8 * (2 * x ^ (-(1 / 8 : ℝ))) := by
          apply mul_le_mul_of_nonneg_left
          · linarith
          · norm_num
        _ = 16 * x ^ (-(1 / 8 : ℝ)) := by ring
    have hlog0 : 0 ≤ |Real.log x| := abs_nonneg _
    have hlogsq : |Real.log x| ^ 2 ≤ 256 * x ^ (-(1 / 4 : ℝ)) := by
      calc
        |Real.log x| ^ 2 = |Real.log x| * |Real.log x| := by ring
        _ ≤ (16 * x ^ (-(1 / 8 : ℝ))) * (16 * x ^ (-(1 / 8 : ℝ))) :=
          mul_self_le_mul_self hlog0 hlog'
        _ = 256 * (x ^ (-(1 / 8 : ℝ)) * x ^ (-(1 / 8 : ℝ))) := by ring
        _ = 256 * x ^ (-(1 / 4 : ℝ)) := by
          rw [← Real.rpow_add hx]
          congr 1
          norm_num
    have hraw : x ^ (s - 1) * |Real.log x| ^ 2 *
        nativeC2MellinGeometricDensity x ≤
        512 * (Real.exp (-x) * x ^ (-(7 / 8 : ℝ))) := by
      calc
        _ ≤ x ^ (-(5 / 8 : ℝ)) *
            (256 * x ^ (-(1 / 4 : ℝ))) * (2 * Real.exp (-x)) := by
              gcongr
        _ = 512 * (Real.exp (-x) * x ^ (-(7 / 8 : ℝ))) := by
          have hprod : x ^ (-(5 / 8 : ℝ)) * x ^ (-(1 / 4 : ℝ)) =
              x ^ (-(7 / 8 : ℝ)) := by
            rw [← Real.rpow_add hx]
            congr 1
            norm_num
          calc
            _ = 512 * (Real.exp (-x) *
                (x ^ (-(5 / 8 : ℝ)) * x ^ (-(1 / 4 : ℝ)))) := by ring
            _ = _ := by rw [hprod]
    rw [nativeC2MellinGeometricLogIntegrand, abs_mul, abs_mul, abs_pow,
      abs_of_nonneg hpow0, abs_of_nonneg hdensity0]
    calc
      x ^ (s - 1) * |Real.log x| ^ 2 * nativeC2MellinGeometricDensity x ≤
          512 * (Real.exp (-x) * x ^ (-(7 / 8 : ℝ))) := hraw
      _ = 512 * (Real.exp (-x) * x ^ (-(7 / 8 : ℝ))) := rfl
      _ ≤ 512 * (Real.exp (-x) *
          (x ^ (-(7 / 8 : ℝ)) + x ^ (-(1 / 8 : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left
          · exact le_add_of_nonneg_right (Real.rpow_nonneg hx.le _)
          · exact (Real.exp_pos (-x)).le
        · norm_num
  · have hpow : x ^ (s - 1) ≤ x ^ (-(3 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num; linarith [hs.2])
    have hroot : x ^ (-(1 / 8 : ℝ)) ≤ x ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hlog' : |Real.log x| ≤ 16 * x ^ (1 / 8 : ℝ) := by
      calc
        |Real.log x| ≤ 8 * (x ^ (1 / 8 : ℝ) + x ^ (-(1 / 8 : ℝ))) := hlog
        _ ≤ 8 * (2 * x ^ (1 / 8 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left
          · linarith
          · norm_num
        _ = 16 * x ^ (1 / 8 : ℝ) := by ring
    have hlog0 : 0 ≤ |Real.log x| := abs_nonneg _
    have hlogsq : |Real.log x| ^ 2 ≤ 256 * x ^ (1 / 4 : ℝ) := by
      calc
        |Real.log x| ^ 2 = |Real.log x| * |Real.log x| := by ring
        _ ≤ (16 * x ^ (1 / 8 : ℝ)) * (16 * x ^ (1 / 8 : ℝ)) :=
          mul_self_le_mul_self hlog0 hlog'
        _ = 256 * (x ^ (1 / 8 : ℝ) * x ^ (1 / 8 : ℝ)) := by ring
        _ = 256 * x ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_add hx]
          congr 1
          norm_num
    have hraw : x ^ (s - 1) * |Real.log x| ^ 2 *
        nativeC2MellinGeometricDensity x ≤
        512 * (Real.exp (-x) * x ^ (-(1 / 8 : ℝ))) := by
      calc
        _ ≤ x ^ (-(3 / 8 : ℝ)) *
            (256 * x ^ (1 / 4 : ℝ)) * (2 * Real.exp (-x)) := by
              gcongr
        _ = 512 * (Real.exp (-x) * x ^ (-(1 / 8 : ℝ))) := by
          have hprod : x ^ (-(3 / 8 : ℝ)) * x ^ (1 / 4 : ℝ) =
              x ^ (-(1 / 8 : ℝ)) := by
            rw [← Real.rpow_add hx]
            congr 1
            norm_num
          calc
            _ = 512 * (Real.exp (-x) *
                (x ^ (-(3 / 8 : ℝ)) * x ^ (1 / 4 : ℝ))) := by ring
            _ = _ := by rw [hprod]
    rw [nativeC2MellinGeometricLogIntegrand, abs_mul, abs_mul, abs_pow,
      abs_of_nonneg hpow0, abs_of_nonneg hdensity0]
    calc
      x ^ (s - 1) * |Real.log x| ^ 2 * nativeC2MellinGeometricDensity x ≤
          512 * (Real.exp (-x) * x ^ (-(1 / 8 : ℝ))) := hraw
      _ = 512 * (Real.exp (-x) * x ^ (-(1 / 8 : ℝ))) := rfl
      _ ≤ 512 * (Real.exp (-x) *
          (x ^ (-(7 / 8 : ℝ)) + x ^ (-(1 / 8 : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))
            (Real.exp_pos (-x)).le
        · norm_num

private theorem nativeC2MellinGeometricLogIntegrand_zero_norm_bound
    {s x : ℝ} (hx : 0 < x)
    (hs : s ∈ Set.Ioo (3 / 8 : ℝ) (5 / 8)) :
    |nativeC2MellinGeometricLogIntegrand 0 s x| ≤
      16 * (Real.exp (-x) *
        (x ^ (-(3 / 4 : ℝ)) + x ^ (-(1 / 4 : ℝ)) +
          x ^ (-(1 / 2 : ℝ)) + 1)) := by
  have hdensity0 : 0 ≤ nativeC2MellinGeometricDensity x :=
    (nativeC2MellinGeometricDensity_pos hx).le
  have hdensityle : nativeC2MellinGeometricDensity x ≤ 2 * Real.exp (-x) :=
    nativeC2MellinGeometricDensity_le_two_exp_neg hx
  have hpow0 : 0 ≤ x ^ (s - 1) := Real.rpow_nonneg hx.le _
  rcases le_total x 1 with hx1 | hx1
  · have hpow : x ^ (s - 1) ≤ x ^ (-(5 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (by norm_num; linarith [hs.1])
    have hle : x ^ (s - 1) * nativeC2MellinGeometricDensity x ≤
        2 * Real.exp (-x) * x ^ (-(3 / 4 : ℝ)) := by
      calc
        _ ≤ x ^ (-(5 / 8 : ℝ)) * (2 * Real.exp (-x)) := by gcongr
        _ ≤ 2 * Real.exp (-x) * x ^ (-(3 / 4 : ℝ)) := by
          have hrpow : x ^ (-(5 / 8 : ℝ)) ≤ x ^ (-(3 / 4 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_ge hx hx1 (by norm_num)
          nlinarith [mul_nonneg (Real.exp_pos (-x)).le (Real.rpow_nonneg hx.le (-(3 / 4 : ℝ)))]
    rw [nativeC2MellinGeometricLogIntegrand, pow_zero, mul_one, abs_mul,
      abs_of_nonneg hpow0, abs_of_nonneg hdensity0]
    nlinarith [hle, Real.rpow_nonneg hx.le (-(1 / 4 : ℝ)),
      Real.rpow_nonneg hx.le (-(1 / 2 : ℝ)), Real.exp_pos (-x)]
  · have hpow : x ^ (s - 1) ≤ x ^ (-(3 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num; linarith [hs.2])
    have hle : x ^ (s - 1) * nativeC2MellinGeometricDensity x ≤
        2 * Real.exp (-x) := by
      calc
        _ ≤ x ^ (-(3 / 8 : ℝ)) * (2 * Real.exp (-x)) := by gcongr
        _ ≤ 2 * Real.exp (-x) := by
          have hrpow : x ^ (-(3 / 8 : ℝ)) ≤ 1 := by
            simpa using (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : -(3 / 8 : ℝ) ≤ 0))
          nlinarith [Real.exp_pos (-x)]
    rw [nativeC2MellinGeometricLogIntegrand, pow_zero, mul_one, abs_mul,
      abs_of_nonneg hpow0, abs_of_nonneg hdensity0]
    nlinarith [hle, Real.rpow_nonneg hx.le (-(3 / 4 : ℝ)),
      Real.rpow_nonneg hx.le (-(1 / 4 : ℝ)), Real.rpow_nonneg hx.le (-(1 / 2 : ℝ)),
      Real.exp_pos (-x)]

/-- The source Mellin integral is differentiable throughout the compact parameter
window `3/8 < s < 5/8`, with derivative equal to its first logarithmic
moment. This neighborhood identity is needed to identify its second
iterated derivative at the critical parameter. -/
theorem nativeC2MellinGeometricSourceIntegral_hasDerivAt
    {s : ℝ} (hs : s ∈ Set.Ioo (3 / 8 : ℝ) (5 / 8)) :
    HasDerivAt nativeC2MellinGeometricSourceIntegral
      (nativeC2MellinGeometricLogMoment 1 s) s := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let S : Set ℝ := Ioo (3 / 8 : ℝ) (5 / 8)
  have hS : S ∈ 𝓝 s := Ioo_mem_nhds hs.1 hs.2
  have hmajor := nativeC2Mellin_log_majorant_integrable
  have hmeas0 : AEStronglyMeasurable
      (nativeC2MellinGeometricLogIntegrand 0 s) μ := by
    simpa [μ] using nativeC2MellinGeometricLogIntegrand_aestronglyMeasurable 0 s
  have hmeas1 : AEStronglyMeasurable
      (nativeC2MellinGeometricLogIntegrand 1 s) μ := by
    simpa [μ] using nativeC2MellinGeometricLogIntegrand_aestronglyMeasurable 1 s
  have hbound0 : ∀ᵐ x ∂μ,
      ‖nativeC2MellinGeometricLogIntegrand 0 s x‖ ≤
        16 * (Real.exp (-x) *
          (x ^ (-(3 / 4 : ℝ)) + x ^ (-(1 / 4 : ℝ)) +
            x ^ (-(1 / 2 : ℝ)) + 1)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    simpa [Real.norm_eq_abs] using
      nativeC2MellinGeometricLogIntegrand_zero_norm_bound hx hs
  have hFint : Integrable
      (nativeC2MellinGeometricLogIntegrand 0 s) μ :=
    hmajor.mono' hmeas0 hbound0
  have hderivbound : ∀ᵐ x ∂μ, ∀ s ∈ S,
      ‖nativeC2MellinGeometricLogIntegrand 1 s x‖ ≤
        16 * (Real.exp (-x) *
          (x ^ (-(3 / 4 : ℝ)) + x ^ (-(1 / 4 : ℝ)) +
            x ^ (-(1 / 2 : ℝ)) + 1)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    intro s hs
    simpa [Real.norm_eq_abs] using nativeC2MellinGeometricLogIntegrand_norm_bound
      (x := x) hx hs
  have hdiff : ∀ᵐ x ∂μ, ∀ s ∈ S,
      HasDerivAt (fun t : ℝ => nativeC2MellinGeometricLogIntegrand 0 t x)
        (nativeC2MellinGeometricLogIntegrand 1 s x) s := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    intro s hs
    exact nativeC2MellinGeometricLogIntegrand_hasDerivAt 0 hx
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => nativeC2MellinGeometricLogIntegrand 0 s x)
    (x₀ := s) (s := S) (bound := fun x =>
      16 * (Real.exp (-x) *
        (x ^ (-(3 / 4 : ℝ)) + x ^ (-(1 / 4 : ℝ)) +
          x ^ (-(1 / 2 : ℝ)) + 1))) hS
    (by filter_upwards [] with s; exact nativeC2MellinGeometricLogIntegrand_aestronglyMeasurable 0 s)
    hFint hmeas1 hderivbound hmajor hdiff
  change HasDerivAt
    (fun s : ℝ => ∫ x in Ioi (0 : ℝ),
      nativeC2MellinGeometricLogIntegrand 0 s x)
    (∫ x in Ioi (0 : ℝ),
      nativeC2MellinGeometricLogIntegrand 1 s x) s
  simpa [μ, nativeC2MellinGeometricLogIntegrand, pow_succ, mul_assoc,
    mul_left_comm, mul_comm] using hparam.2

/-- Critical-parameter specialization of the neighborhood differentiation theorem. -/
theorem nativeC2MellinGeometricSourceIntegral_hasDerivAt_half :
    HasDerivAt nativeC2MellinGeometricSourceIntegral
      (nativeC2MellinGeometricLogMoment 1 (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
  exact nativeC2MellinGeometricSourceIntegral_hasDerivAt (by norm_num)

/-- The second logarithmic Mellin moment is the derivative of the first source
log-moment at `s = 1/2`. This supplies the source second moment (and hence the
second derivative input for cumulant calculations), still before camera and
completion factors are included. -/
theorem nativeC2MellinGeometricLogMoment_one_hasDerivAt_half :
    HasDerivAt (fun s : ℝ => nativeC2MellinGeometricLogMoment 1 s)
      (nativeC2MellinGeometricLogMoment 2 (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let S : Set ℝ := Ioo (3 / 8 : ℝ) (5 / 8)
  have hS : S ∈ 𝓝 (1 / 2 : ℝ) := by
    apply Ioo_mem_nhds
    <;> norm_num
  have hmajor1 := nativeC2Mellin_log_majorant_integrable
  have hmajor2 := nativeC2Mellin_log2_majorant_integrable
  have hmeas1 : AEStronglyMeasurable
      (nativeC2MellinGeometricLogIntegrand 1 (1 / 2 : ℝ)) μ := by
    simpa [μ] using nativeC2MellinGeometricLogIntegrand_aestronglyMeasurable 1 (1 / 2 : ℝ)
  have hmeas2 : AEStronglyMeasurable
      (nativeC2MellinGeometricLogIntegrand 2 (1 / 2 : ℝ)) μ := by
    simpa [μ] using nativeC2MellinGeometricLogIntegrand_aestronglyMeasurable 2 (1 / 2 : ℝ)
  have hbound1 : ∀ᵐ x ∂μ,
      ‖nativeC2MellinGeometricLogIntegrand 1 (1 / 2 : ℝ) x‖ ≤
        16 * (Real.exp (-x) *
          (x ^ (-(3 / 4 : ℝ)) + x ^ (-(1 / 4 : ℝ)) +
            x ^ (-(1 / 2 : ℝ)) + 1)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    simpa [Real.norm_eq_abs] using nativeC2MellinGeometricLogIntegrand_norm_bound
      (x := x) hx (by norm_num)
  have hFint : Integrable
      (nativeC2MellinGeometricLogIntegrand 1 (1 / 2 : ℝ)) μ :=
    hmajor1.mono' hmeas1 hbound1
  have hderivbound : ∀ᵐ x ∂μ, ∀ s ∈ S,
      ‖nativeC2MellinGeometricLogIntegrand 2 s x‖ ≤
        512 * (Real.exp (-x) *
          (x ^ (-(7 / 8 : ℝ)) + x ^ (-(1 / 8 : ℝ)))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    intro s hs
    simpa [Real.norm_eq_abs] using nativeC2MellinGeometricLogIntegrand_two_norm_bound
      (x := x) hx hs
  have hdiff : ∀ᵐ x ∂μ, ∀ s ∈ S,
      HasDerivAt (fun t : ℝ => nativeC2MellinGeometricLogIntegrand 1 t x)
        (nativeC2MellinGeometricLogIntegrand 2 s x) s := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    intro s hs
    exact nativeC2MellinGeometricLogIntegrand_hasDerivAt 1 hx
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => nativeC2MellinGeometricLogIntegrand 1 s x)
    (x₀ := (1 / 2 : ℝ)) (s := S) (bound := fun x =>
      512 * (Real.exp (-x) *
        (x ^ (-(7 / 8 : ℝ)) + x ^ (-(1 / 8 : ℝ))))) hS
    (by filter_upwards [] with s; exact nativeC2MellinGeometricLogIntegrand_aestronglyMeasurable 1 s)
    hFint hmeas2 hderivbound hmajor2 hdiff
  change HasDerivAt
    (fun s : ℝ => ∫ x in Ioi (0 : ℝ),
      nativeC2MellinGeometricLogIntegrand 1 s x)
    (∫ x in Ioi (0 : ℝ),
      nativeC2MellinGeometricLogIntegrand 2 (1 / 2 : ℝ) x) (1 / 2 : ℝ)
  simpa [μ, nativeC2MellinGeometricLogIntegrand, pow_succ, mul_assoc,
    mul_left_comm, mul_comm] using hparam.2

/-- The first iterated derivative of the geometric Mellin source is its first
logarithmic moment at the critical parameter. -/
theorem nativeC2MellinGeometricSourceIntegral_iteratedDeriv_one_half :
    iteratedDeriv 1 nativeC2MellinGeometricSourceIntegral (1 / 2 : ℝ) =
      nativeC2MellinGeometricLogMoment 1 (1 / 2 : ℝ) := by
  rw [iteratedDeriv_one]
  exact (nativeC2MellinGeometricSourceIntegral_hasDerivAt (by norm_num)).deriv

/-- The second iterated derivative requires the first-derivative identity in a
neighborhood; the uniform parameter theorem supplies that identity and hence
identifies the second derivative with the second log-moment. -/
theorem nativeC2MellinGeometricSourceIntegral_iteratedDeriv_two_half :
    iteratedDeriv 2 nativeC2MellinGeometricSourceIntegral (1 / 2 : ℝ) =
      nativeC2MellinGeometricLogMoment 2 (1 / 2 : ℝ) := by
  have hS : Set.Ioo (3 / 8 : ℝ) (5 / 8) ∈ 𝓝 (1 / 2 : ℝ) := by
    apply Ioo_mem_nhds
    <;> norm_num
  have hEq : (fun t : ℝ => deriv nativeC2MellinGeometricSourceIntegral t) =ᶠ[𝓝 (1 / 2 : ℝ)]
      (fun t : ℝ => nativeC2MellinGeometricLogMoment 1 t) := by
    filter_upwards [hS] with t ht
    exact (nativeC2MellinGeometricSourceIntegral_hasDerivAt ht).deriv
  have hM1 := nativeC2MellinGeometricLogMoment_one_hasDerivAt_half
  have hM1' : HasDerivAt (fun t : ℝ => deriv nativeC2MellinGeometricSourceIntegral t)
      (nativeC2MellinGeometricLogMoment 2 (1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    hM1.congr_of_eventuallyEq hEq
  have hderiv := hM1'.deriv
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  exact hderiv

end

end CarrySelfAdjointOperator
