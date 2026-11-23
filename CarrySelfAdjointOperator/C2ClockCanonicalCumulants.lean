import CarrySelfAdjointOperator.C2ClockNativeDensityBridge
import CarrySelfAdjointOperator.C2ClockQuadraticJet
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# Canonical cumulants of the original C2 clock

The original Mellin and camera factors cancel before taking the logarithmic
jet. The final passage uses the existing even-coordinate germ.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Camera

noncomputable section

private theorem c2Clock_gamma_mul_bracket_eq {s : ℝ}
    (hs : s ∈ Ioo (3 / 8 : ℝ) (5 / 8)) :
    Complex.Gamma (s : ℂ) * bracketCharacteristic 2 (s : ℂ) =
      ((1 + (2 : ℝ) ^ (-s)) * c2ClockLogMoment 0 s : ℝ) := by
  have hs₀ : 0 < s := by linarith [hs.1]
  rw [← nativeC2MellinComplexGeometricSourceIntegral_eq_gamma_bracketCharacteristic
    (show 0 < (s : ℂ).re by simpa using hs₀),
    ← nativeC2MellinGeometricIntegral_eq_clock_mul hs]
  calc
    _ = ∫ x in Ioi (0 : ℝ),
        ((x ^ (s - 1) * nativeC2MellinGeometricDensity x : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx₀ : 0 < x := hx
      simp only [nativeC2MellinComplexGeometricSourceIntegrand, Complex.ofReal_mul]
      rw [Complex.ofReal_cpow hx₀.le, Complex.ofReal_sub, Complex.ofReal_one]
    _ = _ := integral_ofReal

private theorem c2Clock_dyadicFactor_ne_zero {s : ℝ}
    (hs : s ∈ Ioo (3 / 8 : ℝ) (5 / 8)) :
    1 - (2 : ℝ) ^ (1 - s) ≠ 0 :=
  sub_ne_zero.mpr (ne_of_lt (Real.one_lt_rpow (by norm_num) (by linarith [hs.2])))

/-- The dyadic term from the literal Mellin density is the term cancelled
by division by the original camera factor. -/
theorem c2Clock_eq_gamma_mul_nativeScalar {s : ℝ}
    (hs : s ∈ Ioo (3 / 8 : ℝ) (5 / 8)) :
    (c2ClockLogMoment 0 s : ℂ) =
      Complex.Gamma (s : ℂ) * ((1 - (2 : ℝ) ^ (1 - s) : ℝ) : ℂ) *
        nativeScalar (s : ℂ) := by
  have hdom : (s : ℂ) ∈ nativeScalarDomain := by
    change -1 < s ∧ s < 1
    constructor <;> linarith [hs.1, hs.2]
  have h := c2Clock_gamma_mul_bracket_eq hs
  rw [bracketCharacteristic_eq_factor_mul_nativeScalar (camera := 2) (by norm_num) hdom,
    factor_two, c2Factor] at h
  have hfirst : (1 + (2 : ℝ) ^ (-s) : ℝ) ≠ 0 := by positivity
  have hfirstC : ((1 + (2 : ℝ) ^ (-s) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hfirst
  apply mul_left_cancel₀ hfirstC
  calc
    _ = Complex.Gamma (s : ℂ) *
        ((1 + (2 : ℂ) ^ (-(s : ℂ))) * (1 - (2 : ℂ) ^ (1 - (s : ℂ)))) *
          nativeScalar (s : ℂ) := by
      simpa only [Complex.ofReal_mul, mul_assoc] using h.symm
    _ = _ := by
      push_cast [Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
      ring

/-- The completed characteristic on the real spectral germ uses precisely
the correction of the original C2 clock. -/
theorem c2Clock_completedCharacteristic_eq {s : ℝ}
    (hs : s ∈ Ioo (3 / 8 : ℝ) (5 / 8)) :
    completedNativeOperatorCharacteristic (-Complex.I * ((s : ℂ) - 1 / 2)) =
      ((c2ClockCompletionCorrection s * c2ClockLogMoment 0 s : ℝ) : ℂ) := by
  let z : ℂ := -Complex.I * ((s : ℂ) - 1 / 2)
  have hz : operatorHeightParameter z = (s : ℂ) := by
    unfold operatorHeightParameter z
    linear_combination -((s : ℂ) - 1 / 2) * Complex.I_sq
  have hs₀ : 0 < s := by linarith [hs.1]
  have hG : Real.Gamma s ≠ 0 := (Real.Gamma_pos_of_pos hs₀).ne'
  have hB := c2Clock_dyadicFactor_ne_zero hs
  have hGC : (Real.Gamma s : ℂ) ≠ 0 := by exact_mod_cast hG
  have hBC : ((1 - (2 : ℝ) ^ (1 - s) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hB
  have he : Complex.exp (-((s : ℂ) / 2) * (Real.log Real.pi : ℂ)) =
      (Real.pi ^ (-s / 2) : ℝ) := by
    rw [Real.rpow_def_of_pos Real.pi_pos, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hhalf : (s : ℂ) / 2 = ((s / 2 : ℝ) : ℂ) := by push_cast; rfl
  change completedNativeOperatorCharacteristic z = _
  rw [completedNativeOperatorCharacteristic, nativeXiCompletionFactor, hz, he,
    hhalf, Complex.Gamma_ofReal, Complex.ofReal_mul,
    c2Clock_eq_gamma_mul_nativeScalar hs, Complex.Gamma_ofReal]
  unfold c2ClockCompletionCorrection
  push_cast at *
  field_simp

private def c2CompletedOnRealSpectralAxis (s : ℝ) : ℝ :=
  (completedNativeOperatorCharacteristic (-Complex.I * ((s : ℂ) - 1 / 2))).re

private theorem c2CompletedOnRealSpectralAxis_factor :
    c2CompletedOnRealSpectralAxis =ᶠ[𝓝 (1 / 2 : ℝ)]
      fun s => c2ClockCompletionCorrection s * c2ClockLogMoment 0 s := by
  filter_upwards [Ioo_mem_nhds (by norm_num : (3 / 8 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 5 / 8)] with s hs
  simpa [c2CompletedOnRealSpectralAxis] using congrArg Complex.re
    (c2Clock_completedCharacteristic_eq hs)

private theorem c2CompletedOnRealSpectralAxis_analyticAt :
    AnalyticAt ℝ c2CompletedOnRealSpectralAxis (1 / 2) := by
  let z : ℝ → ℂ := fun s => -Complex.I * ((s : ℂ) - 1 / 2)
  have hcast := Complex.ofRealCLM.analyticAt (1 / 2 : ℝ)
  have hz : AnalyticAt ℝ z (1 / 2) :=
    analyticAt_const.mul (hcast.sub analyticAt_const)
  have h : AnalyticAt ℝ completedNativeOperatorCharacteristic (z (1 / 2)) := by
    have h₀ := (completedNativeOperatorCharacteristic_analyticAt
      zero_mem_completedNativeHeightDomain).restrictScalars (𝕜 := ℝ)
    simpa [z] using h₀
  exact (Complex.reCLM.analyticAt _).comp (h.comp hz)

private theorem c2Clock_Gamma_analyticAt_real {s : ℝ} (hs : 0 < s) :
    AnalyticAt ℝ Real.Gamma s := by
  have hOpen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hDiff : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    refine (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m hm
    have hmRe := congrArg Complex.re hm
    have hm₀ : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    simp at hmRe
    have hz₀ : 0 < z.re := hz
    linarith
  have hmem : (s : ℂ) ∈ {z : ℂ | 0 < z.re} := by simpa using hs
  have h : AnalyticAt ℝ Complex.Gamma (s : ℂ) :=
    (hDiff.analyticOnNhd hOpen _ hmem).restrictScalars
  have hcast : AnalyticAt ℝ (fun t : ℝ => (t : ℂ)) s := Complex.ofRealCLM.analyticAt s
  have hp := (Complex.reCLM.analyticAt _).comp (h.comp hcast)
  simpa [Function.comp_def, Complex.Gamma_ofReal] using hp

private theorem c2ClockCompletionCorrection_analyticAt :
    AnalyticAt ℝ c2ClockCompletionCorrection (1 / 2) := by
  have hg := c2Clock_Gamma_analyticAt_real (by norm_num : (0 : ℝ) < 1 / 2)
  have hhalf : AnalyticAt ℝ (fun s : ℝ => s / 2) (1 / 2) := by
    fun_prop (disch := norm_num)
  have hh₀ : AnalyticAt ℝ Real.Gamma ((1 / 2 : ℝ) / 2) :=
    c2Clock_Gamma_analyticAt_real (by norm_num)
  have hh : AnalyticAt ℝ (fun s : ℝ => Real.Gamma (s / 2)) (1 / 2) :=
    AnalyticAt.comp (f := fun s : ℝ => s / 2) (x := (1 / 2 : ℝ)) hh₀ hhalf
  have hp : AnalyticAt ℝ (fun s : ℝ => Real.pi ^ (-s / 2)) (1 / 2) := by
    simp only [Real.rpow_def_of_pos Real.pi_pos]
    fun_prop
  have hb : AnalyticAt ℝ (fun s : ℝ => 1 - (2 : ℝ) ^ (1 - s)) (1 / 2) := by
    simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    fun_prop
  have hpoly : AnalyticAt ℝ (fun s : ℝ => s * (s - 1)) (1 / 2) := by fun_prop
  have hconst : AnalyticAt ℝ (fun _ : ℝ => (2 : ℝ)) (1 / 2) := analyticAt_const
  exact ((hpoly.mul hp).mul hh).div ((hconst.mul hg).mul hb)
    (mul_ne_zero (mul_ne_zero (by norm_num) (Real.Gamma_pos_of_pos (by norm_num)).ne')
      (c2Clock_dyadicFactor_ne_zero (by norm_num)))

private theorem c2CompletedOnRealSpectralAxis_complex {s : ℝ}
    (hs : s ∈ Ioo (3 / 8 : ℝ) (5 / 8)) :
    (c2CompletedOnRealSpectralAxis s : ℂ) =
      completedNativeOperatorCharacteristic (-Complex.I * ((s : ℂ) - 1 / 2)) := by
  simp only [c2CompletedOnRealSpectralAxis, c2Clock_completedCharacteristic_eq hs,
    Complex.ofReal_re]

private theorem c2CompletedOnRealSpectralAxis_half :
    (c2CompletedOnRealSpectralAxis (1 / 2) : ℂ) =
      completedNativeEvenCharacteristic 0 := by
  have h := completedNativeOperatorCharacteristic_eventuallyEq_evenCharacteristic_sq.eq_of_nhds
  have hz : -Complex.I * (((↑(1 / 2 : ℝ)) : ℂ) - 1 / 2) = 0 := by norm_num
  rw [c2CompletedOnRealSpectralAxis_complex (by norm_num), hz]
  simpa using h

private theorem c2CompletedOnRealSpectralAxis_half_ne_zero :
    c2CompletedOnRealSpectralAxis (1 / 2) ≠ 0 := by
  intro he
  have hc := c2CompletedOnRealSpectralAxis_half
  rw [he, Complex.ofReal_zero] at hc
  exact completedNativeEvenCharacteristic_zero_ne_zero hc.symm

private theorem c2ClockFactor_values_ne_zero :
    c2ClockCompletionCorrection (1 / 2) ≠ 0 ∧ c2ClockLogMoment 0 (1 / 2) ≠ 0 := by
  have he := c2CompletedOnRealSpectralAxis_factor.eq_of_nhds
  have hn := c2CompletedOnRealSpectralAxis_half_ne_zero
  rw [he] at hn
  exact mul_ne_zero_iff.mp hn

private theorem c2ClockIntegral_analyticAt : AnalyticAt ℝ (c2ClockLogMoment 0) (1 / 2) := by
  have hD := c2ClockFactor_values_ne_zero.1
  have heq : (fun s => c2CompletedOnRealSpectralAxis s / c2ClockCompletionCorrection s)
      =ᶠ[𝓝 (1 / 2 : ℝ)] c2ClockLogMoment 0 := by
    filter_upwards [c2CompletedOnRealSpectralAxis_factor,
      c2ClockCompletionCorrection_analyticAt.continuousAt.eventually_ne hD] with s hs hd
    rw [hs, mul_comm, mul_div_cancel_right₀ _ hd]
  exact (c2CompletedOnRealSpectralAxis_analyticAt.div
    c2ClockCompletionCorrection_analyticAt hD).congr heq

private theorem c2ClockCorrectedCumulant_eq_completedLogJet (r : ℕ) :
    c2ClockCorrectedCumulant r =
      iteratedDeriv r (fun s => Real.log (c2CompletedOnRealSpectralAxis s)) (1 / 2) :=
  c2ClockCorrectedCumulant_eq_logJet_of_factor r c2CompletedOnRealSpectralAxis_factor
    c2ClockCompletionCorrection_analyticAt.contDiffAt c2ClockFactor_values_ne_zero.1
    c2ClockIntegral_analyticAt.contDiffAt c2ClockFactor_values_ne_zero.2

private theorem c2CompletedLog_shift_eventuallyEq_even :
    (fun t : ℝ => Real.log (c2CompletedOnRealSpectralAxis (1 / 2 + t))) =ᶠ[𝓝 0]
      fun t => Real.log (c2CompletedOnRealSpectralAxis (1 / 2)) +
        (c2NormalizedEvenLog (-(t : ℂ) ^ 2)).re := by
  have ht : Tendsto (fun t : ℝ => 1 / 2 + t) (𝓝 0) (𝓝 (1 / 2 : ℝ)) := by
    have h : ContinuousAt (fun t : ℝ => 1 / 2 + t) 0 := by fun_prop
    simpa using h.tendsto
  have hrot : Tendsto (fun t : ℝ => -Complex.I * (t : ℂ)) (𝓝 0) (𝓝 0) := by
    have h : ContinuousAt (fun t : ℝ => -Complex.I * (t : ℂ)) 0 := by fun_prop
    simpa using h.tendsto
  have hne := c2CompletedOnRealSpectralAxis_half_ne_zero
  filter_upwards [ht.eventually (Ioo_mem_nhds (by norm_num : (3 / 8 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 5 / 8)),
    ht.eventually (c2CompletedOnRealSpectralAxis_analyticAt.continuousAt.eventually_ne hne),
    hrot.eventually completedNativeOperatorCharacteristic_eventuallyEq_evenCharacteristic_sq]
    with t htI htN htE
  have harg : -Complex.I * ((((1 / 2 + t : ℝ) : ℂ)) - 1 / 2) =
      -Complex.I * (t : ℂ) := by push_cast; ring
  have hsq : (-Complex.I * (t : ℂ)) ^ 2 = -(t : ℂ) ^ 2 := by
    rw [mul_pow, neg_sq, Complex.I_sq]
    ring
  have hval : (c2CompletedOnRealSpectralAxis (1 / 2 + t) : ℂ) =
      completedNativeEvenCharacteristic (-(t : ℂ) ^ 2) := by
    rw [c2CompletedOnRealSpectralAxis_complex htI, harg, htE, hsq]
  change Real.log (c2CompletedOnRealSpectralAxis (1 / 2 + t)) =
    Real.log (c2CompletedOnRealSpectralAxis (1 / 2)) +
      (c2NormalizedEvenLog (-(t : ℂ) ^ 2)).re
  rw [c2NormalizedEvenLog, ← hval, ← c2CompletedOnRealSpectralAxis_half,
    ← Complex.ofReal_div, Complex.log_ofReal_re, Real.log_div htN hne]
  ring

/-- The corrected cumulants of the original C2 clock are the canonical
completed logarithmic moments in the quadratic height coordinate. -/
theorem c2ClockCorrectedCumulant_eq_canonical (n : ℕ) :
    c2ClockCorrectedCumulant (2 * n + 2) =
      2 * (-1 : ℝ) ^ n *
        ((2 * n + 1).factorial : ℝ) * canonicalCompletedNativeLogDerivativeMoment n := by
  let f : ℝ → ℝ := fun s => Real.log (c2CompletedOnRealSpectralAxis s)
  have hshift := congrFun (iteratedDeriv_comp_const_add (2 * n + 2) f (1 / 2)) 0
  rw [add_zero] at hshift
  rw [c2ClockCorrectedCumulant_eq_completedLogJet, ← hshift,
    c2CompletedLog_shift_eventuallyEq_even.iteratedDeriv_eq,
    iteratedDeriv_const_add (by omega : 0 < 2 * n + 2)]
  exact c2NormalizedEvenLog_neg_sq_iteratedDeriv_eq_canonical n

theorem c2ClockCanonicalMoment_eq_correctedCumulant (n : ℕ) :
    canonicalCompletedNativeLogDerivativeMoment n =
      (-1 : ℝ) ^ n * correctedCumulantEntry c2ClockCorrectedCumulant n := by
  let a := (-1 : ℝ) ^ n
  let b : ℝ := 2 * ((2 * n + 1).factorial : ℝ)
  let h := canonicalCompletedNativeLogDerivativeMoment n
  have hb : b ≠ 0 := by dsimp [b]; positivity
  have hsign : a * a = 1 := by
    change (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1
    rw [← mul_pow]
    norm_num
  rw [correctedCumulantEntry, c2ClockCorrectedCumulant_eq_canonical]
  symm
  calc
    _ = (a * a) * h * b / b := by
      change a * (2 * a * ((2 * n + 1).factorial : ℝ) * h / b) = _
      rw [← mul_div_assoc]
      dsimp only [b]
      ac_rfl
    _ = h := by rw [hsign, one_mul, mul_div_cancel_right₀ _ hb]

theorem c2ClockCorrectedCumulantHankel_posDef_iff (N : ℕ) :
    (hankelGram (correctedCumulantEntry c2ClockCorrectedCumulant) N).PosDef ↔
      (hankelGram canonicalCompletedNativeLogDerivativeMoment N).PosDef :=
  correctedCumulantHankel_posDef_iff c2ClockCanonicalMoment_eq_correctedCumulant N

theorem c2ClockCorrectedCumulant_second_minor_pos :
    10 * c2ClockCorrectedCumulant 4 ^ 2 <
      3 * c2ClockCorrectedCumulant 2 * c2ClockCorrectedCumulant 6 :=
  canonical_correctedCumulant_second_minor_pos c2ClockCanonicalMoment_eq_correctedCumulant

end

end CarrySelfAdjointOperator
