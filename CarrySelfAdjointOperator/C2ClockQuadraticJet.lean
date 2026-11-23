import CarrySelfAdjointOperator.C2CorrectedCumulantHankel
import CarrySelfAdjointOperator.CompletedNativeEvenCoordinateResolventBridge

/-! The coefficient transport on the vertical axis of the centered height. -/

open Filter
open scoped Topology NNReal ENNReal

namespace CarrySelfAdjointOperator

noncomputable section

private theorem real_hasFPowerSeriesAt_of_eventually_hasSum
    {g : ℝ → ℝ} {a : ℕ → ℝ}
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), HasSum (fun n : ℕ => t ^ n * a n) (g t)) :
    HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℝ a) 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h
  let r : ℝ≥0 := ⟨ε / 2, by positivity⟩
  have hr₀ : 0 < (r : ℝ) := by change 0 < ε / 2; positivity
  have hrε : (r : ℝ) < ε := by change ε / 2 < ε; linarith
  have hrMem : (r : ℝ) ∈ Metric.ball (0 : ℝ) ε := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hr₀] using hrε
  have hsum : HasSum (fun n : ℕ => (r : ℝ) ^ n * a n) (g r) := hball hrMem
  have hlim := hsum.summable.tendsto_atTop_zero.norm
  simp only [norm_zero, norm_mul, norm_pow, Real.norm_of_nonneg r.coe_nonneg] at hlim
  have hradius : (r : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℝ a).radius := by
    apply FormalMultilinearSeries.le_radius_of_tendsto
    simpa only [FormalMultilinearSeries.ofScalars_norm, mul_comm] using hlim
  refine ⟨(r : ℝ≥0∞), hradius, by exact_mod_cast hr₀, ?_⟩
  intro t ht
  rw [Metric.eball_coe] at ht
  have ht' : t ∈ Metric.ball (0 : ℝ) ε :=
    Metric.ball_subset_ball hrε.le ht
  have hval : HasSum (fun n : ℕ => t ^ n * a n) (g t) := hball ht'
  simpa only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm]
    using hval

def c2NormalizedEvenLog (u : ℂ) : ℂ :=
  Complex.log (completedNativeEvenCharacteristic u / completedNativeEvenCharacteristic 0)

private theorem c2NormalizedEvenLog_analyticAt : AnalyticAt ℂ c2NormalizedEvenLog 0 := by
  have h₀ := completedNativeEvenCharacteristic_zero_ne_zero
  apply (completedNativeEvenCharacteristic_analyticAt.div analyticAt_const h₀).clog
  change completedNativeEvenCharacteristic 0 / completedNativeEvenCharacteristic 0 ∈
    Complex.slitPlane
  rw [div_self h₀]
  simp

private def quadraticRealCoeff (b : ℕ → ℂ) (k : ℕ) : ℝ :=
  if k % 2 = 0 then
    (-1 : ℝ) ^ (k / 2) * (b (k / 2)).re
  else 0

private theorem quadraticRealCoeff_hasSum {b : ℕ → ℂ} {t : ℝ} {z : ℂ}
    (h : HasSum (fun j : ℕ => b j * (-(t : ℂ) ^ 2) ^ j) z) :
    HasSum (fun k : ℕ => t ^ k * quadraticRealCoeff b k) z.re := by
  have hre : HasSum (fun j : ℕ => (b j * (-(t : ℂ) ^ 2) ^ j).re) z.re :=
    Complex.reCLM.hasSum h
  have hev : HasSum (fun j : ℕ => t ^ (2 * j) * quadraticRealCoeff b (2 * j)) z.re := by
    refine hre.congr_fun (fun j => ?_)
    symm
    have hpow : (-(t : ℂ) ^ 2) ^ j = ((t ^ (2 * j) * (-1 : ℝ) ^ j : ℝ) : ℂ) := by
      push_cast
      rw [neg_pow, pow_mul, mul_comm]
    rw [hpow]
    simp only [quadraticRealCoeff, show 2 * j % 2 = 0 by omega, if_pos,
      show 2 * j / 2 = j by omega, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    ac_rfl
  have hod : HasSum (fun j : ℕ => t ^ (2 * j + 1) * quadraticRealCoeff b (2 * j + 1)) 0 := by
    refine hasSum_zero.congr_fun (fun j => ?_)
    simp [quadraticRealCoeff]
  have hall : HasSum (fun k : ℕ => t ^ k * quadraticRealCoeff b k) (z.re + 0) :=
    HasSum.even_add_odd hev hod
  rwa [add_zero] at hall

private def normalizedEvenLogCoeff (j : ℕ) : ℂ :=
  iteratedDeriv j c2NormalizedEvenLog 0 / j.factorial

private def c2LogQuadraticCoeff : ℕ → ℝ := quadraticRealCoeff normalizedEvenLogCoeff

private theorem c2NormalizedEvenLog_neg_sq_hasFPowerSeriesAt :
    HasFPowerSeriesAt (fun t : ℝ => (c2NormalizedEvenLog (-(t : ℂ) ^ 2)).re)
      (FormalMultilinearSeries.ofScalars ℝ c2LogQuadraticCoeff) 0 := by
  apply real_hasFPowerSeriesAt_of_eventually_hasSum
  have hsum : ∀ᶠ u : ℂ in 𝓝 0,
      HasSum (fun j : ℕ => normalizedEvenLogCoeff j * u ^ j) (c2NormalizedEvenLog u) := by
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, normalizedEvenLogCoeff,
      zero_add]
      using
      c2NormalizedEvenLog_analyticAt.hasFPowerSeriesAt.eventually_hasSum
  have ht : Tendsto (fun t : ℝ => -(t : ℂ) ^ 2) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => -(t : ℂ) ^ 2) 0 := by fun_prop
    simpa using hc.tendsto
  filter_upwards [ht.eventually hsum] with t hs
  exact quadraticRealCoeff_hasSum hs

/-- On the rotated height germ, the even-coordinate log jet gives the
canonical moment with precisely the quadratic sign and factorial. -/
theorem c2NormalizedEvenLog_neg_sq_iteratedDeriv_eq_canonical (n : ℕ) :
    iteratedDeriv (2 * n + 2)
        (fun t : ℝ => (c2NormalizedEvenLog (-(t : ℂ) ^ 2)).re) 0 =
      2 * (-1 : ℝ) ^ n * ((2 * n + 1).factorial : ℝ) *
        canonicalCompletedNativeLogDerivativeMoment n := by
  let F : ℝ → ℝ := fun t => (c2NormalizedEvenLog (-(t : ℂ) ^ 2)).re
  let k := 2 * n + 2
  have hseries := c2NormalizedEvenLog_neg_sq_hasFPowerSeriesAt
  have hp := hseries.eq_formalMultilinearSeries hseries.analyticAt.hasFPowerSeriesAt
  have hc := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ =>
    p k (fun _ : Fin k => (1 : ℝ))) hp
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one] at hc
  change c2LogQuadraticCoeff k = iteratedDeriv k F 0 / (k.factorial : ℝ) at hc
  have hFac : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hval := (eq_div_iff hFac).mp hc
  have hn : k / 2 = n + 1 := by dsimp [k]; omega
  rw [c2LogQuadraticCoeff, quadraticRealCoeff,
    if_pos (show k % 2 = 0 by dsimp [k]; omega), hn, normalizedEvenLogCoeff] at hval
  rw [show iteratedDeriv (n + 1) c2NormalizedEvenLog 0 =
        -(n.factorial : ℂ) * (canonicalCompletedNativeLogDerivativeMoment n : ℂ) by
          exact canonicalEvenLogJet_eq_moment n,
    ← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
    ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re] at hval
  change iteratedDeriv k F 0 = _
  rw [← hval, show k = 2 * n + 1 + 1 by rfl,
    Nat.factorial_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul, pow_succ]
  push_cast
  have hnF : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp
  ring

end

end CarrySelfAdjointOperator
