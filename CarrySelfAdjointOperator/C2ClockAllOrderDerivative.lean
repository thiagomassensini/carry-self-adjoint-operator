import CarrySelfAdjointOperator.C2MellinAllOrderMajorant
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# All derivatives of the Mellin clock

The density is the common density of the two camera channels once their
explicit dyadic mixtures are removed. The logarithmic derivatives of its
integral are the cumulants of the clock after tilting at the center.
-/

namespace CarrySelfAdjointOperator

open Set MeasureTheory Filter
open scoped Topology

noncomputable section

def c2ClockDensity (x : ℝ) : ℝ := (1 + Real.exp x)⁻¹

def c2ClockLogIntegrand (r : ℕ) (s x : ℝ) : ℝ :=
  x ^ (s - 1) * (Real.log x) ^ r * c2ClockDensity x

def c2ClockLogMoment (r : ℕ) (s : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), c2ClockLogIntegrand r s x

private theorem c2ClockDensity_le_exp_neg (x : ℝ) :
    c2ClockDensity x ≤ Real.exp (-x) := by
  unfold c2ClockDensity
  rw [Real.exp_neg]
  exact inv_anti₀ (Real.exp_pos x) (by linarith)

private theorem c2ClockLogIntegrand_aestronglyMeasurable (r : ℕ) (s : ℝ) :
    AEStronglyMeasurable (c2ClockLogIntegrand r s) (volume.restrict (Ioi 0)) := by
  have hcont : ContinuousOn (c2ClockLogIntegrand r s) (Ioi 0) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx₀ : 0 < x := hx
    have hpow := Real.continuousAt_rpow_const x (s - 1) (Or.inl hx₀.ne')
    have hlog := Real.continuousAt_log hx₀.ne'
    have hden : ContinuousAt (fun x : ℝ => 1 + Real.exp x) x :=
      continuousAt_const.add Real.continuous_exp.continuousAt
    have hpos : (1 : ℝ) + Real.exp x ≠ 0 := by positivity
    exact (hpow.mul (hlog.pow r)).mul (hden.inv₀ hpos)
  exact hcont.aestronglyMeasurable measurableSet_Ioi

private theorem c2ClockLogIntegrand_hasDerivAt (r : ℕ) {s x : ℝ}
    (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => c2ClockLogIntegrand r t x)
      (c2ClockLogIntegrand (r + 1) s x) s := by
  have hinner : HasDerivAt (fun t : ℝ => t - 1) 1 s :=
    (hasDerivAt_id s).sub_const 1
  have hpow : HasDerivAt (fun t : ℝ => x ^ (t - 1))
      (x ^ (s - 1) * Real.log x) s := by
    simpa [mul_assoc, smul_eq_mul] using (hinner.hasFDerivAt.const_rpow hx).hasDerivAt
  simpa [c2ClockLogIntegrand, pow_succ, mul_assoc, mul_left_comm, mul_comm]
    using hpow.mul_const ((Real.log x) ^ r * c2ClockDensity x)

private theorem c2ClockLogIntegrand_bound (r : ℕ) {s x : ℝ} (hx : 0 < x)
    (hs : s ∈ Ioo (3 / 8 : ℝ) (5 / 8)) :
    ‖c2ClockLogIntegrand r s x‖ ≤ nativeC2MellinAllOrderMajorant r x := by
  have hρ₀ : 0 ≤ c2ClockDensity x := by unfold c2ClockDensity; positivity
  have hρ : c2ClockDensity x ≤ 2 * Real.exp (-x) := by
    linarith [c2ClockDensity_le_exp_neg x, Real.exp_pos (-x)]
  simpa only [Real.norm_eq_abs, c2ClockLogIntegrand] using
    nativeC2MellinAllOrderMajorant_bound r s x _ hx hs hρ₀ hρ

theorem c2ClockLogIntegrand_integrableOn (r : ℕ) {s : ℝ}
    (hs : s ∈ Ioo (3 / 8 : ℝ) (5 / 8)) :
    IntegrableOn (c2ClockLogIntegrand r s) (Ioi 0) := by
  refine (nativeC2MellinAllOrderMajorant_integrable r).mono'
    (c2ClockLogIntegrand_aestronglyMeasurable r s) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  exact c2ClockLogIntegrand_bound r hx hs

theorem c2ClockLogMoment_hasDerivAt (r : ℕ) {s : ℝ}
    (hs : s ∈ Ioo (3 / 8 : ℝ) (5 / 8)) :
    HasDerivAt (c2ClockLogMoment r) (c2ClockLogMoment (r + 1) s) s := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let S : Set ℝ := Ioo (3 / 8 : ℝ) (5 / 8)
  have hS : S ∈ 𝓝 s := Ioo_mem_nhds hs.1 hs.2
  have hbound : ∀ᵐ x ∂μ, ∀ t ∈ S,
      ‖c2ClockLogIntegrand (r + 1) t x‖ ≤ nativeC2MellinAllOrderMajorant (r + 1) x := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    intro t ht
    exact c2ClockLogIntegrand_bound (r + 1) hx ht
  have hdiff : ∀ᵐ x ∂μ, ∀ t ∈ S,
      HasDerivAt (fun u : ℝ => c2ClockLogIntegrand r u x)
        (c2ClockLogIntegrand (r + 1) t x) t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    intro t _
    exact c2ClockLogIntegrand_hasDerivAt r hx
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := c2ClockLogIntegrand r) (x₀ := s) (s := S) hS
    (by filter_upwards [] with t; exact c2ClockLogIntegrand_aestronglyMeasurable r t)
    (c2ClockLogIntegrand_integrableOn r hs)
    (c2ClockLogIntegrand_aestronglyMeasurable (r + 1) s)
    hbound (nativeC2MellinAllOrderMajorant_integrable (r + 1)) hdiff).2

theorem c2ClockLogMoment_iteratedDeriv (r : ℕ) {s : ℝ}
    (hs : s ∈ Ioo (3 / 8 : ℝ) (5 / 8)) :
    iteratedDeriv r (c2ClockLogMoment 0) s = c2ClockLogMoment r s := by
  induction r generalizing s with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv r (c2ClockLogMoment 0) =ᶠ[𝓝 s] c2ClockLogMoment r := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
      exact ih ht
    exact heq.deriv_eq.trans (c2ClockLogMoment_hasDerivAt r hs).deriv

/-- Cumulants of the logarithmic clock tilted at the critical parameter.
A constant normalization of the total mass does not affect positive orders. -/
def c2ClockCumulant (r : ℕ) : ℝ :=
  iteratedDeriv r (fun s => Real.log (c2ClockLogMoment 0 s)) (1 / 2)

/-- Exact splitting of the real logarithmic jet when a completed germ is
identified with the Mellin source times its correction. -/
theorem c2Clock_logJet_of_eventuallyEq_mul (r : ℕ) {F D : ℝ → ℝ}
    (hfactor : F =ᶠ[𝓝 (1 / 2 : ℝ)] fun s => D s * c2ClockLogMoment 0 s)
    (hD : ContDiffAt ℝ r D (1 / 2)) (hD₀ : D (1 / 2) ≠ 0)
    (hI : ContDiffAt ℝ r (c2ClockLogMoment 0) (1 / 2))
    (hI₀ : c2ClockLogMoment 0 (1 / 2) ≠ 0) :
    iteratedDeriv r (fun s => Real.log (F s)) (1 / 2) =
      c2ClockCumulant r + iteratedDeriv r (fun s => Real.log (D s)) (1 / 2) := by
  have heq : (fun s => Real.log (F s)) =ᶠ[𝓝 (1 / 2 : ℝ)]
      (fun s => Real.log (D s) + Real.log (c2ClockLogMoment 0 s)) := by
    filter_upwards [hfactor, hD.continuousAt.eventually_ne hD₀,
      hI.continuousAt.eventually_ne hI₀] with s hs hd hi
    rw [hs, Real.log_mul hd hi]
  rw [heq.iteratedDeriv_eq, ← Pi.add_def,
    iteratedDeriv_add (hD.log hD₀) (hI.log hI₀), c2ClockCumulant, add_comm]

/-- The common dyadic camera factor and the original archimedean
completion, after cancelling the Mellin Gamma. -/
def c2ClockCompletionCorrection (s : ℝ) : ℝ :=
  (s * (s - 1) * Real.pi ^ (-s / 2) * Real.Gamma (s / 2)) /
    (2 * Real.Gamma s * (1 - (2 : ℝ) ^ (1 - s)))

def c2ClockCorrectedCumulant (r : ℕ) : ℝ :=
  c2ClockCumulant r +
    iteratedDeriv r (fun s => Real.log (c2ClockCompletionCorrection s)) (1 / 2)

theorem c2ClockCorrectedCumulant_eq_logJet_of_factor (r : ℕ) {F : ℝ → ℝ}
    (hfactor : F =ᶠ[𝓝 (1 / 2 : ℝ)]
      fun s => c2ClockCompletionCorrection s * c2ClockLogMoment 0 s)
    (hD : ContDiffAt ℝ r c2ClockCompletionCorrection (1 / 2))
    (hD₀ : c2ClockCompletionCorrection (1 / 2) ≠ 0)
    (hI : ContDiffAt ℝ r (c2ClockLogMoment 0) (1 / 2))
    (hI₀ : c2ClockLogMoment 0 (1 / 2) ≠ 0) :
    c2ClockCorrectedCumulant r = iteratedDeriv r (fun s => Real.log (F s)) (1 / 2) :=
  (c2Clock_logJet_of_eventuallyEq_mul r hfactor hD hD₀ hI hI₀).symm

end

end CarrySelfAdjointOperator
