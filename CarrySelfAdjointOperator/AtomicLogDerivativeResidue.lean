import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic

/-!
# Local multiplicity of a logarithmic-derivative readout

An analytic characteristic of finite order has an integer logarithmic residue.
The statements are local and do not assume a global spectral identification.
-/

open Filter Topology

namespace CarrySelfAdjointOperator

/-- The logarithmic residue retains the complete analytic multiplicity,
including order zero at a nonzero value of the characteristic. -/
theorem tendsto_mul_logDeriv_eq_analyticOrderNatAt
    {F : ℂ → ℂ} {a : ℂ} (hF : AnalyticAt ℂ F a)
    (hfinite : analyticOrderAt F a ≠ ⊤) :
    Tendsto (fun z => (z - a) * logDeriv F z) (𝓝[≠] a)
      (𝓝 (analyticOrderNatAt F a : ℂ)) := by
  obtain ⟨g, hg, hg0, heq⟩ := hF.analyticOrderAt_ne_top.mp hfinite
  have heq' : F =ᶠ[𝓝 a]
      (fun z => (z - a) ^ analyticOrderNatAt F a * g z) := by
    simpa only [smul_eq_mul] using heq
  have hgnz : ∀ᶠ z in 𝓝 a, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  have hlocal : (fun z => (z - a) * logDeriv F z) =ᶠ[𝓝[≠] a]
      (fun z => (analyticOrderNatAt F a : ℂ) + (z - a) * logDeriv g z) := by
    filter_upwards [heq'.filter_mono nhdsWithin_le_nhds,
      heq'.deriv.filter_mono nhdsWithin_le_nhds,
      hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      hgnz.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hdz hgz hgnz hzneq
    have hza : z - a ≠ 0 := sub_ne_zero.mpr hzneq
    have hlin : DifferentiableAt ℂ (fun w : ℂ => w - a) z := by fun_prop
    have hpow : DifferentiableAt ℂ
        (fun w : ℂ => (w - a) ^ analyticOrderNatAt F a) z := hlin.pow _
    have hlog : logDeriv F z =
        logDeriv (fun w => (w - a) ^ analyticOrderNatAt F a * g w) z := by
      simp only [logDeriv_apply, hz, hdz]
    rw [hlog, logDeriv_mul (f := fun w => (w - a) ^ analyticOrderNatAt F a)
      (g := g) z (pow_ne_zero _ hza) hgnz hpow hgz.differentiableAt,
      logDeriv_fun_pow hlin]
    simp only [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
    field_simp
  have hcont : ContinuousAt (logDeriv g) a := by
    exact hg.deriv.continuousAt.div hg.continuousAt hg0
  have hlim : Tendsto
      (fun z => (analyticOrderNatAt F a : ℂ) + (z - a) * logDeriv g z)
      (𝓝[≠] a) (𝓝 (analyticOrderNatAt F a : ℂ)) := by
    have hc : ContinuousAt
        (fun z => (analyticOrderNatAt F a : ℂ) + (z - a) * logDeriv g z) a := by
      fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  exact hlim.congr' hlocal.symm

/-- The readout `-F'/(2F)` has residue minus one half of the zero's integer order. -/
theorem tendsto_mul_neg_half_logDeriv_eq_analyticOrderNatAt
    {F : ℂ → ℂ} {a : ℂ} (hF : AnalyticAt ℂ F a)
    (hfinite : analyticOrderAt F a ≠ ⊤) :
    Tendsto (fun z => (z - a) * (-logDeriv F z / 2)) (𝓝[≠] a)
      (𝓝 (-(analyticOrderNatAt F a : ℂ) / 2)) := by
  convert (tendsto_mul_logDeriv_eq_analyticOrderNatAt hF hfinite).neg.div_const 2 using 1
  ext z
  ring

/-- The residue of one parity-resolvent atom is its mass divided by twice
its eigenvalue, with the sign fixed by the denominator `1 - v z²`. -/
theorem tendsto_mul_atomicParityReadout
    {a v w : ℂ} (ha : a ≠ 0) (hroot : v * a ^ 2 = 1) :
    Tendsto (fun z : ℂ => (z - a) * (w * z / (1 - v * z ^ 2)))
      (𝓝[≠] a) (𝓝 (-w / (2 * v))) := by
  have hv : v ≠ 0 := by
    intro h
    simp [h] at hroot
  have haa : a + a ≠ 0 := by
    simpa only [two_mul] using mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) ha
  have hplus : ∀ᶠ z : ℂ in 𝓝 a, z + a ≠ 0 :=
    (continuousAt_id.add_const a).eventually_ne haa
  have heq : (fun z : ℂ => (z - a) * (w * z / (1 - v * z ^ 2))) =ᶠ[𝓝[≠] a]
      (fun z => -w * z / (v * (z + a))) := by
    filter_upwards [hplus.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with z hzp hza
    have hzsub : z - a ≠ 0 := sub_ne_zero.mpr hza
    have hden : 1 - v * z ^ 2 = -v * (z - a) * (z + a) := by
      calc
        1 - v * z ^ 2 = v * a ^ 2 - v * z ^ 2 := by rw [hroot]
        _ = -v * (z - a) * (z + a) := by ring
    rw [hden]
    field_simp
  have hc : ContinuousAt (fun z : ℂ => -w * z / (v * (z + a))) a := by
    fun_prop (disch := exact mul_ne_zero hv haa)
  have hval : -w * a / (v * (a + a)) = -w / (2 * v) := by
    field_simp
    ring
  have ht : Tendsto (fun z : ℂ => -w * z / (v * (z + a))) (𝓝[≠] a)
      (𝓝 (-w * a / (v * (a + a)))) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  rw [hval] at ht
  exact ht.congr' heq.symm

/-- A continuous local remainder does not change the atomic residue. -/
theorem tendsto_mul_atomicParityReadout_add
    {a v w : ℂ} {R : ℂ → ℂ} (ha : a ≠ 0) (hroot : v * a ^ 2 = 1)
    (hR : ContinuousAt R a) :
    Tendsto (fun z : ℂ => (z - a) * (w * z / (1 - v * z ^ 2) + R z))
      (𝓝[≠] a) (𝓝 (-w / (2 * v))) := by
  have hrem : Tendsto (fun z : ℂ => (z - a) * R z) (𝓝[≠] a) (𝓝 0) := by
    have hc : ContinuousAt (fun z : ℂ => (z - a) * R z) a := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  convert (tendsto_mul_atomicParityReadout (w := w) ha hroot).add hrem using 1 <;>
    simp only [mul_add, add_zero]

/-- If an atomic readout agrees locally with `-F'/(2F)`, its mass divided by
its eigenvalue must equal the integer analytic multiplicity. The remainder
only needs continuity, so an analytic remainder is sufficient. -/
theorem atomicParityReadout_mass_div_eigenvalue_eq_analyticOrderNatAt
    {F R : ℂ → ℂ} {a v w : ℂ} (hF : AnalyticAt ℂ F a)
    (hfinite : analyticOrderAt F a ≠ ⊤) (ha : a ≠ 0)
    (hroot : v * a ^ 2 = 1) (hR : ContinuousAt R a)
    (hreadout : (fun z => -logDeriv F z / 2) =ᶠ[𝓝[≠] a]
      (fun z => w * z / (1 - v * z ^ 2) + R z)) :
    w / v = (analyticOrderNatAt F a : ℂ) := by
  have hsame : (fun z => (z - a) * (-logDeriv F z / 2)) =ᶠ[𝓝[≠] a]
      (fun z => (z - a) * (w * z / (1 - v * z ^ 2) + R z)) :=
    hreadout.mono fun z hz => congrArg ((z - a) * ·) hz
  have heq := tendsto_nhds_unique
    (tendsto_mul_neg_half_logDeriv_eq_analyticOrderNatAt hF hfinite)
    ((tendsto_mul_atomicParityReadout_add ha hroot hR).congr' hsame.symm)
  have hv : v ≠ 0 := by
    intro h
    simp [h] at hroot
  field_simp at heq ⊢
  linear_combination heq

end CarrySelfAdjointOperator
