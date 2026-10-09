import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Complex.Basic

/-!
# Relative perturbations in a fixed finite dimension

Compactness controls the complete quadratic correction, including all crosses.
The neighborhood is obtained AFTER fixing n and its boundary coercivity.
This lemma asserts no dimension-independent threshold and proves no source sign.
-/
namespace CarrySelfAdjointOperator
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- A continuous, homogeneous complete correction is relatively small in each
fixed dimension with an already-certified boundary margin. -/
theorem fixedFiniteQuadratic_relative_control (n : ℕ)
    (S : ℝ → (Fin n → ℂ) → ℝ) (E : (Fin n → ℂ) → ℝ)
    (hzero : ∀ x, S 0 x = E x)
    (hcont : ∀ x, ContinuousAt (fun y : ℝ × (Fin n → ℂ) => S y.1 y.2) (0,x))
    (hhom : ∀ h z x, S h (z • x) = Complex.normSq z * S h x)
    (ε : ℝ) (hε : 0 < ε) (hmargin : ∀ x, ε * ‖x‖^2 ≤ E x)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ h : ℝ in nhds 0, ∀ x, |S h x - E x| ≤ η * E x := by
  have hEh (z : ℂ) (x : Fin n → ℂ) : E (z • x) = Complex.normSq z * E x := by
    rw [← hzero, hhom, hzero]
  have hEc : Continuous (fun x : Fin n → ℂ => E x) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hc : ContinuousAt (fun u : Fin n → ℂ => ((0 : ℝ),u)) x := by fun_prop
    have ht := (hcont x).comp_of_eq hc rfl
    change ContinuousAt (fun u => S 0 u) x at ht
    simpa only [hzero] using ht
  let K : Set (Fin n → ℂ) := Metric.sphere 0 1
  have hK : IsCompact K := isCompact_sphere 0 1
  have hl : ∀ x ∈ K, ∀ᶠ y : ℝ × (Fin n → ℂ) in nhds (0,x),
      |S y.1 y.2 - E y.2| < η * ε := by
    intro x _
    have hc := ((hcont x).sub (hEc.comp continuous_snd).continuousAt).abs
    apply hc.tendsto.eventually_lt tendsto_const_nhds
    change |S 0 x - E x| < η * ε
    simpa only [hzero, sub_self, abs_zero] using mul_pos hη hε
  have hu := hK.eventually_forall_of_forall_eventually
    (x₀ := (0 : ℝ)) (P := fun h x => |S h x - E x| < η * ε) hl
  filter_upwards [hu] with h hh
  intro x
  by_cases hx : x = 0
  · subst x
    have hs : S h 0 = 0 := by simpa using hhom h (0 : ℂ) (0 : Fin n → ℂ)
    have he : E 0 = 0 := by simpa using hEh (0 : ℂ) (0 : Fin n → ℂ)
    simp [hs, he]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let z : ℂ := (‖x‖⁻¹ : ℝ)
    have hz : 0 < Complex.normSq z := by
      apply Complex.normSq_pos.mpr
      change ((‖x‖⁻¹ : ℝ) : ℂ) ≠ 0
      exact_mod_cast inv_ne_zero hn
    have hunit : ‖z • x‖ = 1 := by
      simp [z, norm_smul, Complex.norm_real, norm_inv, inv_mul_cancel₀ hn]
    have ht := (hh (z • x) (by simpa only [K, Metric.mem_sphere, dist_zero_right] using hunit)).le
    have hm := hmargin (z • x)
    rw [hunit] at hm
    norm_num only [one_pow, mul_one] at hm
    have hb := ht.trans (mul_le_mul_of_nonneg_left hm hη.le)
    rw [hhom, hEh, ← mul_sub, abs_mul, abs_of_pos hz] at hb
    nlinarith

/-- The threshold is inside the fixed-dimension quantifiers. -/
theorem fixedFiniteQuadratic_positive_radius (n : ℕ)
    (S : ℝ → (Fin n → ℂ) → ℝ) (E : (Fin n → ℂ) → ℝ)
    (hzero : ∀ x, S 0 x = E x)
    (hcont : ∀ x, ContinuousAt (fun y : ℝ × (Fin n → ℂ) => S y.1 y.2) (0,x))
    (hhom : ∀ h z x, S h (z • x) = Complex.normSq z * S h x)
    (ε : ℝ) (hε : 0 < ε) (hmargin : ∀ x, ε * ‖x‖^2 ≤ E x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ → ∀ x, x ≠ 0 → 0 < S h x := by
  have hc := fixedFiniteQuadratic_relative_control n S E hzero hcont hhom
    ε hε hmargin (1/2) (by norm_num)
  obtain ⟨δ,hδ,hb⟩ := Metric.eventually_nhds_iff.mp hc
  refine ⟨δ,hδ,?_⟩
  intro h hh x hx
  have he : 0 < E x := lt_of_lt_of_le (mul_pos hε (sq_pos_of_ne_zero
    (norm_ne_zero_iff.mpr hx))) (hmargin x)
  have hr := hb (by simpa [Real.dist_eq] using hh) x
  have hlo := neg_abs_le (S h x - E x)
  linarith
end
end CarrySelfAdjointOperator
