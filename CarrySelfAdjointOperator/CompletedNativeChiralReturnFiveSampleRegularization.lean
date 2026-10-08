import CarrySelfAdjointOperator.CompletedNativeChiralReturnFiveBoundaryReconstruction
import CarrySelfAdjointOperator.CompletedNativeChiralReturnTenthSourceIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Continuous full-source regularization on the five-sample boundary chart

All higher boundary coordinates and the entire analytic source remainder
are retained. Compactness is used only in a finite source-coordinate chart;
it does not change the original Cauchy inner product.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology ChiralReturn
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- The complete order-nine Green boundary expression in regular coordinates. -/
def radialFiveRegularizedBoundaryEnergy (h : ℝ) (x : Fin 5 → ℂ) : ℝ :=
  2 * ∑ j ∈ Finset.range 5, (-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j *
    (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
      (conj (radialFiveRegularizedBoundary h x a) *
        radialFiveRegularizedBoundary h x (2*j-a)).re)

/-- The exact analytic source remainder, with every Cauchy cross retained.
The factor h comes from h^10 in the source, h^-8 in the reconstructed inputs,
and h^-1 in the original Cauchy feature metric. -/
def radialFiveRegularizedRemainderEnergy (R : ℂ → ℂ) (h : ℝ) (x : Fin 5 → ℂ) : ℝ :=
  4*h * (∑ i : Fin 5, ∑ j : Fin 5,
    conj (radialFiveRegularizedInput h x i) * radialFiveRegularizedInput h x j *
      (((j : ℕ)+1 : ℕ) : ℂ)^10 * R (((((j : ℕ)+1 : ℕ) : ℝ)*h : ℝ) : ℂ) /
        (((i : ℕ)+(j : ℕ)+2 : ℕ) : ℂ)).re

/-- Full regularized source storage, not a new source or metric. -/
def radialFiveRegularizedStorage (R : ℂ → ℂ) (h : ℝ) (x : Fin 5 → ℂ) : ℝ :=
  radialFiveRegularizedBoundaryEnergy h x + radialFiveRegularizedRemainderEnergy R h x

theorem radialFiveRegularizedStorage_zero (R : ℂ → ℂ) (x : Fin 5 → ℂ) :
    radialFiveRegularizedStorage R 0 x = nativeSourceFiveBoundaryEnergy x := by
  simp only [radialFiveRegularizedStorage, radialFiveRegularizedRemainderEnergy,
    mul_zero, zero_mul, add_zero, radialFiveRegularizedBoundaryEnergy]
  simp_rw [radialFiveRegularizedBoundary_zero]
  exact (nativeSourceFiveBoundaryEnergy_eq_alternating_green x).symm

theorem radialFiveRegularizedBoundary_continuous (m : ℕ) :
    Continuous (fun y : ℝ × (Fin 5 → ℂ) => radialFiveRegularizedBoundary y.1 y.2 m) := by
  unfold radialFiveRegularizedBoundary
  split_ifs with hm <;> fun_prop

theorem radialFiveRegularizedInput_continuous (i : Fin 5) :
    Continuous (fun y : ℝ × (Fin 5 → ℂ) => radialFiveRegularizedInput y.1 y.2 i) := by
  unfold radialFiveRegularizedInput
  fun_prop

theorem radialFiveRegularizedStorage_continuousAt (R : ℂ → ℂ)
    (hR : ContinuousAt R 0) (x : Fin 5 → ℂ) :
    ContinuousAt (fun y : ℝ × (Fin 5 → ℂ) => radialFiveRegularizedStorage R y.1 y.2) (0,x) := by
  have hb (a b : ℕ) : Continuous (fun y : ℝ × (Fin 5 → ℂ) =>
      (conj (radialFiveRegularizedBoundary y.1 y.2 a) *
        radialFiveRegularizedBoundary y.1 y.2 b).re) :=
    Complex.continuous_re.comp ((Complex.continuous_conj.comp
      (radialFiveRegularizedBoundary_continuous a)).mul
        (radialFiveRegularizedBoundary_continuous b))
  have hp : Continuous (fun y : ℝ × (Fin 5 → ℂ) => radialFiveRegularizedBoundaryEnergy y.1 y.2) := by
    unfold radialFiveRegularizedBoundaryEnergy
    fun_prop
  have hi (i : Fin 5) : ContinuousAt
      (fun y : ℝ × (Fin 5 → ℂ) => radialFiveRegularizedInput y.1 y.2 i) (0,x) :=
    (radialFiveRegularizedInput_continuous i).continuousAt
  have hr (j : Fin 5) : ContinuousAt
      (fun y : ℝ × (Fin 5 → ℂ) => R (((((j : ℕ)+1 : ℕ) : ℝ)*y.1 : ℝ) : ℂ)) (0,x) := by
    have ht : ContinuousAt
        (fun y : ℝ × (Fin 5 → ℂ) => (((((j : ℕ)+1 : ℕ) : ℝ)*y.1 : ℝ) : ℂ)) (0,x) := by
      fun_prop
    exact hR.comp_of_eq ht (by simp)
  have hs : ContinuousAt (fun y : ℝ × (Fin 5 → ℂ) => ∑ i : Fin 5, ∑ j : Fin 5,
      conj (radialFiveRegularizedInput y.1 y.2 i) * radialFiveRegularizedInput y.1 y.2 j *
        (((j : ℕ)+1 : ℕ) : ℂ)^10 * R (((((j : ℕ)+1 : ℕ) : ℝ)*y.1 : ℝ) : ℂ) /
          (((i : ℕ)+(j : ℕ)+2 : ℕ) : ℂ)) (0,x) := by
    apply tendsto_finsetSum Finset.univ
    intro i _
    apply tendsto_finsetSum Finset.univ
    intro j _
    exact ((((Complex.continuous_conj.continuousAt.comp (hi i)).mul (hi j)).mul_const
      ((((j : ℕ)+1 : ℕ) : ℂ)^10)).mul (hr j)).div_const _
  exact hp.continuousAt.add (((continuous_const.mul continuous_fst).continuousAt).mul
    (Complex.continuous_re.continuousAt.comp hs))

theorem radialFiveRegularizedBoundary_smul (h : ℝ) (z : ℂ) (x : Fin 5 → ℂ) (m : ℕ) :
    radialFiveRegularizedBoundary h (z • x) m = z * radialFiveRegularizedBoundary h x m := by
  unfold radialFiveRegularizedBoundary
  split_ifs with hm
  · rfl
  · simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring

theorem radialFiveRegularizedInput_smul (h : ℝ) (z : ℂ) (x : Fin 5 → ℂ) (i : Fin 5) :
    radialFiveRegularizedInput h (z • x) i = z * radialFiveRegularizedInput h x i := by
  simp only [radialFiveRegularizedInput, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Compactness supplies ONE neighborhood for EVERY nonzero five-coordinate
source. This controls all mixed sectors jointly, not one fixed canary. -/
theorem radialFiveRegularizedStorage_eventually_pos_on_unit (R : ℂ → ℂ) (hR : ContinuousAt R 0) :
    ∀ᶠ h : ℝ in nhds 0, ∀ x : Fin 5 → ℂ, ‖x‖ = 1 →
      0 < radialFiveRegularizedStorage R h x := by
  let K : Set (Fin 5 → ℂ) := Metric.sphere 0 1
  have hK : IsCompact K := isCompact_sphere 0 1
  have hl : ∀ x ∈ K, ∀ᶠ y : ℝ × (Fin 5 → ℂ) in nhds (0,x),
      0 < radialFiveRegularizedStorage R y.1 y.2 := by
    intro x hx
    have hnx : x ≠ 0 := by
      intro he
      simp [K, he] at hx
    have hp : 0 < radialFiveRegularizedStorage R 0 x := by
      rw [radialFiveRegularizedStorage_zero]
      exact nativeSourceFiveBoundaryEnergy_pos x hnx
    exact Filter.Tendsto.eventually_lt tendsto_const_nhds
      (radialFiveRegularizedStorage_continuousAt R hR x).tendsto hp
  have hu := hK.eventually_forall_of_forall_eventually
    (x₀ := (0 : ℝ)) (P := fun h x => 0 < radialFiveRegularizedStorage R h x) hl
  filter_upwards [hu] with h hh
  intro x hx
  exact hh x (by simpa only [K, Metric.mem_sphere, dist_zero_right] using hx)


/-- The source-derived strict five-jet face has one positive margin, retained
uniformly on the finite unit sphere for all sufficiently small radial steps. -/
theorem radialFiveRegularizedStorage_eventually_unit_margin (R : ℂ → ℂ) (hR : ContinuousAt R 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ h : ℝ in nhds 0,
      ∀ x : Fin 5 → ℂ, ‖x‖ = 1 → ε < radialFiveRegularizedStorage R h x := by
  let K : Set (Fin 5 → ℂ) := Metric.sphere 0 1
  have hK : IsCompact K := isCompact_sphere 0 1
  have hne : K.Nonempty := by
    refine ⟨(1 : Fin 5 → ℂ), ?_⟩
    simp [K]
  have hf : Continuous nativeSourceFiveBoundaryEnergy := by
    unfold nativeSourceFiveBoundaryEnergy nativeSourceFiveEvenBoundaryEnergy nativeSourceOddBoundaryEnergy
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    fun_prop
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hf.continuousOn
  have hn₀ : x₀ ≠ 0 := by intro he; simp [K, he] at hx₀
  have hp₀ := nativeSourceFiveBoundaryEnergy_pos x₀ hn₀
  let ε := nativeSourceFiveBoundaryEnergy x₀ / 2
  have he : 0 < ε := div_pos hp₀ (by norm_num)
  refine ⟨ε, he, ?_⟩
  have hl : ∀ x ∈ K, ∀ᶠ y : ℝ × (Fin 5 → ℂ) in nhds (0,x),
      ε < radialFiveRegularizedStorage R y.1 y.2 := by
    intro x hx
    have hb : nativeSourceFiveBoundaryEnergy x₀ ≤ nativeSourceFiveBoundaryEnergy x := hmin hx
    have hp : ε < radialFiveRegularizedStorage R 0 x := by
      rw [radialFiveRegularizedStorage_zero]
      dsimp only [ε]
      linarith
    exact Filter.Tendsto.eventually_lt tendsto_const_nhds
      (radialFiveRegularizedStorage_continuousAt R hR x).tendsto hp
  have hu := hK.eventually_forall_of_forall_eventually
    (x₀ := (0 : ℝ)) (P := fun h x => ε < radialFiveRegularizedStorage R h x) hl
  filter_upwards [hu] with h hh
  intro x hx
  exact hh x (by simpa only [K, Metric.mem_sphere, dist_zero_right] using hx)

end
end CarrySelfAdjointOperator
