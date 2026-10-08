import CarrySelfAdjointOperator.CompletedNativeChiralReturnFourBoundaryReconstruction
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Continuous full-source regularization on the four-sample boundary chart

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

/-- The complete order-seven Green boundary expression in regular coordinates. -/
def radialFourRegularizedBoundaryEnergy (h : ℝ) (x : Fin 4 → ℂ) : ℝ :=
  2 * ∑ j ∈ Finset.range 4, (-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j *
    (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
      (conj (radialFourRegularizedBoundary h x a) *
        radialFourRegularizedBoundary h x (2*j-a)).re)

/-- The exact analytic source remainder, with every Cauchy cross retained.
The factor h comes from h^8 in the source, h^-6 in the reconstructed inputs,
and h^-1 in the original Cauchy feature metric. -/
def radialFourRegularizedRemainderEnergy (R : ℂ → ℂ) (h : ℝ) (x : Fin 4 → ℂ) : ℝ :=
  4*h * (∑ i : Fin 4, ∑ j : Fin 4,
    conj (radialFourRegularizedInput h x i) * radialFourRegularizedInput h x j *
      (((j : ℕ)+1 : ℕ) : ℂ)^8 * R (((((j : ℕ)+1 : ℕ) : ℝ)*h : ℝ) : ℂ) /
        (((i : ℕ)+(j : ℕ)+2 : ℕ) : ℂ)).re

/-- Full regularized source storage, not a new source or metric. -/
def radialFourRegularizedStorage (R : ℂ → ℂ) (h : ℝ) (x : Fin 4 → ℂ) : ℝ :=
  radialFourRegularizedBoundaryEnergy h x + radialFourRegularizedRemainderEnergy R h x

theorem radialFourRegularizedStorage_zero (R : ℂ → ℂ) (x : Fin 4 → ℂ) :
    radialFourRegularizedStorage R 0 x = nativeSourceFourBoundaryEnergy x := by
  simp only [radialFourRegularizedStorage, radialFourRegularizedRemainderEnergy,
    mul_zero, zero_mul, add_zero, radialFourRegularizedBoundaryEnergy]
  simp_rw [radialFourRegularizedBoundary_zero]
  exact (nativeSourceFourBoundaryEnergy_eq_alternating_green x).symm

theorem radialFourRegularizedBoundary_continuous (m : ℕ) :
    Continuous (fun y : ℝ × (Fin 4 → ℂ) => radialFourRegularizedBoundary y.1 y.2 m) := by
  unfold radialFourRegularizedBoundary
  split_ifs with hm <;> fun_prop

theorem radialFourRegularizedInput_continuous (i : Fin 4) :
    Continuous (fun y : ℝ × (Fin 4 → ℂ) => radialFourRegularizedInput y.1 y.2 i) := by
  unfold radialFourRegularizedInput
  fun_prop

theorem radialFourRegularizedStorage_continuousAt (R : ℂ → ℂ)
    (hR : ContinuousAt R 0) (x : Fin 4 → ℂ) :
    ContinuousAt (fun y : ℝ × (Fin 4 → ℂ) => radialFourRegularizedStorage R y.1 y.2) (0,x) := by
  have hb (a b : ℕ) : Continuous (fun y : ℝ × (Fin 4 → ℂ) =>
      (conj (radialFourRegularizedBoundary y.1 y.2 a) *
        radialFourRegularizedBoundary y.1 y.2 b).re) :=
    Complex.continuous_re.comp ((Complex.continuous_conj.comp
      (radialFourRegularizedBoundary_continuous a)).mul
        (radialFourRegularizedBoundary_continuous b))
  have hp : Continuous (fun y : ℝ × (Fin 4 → ℂ) => radialFourRegularizedBoundaryEnergy y.1 y.2) := by
    unfold radialFourRegularizedBoundaryEnergy
    fun_prop
  have hi (i : Fin 4) : ContinuousAt
      (fun y : ℝ × (Fin 4 → ℂ) => radialFourRegularizedInput y.1 y.2 i) (0,x) :=
    (radialFourRegularizedInput_continuous i).continuousAt
  have hr (j : Fin 4) : ContinuousAt
      (fun y : ℝ × (Fin 4 → ℂ) => R (((((j : ℕ)+1 : ℕ) : ℝ)*y.1 : ℝ) : ℂ)) (0,x) := by
    have ht : ContinuousAt
        (fun y : ℝ × (Fin 4 → ℂ) => (((((j : ℕ)+1 : ℕ) : ℝ)*y.1 : ℝ) : ℂ)) (0,x) := by
      fun_prop
    exact hR.comp_of_eq ht (by simp)
  have hs : ContinuousAt (fun y : ℝ × (Fin 4 → ℂ) => ∑ i : Fin 4, ∑ j : Fin 4,
      conj (radialFourRegularizedInput y.1 y.2 i) * radialFourRegularizedInput y.1 y.2 j *
        (((j : ℕ)+1 : ℕ) : ℂ)^8 * R (((((j : ℕ)+1 : ℕ) : ℝ)*y.1 : ℝ) : ℂ) /
          (((i : ℕ)+(j : ℕ)+2 : ℕ) : ℂ)) (0,x) := by
    apply tendsto_finsetSum Finset.univ
    intro i _
    apply tendsto_finsetSum Finset.univ
    intro j _
    exact ((((Complex.continuous_conj.continuousAt.comp (hi i)).mul (hi j)).mul_const
      ((((j : ℕ)+1 : ℕ) : ℂ)^8)).mul (hr j)).div_const _
  exact hp.continuousAt.add (((continuous_const.mul continuous_fst).continuousAt).mul
    (Complex.continuous_re.continuousAt.comp hs))

theorem radialFourRegularizedBoundary_smul (h : ℝ) (z : ℂ) (x : Fin 4 → ℂ) (m : ℕ) :
    radialFourRegularizedBoundary h (z • x) m = z * radialFourRegularizedBoundary h x m := by
  unfold radialFourRegularizedBoundary
  split_ifs with hm
  · rfl
  · simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring

theorem radialFourRegularizedInput_smul (h : ℝ) (z : ℂ) (x : Fin 4 → ℂ) (i : Fin 4) :
    radialFourRegularizedInput h (z • x) i = z * radialFourRegularizedInput h x i := by
  simp only [radialFourRegularizedInput, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Compactness supplies ONE neighborhood for EVERY nonzero four-coordinate
source. This controls all mixed sectors jointly, not one fixed canary. -/
theorem radialFourRegularizedStorage_eventually_pos_on_unit (R : ℂ → ℂ) (hR : ContinuousAt R 0) :
    ∀ᶠ h : ℝ in nhds 0, ∀ x : Fin 4 → ℂ, ‖x‖ = 1 →
      0 < radialFourRegularizedStorage R h x := by
  let K : Set (Fin 4 → ℂ) := Metric.sphere 0 1
  have hK : IsCompact K := isCompact_sphere 0 1
  have hl : ∀ x ∈ K, ∀ᶠ y : ℝ × (Fin 4 → ℂ) in nhds (0,x),
      0 < radialFourRegularizedStorage R y.1 y.2 := by
    intro x hx
    have hnx : x ≠ 0 := by
      intro he
      simp [K, he] at hx
    have hp : 0 < radialFourRegularizedStorage R 0 x := by
      rw [radialFourRegularizedStorage_zero]
      exact nativeSourceFourBoundaryEnergy_pos x hnx
    exact Filter.Tendsto.eventually_lt tendsto_const_nhds
      (radialFourRegularizedStorage_continuousAt R hR x).tendsto hp
  have hu := hK.eventually_forall_of_forall_eventually
    (x₀ := (0 : ℝ)) (P := fun h x => 0 < radialFourRegularizedStorage R h x) hl
  filter_upwards [hu] with h hh
  intro x hx
  exact hh x (by simpa only [K, Metric.mem_sphere, dist_zero_right] using hx)


/-- The source-derived strict four-jet face has one positive margin, retained
uniformly on the finite unit sphere for all sufficiently small radial steps. -/
theorem radialFourRegularizedStorage_eventually_unit_margin (R : ℂ → ℂ) (hR : ContinuousAt R 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ h : ℝ in nhds 0,
      ∀ x : Fin 4 → ℂ, ‖x‖ = 1 → ε < radialFourRegularizedStorage R h x := by
  let K : Set (Fin 4 → ℂ) := Metric.sphere 0 1
  have hK : IsCompact K := isCompact_sphere 0 1
  have hne : K.Nonempty := by
    refine ⟨(1 : Fin 4 → ℂ), ?_⟩
    simp [K]
  have hf : Continuous nativeSourceFourBoundaryEnergy := by
    unfold nativeSourceFourBoundaryEnergy nativeSourceEvenBoundaryEnergy nativeSourceOddBoundaryEnergy
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    fun_prop
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hf.continuousOn
  have hn₀ : x₀ ≠ 0 := by intro he; simp [K, he] at hx₀
  have hp₀ := nativeSourceFourBoundaryEnergy_pos x₀ hn₀
  let ε := nativeSourceFourBoundaryEnergy x₀ / 2
  have he : 0 < ε := div_pos hp₀ (by norm_num)
  refine ⟨ε, he, ?_⟩
  have hl : ∀ x ∈ K, ∀ᶠ y : ℝ × (Fin 4 → ℂ) in nhds (0,x),
      ε < radialFourRegularizedStorage R y.1 y.2 := by
    intro x hx
    have hb : nativeSourceFourBoundaryEnergy x₀ ≤ nativeSourceFourBoundaryEnergy x := hmin hx
    have hp : ε < radialFourRegularizedStorage R 0 x := by
      rw [radialFourRegularizedStorage_zero]
      dsimp only [ε]
      linarith
    exact Filter.Tendsto.eventually_lt tendsto_const_nhds
      (radialFourRegularizedStorage_continuousAt R hR x).tendsto hp
  have hu := hK.eventually_forall_of_forall_eventually
    (x₀ := (0 : ℝ)) (P := fun h x => ε < radialFourRegularizedStorage R h x) hl
  filter_upwards [hu] with h hh
  intro x hx
  exact hh x (by simpa only [K, Metric.mem_sphere, dist_zero_right] using hx)

end
end CarrySelfAdjointOperator
