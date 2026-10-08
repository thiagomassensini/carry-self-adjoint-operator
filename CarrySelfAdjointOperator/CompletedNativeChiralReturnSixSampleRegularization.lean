import CarrySelfAdjointOperator.CompletedNativeChiralReturnSixBoundaryReconstruction
import CarrySelfAdjointOperator.CompletedNativeChiralReturnTwelfthSourceIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Continuous full-source regularization on the six-sample boundary chart

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

/-- The complete order-eleven Green boundary expression in regular coordinates. -/
def radialSixRegularizedBoundaryEnergy (h : ℝ) (x : Fin 6 → ℂ) : ℝ :=
  2 * ∑ j ∈ Finset.range 6, (-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j *
    (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
      (conj (radialSixRegularizedBoundary h x a) *
        radialSixRegularizedBoundary h x (2*j-a)).re)

/-- The exact analytic source remainder, with every Cauchy cross retained.
The factor h comes from h^12 in the source, h^-10 in the reconstructed inputs,
and h^-1 in the original Cauchy feature metric. -/
def radialSixRegularizedRemainderEnergy (R : ℂ → ℂ) (h : ℝ) (x : Fin 6 → ℂ) : ℝ :=
  4*h * (∑ i : Fin 6, ∑ j : Fin 6,
    conj (radialSixRegularizedInput h x i) * radialSixRegularizedInput h x j *
      (((j : ℕ)+1 : ℕ) : ℂ)^12 * R (((((j : ℕ)+1 : ℕ) : ℝ)*h : ℝ) : ℂ) /
        (((i : ℕ)+(j : ℕ)+2 : ℕ) : ℂ)).re

/-- Full regularized source storage, not a new source or metric. -/
def radialSixRegularizedStorage (R : ℂ → ℂ) (h : ℝ) (x : Fin 6 → ℂ) : ℝ :=
  radialSixRegularizedBoundaryEnergy h x + radialSixRegularizedRemainderEnergy R h x

theorem radialSixRegularizedStorage_zero (R : ℂ → ℂ) (x : Fin 6 → ℂ) :
    radialSixRegularizedStorage R 0 x = nativeSourceSixBoundaryEnergy x := by
  simp only [radialSixRegularizedStorage, radialSixRegularizedRemainderEnergy,
    mul_zero, zero_mul, add_zero, radialSixRegularizedBoundaryEnergy]
  simp_rw [radialSixRegularizedBoundary_zero]
  exact (nativeSourceSixBoundaryEnergy_eq_alternating_green x).symm

theorem radialSixRegularizedBoundary_continuous (m : ℕ) :
    Continuous (fun y : ℝ × (Fin 6 → ℂ) => radialSixRegularizedBoundary y.1 y.2 m) := by
  unfold radialSixRegularizedBoundary
  split_ifs with hm <;> fun_prop

theorem radialSixRegularizedInput_continuous (i : Fin 6) :
    Continuous (fun y : ℝ × (Fin 6 → ℂ) => radialSixRegularizedInput y.1 y.2 i) := by
  unfold radialSixRegularizedInput
  fun_prop

theorem radialSixRegularizedStorage_continuousAt (R : ℂ → ℂ)
    (hR : ContinuousAt R 0) (x : Fin 6 → ℂ) :
    ContinuousAt (fun y : ℝ × (Fin 6 → ℂ) => radialSixRegularizedStorage R y.1 y.2) (0,x) := by
  have hb (a b : ℕ) : Continuous (fun y : ℝ × (Fin 6 → ℂ) =>
      (conj (radialSixRegularizedBoundary y.1 y.2 a) *
        radialSixRegularizedBoundary y.1 y.2 b).re) :=
    Complex.continuous_re.comp ((Complex.continuous_conj.comp
      (radialSixRegularizedBoundary_continuous a)).mul
        (radialSixRegularizedBoundary_continuous b))
  have hp : Continuous (fun y : ℝ × (Fin 6 → ℂ) => radialSixRegularizedBoundaryEnergy y.1 y.2) := by
    unfold radialSixRegularizedBoundaryEnergy
    fun_prop
  have hi (i : Fin 6) : ContinuousAt
      (fun y : ℝ × (Fin 6 → ℂ) => radialSixRegularizedInput y.1 y.2 i) (0,x) :=
    (radialSixRegularizedInput_continuous i).continuousAt
  have hr (j : Fin 6) : ContinuousAt
      (fun y : ℝ × (Fin 6 → ℂ) => R (((((j : ℕ)+1 : ℕ) : ℝ)*y.1 : ℝ) : ℂ)) (0,x) := by
    have ht : ContinuousAt
        (fun y : ℝ × (Fin 6 → ℂ) => (((((j : ℕ)+1 : ℕ) : ℝ)*y.1 : ℝ) : ℂ)) (0,x) := by
      fun_prop
    exact hR.comp_of_eq ht (by simp)
  have hs : ContinuousAt (fun y : ℝ × (Fin 6 → ℂ) => ∑ i : Fin 6, ∑ j : Fin 6,
      conj (radialSixRegularizedInput y.1 y.2 i) * radialSixRegularizedInput y.1 y.2 j *
        (((j : ℕ)+1 : ℕ) : ℂ)^12 * R (((((j : ℕ)+1 : ℕ) : ℝ)*y.1 : ℝ) : ℂ) /
          (((i : ℕ)+(j : ℕ)+2 : ℕ) : ℂ)) (0,x) := by
    apply tendsto_finsetSum Finset.univ
    intro i _
    apply tendsto_finsetSum Finset.univ
    intro j _
    exact ((((Complex.continuous_conj.continuousAt.comp (hi i)).mul (hi j)).mul_const
      ((((j : ℕ)+1 : ℕ) : ℂ)^12)).mul (hr j)).div_const _
  exact hp.continuousAt.add (((continuous_const.mul continuous_fst).continuousAt).mul
    (Complex.continuous_re.continuousAt.comp hs))

theorem radialSixRegularizedBoundary_smul (h : ℝ) (z : ℂ) (x : Fin 6 → ℂ) (m : ℕ) :
    radialSixRegularizedBoundary h (z • x) m = z * radialSixRegularizedBoundary h x m := by
  unfold radialSixRegularizedBoundary
  split_ifs with hm
  · rfl
  · simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring

theorem radialSixRegularizedInput_smul (h : ℝ) (z : ℂ) (x : Fin 6 → ℂ) (i : Fin 6) :
    radialSixRegularizedInput h (z • x) i = z * radialSixRegularizedInput h x i := by
  simp only [radialSixRegularizedInput, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Compactness supplies ONE neighborhood for EVERY nonzero six-coordinate
source. This controls all mixed sectors jointly, not one fixed canary. -/
theorem radialSixRegularizedStorage_eventually_pos_on_unit (R : ℂ → ℂ) (hR : ContinuousAt R 0) :
    ∀ᶠ h : ℝ in nhds 0, ∀ x : Fin 6 → ℂ, ‖x‖ = 1 →
      0 < radialSixRegularizedStorage R h x := by
  let K : Set (Fin 6 → ℂ) := Metric.sphere 0 1
  have hK : IsCompact K := isCompact_sphere 0 1
  have hl : ∀ x ∈ K, ∀ᶠ y : ℝ × (Fin 6 → ℂ) in nhds (0,x),
      0 < radialSixRegularizedStorage R y.1 y.2 := by
    intro x hx
    have hnx : x ≠ 0 := by
      intro he
      simp [K, he] at hx
    have hp : 0 < radialSixRegularizedStorage R 0 x := by
      rw [radialSixRegularizedStorage_zero]
      exact nativeSourceSixBoundaryEnergy_pos x hnx
    exact Filter.Tendsto.eventually_lt tendsto_const_nhds
      (radialSixRegularizedStorage_continuousAt R hR x).tendsto hp
  have hu := hK.eventually_forall_of_forall_eventually
    (x₀ := (0 : ℝ)) (P := fun h x => 0 < radialSixRegularizedStorage R h x) hl
  filter_upwards [hu] with h hh
  intro x hx
  exact hh x (by simpa only [K, Metric.mem_sphere, dist_zero_right] using hx)


/-- The source-derived strict six-jet face has one positive margin, retained
uniformly on the finite unit sphere for all sufficiently small radial steps. -/
theorem radialSixRegularizedStorage_eventually_unit_margin (R : ℂ → ℂ) (hR : ContinuousAt R 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ h : ℝ in nhds 0,
      ∀ x : Fin 6 → ℂ, ‖x‖ = 1 → ε < radialSixRegularizedStorage R h x := by
  let K : Set (Fin 6 → ℂ) := Metric.sphere 0 1
  have hK : IsCompact K := isCompact_sphere 0 1
  have hne : K.Nonempty := by
    refine ⟨(1 : Fin 6 → ℂ), ?_⟩
    simp [K]
  have hf : Continuous nativeSourceSixBoundaryEnergy := by
    unfold nativeSourceSixBoundaryEnergy nativeSourceFiveEvenBoundaryEnergy nativeSourceSixOddBoundaryEnergy
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    fun_prop
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hf.continuousOn
  have hn₀ : x₀ ≠ 0 := by intro he; simp [K, he] at hx₀
  have hp₀ := nativeSourceSixBoundaryEnergy_pos x₀ hn₀
  let ε := nativeSourceSixBoundaryEnergy x₀ / 2
  have he : 0 < ε := div_pos hp₀ (by norm_num)
  refine ⟨ε, he, ?_⟩
  have hl : ∀ x ∈ K, ∀ᶠ y : ℝ × (Fin 6 → ℂ) in nhds (0,x),
      ε < radialSixRegularizedStorage R y.1 y.2 := by
    intro x hx
    have hb : nativeSourceSixBoundaryEnergy x₀ ≤ nativeSourceSixBoundaryEnergy x := hmin hx
    have hp : ε < radialSixRegularizedStorage R 0 x := by
      rw [radialSixRegularizedStorage_zero]
      dsimp only [ε]
      linarith
    exact Filter.Tendsto.eventually_lt tendsto_const_nhds
      (radialSixRegularizedStorage_continuousAt R hR x).tendsto hp
  have hu := hK.eventually_forall_of_forall_eventually
    (x₀ := (0 : ℝ)) (P := fun h x => ε < radialSixRegularizedStorage R h x) hl
  filter_upwards [hu] with h hh
  intro x hx
  exact hh x (by simpa only [K, Metric.mem_sphere, dist_zero_right] using hx)

end
end CarrySelfAdjointOperator
