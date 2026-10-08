import CarrySelfAdjointOperator.CompletedNativeChiralReturnFourteenthSourceRemainder
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Uniform O(h) bound of the complete seven-source analytic remainder

Compactness bounds the quadratic coefficient on the EXISTING finite boundary
chart. The exact source remainder is synthesized in the original Cauchy
carrier before readout. No positivity of the boundary face is assumed.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology ChiralReturn
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Polynomial boundary input is continuous even at h=0. -/
theorem radialSevenRegularizedInput_continuous (i : Fin 7) :
    Continuous (fun y : ℝ × (Fin 7 → ℂ) => radialSevenRegularizedInput y.1 y.2 i) := by
  unfold radialSevenRegularizedInput
  fun_prop

theorem radialSevenRegularizedInput_smul (h : ℝ) (z : ℂ) (x : Fin 7 → ℂ) (i : Fin 7) :
    radialSevenRegularizedInput h (z • x) i = z * radialSevenRegularizedInput h x i := by
  simp only [radialSevenRegularizedInput, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The continuous quadratic coefficient AFTER the exact complete remainder
synthesis. Multiplying it by 4h gives the old Cauchy remainder readout. -/
def radialSevenRemainderQuadraticReadout (R : ℂ → ℂ) (h : ℝ) (x : Fin 7 → ℂ) : ℝ :=
  (∑ i : Fin 7, ∑ j : Fin 7,
    conj (radialSevenRegularizedInput h x i) * radialSevenRegularizedInput h x j *
      (((j+1 : ℕ) : ℂ)^14) * R (((((j+1 : ℕ) : ℝ)*h : ℝ) : ℂ)) /
        (((i : ℕ)+(j : ℕ)+2 : ℕ) : ℂ)).re

theorem radialSevenRemainderQuadraticReadout_continuousAt
    (R : ℂ → ℂ) (hR : ContinuousAt R 0) (x : Fin 7 → ℂ) :
    ContinuousAt (fun y : ℝ × (Fin 7 → ℂ) =>
      radialSevenRemainderQuadraticReadout R y.1 y.2) (0,x) := by
  have hi (i : Fin 7) : ContinuousAt
      (fun y : ℝ × (Fin 7 → ℂ) => radialSevenRegularizedInput y.1 y.2 i) (0,x) :=
    (radialSevenRegularizedInput_continuous i).continuousAt
  have hr (j : Fin 7) : ContinuousAt
      (fun y : ℝ × (Fin 7 → ℂ) => R (((((j+1 : ℕ) : ℝ)*y.1 : ℝ) : ℂ))) (0,x) := by
    have ht : ContinuousAt
        (fun y : ℝ × (Fin 7 → ℂ) => (((((j+1 : ℕ) : ℝ)*y.1 : ℝ) : ℂ))) (0,x) := by
      fun_prop
    exact hR.comp_of_eq ht (by simp)
  have hs : ContinuousAt (fun y : ℝ × (Fin 7 → ℂ) => ∑ i : Fin 7, ∑ j : Fin 7,
      conj (radialSevenRegularizedInput y.1 y.2 i) * radialSevenRegularizedInput y.1 y.2 j *
        (((j+1 : ℕ) : ℂ)^14) * R (((((j+1 : ℕ) : ℝ)*y.1 : ℝ) : ℂ)) /
          (((i : ℕ)+(j : ℕ)+2 : ℕ) : ℂ)) (0,x) := by
    apply tendsto_finsetSum Finset.univ
    intro i _
    apply tendsto_finsetSum Finset.univ
    intro j _
    exact ((((Complex.continuous_conj.continuousAt.comp (hi i)).mul (hi j)).mul_const
      (((j+1 : ℕ) : ℂ)^14)).mul (hr j)).div_const _
  exact Complex.continuous_re.continuousAt.comp hs

theorem radialSevenRemainderQuadraticReadout_smul
    (R : ℂ → ℂ) (h : ℝ) (z : ℂ) (x : Fin 7 → ℂ) :
    radialSevenRemainderQuadraticReadout R h (z • x) =
      Complex.normSq z * radialSevenRemainderQuadraticReadout R h x := by
  unfold radialSevenRemainderQuadraticReadout
  simp_rw [radialSevenRegularizedInput_smul]
  have he : (∑ i : Fin 7, ∑ j : Fin 7,
      conj (z * radialSevenRegularizedInput h x i) * (z * radialSevenRegularizedInput h x j) *
        (((j+1 : ℕ) : ℂ)^14) * R (((((j+1 : ℕ) : ℝ)*h : ℝ) : ℂ)) /
          (((i : ℕ)+(j : ℕ)+2 : ℕ) : ℂ)) =
      (Complex.normSq z : ℂ) * (∑ i : Fin 7, ∑ j : Fin 7,
        conj (radialSevenRegularizedInput h x i) * radialSevenRegularizedInput h x j *
          (((j+1 : ℕ) : ℂ)^14) * R (((((j+1 : ℕ) : ℝ)*h : ℝ) : ℂ)) /
            (((i : ℕ)+(j : ℕ)+2 : ℕ) : ℂ)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Complex.normSq_eq_conj_mul_self, map_mul]
    ring
  rw [he, Complex.re_ofReal_mul]

/-- ONE neighborhood and finite constant control EVERY coefficient vector,
including the cancellation directions. This is boundedness, not sign. -/
theorem radialSevenRemainderQuadraticReadout_eventually_bound
    (R : ℂ → ℂ) (hR : ContinuousAt R 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ h : ℝ in nhds 0, ∀ x : Fin 7 → ℂ,
      |radialSevenRemainderQuadraticReadout R h x| ≤ C * ‖x‖^2 := by
  let K : Set (Fin 7 → ℂ) := Metric.sphere 0 1
  have hK : IsCompact K := isCompact_sphere 0 1
  have hne : K.Nonempty := by
    refine ⟨(1 : Fin 7 → ℂ), ?_⟩
    simp [K]
  have hf : Continuous (fun x : Fin 7 → ℂ => |radialSevenRemainderQuadraticReadout R 0 x|) := by
    unfold radialSevenRemainderQuadraticReadout radialSevenRegularizedInput
    simp only [mul_zero, Complex.ofReal_zero]
    fun_prop
  obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn hne hf.continuousOn
  let C := |radialSevenRemainderQuadraticReadout R 0 x₀| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hl : ∀ x ∈ K, ∀ᶠ y : ℝ × (Fin 7 → ℂ) in nhds (0,x),
      |radialSevenRemainderQuadraticReadout R y.1 y.2| < C := by
    intro x hx
    have hp : |radialSevenRemainderQuadraticReadout R 0 x| < C :=
      lt_of_le_of_lt (hmax hx) (by dsimp [C]; linarith)
    exact (radialSevenRemainderQuadraticReadout_continuousAt R hR x).abs.tendsto.eventually_lt
      tendsto_const_nhds hp
  have hu := hK.eventually_forall_of_forall_eventually
    (x₀ := (0 : ℝ)) (P := fun h x => |radialSevenRemainderQuadraticReadout R h x| < C) hl
  refine ⟨C, hC, ?_⟩
  filter_upwards [hu] with h hk
  intro x
  by_cases hx : x = 0
  · simp [hx, radialSevenRemainderQuadraticReadout, radialSevenRegularizedInput]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let z : ℂ := (‖x‖⁻¹ : ℝ)
    let y := z • x
    have hy : ‖y‖ = 1 := by
      simp [y, z, norm_smul, norm_inv, inv_mul_cancel₀ hn]
    have hb := (hk y (by simpa only [K, Metric.mem_sphere, dist_zero_right] using hy)).le
    have hxy : (‖x‖ : ℂ) • y = x := by
      dsimp only [y, z]
      rw [smul_smul]
      have hnC : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast hn
      simp [mul_inv_cancel₀ hnC]
    have he := radialSevenRemainderQuadraticReadout_smul R h (‖x‖ : ℂ) y
    rw [hxy, Complex.normSq_ofReal] at he
    rw [he, ← pow_two, abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)]
    calc
      ‖x‖^2 * |radialSevenRemainderQuadraticReadout R h y| ≤ ‖x‖^2 * C :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg ‖x‖)
      _ = C * ‖x‖^2 := mul_comm _ _

/-- Uniform O(h) estimate in the existing seven-jet boundary coordinates.
The constant is independent of h and x, with no positivity premise. -/
theorem radialSevenRegularizedRemainderEnergy_eventually_abs_bound
    (R : ℂ → ℂ) (hR : ContinuousAt R 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ h : ℝ in nhds 0, ∀ x : Fin 7 → ℂ,
      |radialSevenRegularizedRemainderEnergy R h x| ≤ C * |h| * ‖x‖^2 := by
  obtain ⟨C, hC, hb⟩ := radialSevenRemainderQuadraticReadout_eventually_bound R hR
  refine ⟨4*C, mul_pos (by norm_num) hC, ?_⟩
  filter_upwards [hb] with h hk
  intro x
  change |4*h*radialSevenRemainderQuadraticReadout R h x| ≤ _
  rw [abs_mul, abs_mul]
  norm_num only [abs_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num)]
  have hb' := mul_le_mul_of_nonneg_left (hk x) (show 0 ≤ 4*|h| by positivity)
  nlinarith

/-- The actual completed source supplies R; the bound concerns the FULL
mixed remainder synthesis, not an independently chosen analytic function. -/
theorem radialSevenSourceTaylorRemainder_eventually_abs_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop, ∀ x : Fin 7 → ℂ,
      |4 * (inner ℂ (radialIncidentSynthesis k 7
        (radialSevenNormalizedBoundaryInput (radialFourSourceStep k) x))
        (radialSevenSourceTaylorRemainderSynthesis k (radialFourSourceStep k) x)).re| ≤
      C * radialFourSourceStep k * ‖x‖^2 := by
  obtain ⟨R, hRa, hR⟩ := radialSevenSourceTaylorTemplate_eventually_eq_slopes
  obtain ⟨C, hC, hb⟩ := radialSevenRegularizedRemainderEnergy_eventually_abs_bound R hRa.continuousAt
  have hu := radialFourSourceStep_tendsto_zero.eventually hb
  refine ⟨C, hC, ?_⟩
  filter_upwards [hR, hu] with k hk hku
  intro x
  have hh := (radialFourSourceStep_pos k).ne'
  have hkh : ((k : ℝ)+1)*radialFourSourceStep k = 1 := by
    unfold radialFourSourceStep
    exact mul_inv_cancel₀ (by positivity)
  have hv : radialSevenSourceTaylorRemainderSynthesis k (radialFourSourceStep k) x =
      radialIncidentSynthesis k 7 (fun i => radialSevenNormalizedBoundaryInput (radialFourSourceStep k) x i *
        (((radialFourSourceStep k ^ 14 : ℝ) : ℂ) * (((i+1 : ℕ) : ℂ)^14) *
          R (((((i+1 : ℕ) : ℝ)*radialFourSourceStep k : ℝ) : ℂ)))) := by
    unfold radialSevenSourceTaylorRemainderSynthesis
    simp_rw [hk, canonicalGreenJetStep_eq_radialFourSourceStep]
    rw [radialSevenSourceTaylorTemplate_synthesis]
    abel
  rw [hv, radialSevenSourceRemainder_energy k _ hh hkh R x]
  simpa only [abs_of_pos (radialFourSourceStep_pos k)] using hku x


/-- The same single radial threshold controls ALL original source inputs.
The right side uses their complete seven scaled boundary coordinates. -/
theorem radialSevenOriginalSourceRemainder_eventually_abs_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop, ∀ d : Fin 7 → ℂ,
      |4 * (inner ℂ (radialIncidentSynthesis k 7 d)
        (radialIncidentSynthesis k 7 (fun i => d i * radialCompletedSlope k i) -
          radialIncidentSynthesis k 7 (fun i => d i *
            radialSevenSourceTaylorPrefix (radialFourSourceStep k : ℂ) i))).re| ≤
      C * radialFourSourceStep k * ‖radialSevenScaledBoundary (radialFourSourceStep k) d‖^2 := by
  obtain ⟨C, hC, hb⟩ := radialSevenSourceTaylorRemainder_eventually_abs_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with k hk
  intro d
  have ht := hk (radialSevenScaledBoundary (radialFourSourceStep k) d)
  simpa only [radialSevenSourceTaylorRemainderSynthesis,
    radialSevenNormalizedBoundaryInput_scaled _ (radialFourSourceStep_pos k).ne' d] using ht

end
end CarrySelfAdjointOperator
