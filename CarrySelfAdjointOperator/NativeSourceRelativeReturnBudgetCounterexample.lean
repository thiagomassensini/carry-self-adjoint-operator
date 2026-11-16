import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Scalar control for the relative-versus-additive inference

This is a generic scalar example, not a counterexample to the C² source.
It records why a relative excess tending to zero does not by itself produce
the additive error needed for a sign limit when the incident map grows.
-/

namespace CarrySelfAdjointOperator.NativeSourceRelativeReturnBudgetCounterexample

open Filter Topology
noncomputable section

def incident (k : ℕ) (x : ℝ) : ℝ := (k : ℝ) * x

def returned (k : ℕ) (x : ℝ) : ℝ := ((k : ℝ) + 1 / (k : ℝ)) * x

def relativeExcess (k : ℕ) : ℝ :=
  2 / (k : ℝ)^2 + 1 / (k : ℝ)^4

def incidentGrowthBudget (k : ℕ) : ℝ := (k : ℝ)^2

theorem relativeExcess_tendsto_zero :
    Tendsto relativeExcess atTop (nhds 0) := by
  have h₂ : Tendsto (fun k : ℕ => (2 : ℝ) / (k : ℝ)^2) atTop (nhds 0) :=
    tendsto_const_div_pow 2 2 (by decide)
  have h₄ : Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ)^4) atTop (nhds 0) :=
    tendsto_const_div_pow 1 4 (by decide)
  change Tendsto (fun k : ℕ => (2 : ℝ) / (k : ℝ)^2 +
    1 / (k : ℝ)^4) atTop (nhds 0)
  simpa only [one_div, zero_add] using h₂.add h₄

theorem returned_square_eq_relative_incident_square
    (k : ℕ) (x : ℝ) (hk : 1 ≤ k) :
    (returned k x)^2 = (1 + relativeExcess k) * (incident k x)^2 := by
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < k by omega))
  simp only [returned, relativeExcess, incident]
  field_simp [hk0]
  ring

theorem signed_balance_exact
    (k : ℕ) (x : ℝ) (hk : 1 ≤ k) :
    (incident k x)^2 - (returned k x)^2 =
      -(2 + 1 / (k : ℝ)^2) * x^2 := by
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < k by omega))
  simp only [incident, returned]
  field_simp [hk0]
  ring

theorem norm_signed_balance_exact
    (k : ℕ) (x : ℝ) (hk : 1 ≤ k) :
    ‖incident k x‖^2 - ‖returned k x‖^2 =
      -(2 + 1 / (k : ℝ)^2) * ‖x‖^2 := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs, sq_abs]
  exact signed_balance_exact k x hk

theorem relativeExcess_mul_incidentGrowthBudget_tendsto_two :
    Tendsto (fun k => relativeExcess k * incidentGrowthBudget k)
      atTop (nhds 2) := by
  have hinv := tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  have htwo : Tendsto (fun k : ℕ => (2 : ℝ) + ((k : ℝ)⁻¹)^2)
      atTop (nhds 2) := by
    simpa using (tendsto_const_nhds.add (hinv.pow 2))
  have hpos : ∀ᶠ k : ℕ in atTop, 0 < k := by
    filter_upwards [eventually_atTop.2 ⟨1, fun k hk =>
      lt_of_lt_of_le Nat.zero_lt_one hk⟩] with k hk
    exact hk
  have heq : (fun k : ℕ => (2 : ℝ) + ((k : ℝ)⁻¹)^2) =ᶠ[atTop]
      (fun k => relativeExcess k * incidentGrowthBudget k) := by
    filter_upwards [hpos] with k hk
    have hk0 : (k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hk)
    dsimp [relativeExcess, incidentGrowthBudget]
    field_simp [hk0]
  exact htwo.congr' heq

end
end CarrySelfAdjointOperator.NativeSourceRelativeReturnBudgetCounterexample
