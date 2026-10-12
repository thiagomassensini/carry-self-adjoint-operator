import CarrySelfAdjointOperator.NativeCauchyLaguerreExactGram
import Mathlib.Analysis.SpecificLimits.Normed

/-! The binomial matrix and its exact, summable action on radial features.
No unitary Laguerre transform is postulated. Its Lp realization is a separate gate. -/
namespace CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000

def advanceEntry (r s : ℕ) : ℝ := ((r+s).choose r : ℝ) / 2^(r+s+1)

theorem advanceEntry_symmetric (r s : ℕ) : advanceEntry r s = advanceEntry s r := by
  unfold advanceEntry
  rw [Nat.choose_symm_add, Nat.add_comm]

theorem advanceEntry_nonneg (r s : ℕ) : 0 ≤ advanceEntry r s := by
  unfold advanceEntry; positivity

private theorem advance_summand (r s j : ℕ) :
    advanceEntry r s * feature s j =
      (2 / (2*(j : ℝ)+3) / 2^(r+1)) * ((s+r).choose r : ℝ) * (rho j/2)^s := by
  unfold advanceEntry feature
  rw [show r+s+1 = (r+1)+s by omega, pow_add, div_pow, Nat.add_comm s r]
  ring

theorem advance_closed_feature (r j : ℕ) :
    (2 / (2*(j : ℝ)+3) / 2^(r+1)) * (1 / (1-rho j/2)^(r+1)) =
      feature r (j+1) := by
  have ht : 1-rho j/2 = (2*(j : ℝ)+5)/(2*(2*j+3)) := by
    unfold rho
    field_simp
    ring
  rw [ht]
  unfold feature rho
  push_cast
  simp only [div_pow, mul_pow, pow_succ]
  have ha : (2*(j : ℝ)+3) ≠ 0 := by positivity
  have hb : (2*(j : ℝ)+5) ≠ 0 := by positivity
  have hc : (2*((j : ℝ)+1)+3) = 2*j+5 := by ring
  have hd : (2*((j : ℝ)+1)+1) = 2*j+3 := by ring
  rw [hc, hd]
  field_simp

/-- Universal row action, with convergence proved rather than a rearranged
formal infinite sum. This acts on features, without claiming an Lp basis. -/
theorem hasSum_advance_feature (r j : ℕ) :
    HasSum (fun s : ℕ => advanceEntry r s * feature s j) (feature r (j+1)) := by
  have hz : ‖rho j/2‖ < 1 := by
    have hp := rho_pos j
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < rho j/2)]
    linarith [rho_lt_one j]
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one r hz).mul_left
    (2 / (2*(j : ℝ)+3) / 2^(r+1))
  rw [advance_closed_feature] at h
  convert h using 1 <;> try rfl
  funext s
  rw [advance_summand]
  ring

theorem tsum_advance_feature (r j : ℕ) :
    (∑' s : ℕ, advanceEntry r s * feature s j) = feature r (j+1) :=
  (hasSum_advance_feature r j).tsum_eq

theorem advance_seed_entry : advanceEntry 0 0 = 1/2 := by norm_num [advanceEntry]

end
end CarrySelfAdjointOperator.NativeLaguerre
