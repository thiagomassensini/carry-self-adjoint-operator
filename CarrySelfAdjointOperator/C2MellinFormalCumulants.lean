import CarrySelfAdjointOperator.C2MellinMixtureIdentities
import Mathlib.Tactic

open scoped BigOperators

namespace CarrySelfAdjointOperator

noncomputable section

/-- One step of the classical triangular cumulant recurrence. -/
def nativeC2FormalCumulantStep (m : ℕ → ℝ) (n : ℕ)
    (previous : ∀ k, k < n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n + 1 => m (n + 1) - ∑ j : Fin n,
      (Nat.choose n j.val : ℝ) * previous (j.val + 1) (by omega) *
        m (n - j.val)

/-- The order-`n` formal cumulant associated with normalized raw moments,
defined by the classical triangular recurrence. The zeroth entry is zero since
the cumulants and their recurrence start at order one. -/
def nativeC2FormalCumulant (m : ℕ → ℝ) (n : ℕ) : ℝ :=
  Nat.strongRecOn n (nativeC2FormalCumulantStep m)

/-- The formal cumulants satisfy the required moment recurrence. This is the
algebraic core only; identification with derivatives of `log Z` requires the
separate analytic differentiation-under-the-integral obligation. -/
theorem nativeC2FormalCumulant_recurrence
    (m : ℕ → ℝ) (n : ℕ) :
    nativeC2FormalCumulant m (n + 1) =
      m (n + 1) - ∑ j : Fin n,
        (Nat.choose n j.val : ℝ) * nativeC2FormalCumulant m (j.val + 1) *
          m (n - j.val) := by
  unfold nativeC2FormalCumulant
  rw [Nat.strongRecOn_eq]
  simp [nativeC2FormalCumulantStep]

/-- The zero-based `Fin n` form is the same recurrence as the sum over
`j = 1, ..., n` in the specification. -/
theorem nativeC2FormalCumulant_recurrence_range
    (m : ℕ → ℝ) (n : ℕ) :
    nativeC2FormalCumulant m (n + 1) =
      m (n + 1) - ∑ j ∈ Finset.range n,
        (Nat.choose n j : ℝ) * nativeC2FormalCumulant m (j + 1) * m (n - j) := by
  rw [nativeC2FormalCumulant_recurrence]
  simp_rw [← Fin.sum_univ_eq_sum_range]

/-- Exact analytic obligation that upgrades the formal recursion to cumulants
of the Mellin source. -/
def nativeC2LogDerivativeCumulantIdentificationObligation
    (Z : ℝ → ℝ) (s : ℝ) (κ : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, n ≠ 0 →
    iteratedDeriv n (fun t : ℝ => Real.log (Z t)) s = κ n

end

end CarrySelfAdjointOperator
