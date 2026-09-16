import Mathlib

/-!
# Endpoint duality for the native two-jump moment recurrence

This is the all-order algebraic step in sections 1–3 of
`CHIRAL_ENDPOINT_THEOREM_FROM_DARBOUX_ORTHOGONALITY.md`.
The homogeneous moments and endpoint polynomials are defined by their actual
recurrences, not by the endpoint identity that is to be proved.

No classical characteristic, symplectic pullback, physical tail identification,
or five-field capstone equality is assumed. The integral representation of the
endpoint polynomials is not asserted in this file.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

open scoped BigOperators

/-- Homogeneous part of the two-jump recurrence, with its two initial data.
The index `n + 3` corresponds to `m = n + 1` in the notes. -/
def twoJumpHomogeneousMoment (t1 t2 u0 u1 : ℂ) : ℕ → ℂ
  | 0 => u0
  | 1 => u1
  | 2 => (2 + (t1 + t2)) * u1 - ((t1 + t2) + t1 * t2) * u0
  | n + 3 =>
      ((n : ℂ) + 3 + (t1 + t2)) * twoJumpHomogeneousMoment t1 t2 u0 u1 (n + 2) -
        (((n : ℂ) + 2) * (t1 + t2) + t1 * t2) *
          twoJumpHomogeneousMoment t1 t2 u0 u1 (n + 1) +
        ((n : ℂ) + 1) * (t1 * t2) * twoJumpHomogeneousMoment t1 t2 u0 u1 n

/-- Coefficient of the zeroth base moment in the homogeneous recurrence. -/
def twoJumpMomentF (t1 t2 : ℂ) : ℕ → ℂ :=
  twoJumpHomogeneousMoment t1 t2 1 0

/-- Coefficient of the first base moment in the homogeneous recurrence. -/
def twoJumpMomentG (t1 t2 : ℂ) : ℕ → ℂ :=
  twoJumpHomogeneousMoment t1 t2 0 1

/-- Polynomial endpoint sequence, defined without an incomplete-gamma function. -/
def recurrenceEndpointPolynomial (x : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => ((n : ℂ) + 1) * recurrenceEndpointPolynomial x n + x ^ (n + 1)

/-- The recursive polynomial is exactly the factorial sum used in the notes. -/
theorem recurrenceEndpointPolynomial_eq_factorial_sum (x : ℂ) (m : ℕ) :
    recurrenceEndpointPolynomial x m =
      (m.factorial : ℂ) * ∑ r ∈ Finset.range (m + 1), x ^ r / (r.factorial : ℂ) := by
  induction m with
  | zero => simp [recurrenceEndpointPolynomial]
  | succ m ih =>
    have hf : ((m + 1).factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (m + 1)
    rw [recurrenceEndpointPolynomial, ih, Finset.sum_range_succ _ (m + 1), mul_add]
    rw [mul_div_cancel₀ _ hf, Nat.factorial_succ]
    push_cast
    ring

/-- The initial residual is the same quadratic factor as in positive orders. -/
theorem recurrenceEndpointPolynomial_initial_residual (t1 t2 x : ℂ) :
    recurrenceEndpointPolynomial x 2 -
        (2 + (t1 + t2)) * recurrenceEndpointPolynomial x 1 +
        ((t1 + t2) + t1 * t2) * recurrenceEndpointPolynomial x 0 =
      (x - t1) * (x - t2) := by
  simp only [recurrenceEndpointPolynomial, Nat.cast_zero, Nat.cast_one]
  ring

/-- Exact recurrence residual, for `m = n + 1 ≥ 1`. -/
theorem recurrenceEndpointPolynomial_residual (t1 t2 x : ℂ) (n : ℕ) :
    recurrenceEndpointPolynomial x (n + 3) -
        ((n : ℂ) + 3 + (t1 + t2)) * recurrenceEndpointPolynomial x (n + 2) +
        (((n : ℂ) + 2) * (t1 + t2) + t1 * t2) *
          recurrenceEndpointPolynomial x (n + 1) -
        ((n : ℂ) + 1) * (t1 * t2) * recurrenceEndpointPolynomial x n =
      x ^ (n + 1) * (x - t1) * (x - t2) := by
  simp only [recurrenceEndpointPolynomial, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, pow_succ]
  ring

/-- The two concrete basis sequences reconstruct any homogeneous initial data. -/
theorem twoJumpHomogeneousMoment_eq_basis
    (t1 t2 u0 u1 : ℂ) (m : ℕ) :
    twoJumpHomogeneousMoment t1 t2 u0 u1 m =
      u0 * twoJumpMomentF t1 t2 m + u1 * twoJumpMomentG t1 t2 m := by
  unfold twoJumpMomentF twoJumpMomentG
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _ | _ | _ | n
    · simp [twoJumpHomogeneousMoment]
    · simp [twoJumpHomogeneousMoment]
    · simp only [twoJumpHomogeneousMoment]
      ring
    · rw [twoJumpHomogeneousMoment, twoJumpHomogeneousMoment,
        twoJumpHomogeneousMoment, ih (n + 2) (by omega),
        ih (n + 1) (by omega), ih n (by omega)]
      ring

/-- At either jump endpoint, the polynomial sequence solves the homogeneous
recurrence with initial data `1` and `x + 1`. -/
theorem twoJumpHomogeneousMoment_eq_endpoint
    (t1 t2 x : ℂ) (hx : x = t1 ∨ x = t2) (m : ℕ) :
    twoJumpHomogeneousMoment t1 t2 1 (x + 1) m =
      recurrenceEndpointPolynomial x m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _ | _ | _ | n
    · rfl
    · simp [twoJumpHomogeneousMoment, recurrenceEndpointPolynomial, add_comm]
    · have h := recurrenceEndpointPolynomial_initial_residual t1 t2 x
      have hroot : (x - t1) * (x - t2) = 0 := by
        rcases hx with rfl | rfl <;> simp
      rw [hroot] at h
      simp only [twoJumpHomogeneousMoment, recurrenceEndpointPolynomial,
        Nat.cast_zero, zero_add, pow_one, mul_one] at h ⊢
      linear_combination -h
    · rw [twoJumpHomogeneousMoment, ih (n + 2) (by omega),
        ih (n + 1) (by omega), ih n (by omega)]
      have h := recurrenceEndpointPolynomial_residual t1 t2 x n
      have hroot : x ^ (n + 1) * (x - t1) * (x - t2) = 0 := by
        rcases hx with rfl | rfl <;> simp
      rw [hroot] at h
      linear_combination -h

/-- Recurrence endpoint duality in every order, with no numerical truncation. -/
theorem twoJumpMoment_endpoint_duality
    (t1 t2 x : ℂ) (hx : x = t1 ∨ x = t2) (m : ℕ) :
    twoJumpMomentF t1 t2 m + (x + 1) * twoJumpMomentG t1 t2 m =
      recurrenceEndpointPolynomial x m := by
  have h := twoJumpHomogeneousMoment_eq_endpoint t1 t2 x hx m
  rw [twoJumpHomogeneousMoment_eq_basis] at h
  simpa only [one_mul] using h

/-- Endpoint duality for any finitely supported polynomial coefficient readout.
The left sums are the `α_R` and `β_R` of the notes. -/
theorem twoJumpMoment_projected_endpoint_duality
    (t1 t2 x : ℂ) (hx : x = t1 ∨ x = t2)
    (s : Finset ℕ) (r : ℕ → ℂ) :
    (∑ m ∈ s, r m * twoJumpMomentF t1 t2 m) +
        (x + 1) * (∑ m ∈ s, r m * twoJumpMomentG t1 t2 m) =
      ∑ m ∈ s, r m * recurrenceEndpointPolynomial x m := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← twoJumpMoment_endpoint_duality t1 t2 x hx m]
  ring

end

end NativeCarryFiveFieldCapstone
