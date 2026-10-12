import CarrySelfAdjointOperator.NativePhysicalEndpointEncoder

namespace CarrySelfAdjointOperator.PhysicalSewing
open scoped BigOperators Matrix
open Polynomial
noncomputable section
set_option autoImplicit false

/-- Literal progressive differences, not centered differences. -/
def completionForwardDifference (theta : ℕ → ℂ) (a d : ℕ) : ℂ :=
  ∑ t ∈ Finset.range (d+1), completedGreenForwardWeight d t * theta (a+t)

theorem descFactorial_choose_shift (a b t : ℕ) :
    (a+t).descFactorial a * b.choose (a+t) =
      b.descFactorial a * (b-a).choose t := by
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose]
  have hc := Nat.choose_mul (n := b) (k := a+t) (s := a) (Nat.le_add_right a t)
  rw [Nat.add_sub_cancel_left] at hc
  calc
    a.factorial * (a+t).choose a * b.choose (a+t) =
        a.factorial * (b.choose (a+t) * (a+t).choose a) := by ring
    _ = a.factorial * (b.choose a * (b-a).choose t) := by rw [hc]
    _ = a.factorial * b.choose a * (b-a).choose t := by ring

theorem endpointCompletion_column_sum (N : ℕ) (theta : ℕ → ℂ) (a b : Fin N) :
    (∑ j : Fin N, (j.val.descFactorial a.val : ℂ) *
      completedGreenForwardWeight b.val j.val * theta j.val) =
    if a.val ≤ b.val then (b.val.descFactorial a.val : ℂ) *
      completionForwardDifference theta a.val (b.val-a.val) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (j.descFactorial a.val : ℂ) *
    completedGreenForwardWeight b.val j * theta j) N]
  have hs : (∑ j ∈ Finset.range N, (j.descFactorial a.val : ℂ) *
      completedGreenForwardWeight b.val j * theta j) =
      ∑ j ∈ Finset.range (b.val+1), (j.descFactorial a.val : ℂ) *
        completedGreenForwardWeight b.val j * theta j := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by have hb := b.isLt; omega))
    intro j _ hj
    have hb : b.val < j := by simp only [Finset.mem_range] at hj; omega
    simp [completedGreenForwardWeight, Nat.choose_eq_zero_of_lt hb]
  rw [hs]
  by_cases hab : a.val ≤ b.val
  · rw [if_pos hab]
    have he : b.val+1 = a.val+(b.val-a.val+1) := by omega
    rw [he, Finset.sum_range_add]
    have hz : (∑ j ∈ Finset.range a.val, (j.descFactorial a.val : ℂ) *
        completedGreenForwardWeight b.val j * theta j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [Nat.descFactorial_eq_zero_iff_lt.mpr (Finset.mem_range.mp hj)]
    rw [hz, zero_add]
    unfold completionForwardDifference
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    have hc : ((a.val+t).descFactorial a.val : ℂ) * (b.val.choose (a.val+t) : ℂ) =
        (b.val.descFactorial a.val : ℂ) * ((b.val-a.val).choose t : ℂ) := by
      exact_mod_cast descFactorial_choose_shift a.val b.val t
    have ht : b.val-(a.val+t) = b.val-a.val-t := by omega
    simp only [completedGreenForwardWeight, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, Int.cast_natCast, ht]
    linear_combination (-1 : ℂ)^(b.val-a.val-t) * theta (a.val+t) * hc
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro j hj
    have hja : j < a.val := by have hjb := Finset.mem_range.mp hj; omega
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr hja]

def endpointCompletionMatrix (N k : ℕ) (theta : ℕ → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => if a.val ≤ b.val then endpointGauge k a.val / endpointGauge k b.val *
    completionForwardDifference theta a.val (b.val-a.val) / ((b.val-a.val).factorial : ℂ) else 0

def endpointCompletion (N k : ℕ) (theta : ℕ → ℂ) (x : Fin N → ℂ) : Fin N → ℂ :=
  (endpointCompletionMatrix N k theta) *ᵥ x

theorem physicalEndpointJetInput_eq_taylor (N k : ℕ) (v : Fin N → ℂ) (a : Fin N) :
    physicalEndpointJetInput N k v a = endpointGauge k a * (a.val.factorial : ℂ) *
      (taylor 1 (materialPolynomial N v)).coeff a := by
  have hf : (a.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a.val
  have h := (div_eq_iff hf).mp (endpointDerivative_div_factorial (materialPolynomial N v) a.val)
  change endpointGauge k a * _ = _
  rw [h]
  ring

/-- Derived diagonal completion action on all endpoint derivatives. -/
theorem physicalEndpointJetInput_completion (N k : ℕ) (theta : ℕ → ℂ) (v : Fin N → ℂ) :
    physicalEndpointJetInput N k (fun j => theta j.val * v j) =
      endpointCompletion N k theta (physicalEndpointJetInput N k v) := by
  funext a
  rw [physicalEndpointJetInput_finite]
  change endpointGauge k a * (∑ j : Fin N, (j.val.descFactorial a.val : ℂ) * (theta j.val * v j)) =
    ∑ b : Fin N, endpointCompletionMatrix N k theta a b * physicalEndpointJetInput N k v b
  simp_rw [← material_taylor_coeff N v]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have hs : (∑ j : Fin N, endpointGauge k a * ((j.val.descFactorial a.val : ℂ) *
      (theta j.val * ((taylor 1 (materialPolynomial N v)).coeff b *
        completedGreenForwardWeight b.val j.val)))) =
      endpointGauge k a * (taylor 1 (materialPolynomial N v)).coeff b *
        (∑ j : Fin N, (j.val.descFactorial a.val : ℂ) *
          completedGreenForwardWeight b.val j.val * theta j.val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs, endpointCompletion_column_sum, physicalEndpointJetInput_eq_taylor]
  unfold endpointCompletionMatrix
  by_cases hab : a.val ≤ b.val
  · simp only [if_pos hab]
    have hg := endpointGauge_ne_zero k b.val
    have hf : ((b.val-a.val).factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (b.val-a.val)
    have hd : ((b.val-a.val).factorial : ℂ) * (b.val.descFactorial a.val : ℂ) =
        (b.val.factorial : ℂ) := by exact_mod_cast Nat.factorial_mul_descFactorial hab
    field_simp
    linear_combination endpointGauge k a *
      (taylor 1 (materialPolynomial N v)).coeff b *
      completionForwardDifference theta a.val (b.val-a.val) * hd
  · simp [hab]

end
end CarrySelfAdjointOperator.PhysicalSewing
