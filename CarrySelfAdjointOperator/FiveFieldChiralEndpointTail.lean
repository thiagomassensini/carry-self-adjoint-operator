import CarrySelfAdjointOperator.FiveFieldChiralEndpointRecurrence

/-!
# Exponential-tail realization of recurrence endpoint duality

This supplies the analytic step in section 3 of the endpoint notes. The
coefficients remain arbitrary: no physical amplitude or symplectic pairing
is identified with a tail by definition.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators

theorem integrableOn_exp_neg_mul_natPow (x : ℝ) (m : ℕ) :
    IntegrableOn (fun s : ℝ => Real.exp (-s) * s ^ m) (Ioi x) := by
  apply integrable_of_isBigO_exp_neg (b := 1 / 2) (by norm_num)
    (by fun_prop)
  have h := (isLittleO_pow_exp_pos_mul_atTop m
    (b := 1 / 2) (by norm_num)).isBigO.mul
      (Asymptotics.isBigO_refl (fun s : ℝ => Real.exp (-s)) atTop)
  convert! h using 1
  · ext s
    ring
  · ext s
    rw [← Real.exp_add]
    congr 1
    ring

/-- Integration by parts on an arbitrary real exponential tail. -/
theorem integral_exp_neg_mul_natPow_succ (x : ℝ) (m : ℕ) :
    (∫ s in Ioi x, Real.exp (-s) * s ^ (m + 1)) =
      ((m : ℝ) + 1) * (∫ s in Ioi x, Real.exp (-s) * s ^ m) +
        Real.exp (-x) * x ^ (m + 1) := by
  have hi := integrableOn_exp_neg_mul_natPow x m
  have hj := integrableOn_exp_neg_mul_natPow x (m + 1)
  have hd (s : ℝ) :
      HasDerivAt (fun t : ℝ => Real.exp (-t) * t ^ (m + 1))
        (((m : ℝ) + 1) * (Real.exp (-s) * s ^ m) -
          Real.exp (-s) * s ^ (m + 1)) s := by
    convert! ((hasDerivAt_id s).neg.exp).mul ((hasDerivAt_id s).pow (m + 1)) using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_one,
      Pi.neg_apply, Pi.pow_apply, id_eq]
    ring
  have ht : Tendsto (fun s : ℝ => Real.exp (-s) * s ^ (m + 1)) atTop (𝓝 0) := by
    simpa only [mul_comm] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (m + 1)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun s (_ : s ∈ Ici x) => hd s) ((hi.const_mul ((m : ℝ) + 1)).sub hj) ht
  rw [integral_sub (hi.const_mul _) hj, integral_const_mul] at h
  linarith

/-- The real tail realizes the complex polynomial already constructed by recurrence. -/
theorem recurrenceEndpointPolynomial_eq_exp_mul_realTail (x : ℝ) (m : ℕ) :
    recurrenceEndpointPolynomial (x : ℂ) m =
      ((Real.exp x * (∫ s in Ioi x, Real.exp (-s) * s ^ m) : ℝ) : ℂ) := by
  induction m with
  | zero =>
    simp only [recurrenceEndpointPolynomial, pow_zero, mul_one]
    rw [integral_exp_neg_Ioi, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      Complex.ofReal_one]
  | succ m ih =>
    rw [recurrenceEndpointPolynomial, ih, integral_exp_neg_mul_natPow_succ]
    have he : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow,
      Complex.ofReal_natCast, Complex.ofReal_one]
    have hec : (Real.exp x : ℂ) * (Real.exp (-x) : ℂ) = 1 := by exact_mod_cast he
    linear_combination -(x : ℂ) ^ (m + 1) * hec

theorem integrableOn_complex_exp_neg_mul_natPow (x : ℝ) (m : ℕ) :
    IntegrableOn (fun s : ℝ => (Real.exp (-s) : ℂ) * (s : ℂ) ^ m) (Ioi x) := by
  have h : IntegrableOn (fun s : ℝ => ((Real.exp (-s) * s ^ m : ℝ) : ℂ)) (Ioi x) :=
    (integrableOn_exp_neg_mul_natPow x m).ofReal
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow] using h

/-- Exact complex-valued tail formula, without an incomplete-gamma definition. -/
theorem recurrenceEndpointPolynomial_eq_exp_mul_tail (x : ℝ) (m : ℕ) :
    recurrenceEndpointPolynomial (x : ℂ) m =
      (Real.exp x : ℂ) *
        ∫ s in Ioi x, (Real.exp (-s) : ℂ) * (s : ℂ) ^ m := by
  rw [recurrenceEndpointPolynomial_eq_exp_mul_realTail]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, integral_complex_ofReal]

/-- The finite coefficient readout is the exponential tail of its polynomial. -/
theorem recurrenceEndpointPolynomial_sum_eq_exp_mul_tail
    (x : ℝ) (s : Finset ℕ) (r : ℕ → ℂ) :
    (∑ m ∈ s, r m * recurrenceEndpointPolynomial (x : ℂ) m) =
      (Real.exp x : ℂ) *
        ∫ t in Ioi x, (Real.exp (-t) : ℂ) * (∑ m ∈ s, r m * (t : ℂ) ^ m) := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum s (fun m _ => ?_)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [recurrenceEndpointPolynomial_eq_exp_mul_tail]
    have h : (∫ t in Ioi x, (Real.exp (-t) : ℂ) * (r m * (t : ℂ) ^ m)) =
        r m * ∫ t in Ioi x, (Real.exp (-t) : ℂ) * (t : ℂ) ^ m := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      ring
    rw [h]
    ring
  · convert! (integrableOn_complex_exp_neg_mul_natPow x m).const_mul (r m) using 1
    ext t
    ring

/-- Section 3 of the endpoint notes: the projected homogeneous coefficients
equal the actual exponential tail at either jump endpoint. -/
theorem twoJumpMoment_projected_endpoint_eq_exp_mul_tail
    (t1 t2 : ℂ) (x : ℝ) (hx : (x : ℂ) = t1 ∨ (x : ℂ) = t2)
    (s : Finset ℕ) (r : ℕ → ℂ) :
    (∑ m ∈ s, r m * twoJumpMomentF t1 t2 m) +
        ((x : ℂ) + 1) * (∑ m ∈ s, r m * twoJumpMomentG t1 t2 m) =
      (Real.exp x : ℂ) *
        ∫ t in Ioi x, (Real.exp (-t) : ℂ) * (∑ m ∈ s, r m * (t : ℂ) ^ m) := by
  rw [twoJumpMoment_projected_endpoint_duality t1 t2 (x : ℂ) hx]
  exact recurrenceEndpointPolynomial_sum_eq_exp_mul_tail x s r

end

end NativeCarryFiveFieldCapstone
