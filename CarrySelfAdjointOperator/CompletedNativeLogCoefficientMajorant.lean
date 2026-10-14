import CarrySelfAdjointOperator.CompletedNativeAllOrderMomentUpperBound
import CarrySelfAdjointOperator.CompletedNativeChiralReturnBoundaryCoefficientProvenance

/-! An all-order source-derived majorant, with no sign premise. -/
namespace CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem sharp_relative_coefficient (n : ℕ) :
    |completedNativeRealEvenCharacteristicCoefficient (n+1)| ≤
      completedNativeRealEvenCharacteristicCoefficient 0 * (3/35 : ℝ) * (1/25 : ℝ)^n := by
  have hb := completedNativeRealEvenCharacteristicCoefficient_succ_abs_upper n
  have h0 := completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  have he : (1 / (35 * 25^n) : ℝ) = (1/35 : ℝ)*(1/25 : ℝ)^n := by
    rw [one_div_pow, ← one_div_mul_one_div]
  rw [he] at hb
  have hh := mul_le_mul_of_nonneg_right h0 (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/25) n)
  nlinarith

private theorem sharp_majorant_recurrence (n : ℕ) :
    (3/35 : ℝ) * (((n+1 : ℕ) : ℝ) * (1/25 : ℝ)^n +
      ∑ k ∈ Finset.range n,
        ((22/175 : ℝ)^(k+1)-(1/25 : ℝ)^(k+1)) * (1/25 : ℝ)^(n-k-1)) =
      (22/175 : ℝ)^(n+1)-(1/25 : ℝ)^(n+1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have he : (∑ k ∈ Finset.range (n+1),
        ((22/175 : ℝ)^(k+1)-(1/25 : ℝ)^(k+1)) * (1/25 : ℝ)^(n+1-k-1)) =
        (1/25 : ℝ) * (∑ k ∈ Finset.range n,
        ((22/175 : ℝ)^(k+1)-(1/25 : ℝ)^(k+1)) * (1/25 : ℝ)^(n-k-1)) +
        ((22/175 : ℝ)^(n+1)-(1/25 : ℝ)^(n+1)) := by
      rw [Finset.sum_range_succ, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        rw [show n+1-k-1 = (n-k-1)+1 by omega, pow_succ]
        ring
      · simp
    rw [he]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] at ih ⊢
    nlinarith

/-- Sharper exponential control of every actual logarithmic moment. This
uses the source recurrence and unconditional theta bounds, never positivity. -/
theorem canonicalCompletedNativeLogDerivativeMoment_sharp_decay (n : ℕ) :
    |canonicalCompletedNativeLogDerivativeMoment n| ≤
      (22/175 : ℝ)^(n+1)-(1/25 : ℝ)^(n+1) := by
  have h0 : 0 < completedNativeRealEvenCharacteristicCoefficient 0 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/3)
      completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [canonicalCompletedNativeLogDerivativeMoment_eq, abs_div, abs_of_pos h0]
    apply (div_le_iff₀ h0).mpr
    have hs : |∑ k ∈ Finset.range n,
        canonicalCompletedNativeLogDerivativeMoment k *
          completedNativeRealEvenCharacteristicCoefficient (n-k)| ≤
        completedNativeRealEvenCharacteristicCoefficient 0 * (3/35 : ℝ) *
          ∑ k ∈ Finset.range n,
            ((22/175 : ℝ)^(k+1)-(1/25 : ℝ)^(k+1)) * (1/25 : ℝ)^(n-k-1) := by
      calc
        _ ≤ ∑ k ∈ Finset.range n,
            |canonicalCompletedNativeLogDerivativeMoment k| *
              |completedNativeRealEvenCharacteristicCoefficient (n-k)| := by
          simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
            (fun k => canonicalCompletedNativeLogDerivativeMoment k *
              completedNativeRealEvenCharacteristicCoefficient (n-k)) (Finset.range n)
        _ ≤ ∑ k ∈ Finset.range n,
            ((22/175 : ℝ)^(k+1)-(1/25 : ℝ)^(k+1)) *
              (completedNativeRealEvenCharacteristicCoefficient 0 * (3/35 : ℝ) *
                (1/25 : ℝ)^(n-k-1)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkn := Finset.mem_range.mp hk
          have hc := sharp_relative_coefficient (n-k-1)
          rw [show n-k-1+1 = n-k by omega] at hc
          exact mul_le_mul (ih k hkn) hc (abs_nonneg _)
            (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) (by norm_num) (k+1)))
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
    have hn := mul_le_mul_of_nonneg_left (sharp_relative_coefficient n)
      (Nat.cast_nonneg (α := ℝ) (n+1))
    have ha : |-(((n+1 : ℕ) : ℝ) * completedNativeRealEvenCharacteristicCoefficient (n+1)) -
        ∑ k ∈ Finset.range n, canonicalCompletedNativeLogDerivativeMoment k *
          completedNativeRealEvenCharacteristicCoefficient (n-k)| ≤
        ((n+1 : ℕ) : ℝ) * |completedNativeRealEvenCharacteristicCoefficient (n+1)| +
        |∑ k ∈ Finset.range n, canonicalCompletedNativeLogDerivativeMoment k *
          completedNativeRealEvenCharacteristicCoefficient (n-k)| := by
      simpa only [abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n+1))] using
        abs_sub (-(((n+1 : ℕ) : ℝ) * completedNativeRealEvenCharacteristicCoefficient (n+1))) _
    have hm := congrArg (fun t : ℝ => completedNativeRealEvenCharacteristicCoefficient 0 * t)
      (sharp_majorant_recurrence n)
    simp only [neg_mul]
    nlinarith

/-- Same bound on the actual odd coefficients, retaining their fixed factor 2. -/
theorem nativeSourceOddBoundaryCoefficient_sharp_abs_bound (n : ℕ) :
    |nativeSourceOddBoundaryCoefficient n| ≤ 2 * (22/175 : ℝ)^(n+1) := by
  rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hb := canonicalCompletedNativeLogDerivativeMoment_sharp_decay n
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/25) (n+1)]

/-- Every omitted term has a geometric majorant with its original index. -/
theorem nativeSourceOddBoundaryCoefficient_weighted_tail_term_le
    (w : ℝ) (M n : ℕ) :
    |nativeSourceOddBoundaryCoefficient (n+M)| * |w|^(n+M) ≤
      (2*(22/175 : ℝ)*((22/175 : ℝ)*|w|)^M) * ((22/175 : ℝ)*|w|)^n := by
  calc
    _ ≤ (2*(22/175 : ℝ)^(n+M+1)) * |w|^(n+M) :=
      mul_le_mul_of_nonneg_right (nativeSourceOddBoundaryCoefficient_sharp_abs_bound (n+M))
        (pow_nonneg (abs_nonneg _) _)
    _ = _ := by
      simp only [pow_succ, pow_add, mul_pow]
      ring

/-- Absolute convergence and an explicit infinite tail, uniform in the
omitted order M. This controls coefficients, not the sign of an energy. -/
theorem nativeSourceOddBoundaryCoefficient_weighted_tail
    (w : ℝ) (hw : (22/175 : ℝ)*|w| < 1) (M : ℕ) :
    Summable (fun n : ℕ => |nativeSourceOddBoundaryCoefficient (n+M)| * |w|^(n+M)) ∧
    (∑' n : ℕ, |nativeSourceOddBoundaryCoefficient (n+M)| * |w|^(n+M)) ≤
      2*(22/175 : ℝ)*((22/175 : ℝ)*|w|)^M / (1-(22/175 : ℝ)*|w|) := by
  have hz : 0 ≤ (22/175 : ℝ)*|w| := by positivity
  have hg := (summable_geometric_of_lt_one hz hw).mul_left
    (2*(22/175 : ℝ)*((22/175 : ℝ)*|w|)^M)
  have hs : Summable (fun n : ℕ =>
      |nativeSourceOddBoundaryCoefficient (n+M)| * |w|^(n+M)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun n => nativeSourceOddBoundaryCoefficient_weighted_tail_term_le w M n) hg
  refine ⟨hs, ?_⟩
  have hb := hs.tsum_le_tsum
    (fun n => nativeSourceOddBoundaryCoefficient_weighted_tail_term_le w M n) hg
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hz]),
    ← div_eq_mul_inv] at hb
  exact hb

end
end CarrySelfAdjointOperator
