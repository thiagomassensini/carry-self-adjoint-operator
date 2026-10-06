import CarrySelfAdjointOperator.CompletedNativeAllOrderMomentUpperBound
import Mathlib.Analysis.Matrix.PosDef
import CarrySelfAdjointOperator.CompletedNativeTfvdGreenCorrectedMetric

/-! An unconditional upper frame bound for the canonical Hankel towers.
This is a necessary test for the six-source loss channel, not a construction
of that channel and not positivity of the native Hankel matrices themselves. -/
open scoped BigOperators ComplexOrder Matrix
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 800000

private theorem geometric_prefix_le_four (N : ℕ) :
    (∑ i : Fin N, (3/4 : ℝ)^(i : ℕ)) ≤ 4 := by
  have heq : ∑ i ∈ Finset.range N, (3/4 : ℝ)^i = 4*(1-(3/4 : ℝ)^N) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [Fin.sum_univ_eq_sum_range, heq]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3/4) N]

private theorem weighted_norm_sum_sq_le (N : ℕ) (x : Fin N → ℂ) :
    (∑ i : Fin N, (3/4 : ℝ)^(i : ℕ) * ‖x i‖)^2 ≤ 4 * ∑ i : Fin N, ‖x i‖^2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin N => (3/4 : ℝ)^(i : ℕ)) (fun i => ‖x i‖)
  have hg : (∑ i : Fin N, ((3/4 : ℝ)^(i : ℕ))^2) ≤ 4 := by
    apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) (geometric_prefix_le_four N)
    have hnn := pow_nonneg (by norm_num : (0 : ℝ) ≤ 3/4) (i : ℕ)
    have hone : (3/4 : ℝ)^(i : ℕ) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hb := mul_le_mul_of_nonneg_right hg
    (Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg ‖x i‖))
  exact le_trans hc hb

private theorem canonical_hankel_entry_abs_bound (i j shift : ℕ) :
    |canonicalCompletedNativeLogDerivativeMoment (i+j+shift)| ≤
      (1/2 : ℝ) * (3/4 : ℝ)^i * (3/4 : ℝ)^j := by
  have hb := canonicalCompletedNativeLogDerivativeMoment_explicit_decay (i+j+shift)
  have hp : (3/4 : ℝ)^shift ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [pow_add, pow_add] at hb
  nlinarith [mul_le_mul_of_nonneg_left hp
    (by positivity : 0 ≤ (1/2 : ℝ) * (3/4 : ℝ)^i * (3/4 : ℝ)^j)]

/-- Every finite canonical Hankel quadratic form has absolute value at most
2 times the standard coefficient energy, uniformly in the cutoff and shift.
No lower-positivity assertion is involved. -/
theorem canonicalCompletedNativeHankel_quadratic_norm_le_two
    (N shift : ℕ) (x : Fin N → ℂ) :
    ‖star x ⬝ᵥ ((Matrix.of fun i j : Fin N =>
      (canonicalCompletedNativeLogDerivativeMoment ((i : ℕ)+(j : ℕ)+shift) : ℂ)) *ᵥ x)‖ ≤
      2 * ∑ i : Fin N, ‖x i‖^2 := by
  conv_lhs =>
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, ← mul_assoc]
  calc
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, ‖star (x i) *
        (canonicalCompletedNativeLogDerivativeMoment ((i : ℕ)+(j : ℕ)+shift) : ℂ) * x j‖ := by
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro i _
      exact norm_sum_le _ _
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, (1/2 : ℝ) *
        ((3/4 : ℝ)^(i : ℕ) * ‖x i‖) * ((3/4 : ℝ)^(j : ℕ) * ‖x j‖) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
      have hb := canonical_hankel_entry_abs_bound (i : ℕ) (j : ℕ) shift
      nlinarith [mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hb (norm_nonneg (x j))) (norm_nonneg (x i))]
    _ = (1/2 : ℝ) * (∑ i : Fin N, (3/4 : ℝ)^(i : ℕ) * ‖x i‖)^2 := by
      simp only [sq, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := by
      nlinarith [weighted_norm_sum_sq_le N x]

/-- The six-frame complement is PSD for every shift, directly from the
canonical definitions and their explicit analytic bound. -/
theorem canonicalCompletedNative_six_sub_hankel_posSemidef (N shift : ℕ) :
    (Matrix.of fun i j : Fin N => (if i=j then 6 else 0) -
      (canonicalCompletedNativeLogDerivativeMoment ((i : ℕ)+(j : ℕ)+shift) : ℂ)).PosSemidef := by
  let H : Matrix (Fin N) (Fin N) ℂ := fun i j =>
    (canonicalCompletedNativeLogDerivativeMoment ((i : ℕ)+(j : ℕ)+shift) : ℂ)
  have hH : H.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [H, Nat.add_comm]
  have hM : ((6 : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - H).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    by_cases h : i=j <;> simp [H, h, eq_comm, Nat.add_comm]
  have heq : (Matrix.of fun i j : Fin N => (if i=j then 6 else 0) -
      (canonicalCompletedNativeLogDerivativeMoment ((i : ℕ)+(j : ℕ)+shift) : ℂ)) =
      (6 : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - H := by
    ext i j
    by_cases h : i=j <;> simp [H, h]
  rw [heq]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM
  intro x
  rw [Complex.nonneg_iff]
  refine ⟨?_, (hM.im_star_dotProduct_mulVec_self x).symm⟩
  have hn : star x ⬝ᵥ x = ((∑ i : Fin N, ‖x i‖^2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul',
      ← Complex.ofReal_pow, Complex.ofReal_sum]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, hn]
  simp only [smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  norm_num
  have hb := canonicalCompletedNativeHankel_quadratic_norm_le_two N shift x
  have hr := Complex.re_le_norm (star x ⬝ᵥ (H *ᵥ x))
  change ‖star x ⬝ᵥ (H *ᵥ x)‖ ≤ _ at hb
  nlinarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg ‖x i‖)]

/-- Both exact necessary six-source upper bounds hold unconditionally at
all orders. This does not construct a provenance-preserving lossMap. -/
theorem canonicalCompletedNative_six_sub_hankelPair_posSemidef (N : ℕ) :
    (Matrix.of fun i j : Fin N => (if i=j then 6 else 0) -
      (canonicalCompletedNativeLogDerivativeMoment ((i : ℕ)+(j : ℕ)) : ℂ)).PosSemidef ∧
    (Matrix.of fun i j : Fin N => (if i=j then 6 else 0) -
      (canonicalCompletedNativeLogDerivativeMoment ((i : ℕ)+(j : ℕ)+1) : ℂ)).PosSemidef := by
  constructor
  · simpa using canonicalCompletedNative_six_sub_hankel_posSemidef N 0
  · exact canonicalCompletedNative_six_sub_hankel_posSemidef N 1

/-- The actual six-source C3 excess blocks pass the all-order necessary PSD
check without assuming any correction or loss-channel realization. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_blocks_posSemidef_unconditional
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset CPFormal.Analytic.Cp.NativeGpreBoundaryContext) (N : ℕ) :
    (nativeC3SeededClockTfvdSixSourceBr2EnergyExcessEvenBlock
      M q hqpos.le hq1 S N).PosSemidef ∧
    (nativeC3SeededClockTfvdSixSourceBr2EnergyExcessOddBlock
      M q hqpos.le hq1 S N).PosSemidef := by
  rw [nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_evenBlock_eq M q hqpos hq1 S N,
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_oddBlock_eq M q hqpos hq1 S N]
  exact canonicalCompletedNative_six_sub_hankelPair_posSemidef N

end
end CarrySelfAdjointOperator
