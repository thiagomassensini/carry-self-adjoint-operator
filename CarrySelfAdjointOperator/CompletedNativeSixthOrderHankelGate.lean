import CarrySelfAdjointOperator.CompletedNativeXiCosineMomentHerglotzGate
import Mathlib.Tactic

/-!
# The sixth-order scalar required by the three-point chiral section

The moments and the Hankel matrix are the existing native ones. We compute
their second determinant through the cosine kernel and through theta-tail
moments, without assigning it a sign. The last scalar inequality remains an
explicit analytic obligation, not a positivity assumption on the native Gram.
-/

namespace CarrySelfAdjointOperator

noncomputable section
set_option autoImplicit false

/-- Sixth-order logarithmic coefficient from the existing recurrence. -/
theorem canonicalCompletedNativeLogDerivativeMoment_two_eq_sixthOrderRatio :
    canonicalCompletedNativeLogDerivativeMoment 2 =
      (-completedNativeRealEvenCharacteristicCoefficient 1 ^ 3 +
        3 * completedNativeRealEvenCharacteristicCoefficient 0 *
          completedNativeRealEvenCharacteristicCoefficient 1 *
          completedNativeRealEvenCharacteristicCoefficient 2 -
        3 * completedNativeRealEvenCharacteristicCoefficient 0 ^ 2 *
          completedNativeRealEvenCharacteristicCoefficient 3) /
        completedNativeRealEvenCharacteristicCoefficient 0 ^ 3 := by
  have hr := canonicalCompletedNativeLogDerivativeMoment_real_recurrence 2
  norm_num [Finset.sum_range_succ] at hr
  rw [canonicalCompletedNativeLogDerivativeMoment_zero_eq_secondOrderRatio,
    canonicalCompletedNativeLogDerivativeMoment_one_eq_fourthOrderDiscriminant] at hr
  have hc := completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero
  field_simp [hc] at hr ⊢
  linear_combination hr

/-- The actual second Hankel determinant is `h₀h₂-h₁²`. -/
theorem canonicalCompletedNativeHankel_two_det_eq :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment 2).det =
      canonicalCompletedNativeLogDerivativeMoment 0 *
        canonicalCompletedNativeLogDerivativeMoment 2 -
        canonicalCompletedNativeLogDerivativeMoment 1 ^ 2 := by
  rw [Matrix.det_fin_two]
  norm_num [hankelGram, pow_two]

/-- Polynomial numerator in the original even characteristic coefficients. -/
theorem canonicalCompletedNativeHankel_two_det_eq_sixthOrderRatio :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment 2).det =
      (completedNativeRealEvenCharacteristicCoefficient 1 ^ 2 *
          completedNativeRealEvenCharacteristicCoefficient 2 +
        3 * completedNativeRealEvenCharacteristicCoefficient 0 *
          completedNativeRealEvenCharacteristicCoefficient 1 *
          completedNativeRealEvenCharacteristicCoefficient 3 -
        4 * completedNativeRealEvenCharacteristicCoefficient 0 *
          completedNativeRealEvenCharacteristicCoefficient 2 ^ 2) /
        completedNativeRealEvenCharacteristicCoefficient 0 ^ 3 := by
  rw [canonicalCompletedNativeHankel_two_det_eq,
    canonicalCompletedNativeLogDerivativeMoment_zero_eq_secondOrderRatio,
    canonicalCompletedNativeLogDerivativeMoment_one_eq_fourthOrderDiscriminant,
    canonicalCompletedNativeLogDerivativeMoment_two_eq_sixthOrderRatio]
  field_simp [completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero]
  ring

/-- Exact cosine-moment formula proposed for the second native determinant.
The `1440` denominator follows from the same `-F'/2F` normalization. -/
theorem canonicalCompletedNativeHankel_two_det_eq_xiCosineMoments :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment 2).det =
      (15 * completedNativeXiCosineMoment 1 ^ 2 * completedNativeXiCosineMoment 2 +
        3 * completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 1 *
          completedNativeXiCosineMoment 3 -
        10 * completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 2 ^ 2) /
        (1440 * completedNativeXiCosineMoment 0 ^ 3) := by
  rw [canonicalCompletedNativeHankel_two_det_eq_sixthOrderRatio,
    completedNativeRealEvenCharacteristicCoefficient_zero_eq_xiCosineMoment,
    completedNativeRealEvenCharacteristicCoefficient_one_eq_xiCosineMoment,
    completedNativeRealEvenCharacteristicCoefficient_two_eq_xiCosineMoment,
    completedNativeRealEvenCharacteristicCoefficient_three_eq_xiCosineMoment]
  ring

/-- All denominators have a proved positive sign, so the new analytic gate
is exactly the strict sign of this one explicit numerator. -/
theorem canonicalCompletedNativeHankel_two_det_pos_iff_xiSixthMoment :
    0 < (hankelGram canonicalCompletedNativeLogDerivativeMoment 2).det ↔
      10 * completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 2 ^ 2 <
        15 * completedNativeXiCosineMoment 1 ^ 2 * completedNativeXiCosineMoment 2 +
          3 * completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 1 *
            completedNativeXiCosineMoment 3 := by
  rw [canonicalCompletedNativeHankel_two_det_eq_xiCosineMoments,
    div_pos_iff_of_pos_right (mul_pos (by norm_num) (pow_pos (completedNativeXiCosineMoment_pos 0) 3)),
    sub_pos]

/-- The geometric Schur complement is an exact scalar reduction. Positivity
of `h₀` comes from the previous theta certificate, not a new hypothesis. -/
theorem canonicalCompletedNativeHankel_two_det_pos_iff_schur :
    0 < (hankelGram canonicalCompletedNativeLogDerivativeMoment 2).det ↔
      0 < canonicalCompletedNativeLogDerivativeMoment 2 -
        canonicalCompletedNativeLogDerivativeMoment 1 ^ 2 /
          canonicalCompletedNativeLogDerivativeMoment 0 := by
  have hzero := (canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp
    canonicalCompletedNativeLowOrderHerglotzCurvaturePositive).1
  rw [canonicalCompletedNativeHankel_two_det_eq]
  have heq : canonicalCompletedNativeLogDerivativeMoment 0 *
      (canonicalCompletedNativeLogDerivativeMoment 2 -
        canonicalCompletedNativeLogDerivativeMoment 1 ^ 2 /
          canonicalCompletedNativeLogDerivativeMoment 0) =
      canonicalCompletedNativeLogDerivativeMoment 0 *
        canonicalCompletedNativeLogDerivativeMoment 2 -
        canonicalCompletedNativeLogDerivativeMoment 1 ^ 2 := by
    field_simp [ne_of_gt hzero]
  rw [← heq, mul_pos_iff_of_pos_left hzero]

/-- The same obligation entirely in the theta-tail moments. In particular,
the sixth tail term is retained with its negative sign. -/
theorem canonicalCompletedNativeHankel_two_det_pos_iff_thetaTail :
    let A := completedNativeThetaTailMoment
    0 < (hankelGram canonicalCompletedNativeLogDerivativeMoment 2).det ↔
      10 * (1/2 - A 0/4) * (12*A 2-A 4/4)^2 <
        15 * (2*A 0-A 2/4)^2 * (12*A 2-A 4/4) +
          3 * (1/2-A 0/4) * (2*A 0-A 2/4) * (30*A 4-A 6/4) := by
  dsimp only
  rw [canonicalCompletedNativeHankel_two_det_pos_iff_xiSixthMoment,
    completedNativeXiCosineMoment_zero_eq_thetaTailMoments,
    completedNativeXiCosineMoment_one_eq_thetaTailMoments,
    completedNativeXiCosineMoment_two_eq_thetaTailMoments,
    completedNativeXiCosineMoment_three_eq_thetaTailMoments]
  ring_nf

/-- A concrete rational certificate sufficient for the new numerator.
These six bounds are premises of this reduction; they are not claimed as
proved theta bounds. The positive margin specifies the required accuracy. -/
theorem xiSixthMoment_numerator_lower_bound_of_box (μ₀ μ₂ μ₄ μ₆ : ℝ)
    (h₀lo : 497/1000 ≤ μ₀) (h₀hi : μ₀ ≤ 249/500)
    (h₂lo : 287/12500 ≤ μ₂)
    (h₄lo : 37/12500 ≤ μ₄) (h₄hi : μ₄ ≤ 593/200000)
    (h₆lo : 299/500000 ≤ μ₆) :
    (4861191/50000000000000 : ℝ) ≤
      15*μ₂^2*μ₄ + 3*μ₀*μ₂*μ₆ - 10*μ₀*μ₄^2 := by
  have h₀ : 0 ≤ μ₀ := by linarith
  have h₂ : 0 ≤ μ₂ := by linarith
  have h₄ : 0 ≤ μ₄ := by linarith
  have h₆ : 0 ≤ μ₆ := by linarith
  have hfirst : 15*(287/12500 : ℝ)^2*(37/12500) ≤ 15*μ₂^2*μ₄ := by gcongr
  have hsecond : 3*(497/1000 : ℝ)*(287/12500)*(299/500000) ≤ 3*μ₀*μ₂*μ₆ := by
    gcongr
  have hnegative : 10*μ₀*μ₄^2 ≤ 10*(249/500 : ℝ)*(593/200000)^2 := by gcongr
  linarith

/-- One side of the rational mass box already follows from the certified
zeroth theta-tail bound. It is reused instead of becoming a new premise. -/
theorem completedNativeXiCosineMoment_zero_lt_249_div_500 :
    completedNativeXiCosineMoment 0 < (249/500 : ℝ) := by
  rw [completedNativeXiCosineMoment_zero_eq_thetaTailMoments]
  linarith [completedNativeThetaTailMoment_zero_gt]

/-- A sufficient native certificate with only the five remaining integral
bounds. The external interval laboratory checks them, but this theorem
does not turn those external calculations into Lean proofs. -/
theorem canonicalCompletedNativeHankel_two_det_pos_of_xiMoment_bounds
    (h₀lo : (497/1000 : ℝ) ≤ completedNativeXiCosineMoment 0)
    (h₂lo : (287/12500 : ℝ) ≤ completedNativeXiCosineMoment 1)
    (h₄lo : (37/12500 : ℝ) ≤ completedNativeXiCosineMoment 2)
    (h₄hi : completedNativeXiCosineMoment 2 ≤ (593/200000 : ℝ))
    (h₆lo : (299/500000 : ℝ) ≤ completedNativeXiCosineMoment 3) :
    0 < (hankelGram canonicalCompletedNativeLogDerivativeMoment 2).det := by
  rw [canonicalCompletedNativeHankel_two_det_pos_iff_xiSixthMoment]
  have h := xiSixthMoment_numerator_lower_bound_of_box _ _ _ _ h₀lo
    completedNativeXiCosineMoment_zero_lt_249_div_500.le h₂lo h₄lo h₄hi h₆lo
  linarith

/-- Counterexample to using positivity of cosine moments and the previous
strict kurtosis inequality alone. This is an abstract moment tuple, not
the completed native characteristic. -/
theorem xiFourthMoment_sign_does_not_imply_sixthNumerator :
    let μ₀ : ℝ := 1
    let μ₂ : ℝ := 1
    let μ₄ : ℝ := 5/2
    let μ₆ : ℝ := 25/4
    0 < μ₀ ∧ 0 < μ₂ ∧ 0 < μ₄ ∧ 0 < μ₆ ∧
      μ₀*μ₄ < 3*μ₂^2 ∧
      15*μ₂^2*μ₄+3*μ₀*μ₂*μ₆-10*μ₀*μ₄^2 = -25/4 := by norm_num

/-- Even the two certified coarse theta bounds, positivity, and the first
theta moment minors do not imply the new numerator inequality for arbitrary
tuples. The witness does not assert that these numbers are native moments. -/
theorem thetaTail_coarse_bounds_do_not_imply_sixthNumerator :
    let A₀ : ℝ := 23/2000
    let A₂ : ℝ := 1/4000
    let A₄ : ℝ := 19/1000000
    let A₆ : ℝ := 3/1000000
    let μ₀ := 1/2-A₀/4
    let μ₂ := 2*A₀-A₂/4
    let μ₄ := 12*A₂-A₄/4
    let μ₆ := 30*A₄-A₆/4
    113/10000 < A₀ ∧ A₂ < 51/200000 ∧
      0 < A₀*A₄-A₂^2 ∧ 0 < A₂*A₆-A₄^2 ∧
      0 < μ₀ ∧ 0 < μ₂ ∧ 0 < μ₄ ∧ 0 < μ₆ ∧
      μ₀*μ₄ < 3*μ₂^2 ∧
      15*μ₂^2*μ₄+3*μ₀*μ₂*μ₆-10*μ₀*μ₄^2 < 0 := by norm_num

end
end CarrySelfAdjointOperator
