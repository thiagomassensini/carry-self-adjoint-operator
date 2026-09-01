import CarrySelfAdjointOperator.CompletedNativeRadialHerglotzTwoPoint
import CarrySelfAdjointOperator.CompletedNativeChiralBlockMomentProbe
import Mathlib.Tactic

/-!
# Fourth-order gate for the first polarized Herglotz section

The first two-point radial Herglotz determinant has leading coefficient
`4 h₀ h₁`.  This file opens `h₁` directly in the Taylor coefficients
`cₙ` of the real reduced even characteristic.  The exact identity is

`h₁ = (c₁² - 2 c₀ c₂) / c₀²`.

Consequently the honest scalar gate for the first polarized section is the
strict fourth-order logarithmic-curvature inequality

`2 c₀ c₂ < c₁²`.

The same scalar is exactly the real third variation of the completed chiral
signature.  This isolates the next geometric obligation without identifying
the analytic moment with an unrelated positive raw TFVD Gram diagonal.
-/

namespace CarrySelfAdjointOperator

open Filter
open scoped ComplexOrder MatrixOrder

noncomputable section

/-! ## Exact second- and fourth-order logarithmic curvature -/

/-- Closed formula for the central logarithmic-derivative moment. -/
theorem canonicalCompletedNativeLogDerivativeMoment_zero_eq_secondOrderRatio :
    canonicalCompletedNativeLogDerivativeMoment 0 =
      -completedNativeRealEvenCharacteristicCoefficient 1 /
        completedNativeRealEvenCharacteristicCoefficient 0 := by
  have hzero :=
    canonicalCompletedNativeLogDerivativeMoment_real_recurrence 0
  simp only [Finset.range_zero, Finset.sum_empty, add_zero] at hzero
  norm_num at hzero
  have hc0 := completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero
  apply (eq_div_iff hc0).2
  simpa [mul_comm] using hzero

/-- The direct second-order characteristic-curvature sign. -/
def CanonicalCompletedNativeSecondOrderCharacteristicCurvaturePositive : Prop :=
  completedNativeRealEvenCharacteristicCoefficient 0 *
      completedNativeRealEvenCharacteristicCoefficient 1 < 0

/-- The second-order characteristic sign is exactly strict positivity of
the central ruler `h₀`. -/
theorem
    canonicalCompletedNativeLogDerivativeMoment_zero_pos_iff_secondOrderCharacteristicCurvature :
    0 < canonicalCompletedNativeLogDerivativeMoment 0 ↔
      CanonicalCompletedNativeSecondOrderCharacteristicCurvaturePositive := by
  rw [canonicalCompletedNativeLogDerivativeMoment_zero_eq_secondOrderRatio,
    div_pos_iff]
  unfold CanonicalCompletedNativeSecondOrderCharacteristicCurvaturePositive
  constructor
  · intro h
    rcases h with h | h
    · exact mul_neg_of_pos_of_neg h.2 (by linarith)
    · exact mul_neg_of_neg_of_pos h.2 (by linarith)
  · intro h
    rcases mul_neg_iff.mp h with h | h
    · exact Or.inl ⟨by linarith, h.1⟩
    · exact Or.inr ⟨by linarith, h.1⟩

/-- Closed formula for the first shifted logarithmic-derivative moment. -/
theorem canonicalCompletedNativeLogDerivativeMoment_one_eq_fourthOrderDiscriminant :
    canonicalCompletedNativeLogDerivativeMoment 1 =
      (completedNativeRealEvenCharacteristicCoefficient 1 ^ 2 -
        2 * completedNativeRealEvenCharacteristicCoefficient 0 *
          completedNativeRealEvenCharacteristicCoefficient 2) /
        completedNativeRealEvenCharacteristicCoefficient 0 ^ 2 := by
  have hzero :=
    canonicalCompletedNativeLogDerivativeMoment_real_recurrence 0
  have hone :=
    canonicalCompletedNativeLogDerivativeMoment_real_recurrence 1
  simp only [Finset.range_zero, Finset.sum_empty, add_zero] at hzero
  norm_num [Finset.sum_range_succ] at hone
  have hc0 := completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero
  field_simp [hc0]
  linear_combination
    completedNativeRealEvenCharacteristicCoefficient 0 * hone -
      completedNativeRealEvenCharacteristicCoefficient 1 * hzero

/-- The strict fourth-order logarithmic-curvature inequality. -/
def CanonicalCompletedNativeFourthOrderLogCurvaturePositive : Prop :=
  2 * completedNativeRealEvenCharacteristicCoefficient 0 *
      completedNativeRealEvenCharacteristicCoefficient 2 <
    completedNativeRealEvenCharacteristicCoefficient 1 ^ 2

/-- The fourth-order curvature gate is exactly strict positivity of `h₁`;
there is no loss or additional normalization in this reduction. -/
theorem
    canonicalCompletedNativeLogDerivativeMoment_one_pos_iff_fourthOrderLogCurvature :
    0 < canonicalCompletedNativeLogDerivativeMoment 1 ↔
      CanonicalCompletedNativeFourthOrderLogCurvaturePositive := by
  rw [canonicalCompletedNativeLogDerivativeMoment_one_eq_fourthOrderDiscriminant]
  have hc0sq :
      0 < completedNativeRealEvenCharacteristicCoefficient 0 ^ 2 :=
    sq_pos_of_ne_zero
      completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero
  rw [div_pos_iff]
  unfold CanonicalCompletedNativeFourthOrderLogCurvaturePositive
  constructor
  · intro h
    rcases h with h | h
    · linarith
    · exact False.elim ((not_lt_of_ge hc0sq.le) h.2)
  · intro h
    exact Or.inl ⟨by linarith, hc0sq⟩

/-- The complete direct low-order analytic gate needed by the two-point
Herglotz section. -/
def CanonicalCompletedNativeLowOrderHerglotzCurvaturePositive : Prop :=
  CanonicalCompletedNativeSecondOrderCharacteristicCurvaturePositive ∧
    CanonicalCompletedNativeFourthOrderLogCurvaturePositive

/-- The direct coefficient gate is exactly positivity of the first two
logarithmic-derivative moments. -/
theorem
    canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments :
    CanonicalCompletedNativeLowOrderHerglotzCurvaturePositive ↔
      0 < canonicalCompletedNativeLogDerivativeMoment 0 ∧
        0 < canonicalCompletedNativeLogDerivativeMoment 1 := by
  rw [CanonicalCompletedNativeLowOrderHerglotzCurvaturePositive,
    ← canonicalCompletedNativeLogDerivativeMoment_zero_pos_iff_secondOrderCharacteristicCurvature,
    ← canonicalCompletedNativeLogDerivativeMoment_one_pos_iff_fourthOrderLogCurvature]

/-! ## Chiral spelling of the same gate -/

/-- Positivity of the real first chiral-signature variation is exactly the
direct second-order characteristic-curvature sign. -/
theorem
    canonicalCompletedC3ChiralBlockSignature_firstVariation_re_pos_iff_secondOrderCharacteristicCurvature
    (M : ℕ) :
    0 < (canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 1).re ↔
      CanonicalCompletedNativeSecondOrderCharacteristicCurvaturePositive := by
  rw [canonicalCompletedC3ChiralBlockSignature_firstVariation_eq_moment_zero]
  simpa using
    canonicalCompletedNativeLogDerivativeMoment_zero_pos_iff_secondOrderCharacteristicCurvature

/-- At every cutoff, positivity of the real third chiral-signature variation
is exactly the fourth-order logarithmic-curvature inequality. -/
theorem
    canonicalCompletedC3ChiralBlockSignature_thirdVariation_re_pos_iff_fourthOrderLogCurvature
    (M : ℕ) :
    0 < (canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 3).re ↔
      CanonicalCompletedNativeFourthOrderLogCurvaturePositive := by
  rw [canonicalCompletedC3ChiralBlockSignature_thirdVariation_eq_moment_one]
  simpa using
    canonicalCompletedNativeLogDerivativeMoment_one_pos_iff_fourthOrderLogCurvature

/-- The first and third real chiral variations together are exactly the
direct low-order Herglotz curvature gate. -/
theorem
    canonicalCompletedC3ChiralBlockSignature_firstAndThirdVariations_re_pos_iff_lowOrderHerglotzCurvature
    (M : ℕ) :
    (0 < (canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 1).re ∧
      0 < (canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 3).re) ↔
        CanonicalCompletedNativeLowOrderHerglotzCurvaturePositive := by
  rw [canonicalCompletedC3ChiralBlockSignature_firstVariation_re_pos_iff_secondOrderCharacteristicCurvature,
    canonicalCompletedC3ChiralBlockSignature_thirdVariation_re_pos_iff_fourthOrderLogCurvature]
  rfl

/-! ## Two-point Herglotz and Pick consequences -/

/-- The honest direct low-order coefficient gate closes the literal
two-point radial Herglotz section, without a cross-carrier normalization
premise. -/
theorem
    canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_posSemidef_of_lowOrderCurvature
    (hlow : CanonicalCompletedNativeLowOrderHerglotzCurvaturePositive) :
    ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialHerglotzSampleMatrix k 2).PosSemidef := by
  obtain ⟨hzero, hone⟩ :=
    canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp hlow
  exact
    canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_posSemidef_of_moments
      hzero hone

/-- The same direct low-order coefficient gate closes the literal two-point
chiral Pick section. -/
theorem
    canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef_of_lowOrderCurvature
    (hlow : CanonicalCompletedNativeLowOrderHerglotzCurvaturePositive) :
    ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialChiralPickSampleMatrix k 2).PosSemidef := by
  obtain ⟨hzero, hone⟩ :=
    canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp hlow
  exact
    canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef_of_moments
      hzero hone

/-- Positive central ruler together with the exact fourth-order curvature
gate closes the literal two-point radial Herglotz section. -/
theorem
    canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_posSemidef_of_fourthOrderLogCurvature
    (hmomentZero : 0 < canonicalCompletedNativeLogDerivativeMoment 0)
    (hfourth : CanonicalCompletedNativeFourthOrderLogCurvaturePositive) :
    ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialHerglotzSampleMatrix k 2).PosSemidef := by
  exact
    canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_posSemidef_of_moments
      hmomentZero
      (canonicalCompletedNativeLogDerivativeMoment_one_pos_iff_fourthOrderLogCurvature.mpr
        hfourth)

/-- Central coisometric flatness supplies the ruler `h₀ > 0`; the exact
fourth-order curvature inequality then closes the two-point Herglotz gate. -/
theorem
    canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_posSemidef_of_centralFlat_and_fourthOrderLogCurvature
    (hflat : deriv canonicalCompletedC3CentralCoisometricEnergyDefect 0 = 0)
    (hfourth : CanonicalCompletedNativeFourthOrderLogCurvaturePositive) :
    ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialHerglotzSampleMatrix k 2).PosSemidef := by
  apply
    canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_posSemidef_of_fourthOrderLogCurvature
  · exact canonicalCompletedNativeLogDerivativeMoment_zero_pos_of_transverseCurvature
      (deriv_canonicalCompletedC3CentralCoisometricEnergyDefect_zero_eq_zero_iff.mp
        hflat)
  · exact hfourth

/-- The same two scalar curvature gates close the two-point chiral Pick
section through the exact Cayley--Herglotz congruence. -/
theorem
    canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef_of_centralFlat_and_fourthOrderLogCurvature
    (hflat : deriv canonicalCompletedC3CentralCoisometricEnergyDefect 0 = 0)
    (hfourth : CanonicalCompletedNativeFourthOrderLogCurvaturePositive) :
    ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialChiralPickSampleMatrix k 2).PosSemidef := by
  apply
    canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef_of_moments
  · exact canonicalCompletedNativeLogDerivativeMoment_zero_pos_of_transverseCurvature
      (deriv_canonicalCompletedC3CentralCoisometricEnergyDefect_zero_eq_zero_iff.mp
        hflat)
  · exact
      canonicalCompletedNativeLogDerivativeMoment_one_pos_iff_fourthOrderLogCurvature.mpr
        hfourth

end

end CarrySelfAdjointOperator
