import CPFormal.Analytic.CpPositionalCarryQuadraticRigidity
import Mathlib.Tactic

/-!
# All-base positional branch barrier

The positional carry geometry already identifies the unit branch mass with
the centered exponent `sigma = 1 / 2`.  This module records the corresponding
strict inequalities on both sides of the center for every base `b > 1`.

No primality, zero-set, Green, Wronskian, or spectral hypothesis is used.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open CPFormal.Carry.Cp

noncomputable section

/-- Above the centered exponent, the all-base branch ratio is below `1 / b`. -/
theorem branchRatio_lt_inv_of_half_lt_of_one_lt
    (b : ℕ) (hb : 1 < b) {sigma : ℝ}
    (hsigma : (1 : ℝ) / 2 < sigma) :
    branchRatio b sigma < (b : ℝ)⁻¹ := by
  have hbReal : 1 < (b : ℝ) := by
    exact_mod_cast hb
  have hexponent : -2 * sigma < (-1 : ℝ) := by
    linarith
  have hpow :
      (b : ℝ) ^ (-2 * sigma) < (b : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hbReal hexponent
  simpa [branchRatio, Real.rpow_neg_one] using hpow

/-- Below the centered exponent, the all-base branch ratio is above `1 / b`. -/
theorem inv_lt_branchRatio_of_pos_of_lt_half_of_one_lt
    (b : ℕ) (hb : 1 < b) {sigma : ℝ}
    (hsigma : sigma < (1 : ℝ) / 2) :
    (b : ℝ)⁻¹ < branchRatio b sigma := by
  have hbReal : 1 < (b : ℝ) := by
    exact_mod_cast hb
  have hexponent : (-1 : ℝ) < -2 * sigma := by
    linarith
  have hpow :
      (b : ℝ) ^ (-1 : ℝ) < (b : ℝ) ^ (-2 * sigma) :=
    Real.rpow_lt_rpow_of_exponent_lt hbReal hexponent
  simpa [branchRatio, Real.rpow_neg_one] using hpow

/-- Above `1 / 2`, the complete positional branch mass is strictly subunit. -/
theorem branchNormSq_lt_one_of_half_lt_of_one_lt
    (b : ℕ) (hb : 1 < b) {sigma : ℝ}
    (hsigma : (1 : ℝ) / 2 < sigma) :
    branchNormSq b sigma < 1 := by
  have hsigmaPos : 0 < sigma := by
    linarith
  have hbPos : 0 < (b : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hb)
  have hbNe : (b : ℝ) ≠ 0 := ne_of_gt hbPos
  have hratioLtOne := branchRatio_lt_one_of_one_lt b hb hsigmaPos
  have hratioLtInv :=
    branchRatio_lt_inv_of_half_lt_of_one_lt b hb hsigma
  have hbRatioLt : (b : ℝ) * branchRatio b sigma < 1 := by
    have hmul := mul_lt_mul_of_pos_left hratioLtInv hbPos
    simpa [hbNe] using hmul
  rw [branchNormSq_eq_closed_of_one_lt b hb hsigmaPos]
  rw [Nat.cast_sub (Nat.le_of_lt hb), Nat.cast_one]
  rw [← div_eq_mul_inv]
  apply (div_lt_one (sub_pos.mpr hratioLtOne)).2
  nlinarith

/-- Below `1 / 2`, the complete positional branch mass is strictly superunit. -/
theorem one_lt_branchNormSq_of_pos_of_lt_half_of_one_lt
    (b : ℕ) (hb : 1 < b) {sigma : ℝ}
    (hsigmaPos : 0 < sigma) (hsigma : sigma < (1 : ℝ) / 2) :
    1 < branchNormSq b sigma := by
  have hbPos : 0 < (b : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hb)
  have hbNe : (b : ℝ) ≠ 0 := ne_of_gt hbPos
  have hratioLtOne := branchRatio_lt_one_of_one_lt b hb hsigmaPos
  have hInvLtRatio :=
    inv_lt_branchRatio_of_pos_of_lt_half_of_one_lt b hb hsigma
  have hOneLtBRatio : 1 < (b : ℝ) * branchRatio b sigma := by
    have hmul := mul_lt_mul_of_pos_left hInvLtRatio hbPos
    simpa [hbNe] using hmul
  rw [branchNormSq_eq_closed_of_one_lt b hb hsigmaPos]
  rw [Nat.cast_sub (Nat.le_of_lt hb), Nat.cast_one]
  rw [← div_eq_mul_inv]
  apply (one_lt_div (sub_pos.mpr hratioLtOne)).2
  nlinarith

/-- Full all-base barrier: subunit branch mass occurs exactly to the right of
the centered exponent. -/
theorem branchNormSq_lt_one_iff_half_lt_of_one_lt
    (b : ℕ) (hb : 1 < b) {sigma : ℝ} (hsigmaPos : 0 < sigma) :
    branchNormSq b sigma < 1 ↔ (1 : ℝ) / 2 < sigma := by
  constructor
  · intro hmass
    rcases lt_trichotomy sigma ((1 : ℝ) / 2) with hleft | hcenter | hright
    · have hsuper :=
        one_lt_branchNormSq_of_pos_of_lt_half_of_one_lt
          b hb hsigmaPos hleft
      linarith
    · subst sigma
      have hunit : branchNormSq b ((1 : ℝ) / 2) = 1 :=
        (branchNormSq_eq_one_iff_of_one_lt b hb (by norm_num)).2 rfl
      linarith
    · exact hright
  · exact branchNormSq_lt_one_of_half_lt_of_one_lt b hb

/-- Full all-base barrier: superunit branch mass occurs exactly to the left
of the centered exponent. -/
theorem one_lt_branchNormSq_iff_lt_half_of_one_lt
    (b : ℕ) (hb : 1 < b) {sigma : ℝ} (hsigmaPos : 0 < sigma) :
    1 < branchNormSq b sigma ↔ sigma < (1 : ℝ) / 2 := by
  constructor
  · intro hmass
    rcases lt_trichotomy sigma ((1 : ℝ) / 2) with hleft | hcenter | hright
    · exact hleft
    · subst sigma
      have hunit : branchNormSq b ((1 : ℝ) / 2) = 1 :=
        (branchNormSq_eq_one_iff_of_one_lt b hb (by norm_num)).2 rfl
      linarith
    · have hsub := branchNormSq_lt_one_of_half_lt_of_one_lt b hb hright
      linarith
  · exact one_lt_branchNormSq_of_pos_of_lt_half_of_one_lt b hb hsigmaPos

/-- Compact trichotomy of the positional branch mass around `1 / 2`. -/
theorem branchNormSq_allBase_barrier
    (b : ℕ) (hb : 1 < b) {sigma : ℝ} (hsigmaPos : 0 < sigma) :
    (branchNormSq b sigma < 1 ↔ (1 : ℝ) / 2 < sigma) ∧
      (branchNormSq b sigma = 1 ↔ sigma = (1 : ℝ) / 2) ∧
        (1 < branchNormSq b sigma ↔ sigma < (1 : ℝ) / 2) := by
  exact ⟨branchNormSq_lt_one_iff_half_lt_of_one_lt b hb hsigmaPos,
    branchNormSq_eq_one_iff_of_one_lt b hb hsigmaPos,
    one_lt_branchNormSq_iff_lt_half_of_one_lt b hb hsigmaPos⟩

end

end CarrySelfAdjointOperator
