import CarrySelfAdjointOperator.NativeCompletedSourceFourthThetaScale
import Mathlib.Tactic

/-!
# Five-channel source Schur gate (20 November 2026)

This module does NOT assume an all-order positive kernel.
The first four S-fraction scales are already obtained from the actual
completed source. The formal fifth Stieltjes coefficient is a positive
square ratio times the canonical *even* third Schur pivot.

The open analytic obligation is to identify the fifth coefficient with
the derivative of `chainResponse 4`. The third pivot itself is proved
from the native C3 source in geometry-of-numbers PR #324, but that
revision is not yet an imported dependency of this checkout.
No positivity is asserted without those two explicit inputs.
-/

namespace CarrySelfAdjointOperator.SourcePositiveReduction

open scoped Matrix
noncomputable section
set_option autoImplicit false

local notation "m" => canonicalCompletedNativeLogDerivativeMoment

/-- First unshifted 2-by-2 moment minor. -/
def nativeFifthEvenD2 : ℝ := m 0 * m 2 - m 1 ^ 2

/-- First shifted 2-by-2 moment minor. -/
def nativeFifthOddD2 : ℝ := m 1 * m 3 - m 2 ^ 2

/-- Formal fifth Stieltjes fraction coefficient. It is expressed through
the source Schur complement, not fitted to the Jacobi numerical zeros. -/
def nativeFifthScaleCandidate : ℝ :=
  nativeFifthEvenD2 ^ 2 / nativeFifthOddD2 ^ 2 *
    sourceMomentSchur m 0 2

theorem nativeFifthEvenD2_pos : 0 < nativeFifthEvenD2 := by
  exact nativeMoment_first_discriminant_pos

theorem nativeFifthOddD2_pos : 0 < nativeFifthOddD2 := by
  exact nativeMoment_shifted_discriminant_pos

/-- The source certificate for the next unshifted three-by-three pivot
is the only remaining independent SIGN input for this formal scale. -/
theorem nativeFifthScaleCandidate_pos_of_evenThirdSchur
    (hthird : 0 < sourceMomentSchur m 0 2) :
    0 < nativeFifthScaleCandidate := by
  unfold nativeFifthScaleCandidate
  exact mul_pos
    (div_pos (sq_pos_of_pos nativeFifthEvenD2_pos)
      (sq_pos_of_pos nativeFifthOddD2_pos)) hthird

/-- A fifth positive source channel follows from (i) native C3 positive
even third pivot and (ii) the source-analytic Taylor identification.
Neither is slipped into the definition of the channel. -/
theorem chainScale_four_pos_of_evenThirdSchur_and_Taylor
    (hthird : 0 < sourceMomentSchur m 0 2)
    (hTaylor : chainScale 4 = nativeFifthScaleCandidate) :
    0 < chainScale 4 := by
  rw [hTaylor]
  exact nativeFifthScaleCandidate_pos_of_evenThirdSchur hthird

/-- The Taylor obligation can be stated as one explicit scalar defect. -/
def nativeFifthTaylorResidual : ℝ :=
  chainScale 4 - nativeFifthScaleCandidate

theorem chainScale_four_eq_candidate_iff_residual_zero :
    chainScale 4 = nativeFifthScaleCandidate ↔
      nativeFifthTaylorResidual = 0 := by
  simp [nativeFifthTaylorResidual, sub_eq_zero]


/-- The four-channel residual vanishes to order four in EACH complex
spectral argument, rather than disappearing from the full kernel. -/
theorem chainWeight_four_exact_factor (z : ℂ) :
    chainWeight 4 z =
      z ^ 4 * ∏ j ∈ Finset.range 4, chainAxis j z :=
  chainWeight_factor 4 chain_first_four_centers z

/-- The factor multiplying the fourth-stage residual has a strictly
positive central coefficient from the four already-proved scales. -/
theorem chainWeight_four_center_factor_pos :
    0 < (∏ j ∈ Finset.range 4, chainAxis j (0 : ℂ)).re := by
  have haxis (j : ℕ) (hj : j ∈ Finset.range 4) :
      chainAxis j (0 : ℂ) = (chainScale j : ℂ) :=
    chain_first_four_real_scales j (Finset.mem_range.mp hj)
  simp_rw [Finset.prod_congr rfl haxis]
  rw [← Complex.ofReal_prod]
  simp only [Complex.ofReal_re]
  apply Finset.prod_pos
  intro j hj
  exact chain_first_four_scales_pos j (Finset.mem_range.mp hj)

end

end CarrySelfAdjointOperator.SourcePositiveReduction

#print axioms CarrySelfAdjointOperator.SourcePositiveReduction.nativeFifthScaleCandidate_pos_of_evenThirdSchur
#print axioms CarrySelfAdjointOperator.SourcePositiveReduction.chainScale_four_pos_of_evenThirdSchur_and_Taylor
