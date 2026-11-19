import CarrySelfAdjointOperator.NativeCompletedSourceFourthThetaScale
import Mathlib.Tactic

/-!
Small absolute changes of one diagonal entry of a positive 2x2 Hankel prefix
can cause an order-one *relative* change of its Schur pivot. This proves
that a Parseval/energy bound in an unnormalized source coordinate does not
automatically bound the relative three-point Schur curvature.
-/
namespace CarrySelfAdjointOperator.SchurRelativeAmplification
open CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false

def nearSingularMoment (eps : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 1+eps
  | _ => 0

theorem nearSingularSchur (eps : ℝ) :
    sourceMomentSchur (nearSingularMoment eps) 0 1 = eps := by
  rw [SourcePositiveReduction.sourceMomentSchur_singleton]
  norm_num [nearSingularMoment]

theorem nearSingularMoment_diagonal_change (eps : ℝ) :
    nearSingularMoment (2*eps) 2 - nearSingularMoment eps 2 = eps := by
  simp [nearSingularMoment]
  ring

/-- Relative change is always 100%, however small the input perturbation. -/
theorem nearSingularSchur_relative_change_one (eps : ℝ) (he : 0 < eps) :
    (sourceMomentSchur (nearSingularMoment (2*eps)) 0 1 -
       sourceMomentSchur (nearSingularMoment eps) 0 1) /
       sourceMomentSchur (nearSingularMoment eps) 0 1 = 1 := by
  rw [nearSingularSchur, nearSingularSchur]
  have hne : eps ≠ 0 := ne_of_gt he
  field_simp
  ring

theorem relative_schur_not_controlled_by_absolute_diagonal_margin
    (delta : ℝ) (hd : 0 < delta) :
    ∃ eps : ℝ, 0 < eps ∧
      nearSingularMoment (2*eps) 2 - nearSingularMoment eps 2 < delta ∧
      (sourceMomentSchur (nearSingularMoment (2*eps)) 0 1 -
         sourceMomentSchur (nearSingularMoment eps) 0 1) /
         sourceMomentSchur (nearSingularMoment eps) 0 1 = 1 := by
  refine ⟨delta/2, by positivity, ?_, ?_⟩
  · rw [nearSingularMoment_diagonal_change]
    linarith
  · exact nearSingularSchur_relative_change_one _ (by positivity)

#print axioms nearSingularSchur_relative_change_one
#print axioms relative_schur_not_controlled_by_absolute_diagonal_margin
end
end CarrySelfAdjointOperator.SchurRelativeAmplification
