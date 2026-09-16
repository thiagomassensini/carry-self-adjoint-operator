import CarrySelfAdjointOperator.FiveFieldLadderRecurrence
import Mathlib.Tactic

/-!
# Exact invariants of the finite ladder state

The recurrence stores the six fields in the same order as the numerical
script.  This file records the two identities reconstructed by the script
after each finite loop: the zeroth residue is the sum constraint and the
zeroth auxiliary field is the affine residue constraint.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

theorem twoJumpLadderState_R0_eq_one_add
    (t1 t2 a1 a2 : ℂ) (n : ℕ) :
    (twoJumpLadderState t1 t2 a1 a2 n) 0 =
      1 + (twoJumpLadderState t1 t2 a1 a2 n) 1 +
        (twoJumpLadderState t1 t2 a1 a2 n) 2 := by
  induction n with
  | zero =>
      simp [twoJumpLadderState, twoJumpInitialState]
  | succ n ih =>
      simp [twoJumpLadderState_succ, twoJumpLadderStep,
        twoJumpLadderNextR1Residue, twoJumpLadderNextR2Residue]

theorem twoJumpLadderState_r0_eq_neg_level_add
    (t1 t2 a1 a2 : ℂ) (n : ℕ) :
    (twoJumpLadderState t1 t2 a1 a2 n) 3 =
      -((n : ℕ) : ℂ) +
        (twoJumpLadderState t1 t2 a1 a2 n) 4 +
        (twoJumpLadderState t1 t2 a1 a2 n) 5 := by
  induction n with
  | zero =>
      simp [twoJumpLadderState, twoJumpInitialState]
  | succ n ih =>
      simp [twoJumpLadderState_succ, twoJumpLadderStep,
        twoJumpLadderNextR0, twoJumpLadderNextR1,
        twoJumpLadderNextR2]

end

end NativeCarryFiveFieldCapstone
