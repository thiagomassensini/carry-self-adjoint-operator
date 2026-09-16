import CarrySelfAdjointOperator.FiveFieldInitialStateDifferentiation
import Mathlib.Tactic

/-!
# Finite two-jump ladder recurrence

This file records the six scalar quantities used by the finite numerical
ladder as a typed Lean recurrence.  The state is ordered as
`(R₀,R₁,R₂,r₀,r₁,r₂)`.  Division is the total field division of `ℂ`; the
non-vanishing conditions needed for an analytic interpretation are therefore
kept outside this algebraic definition.

No positivity, Gamma identification, physical tangent identification, or
recurrence differentiability claim is made here.  The purpose of this layer
is only to expose the exact rational transition which the next derivative
bridge will use.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

def twoJumpLadderAlpha (n : ℕ) (t1 t2 : ℂ) (s : Fin 6 → ℂ) : ℂ :=
  ((2 * n + 1 : ℕ) : ℂ) - t1 * s 1 - t2 * s 2

def twoJumpLadderNextR1 (n : ℕ) (t1 t2 : ℂ) (s : Fin 6 → ℂ) : ℂ :=
  (t1 - twoJumpLadderAlpha n t1 t2 s) * s 1 - s 4

def twoJumpLadderNextR2 (n : ℕ) (t1 t2 : ℂ) (s : Fin 6 → ℂ) : ℂ :=
  (t2 - twoJumpLadderAlpha n t1 t2 s) * s 2 - s 5

def twoJumpLadderNextR0 (n : ℕ) (t1 t2 : ℂ) (s : Fin 6 → ℂ) : ℂ :=
  -((n + 1 : ℕ) : ℂ) + twoJumpLadderNextR1 n t1 t2 s +
    twoJumpLadderNextR2 n t1 t2 s

def twoJumpLadderBeta (n : ℕ) (t1 t2 : ℂ) (s : Fin 6 → ℂ) : ℂ :=
  (twoJumpLadderNextR0 n t1 t2 s) ^ 2 / s 0 -
    (twoJumpLadderNextR1 n t1 t2 s) ^ 2 / s 1 -
    (twoJumpLadderNextR2 n t1 t2 s) ^ 2 / s 2

def twoJumpLadderNextR1Residue (n : ℕ) (t1 t2 : ℂ) (s : Fin 6 → ℂ) : ℂ :=
  (twoJumpLadderNextR1 n t1 t2 s) ^ 2 /
    (twoJumpLadderBeta n t1 t2 s * s 1)

def twoJumpLadderNextR2Residue (n : ℕ) (t1 t2 : ℂ) (s : Fin 6 → ℂ) : ℂ :=
  (twoJumpLadderNextR2 n t1 t2 s) ^ 2 /
    (twoJumpLadderBeta n t1 t2 s * s 2)

/-- One exact rational transition of the six-field ladder. -/
def twoJumpLadderStep (n : ℕ) (t1 t2 : ℂ) (s : Fin 6 → ℂ) : Fin 6 → ℂ :=
  ![1 + twoJumpLadderNextR1Residue n t1 t2 s +
      twoJumpLadderNextR2Residue n t1 t2 s,
    twoJumpLadderNextR1Residue n t1 t2 s,
    twoJumpLadderNextR2Residue n t1 t2 s,
    twoJumpLadderNextR0 n t1 t2 s,
    twoJumpLadderNextR1 n t1 t2 s,
    twoJumpLadderNextR2 n t1 t2 s]

/-- The finite state obtained after `n` exact rational transitions. -/
def twoJumpLadderState (t1 t2 a1 a2 : ℂ) (n : ℕ) : Fin 6 → ℂ :=
  Nat.rec (twoJumpInitialState t1 t2 a1 a2)
    (fun n s => twoJumpLadderStep n t1 t2 s) n

@[simp] theorem twoJumpLadderState_zero (t1 t2 a1 a2 : ℂ) :
    twoJumpLadderState t1 t2 a1 a2 0 =
      twoJumpInitialState t1 t2 a1 a2 := by
  rfl

@[simp] theorem twoJumpLadderState_succ
    (t1 t2 a1 a2 : ℂ) (n : ℕ) :
    twoJumpLadderState t1 t2 a1 a2 (n + 1) =
      twoJumpLadderStep n t1 t2
        (twoJumpLadderState t1 t2 a1 a2 n) := by
  rfl

theorem twoJumpLadderStep_apply
    (n : ℕ) (t1 t2 : ℂ) (s : Fin 6 → ℂ) :
    twoJumpLadderStep n t1 t2 s =
      ![1 + twoJumpLadderNextR1Residue n t1 t2 s +
          twoJumpLadderNextR2Residue n t1 t2 s,
        twoJumpLadderNextR1Residue n t1 t2 s,
        twoJumpLadderNextR2Residue n t1 t2 s,
        twoJumpLadderNextR0 n t1 t2 s,
        twoJumpLadderNextR1 n t1 t2 s,
        twoJumpLadderNextR2 n t1 t2 s] := by
  rfl

theorem twoJumpLadderStep_r0
    (n : ℕ) (t1 t2 : ℂ) (s : Fin 6 → ℂ) :
    (twoJumpLadderStep n t1 t2 s) 3 =
      -((n + 1 : ℕ) : ℂ) +
        twoJumpLadderNextR1 n t1 t2 s +
        twoJumpLadderNextR2 n t1 t2 s := by
  simp [twoJumpLadderStep, twoJumpLadderNextR0]

theorem twoJumpLadderStep_r1
    (n : ℕ) (t1 t2 : ℂ) (s : Fin 6 → ℂ) :
    (twoJumpLadderStep n t1 t2 s) 4 =
      twoJumpLadderNextR1 n t1 t2 s := by
  simp [twoJumpLadderStep]

theorem twoJumpLadderStep_r2
    (n : ℕ) (t1 t2 : ℂ) (s : Fin 6 → ℂ) :
    (twoJumpLadderStep n t1 t2 s) 5 =
      twoJumpLadderNextR2 n t1 t2 s := by
  simp [twoJumpLadderStep]

theorem twoJumpLadderStep_R1
    (n : ℕ) (t1 t2 : ℂ) (s : Fin 6 → ℂ) :
    (twoJumpLadderStep n t1 t2 s) 1 =
      twoJumpLadderNextR1Residue n t1 t2 s := by
  simp [twoJumpLadderStep]

theorem twoJumpLadderStep_R2
    (n : ℕ) (t1 t2 : ℂ) (s : Fin 6 → ℂ) :
    (twoJumpLadderStep n t1 t2 s) 2 =
      twoJumpLadderNextR2Residue n t1 t2 s := by
  simp [twoJumpLadderStep]

theorem twoJumpLadderStep_R0
    (n : ℕ) (t1 t2 : ℂ) (s : Fin 6 → ℂ) :
    (twoJumpLadderStep n t1 t2 s) 0 =
      1 + twoJumpLadderNextR1Residue n t1 t2 s +
        twoJumpLadderNextR2Residue n t1 t2 s := by
  simp [twoJumpLadderStep]

theorem twoJumpLadderStep_matches_script_update
    (n : ℕ) (t1 t2 : ℂ) (s : Fin 6 → ℂ) :
    (twoJumpLadderStep n t1 t2 s) 4 =
        (t1 - twoJumpLadderAlpha n t1 t2 s) * s 1 - s 4 ∧
    (twoJumpLadderStep n t1 t2 s) 5 =
        (t2 - twoJumpLadderAlpha n t1 t2 s) * s 2 - s 5 ∧
    (twoJumpLadderStep n t1 t2 s) 3 =
        -((n + 1 : ℕ) : ℂ) +
          ((t1 - twoJumpLadderAlpha n t1 t2 s) * s 1 - s 4) +
          ((t2 - twoJumpLadderAlpha n t1 t2 s) * s 2 - s 5) := by
  constructor
  · simp [twoJumpLadderStep, twoJumpLadderNextR1]
  constructor
  · simp [twoJumpLadderStep, twoJumpLadderNextR2]
  · simp [twoJumpLadderStep, twoJumpLadderNextR0,
      twoJumpLadderNextR1, twoJumpLadderNextR2]

theorem twoJumpLadderState_one_eq_step_initial
    (t1 t2 a1 a2 : ℂ) :
    twoJumpLadderState t1 t2 a1 a2 1 =
      twoJumpLadderStep 0 t1 t2
        (twoJumpInitialState t1 t2 a1 a2) := by
  simp [twoJumpLadderState]

theorem twoJumpLadderState_zero_r0
    (t1 t2 a1 a2 : ℂ) :
    (twoJumpLadderState t1 t2 a1 a2 0) 3 = 0 := by
  simp [twoJumpLadderState, twoJumpInitialState]

theorem twoJumpLadderState_zero_r1
    (t1 t2 a1 a2 : ℂ) :
    (twoJumpLadderState t1 t2 a1 a2 0) 4 = 0 := by
  simp [twoJumpLadderState, twoJumpInitialState]

theorem twoJumpLadderState_zero_r2
    (t1 t2 a1 a2 : ℂ) :
    (twoJumpLadderState t1 t2 a1 a2 0) 5 = 0 := by
  simp [twoJumpLadderState, twoJumpInitialState]

end

end NativeCarryFiveFieldCapstone
