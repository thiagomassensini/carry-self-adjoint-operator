import CarrySelfAdjointOperator.FiveFieldLadderInitialStepDifferentiation
import Mathlib.Tactic

/-!
# Differentiating finite ladder states

The derivative state is the forward-mode iteration of the derivative of one
ladder transition.  The admissibility hypothesis is finite and local: only
the states and beta denominators with index strictly below the requested
level are required to be nonzero.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

def twoJumpLadderStateC1Derivative
    (t1 t2 a1 a2 : ℂ) (n : ℕ) : Fin 6 → ℂ :=
  Nat.rec
    (twoJumpInitialStateC1Derivative t1 t2 a1 a2)
    (fun n ds =>
      twoJumpLadderStepDerivative n t1 t2
        (twoJumpLadderState t1 t2 a1 a2 n) ds) n

def twoJumpLadderStateC2Derivative
    (t1 t2 a1 a2 : ℂ) (n : ℕ) : Fin 6 → ℂ :=
  Nat.rec
    (twoJumpInitialStateC2Derivative t1 t2 a1 a2)
    (fun n ds =>
      twoJumpLadderStepDerivative n t1 t2
        (twoJumpLadderState t1 t2 a1 a2 n) ds) n

theorem twoJumpLadderState_hasDerivAt_c1
    (t1 t2 a1 a2 : ℂ) (n : ℕ)
    (hh : twoJumpInitialHeight t1 t2 a1 a2 ≠ 0)
    (hadmiss : ∀ m < n,
      (twoJumpLadderState t1 t2 a1 a2 m) 0 ≠ 0 ∧
      (twoJumpLadderState t1 t2 a1 a2 m) 1 ≠ 0 ∧
      (twoJumpLadderState t1 t2 a1 a2 m) 2 ≠ 0 ∧
      twoJumpLadderBeta m t1 t2
        (twoJumpLadderState t1 t2 a1 a2 m) ≠ 0) :
    HasDerivAt
      (fun a : ℂ => twoJumpLadderState t1 t2 a a2 n)
      (twoJumpLadderStateC1Derivative t1 t2 a1 a2 n) a1 := by
  revert hadmiss
  induction n with
  | zero =>
      intro _
      simpa [twoJumpLadderStateC1Derivative] using
        (twoJumpInitialState_hasDerivAt_c1 t1 t2 a1 a2 hh)
  | succ n ih =>
      intro hadmiss
      have hprev := ih (fun m hm =>
        hadmiss m (Nat.lt_trans hm (Nat.lt_succ_self n)))
      have hcur := hadmiss n (Nat.lt_succ_self n)
      have hstep := twoJumpLadderStep_hasDerivAt n t1 t2
        (fun a : ℂ => twoJumpLadderState t1 t2 a a2 n)
        (twoJumpLadderStateC1Derivative t1 t2 a1 a2 n) a1
        (fun i => (hasDerivAt_pi.mp hprev) i)
        hcur.1 hcur.2.1 hcur.2.2.1 hcur.2.2.2
      simpa [twoJumpLadderState, twoJumpLadderStateC1Derivative] using hstep

theorem twoJumpLadderState_hasDerivAt_c2
    (t1 t2 a1 a2 : ℂ) (n : ℕ)
    (hh : twoJumpInitialHeight t1 t2 a1 a2 ≠ 0)
    (hadmiss : ∀ m < n,
      (twoJumpLadderState t1 t2 a1 a2 m) 0 ≠ 0 ∧
      (twoJumpLadderState t1 t2 a1 a2 m) 1 ≠ 0 ∧
      (twoJumpLadderState t1 t2 a1 a2 m) 2 ≠ 0 ∧
      twoJumpLadderBeta m t1 t2
        (twoJumpLadderState t1 t2 a1 a2 m) ≠ 0) :
    HasDerivAt
      (fun a : ℂ => twoJumpLadderState t1 t2 a1 a n)
      (twoJumpLadderStateC2Derivative t1 t2 a1 a2 n) a2 := by
  revert hadmiss
  induction n with
  | zero =>
      intro _
      simpa [twoJumpLadderStateC2Derivative] using
        (twoJumpInitialState_hasDerivAt_c2 t1 t2 a1 a2 hh)
  | succ n ih =>
      intro hadmiss
      have hprev := ih (fun m hm =>
        hadmiss m (Nat.lt_trans hm (Nat.lt_succ_self n)))
      have hcur := hadmiss n (Nat.lt_succ_self n)
      have hstep := twoJumpLadderStep_hasDerivAt n t1 t2
        (fun a : ℂ => twoJumpLadderState t1 t2 a1 a n)
        (twoJumpLadderStateC2Derivative t1 t2 a1 a2 n) a2
        (fun i => (hasDerivAt_pi.mp hprev) i)
        hcur.1 hcur.2.1 hcur.2.2.1 hcur.2.2.2
      simpa [twoJumpLadderState, twoJumpLadderStateC2Derivative] using hstep

end

end NativeCarryFiveFieldCapstone
