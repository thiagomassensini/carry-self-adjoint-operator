import CarrySelfAdjointOperator.FiveFieldLadderDifferentiation
import Mathlib.Tactic

/-!
# Differentiating the first finite ladder transition

This file instantiates the generic forward-mode derivative of one ladder
transition at the already differentiated initial state.  The hypotheses keep
the non-vanishing conditions explicit; no physical tangent identification is
made here.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

theorem twoJumpLadderStep_hasDerivAt_initial_c1
    (t1 t2 a1 a2 : ℂ)
    (hh : twoJumpInitialHeight t1 t2 a1 a2 ≠ 0)
    (h0 : (twoJumpInitialState t1 t2 a1 a2) 0 ≠ 0)
    (h1 : (twoJumpInitialState t1 t2 a1 a2) 1 ≠ 0)
    (h2 : (twoJumpInitialState t1 t2 a1 a2) 2 ≠ 0)
    (hβ : twoJumpLadderBeta 0 t1 t2
      (twoJumpInitialState t1 t2 a1 a2) ≠ 0) :
    HasDerivAt
      (fun a : ℂ => twoJumpLadderStep 0 t1 t2
        (twoJumpInitialState t1 t2 a a2))
      (twoJumpLadderStepDerivative 0 t1 t2
        (twoJumpInitialState t1 t2 a1 a2)
        (twoJumpInitialStateC1Derivative t1 t2 a1 a2)) a1 := by
  have hinit := twoJumpInitialState_hasDerivAt_c1 t1 t2 a1 a2 hh
  refine twoJumpLadderStep_hasDerivAt 0 t1 t2
    (fun a : ℂ => twoJumpInitialState t1 t2 a a2)
    (twoJumpInitialStateC1Derivative t1 t2 a1 a2) a1 ?_ h0 h1 h2 hβ
  intro i
  exact (hasDerivAt_pi.mp hinit) i

theorem twoJumpLadderStep_hasDerivAt_initial_c2
    (t1 t2 a1 a2 : ℂ)
    (hh : twoJumpInitialHeight t1 t2 a1 a2 ≠ 0)
    (h0 : (twoJumpInitialState t1 t2 a1 a2) 0 ≠ 0)
    (h1 : (twoJumpInitialState t1 t2 a1 a2) 1 ≠ 0)
    (h2 : (twoJumpInitialState t1 t2 a1 a2) 2 ≠ 0)
    (hβ : twoJumpLadderBeta 0 t1 t2
      (twoJumpInitialState t1 t2 a1 a2) ≠ 0) :
    HasDerivAt
      (fun a : ℂ => twoJumpLadderStep 0 t1 t2
        (twoJumpInitialState t1 t2 a1 a))
      (twoJumpLadderStepDerivative 0 t1 t2
        (twoJumpInitialState t1 t2 a1 a2)
        (twoJumpInitialStateC2Derivative t1 t2 a1 a2)) a2 := by
  have hinit := twoJumpInitialState_hasDerivAt_c2 t1 t2 a1 a2 hh
  refine twoJumpLadderStep_hasDerivAt 0 t1 t2
    (fun a : ℂ => twoJumpInitialState t1 t2 a1 a)
    (twoJumpInitialStateC2Derivative t1 t2 a1 a2) a2 ?_ h0 h1 h2 hβ
  intro i
  exact (hasDerivAt_pi.mp hinit) i

end

end NativeCarryFiveFieldCapstone
