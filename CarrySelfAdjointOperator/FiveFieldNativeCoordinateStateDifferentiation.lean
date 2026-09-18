import CarrySelfAdjointOperator.FiveFieldNativeCoordinateDifferentiation
import Mathlib.Tactic

/-!
# Native coordinates of the finite ladder state

This file composes the finite-state derivative with the native chart used by
the numerical audit.  The result is still a statement about the explicitly
defined finite rational family; it does not identify that family with a
physical Riemann--Hilbert tangent.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

def twoJumpNativeVector
    (t1 t2 a1 a2 : ℂ) (n : ℕ) : Fin 4 → ℂ :=
  twoJumpNativeCoordinateVector (twoJumpLadderState t1 t2 a1 a2 n)

def twoJumpNativeVectorDerivative
    (t1 t2 a1 a2 : ℂ) (n : ℕ) : Fin 4 → ℂ :=
  twoJumpNativeCoordinateDerivative
    (twoJumpLadderState t1 t2 a1 a2 n)
    (twoJumpLadderStateC1Derivative t1 t2 a1 a2 n)
def twoJumpNativeVectorC2Derivative
    (t1 t2 a1 a2 : ℂ) (n : ℕ) : Fin 4 → ℂ :=
  twoJumpNativeCoordinateDerivative
    (twoJumpLadderState t1 t2 a1 a2 n)
    (twoJumpLadderStateC2Derivative t1 t2 a1 a2 n)

theorem twoJumpNativeVector_hasDerivAt_c1
    (t1 t2 a1 a2 : ℂ) (n : ℕ)
    (hh : twoJumpInitialHeight t1 t2 a1 a2 ≠ 0)
    (hadmiss : ∀ m < n,
      (twoJumpLadderState t1 t2 a1 a2 m) 0 ≠ 0 ∧
      (twoJumpLadderState t1 t2 a1 a2 m) 1 ≠ 0 ∧
      (twoJumpLadderState t1 t2 a1 a2 m) 2 ≠ 0 ∧
      twoJumpLadderBeta m t1 t2
        (twoJumpLadderState t1 t2 a1 a2 m) ≠ 0)
    (h0 : (twoJumpLadderState t1 t2 a1 a2 n) 0 ≠ 0)
    (h1 : (twoJumpLadderState t1 t2 a1 a2 n) 1 ≠ 0)
    (h2 : (twoJumpLadderState t1 t2 a1 a2 n) 2 ≠ 0)
    (hlog1 : (twoJumpLadderState t1 t2 a1 a2 n) 1 /
        (twoJumpLadderState t1 t2 a1 a2 n) 0 ∈ Complex.slitPlane)
    (hlog2 : (twoJumpLadderState t1 t2 a1 a2 n) 2 /
        (twoJumpLadderState t1 t2 a1 a2 n) 0 ∈ Complex.slitPlane) :
    HasDerivAt
      (fun a : ℂ => twoJumpNativeVector t1 t2 a a2 n)
      (twoJumpNativeVectorDerivative t1 t2 a1 a2 n) a1 := by
  have hstate := twoJumpLadderState_hasDerivAt_c1
    t1 t2 a1 a2 n hh hadmiss
  have hcoord := twoJumpNativeCoordinateVector_hasDerivAt
    (fun a : ℂ => twoJumpLadderState t1 t2 a a2 n)
    (twoJumpLadderStateC1Derivative t1 t2 a1 a2 n) a1
    (fun i => (hasDerivAt_pi.mp hstate) i) h0 h1 h2 hlog1 hlog2
  simpa [twoJumpNativeVector, twoJumpNativeVectorDerivative] using hcoord

theorem twoJumpNativeVector_hasDerivAt_c2
    (t1 t2 a1 a2 : ℂ) (n : ℕ)
    (hh : twoJumpInitialHeight t1 t2 a1 a2 ≠ 0)
    (hadmiss : ∀ m < n,
      (twoJumpLadderState t1 t2 a1 a2 m) 0 ≠ 0 ∧
      (twoJumpLadderState t1 t2 a1 a2 m) 1 ≠ 0 ∧
      (twoJumpLadderState t1 t2 a1 a2 m) 2 ≠ 0 ∧
      twoJumpLadderBeta m t1 t2
        (twoJumpLadderState t1 t2 a1 a2 m) ≠ 0)
    (h0 : (twoJumpLadderState t1 t2 a1 a2 n) 0 ≠ 0)
    (h1 : (twoJumpLadderState t1 t2 a1 a2 n) 1 ≠ 0)
    (h2 : (twoJumpLadderState t1 t2 a1 a2 n) 2 ≠ 0)
    (hlog1 : (twoJumpLadderState t1 t2 a1 a2 n) 1 /
        (twoJumpLadderState t1 t2 a1 a2 n) 0 ∈ Complex.slitPlane)
    (hlog2 : (twoJumpLadderState t1 t2 a1 a2 n) 2 /
        (twoJumpLadderState t1 t2 a1 a2 n) 0 ∈ Complex.slitPlane) :
    HasDerivAt
      (fun a : ℂ => twoJumpNativeVector t1 t2 a1 a n)
      (twoJumpNativeVectorC2Derivative t1 t2 a1 a2 n) a2 := by
  have hstate := twoJumpLadderState_hasDerivAt_c2
    t1 t2 a1 a2 n hh hadmiss
  have hcoord := twoJumpNativeCoordinateVector_hasDerivAt
    (fun a : ℂ => twoJumpLadderState t1 t2 a1 a n)
    (twoJumpLadderStateC2Derivative t1 t2 a1 a2 n) a2
    (fun i => (hasDerivAt_pi.mp hstate) i) h0 h1 h2 hlog1 hlog2
  simpa [twoJumpNativeVector, twoJumpNativeVectorC2Derivative] using hcoord

end

end NativeCarryFiveFieldCapstone
