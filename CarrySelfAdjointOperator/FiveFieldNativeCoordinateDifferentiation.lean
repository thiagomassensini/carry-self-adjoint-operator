import CarrySelfAdjointOperator.FiveFieldLadderStateDifferentiation
import Mathlib.Tactic

/-!
# Differentiating the native four-coordinate chart

The numerical native vector is the chart
`(log (R₁ / R₀), log (R₂ / R₀), r₁, r₂)`.  Since the parameter is complex,
the derivative of `Complex.log` is used only on the slit plane.  The two
slit-plane hypotheses are therefore kept explicit instead of being replaced
by mere non-vanishing assumptions.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

def twoJumpNativeCoordinateVector (s : Fin 6 → ℂ) : Fin 4 → ℂ :=
  ![Complex.log (s 1 / s 0), Complex.log (s 2 / s 0), s 4, s 5]

def twoJumpNativeCoordinateDerivative
    (s ds : Fin 6 → ℂ) : Fin 4 → ℂ :=
  ![ds 1 / s 1 - ds 0 / s 0, ds 2 / s 2 - ds 0 / s 0, ds 4, ds 5]

theorem twoJumpNativeCoordinateVector_hasDerivAt
    (s : ℂ → Fin 6 → ℂ) (ds : Fin 6 → ℂ) (x : ℂ)
    (hs : ∀ i, HasDerivAt (fun y : ℂ => s y i) (ds i) x)
    (h0 : s x 0 ≠ 0) (h1 : s x 1 ≠ 0) (h2 : s x 2 ≠ 0)
    (hlog1 : s x 1 / s x 0 ∈ Complex.slitPlane)
    (hlog2 : s x 2 / s x 0 ∈ Complex.slitPlane) :
    HasDerivAt
      (fun y : ℂ => twoJumpNativeCoordinateVector (s y))
      (twoJumpNativeCoordinateDerivative (s x) ds) x := by
  have hratio1 := (hs 1).div (hs 0) h0
  have hratio2 := (hs 2).div (hs 0) h0
  have hlog1' := hratio1.clog hlog1
  have hlog2' := hratio2.clog hlog2
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! hlog1' using 1
    simp [twoJumpNativeCoordinateDerivative]
    field_simp [h0, h1]
  · convert! hlog2' using 1
    simp [twoJumpNativeCoordinateDerivative]
    field_simp [h0, h2]
  · simpa [twoJumpNativeCoordinateVector, twoJumpNativeCoordinateDerivative] using hs 4
  · simpa [twoJumpNativeCoordinateVector, twoJumpNativeCoordinateDerivative] using hs 5
end
end NativeCarryFiveFieldCapstone
