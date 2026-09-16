import CarrySelfAdjointOperator.FiveFieldTangentReconstruction
import Mathlib.Tactic

/-!
# Differentiating the residue-coordinate chart

The tangent reconstruction uses the four coordinates obtained from the
matrix entries `A₁ ₀ ₁ / A₀ ₀ ₁`, `A₂ ₀ ₁ / A₀ ₀ ₁`, `A₁ ₀ ₀`, and `A₂ ₀ ₀`.
This file proves the corresponding local derivative formula.  It is a
coordinate-level statement only and does not identify a matrix family with a
physical variation.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

def twoJumpResidueCoordinateVector
    (A : Fin 3 → TwoByTwo) : Fin 4 → ℂ :=
  ![Complex.log (A 1 0 1 / A 0 0 1),
    Complex.log (A 2 0 1 / A 0 0 1), A 1 0 0, A 2 0 0]

theorem twoJumpResidueCoordinateVector_hasDerivAt
    (A : ℂ → Fin 3 → TwoByTwo) (dA : Fin 3 → TwoByTwo) (x : ℂ)
    (hA : ∀ k i j,
      HasDerivAt (fun y : ℂ => A y k i j) (dA k i j) x)
    (h001 : A x 0 0 1 ≠ 0)
    (h101 : A x 1 0 1 ≠ 0)
    (h201 : A x 2 0 1 ≠ 0)
    (hlog1 : A x 1 0 1 / A x 0 0 1 ∈ Complex.slitPlane)
    (hlog2 : A x 2 0 1 / A x 0 0 1 ∈ Complex.slitPlane) :
    HasDerivAt
      (fun y : ℂ => twoJumpResidueCoordinateVector (A y))
      (twoJumpResidueCoordinateLinear (A x) dA) x := by
  have hratio1 := (hA 1 0 1).div (hA 0 0 1) h001
  have hratio2 := (hA 2 0 1).div (hA 0 0 1) h001
  have hlog1' := hratio1.clog hlog1
  have hlog2' := hratio2.clog hlog2
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! hlog1' using 1
    simp [twoJumpResidueCoordinateLinear]
    field_simp [h001, h101]
  · convert! hlog2' using 1
    simp [twoJumpResidueCoordinateLinear]
    field_simp [h001, h201]
  · simpa [twoJumpResidueCoordinateVector, twoJumpResidueCoordinateLinear] using
      hA 1 0 0
  · simpa [twoJumpResidueCoordinateVector, twoJumpResidueCoordinateLinear] using
      hA 2 0 0

end

end NativeCarryFiveFieldCapstone
