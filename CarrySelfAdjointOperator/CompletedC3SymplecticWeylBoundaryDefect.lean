import CarrySelfAdjointOperator.CompletedC3SymplecticWeylTraceDefect
import Mathlib.Tactic

/-!
# Dynamic versus static C3 Weyl boundary pairs

The corrected finite C3 symplectic packing puts the intrinsic Green port in
the same two-quadrature Camera Hilbert space used by the all-bases Cauchy
Weyl boundary.  The source coordinate of the two boundary descriptions is
already identical; all remaining disagreement sits in the first Weyl trace.
-/

open scoped RealInnerProductSpace

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- Static C3 boundary pair after the faithful symplectic packing. -/
def canonicalFiniteC3StaticWeylBoundaryPair
    (M : ℕ) (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    RealifiedCameraComplexification × RealifiedCameraComplexification :=
  ((2 : ℝ)⁻¹ •
      finiteC3SymplecticCameraPacking M
        (weylChartRotation (𝕜 := ℂ) x),
    finiteC3SymplecticCameraPacking M x)

/-- Dynamic Weyl/Cauchy boundary pair for the same packed C3 source. -/
def canonicalFiniteC3DynamicWeylBoundaryPair
    (M : ℕ) (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    RealifiedCameraComplexification × RealifiedCameraComplexification :=
  (allBasesCauchyBlock lambda hlambda
      (finiteC3SymplecticCameraPacking M x),
    finiteC3SymplecticCameraPacking M x)

/-- The static pair can equivalently be written using the Camera-side static
trace. -/
theorem canonicalFiniteC3StaticWeylBoundaryPair_eq_cameraTrace
    (M : ℕ) (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    canonicalFiniteC3StaticWeylBoundaryPair M x =
      (canonicalRealifiedCameraStaticGreenTrace
          (finiteC3SymplecticCameraPacking M x),
        finiteC3SymplecticCameraPacking M x) := by
  unfold canonicalFiniteC3StaticWeylBoundaryPair
  rw [canonicalRealifiedCameraStaticGreenTrace_finiteC3SymplecticCameraPacking]

/-- Dynamic and static boundaries have exactly the same source coordinate;
their difference is the single first-trace Weyl defect. -/
theorem canonicalFiniteC3Dynamic_sub_staticWeylBoundaryPair
    (M : ℕ) (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    canonicalFiniteC3DynamicWeylBoundaryPair M lambda hlambda x -
        canonicalFiniteC3StaticWeylBoundaryPair M x =
      (canonicalRealifiedCameraWeylTraceDefect lambda hlambda
          (finiteC3SymplecticCameraPacking M x),
        0) := by
  rw [canonicalFiniteC3StaticWeylBoundaryPair_eq_cameraTrace]
  unfold canonicalFiniteC3DynamicWeylBoundaryPair
    canonicalRealifiedCameraWeylTraceDefect
  ext <;> simp

/-- The static packed boundary pair reproduces the real part of the complete
intrinsic C3 Green form exactly. -/
theorem greenForm_canonicalFiniteC3StaticWeylBoundaryPair
    (M : ℕ)
    (x y : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    greenForm (𝕜 := ℝ)
        (canonicalFiniteC3StaticWeylBoundaryPair M x)
        (canonicalFiniteC3StaticWeylBoundaryPair M y) =
      (greenForm (𝕜 := ℂ) x y).re := by
  rw [canonicalFiniteC3StaticWeylBoundaryPair_eq_cameraTrace,
    canonicalFiniteC3StaticWeylBoundaryPair_eq_cameraTrace,
    greenForm_staticRealifiedCameraBoundary_eq_skew,
    realifiedGreenSkew_finiteC3SymplecticCameraPacking]

/-- The dynamic-minus-static real Green mismatch is therefore exactly the
pairing of the first-trace defects. -/
theorem greenForm_canonicalFiniteC3Dynamic_sub_static_eq_traceDefects
    (M : ℕ) (lambda mu : ℂ)
    (hlambda : lambda.im ≠ 0) (hmu : mu.im ≠ 0)
    (x y : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    greenForm (𝕜 := ℝ)
        (canonicalFiniteC3DynamicWeylBoundaryPair M lambda hlambda x)
        (canonicalFiniteC3DynamicWeylBoundaryPair M mu hmu y) -
      (greenForm (𝕜 := ℂ) x y).re =
        inner ℝ (finiteC3SymplecticCameraPacking M x)
            (canonicalRealifiedCameraWeylTraceDefect mu hmu
              (finiteC3SymplecticCameraPacking M y)) -
          inner ℝ
            (canonicalRealifiedCameraWeylTraceDefect lambda hlambda
              (finiteC3SymplecticCameraPacking M x))
            (finiteC3SymplecticCameraPacking M y) := by
  unfold canonicalFiniteC3DynamicWeylBoundaryPair
  rw [← realifiedGreenSkew_finiteC3SymplecticCameraPacking]
  exact greenForm_dynamic_sub_static_eq_weylTraceDefects
    lambda mu hlambda hmu
      (finiteC3SymplecticCameraPacking M x)
      (finiteC3SymplecticCameraPacking M y)

end

end CarrySelfAdjointOperator
