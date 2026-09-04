import CarrySelfAdjointOperator.CompletedC3AllOrderSymplecticGammaLimit
import NativeCarrySpectralWeyl.Boundary.SourceRelation
import Mathlib.Tactic

/-!
# Symplectic Weyl trace defect

The source-parameterized Gamma field has Weyl boundary pair

`(M(z) u, u)`

where `M(z)` is the all-bases compressed Cauchy block.  Independently, the
realified camera carrier has a canonical static half-rotation whose boundary
Green form is exactly the real Green skew used by the symplectic C3 packing.

This file isolates the vector difference between those two first boundary
traces.  It is the natural operator-level unit of the dynamic-Cauchy versus
static-Green mismatch; no positivity, Wronskian sewing, or zero hypothesis is
introduced.
-/

open scoped RealInnerProductSpace

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- Quarter-turn on the two real quadratures of the camera completion. -/
def canonicalRealifiedCameraQuarterTurn :
    RealifiedCameraComplexification →ₗ[ℝ]
      RealifiedCameraComplexification where
  toFun u := WithLp.toLp 2 (-u.snd, u.fst)
  map_add' u v := by
    apply WithLp.ofLp_injective 2
    ext <;> simp
  map_smul' r u := by
    apply WithLp.ofLp_injective 2
    ext <;> simp

@[simp] theorem canonicalRealifiedCameraQuarterTurn_fst
    (u : RealifiedCameraComplexification) :
    (canonicalRealifiedCameraQuarterTurn u).fst = -u.snd :=
  rfl

@[simp] theorem canonicalRealifiedCameraQuarterTurn_snd
    (u : RealifiedCameraComplexification) :
    (canonicalRealifiedCameraQuarterTurn u).snd = u.fst :=
  rfl

/-- Static first Weyl trace whose boundary Green form reproduces the positive
orientation of `realifiedGreenSkew`.  The sign and factor `1/2` are forced by
the Green-form convention. -/
def canonicalRealifiedCameraStaticGreenTrace :
    RealifiedCameraComplexification →ₗ[ℝ]
      RealifiedCameraComplexification :=
  (-((2 : ℝ)⁻¹)) • canonicalRealifiedCameraQuarterTurn

@[simp] theorem canonicalRealifiedCameraStaticGreenTrace_fst
    (u : RealifiedCameraComplexification) :
    (canonicalRealifiedCameraStaticGreenTrace u).fst =
      (2 : ℝ)⁻¹ • u.snd := by
  simp [canonicalRealifiedCameraStaticGreenTrace, smul_smul]

@[simp] theorem canonicalRealifiedCameraStaticGreenTrace_snd
    (u : RealifiedCameraComplexification) :
    (canonicalRealifiedCameraStaticGreenTrace u).snd =
      -((2 : ℝ)⁻¹ • u.fst) := by
  simp [canonicalRealifiedCameraStaticGreenTrace, smul_smul]

/-- After the faithful symplectic C3 packing, the static first trace is
literally one half of the packed intrinsic Weyl quarter-turn.  Thus the
static Camera boundary chart is not an auxiliary normalization: it is the C3
Weyl chart transported through the existing packing. -/
theorem canonicalRealifiedCameraStaticGreenTrace_finiteC3SymplecticCameraPacking
    (M : ℕ) (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    canonicalRealifiedCameraStaticGreenTrace
        (finiteC3SymplecticCameraPacking M x) =
      (2 : ℝ)⁻¹ •
        finiteC3SymplecticCameraPacking M
          (weylChartRotation (𝕜 := ℂ) x) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp [finiteC3SymplecticCameraPacking_apply,
      weylChartRotation_apply]
  · simp [finiteC3SymplecticCameraPacking_apply,
      weylChartRotation_apply]

/-- The static half-rotation is exactly the boundary-chart realization of the
real Green skew on the two-quadrature camera carrier. -/
theorem greenForm_staticRealifiedCameraBoundary_eq_skew
    (u v : RealifiedCameraComplexification) :
    greenForm (𝕜 := ℝ)
        (canonicalRealifiedCameraStaticGreenTrace u, u)
        (canonicalRealifiedCameraStaticGreenTrace v, v) =
      NativeCarryC3Crosswalk.realifiedGreenSkew u v := by
  simp only [greenForm,
    canonicalRealifiedCameraStaticGreenTrace_fst,
    canonicalRealifiedCameraStaticGreenTrace_snd,
    NativeCarryC3Crosswalk.realifiedGreenSkew,
    WithLp.prod_inner_apply,
    real_inner_smul_left, real_inner_smul_right,
    inner_neg_left, inner_neg_right]
  ring

/-- Difference between the dynamic Weyl/Cauchy first trace and the static
Green half-rotation at one source vector. -/
def canonicalRealifiedCameraWeylTraceDefect
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u : RealifiedCameraComplexification) :
    RealifiedCameraComplexification :=
  allBasesCauchyBlock lambda hlambda u -
    canonicalRealifiedCameraStaticGreenTrace u

/-- The complete dynamic-minus-static boundary mismatch is the skew pairing
of the two Weyl trace defects with the original source vectors. -/
theorem greenForm_dynamic_sub_static_eq_weylTraceDefects
    (lambda mu : ℂ) (hlambda : lambda.im ≠ 0) (hmu : mu.im ≠ 0)
    (u v : RealifiedCameraComplexification) :
    greenForm (𝕜 := ℝ)
        (allBasesCauchyBlock lambda hlambda u, u)
        (allBasesCauchyBlock mu hmu v, v) -
      NativeCarryC3Crosswalk.realifiedGreenSkew u v =
        inner ℝ u
            (canonicalRealifiedCameraWeylTraceDefect mu hmu v) -
          inner ℝ
            (canonicalRealifiedCameraWeylTraceDefect lambda hlambda u) v := by
  rw [← greenForm_staticRealifiedCameraBoundary_eq_skew]
  unfold canonicalRealifiedCameraWeylTraceDefect
  simp only [greenForm, inner_sub_left, inner_sub_right]
  ring

/-- The same identity can be read as exact equality of the dynamic and static
boundary forms iff the two trace-defect pairings balance. -/
theorem greenForm_dynamic_eq_static_iff_weylTraceDefect_balance
    (lambda mu : ℂ) (hlambda : lambda.im ≠ 0) (hmu : mu.im ≠ 0)
    (u v : RealifiedCameraComplexification) :
    greenForm (𝕜 := ℝ)
        (allBasesCauchyBlock lambda hlambda u, u)
        (allBasesCauchyBlock mu hmu v, v) =
      NativeCarryC3Crosswalk.realifiedGreenSkew u v ↔
        inner ℝ u
            (canonicalRealifiedCameraWeylTraceDefect mu hmu v) =
          inner ℝ
            (canonicalRealifiedCameraWeylTraceDefect lambda hlambda u) v := by
  have h := greenForm_dynamic_sub_static_eq_weylTraceDefects
    lambda mu hlambda hmu u v
  constructor
  · intro heq
    rw [heq, sub_self] at h
    linarith
  · intro hbalance
    apply sub_eq_zero.mp
    rw [h, hbalance, sub_self]

end

end CarrySelfAdjointOperator
