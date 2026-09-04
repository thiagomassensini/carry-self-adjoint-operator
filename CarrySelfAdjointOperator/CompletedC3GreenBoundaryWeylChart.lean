import CarrySelfAdjointOperator.CompletedC3SymplecticGammaState
import NativeCarrySpectralWeyl.Boundary.SourceRelation
import Mathlib.Tactic

/-!
# Full C3 Green port as a Weyl boundary chart

The complete C3 boundary carrier is itself a two-leg Hilbert product.  The
standard Weyl quarter-turn on that product therefore gives a canonical way to
embed one complete C3 Green port into the boundary-pair space of a source
relation.

With the factor `1/2`, the boundary Green form of the embedded pair is exactly
the intrinsic C3 Green form.  This keeps every provenance coordinate and does
not pass through the obstructed coarse `C^2` scalar readout.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Boundary
open NativeCarryC3Crosswalk

noncomputable section

/-- Canonical Weyl-chart embedding of one complete C3 Green port.

For a port `u = (u₀,u₁)`, the first boundary coordinate is one half of the
symplectic quarter-turn `(-u₁,u₀)` and the second coordinate is `u` itself. -/
def canonicalC3GreenPortWeylHalfChart (M : ℕ) :
    FiniteC3GreenPortCarrier M →ₗ[ℂ]
      (FiniteC3GreenPortCarrier M × FiniteC3GreenPortCarrier M) where
  toFun u :=
    ((2 : ℂ)⁻¹ • weylChartRotation (𝕜 := ℂ) u, u)
  map_add' u v := by
    ext <;> simp
  map_smul' c u := by
    ext <;> simp [smul_smul]

@[simp] theorem canonicalC3GreenPortWeylHalfChart_apply
    (M : ℕ) (u : FiniteC3GreenPortCarrier M) :
    canonicalC3GreenPortWeylHalfChart M u =
      ((2 : ℂ)⁻¹ • weylChartRotation (𝕜 := ℂ) u, u) :=
  rfl

/-- No boundary information is lost by the half-Weyl chart. -/
theorem canonicalC3GreenPortWeylHalfChart_injective (M : ℕ) :
    Function.Injective (canonicalC3GreenPortWeylHalfChart M) := by
  intro u v huv
  exact congrArg Prod.snd huv

/-- The factor `1/2` is exactly the normalization for which the Green form of
boundary pairs reproduces the intrinsic Green form of the complete C3 port. -/
theorem greenForm_canonicalC3GreenPortWeylHalfChart
    (M : ℕ) (u v : FiniteC3GreenPortCarrier M) :
    greenForm (𝕜 := ℂ)
        (canonicalC3GreenPortWeylHalfChart M u)
        (canonicalC3GreenPortWeylHalfChart M v) =
      greenForm (𝕜 := ℂ) u v := by
  rw [canonicalC3GreenPortWeylHalfChart_apply,
    canonicalC3GreenPortWeylHalfChart_apply]
  simp only [greenForm, Prod.smul_fst, Prod.smul_snd,
    weylChartRotation_apply, inner_smul_right, inner_smul_left,
    map_inv₀, map_ofNat, Complex.conj_ofReal]
  ring

/-- The canonical completed C3 state, viewed in the full Weyl boundary chart. -/
def canonicalCompletedC3GreenWeylBoundaryState (z : ℂ) :
    FiniteC3GreenPortCarrier 3 × FiniteC3GreenPortCarrier 3 :=
  canonicalC3GreenPortWeylHalfChart 3
    (canonicalCompletedOperatorC3State z)

/-- The boundary Green form of the completed C3 Weyl-chart states is exactly
the intrinsic complex C3 Green form, with all provenance coordinates retained. -/
theorem greenForm_canonicalCompletedC3GreenWeylBoundaryState
    (z w : ℂ) :
    greenForm (𝕜 := ℂ)
        (canonicalCompletedC3GreenWeylBoundaryState z)
        (canonicalCompletedC3GreenWeylBoundaryState w) =
      greenForm (𝕜 := ℂ)
        (canonicalCompletedOperatorC3State z)
        (canonicalCompletedOperatorC3State w) := by
  exact greenForm_canonicalC3GreenPortWeylHalfChart
    3 (canonicalCompletedOperatorC3State z)
      (canonicalCompletedOperatorC3State w)

/-- Consequently the already constructed static symplectic C3 Green readout
is literally a Weyl-boundary Green form on the full, provenance-preserving
C3 port. -/
theorem canonicalCompletedC3SymplecticCameraComplexGreenReadout_eq_weylBoundaryGreenForm
    (z w : ℂ) :
    canonicalCompletedC3SymplecticCameraComplexGreenReadout z w =
      greenForm (𝕜 := ℂ)
        (canonicalCompletedC3GreenWeylBoundaryState z)
        (canonicalCompletedC3GreenWeylBoundaryState w) := by
  rw [canonicalCompletedC3SymplecticCameraComplexGreenReadout_eq_greenForm,
    greenForm_canonicalCompletedC3GreenWeylBoundaryState]

end

end CarrySelfAdjointOperator
