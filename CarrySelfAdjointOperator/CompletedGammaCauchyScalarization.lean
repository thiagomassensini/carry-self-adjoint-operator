import CarrySelfAdjointOperator.CarryGammaState
import NativeCarryC3Crosswalk.RealifiedGammaGreenEnergy
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

/-!
# Exact Cauchy-to-completed Green scalarization seam

The existing realified carry gamma field already proves its diagonal energy
identity at every nonreal spectral parameter.  This file converts that real
identity into the complex normalization used by the completed native
Wronskian.  The conversion factor is forced:

`z - conj z = 2 i Im(z)`

and the existing Cauchy skew equals `-Im(z)` times the gamma energy.  Hence
the completed Wronskian has the required Green energy exactly when it equals
`-2 i` times that concrete Cauchy skew.

This isolates a literal scalarization equation between two already-defined
objects.  It does not assume that equation, nor does it identify an arbitrary
camera source with the enriched C3 port.
-/

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- Concrete real Cauchy skew tested against a selected camera source. -/
def completedGammaCauchySkew
    (source : ℂ → RealifiedCameraComplexification)
    (z : ℂ) (hz : z.im ≠ 0) : ℝ :=
  inner ℝ (source z).fst
      (allBasesCauchyBlock z hz (source z)).snd -
    inner ℝ (source z).snd
      (allBasesCauchyBlock z hz (source z)).fst

/-- Exact remaining scalarization equation in the normalization of the
completed native characteristic. -/
def HasCanonicalCompletedNativeGammaCauchyScalarization
    (source : ℂ → RealifiedCameraComplexification) : Prop :=
  ∀ (z : ℂ) (hz : z.im ≠ 0),
    completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z z =
      (-(2 : ℂ) * Complex.I) *
        (completedGammaCauchySkew source z hz : ℂ)

/-- The already-formalized gamma energy identity supplies the full canonical
off-axis Green state as soon as the concrete Cauchy scalarization is known. -/
theorem canonicalCompletedNativeGreenState_of_gammaCauchyScalarization
    (source : ℂ → RealifiedCameraComplexification)
    (hscalar :
      HasCanonicalCompletedNativeGammaCauchyScalarization source) :
    HasCanonicalCompletedNativeOperatorOffAxisDiagonalGreenState
      (totalCarryGammaState source) := by
  intro z hz
  rw [hscalar z hz]
  unfold completedGammaCauchySkew
  rw [NativeCarryC3Crosswalk.carryGammaSource_cauchy_skew_energy]
  change _ = (z - (starRingEnd ℂ) z) *
    (‖totalCarryGammaState source z‖ ^ 2 : ℂ)
  rw [totalCarryGammaState_of_im_ne_zero source hz]
  rw [WithLp.prod_norm_sq_eq_of_L2]
  apply Complex.ext <;> simp <;> ring

/-- Once the enriched source is nonzero under the hypothetical off-axis
condition, the concrete scalarization equation closes critical-line
confinement. -/
theorem riemannZeta_zero_re_eq_half_of_gammaCauchyScalarization
    (source : ℂ → RealifiedCameraComplexification)
    (hscalar :
      HasCanonicalCompletedNativeGammaCauchyScalarization source)
    {s : ℂ} (hs : s ∈ CPFormal.Analytic.Cp.genuineCriticalStrip)
    (hzero : riemannZeta s = 0)
    (hsource :
      (centeredHeightParameter s).im ≠ 0 →
        source (centeredHeightParameter s) ≠ 0) :
    s.re = (1 : ℝ) / 2 := by
  apply riemannZeta_zero_re_eq_half_of_totalCarryGammaState
    source
    (canonicalCompletedNativeGreenState_of_gammaCauchyScalarization
      source hscalar)
    hs hzero hsource

end

end CarrySelfAdjointOperator
