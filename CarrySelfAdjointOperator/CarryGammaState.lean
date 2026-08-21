import CarrySelfAdjointOperator.ConditionalCriticalLineConfinement
import NativeCarrySpectralWeyl.Boundary.GammaField

/-!
# Total off-axis carry gamma state

The existing carry gamma field is naturally defined for nonreal parameters.
This module packages it as a total state by assigning zero on the real axis.
Off the axis, injectivity of the already formalized gamma source proves that a
nonzero camera source produces a nonzero state.  Thus nonvanishing of the
final Green state reduces to nonvanishing of its concrete enriched source;
no complex Hilbert structure is imposed on the realified model.
-/

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- Totalization of the existing realified carry gamma state. -/
def totalCarryGammaState
    (source : ℂ → RealifiedCameraComplexification) (z : ℂ) :
    RealifiedNaimarkComplexification :=
  if hz : z.im ≠ 0 then
    carryGammaSource z hz (source z)
  else
    0

/-- Off the real axis, totalization is literally the existing gamma field. -/
theorem totalCarryGammaState_of_im_ne_zero
    (source : ℂ → RealifiedCameraComplexification)
    {z : ℂ} (hz : z.im ≠ 0) :
    totalCarryGammaState source z =
      carryGammaSource z hz (source z) := by
  simp [totalCarryGammaState, hz]

/-- Gamma injectivity transfers nonvanishing of the enriched camera source to
nonvanishing of the totalized state. -/
theorem totalCarryGammaState_ne_zero_of_source_ne_zero
    (source : ℂ → RealifiedCameraComplexification)
    {z : ℂ} (hz : z.im ≠ 0) (hsource : source z ≠ 0) :
    totalCarryGammaState source z ≠ 0 := by
  rw [totalCarryGammaState_of_im_ne_zero source hz]
  intro hzero
  apply hsource
  apply carryGammaSource_injective z hz
  simpa using hzero

/-- The corresponding real squared norm is nonzero off axis whenever the
source is nonzero. -/
theorem totalCarryGammaState_norm_sq_ne_zero_of_source_ne_zero
    (source : ℂ → RealifiedCameraComplexification)
    {z : ℂ} (hz : z.im ≠ 0) (hsource : source z ≠ 0) :
    ‖totalCarryGammaState source z‖ ^ 2 ≠ 0 := by
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr
    (totalCarryGammaState_ne_zero_of_source_ne_zero source hz hsource))

/-- Once the canonical diagonal Green identity is established for the
totalized gamma state, nonvanishing of its source under the hypothetical
off-axis condition closes the critical-line implication. -/
theorem riemannZeta_zero_re_eq_half_of_totalCarryGammaState
    (source : ℂ → RealifiedCameraComplexification)
    (hgreen :
      HasCanonicalCompletedNativeOperatorOffAxisDiagonalGreenState
        (totalCarryGammaState source))
    {s : ℂ} (hs : s ∈ CPFormal.Analytic.Cp.genuineCriticalStrip)
    (hzero : riemannZeta s = 0)
    (hsource :
      (centeredHeightParameter s).im ≠ 0 →
        source (centeredHeightParameter s) ≠ 0) :
    s.re = 1 / 2 := by
  apply riemannZeta_zero_re_eq_half_of_canonicalGreenState_of_offAxis_nonzero
    hgreen hs hzero
  intro hz
  exact totalCarryGammaState_ne_zero_of_source_ne_zero
    source hz (hsource hz)

end

end CarrySelfAdjointOperator
