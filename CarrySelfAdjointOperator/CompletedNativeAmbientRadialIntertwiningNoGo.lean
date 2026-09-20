import CarrySelfAdjointOperator.CompletedNativeCentralChiralEnergyFlow
import CarrySelfAdjointOperator.CompletedNativeAmbientCentralCurvatureDecision
import Mathlib.Tactic

/-!
# No-go for the literal normalized ambient radial Gram

The following carrier statuses are now intentionally separate:

| carrier | status |
|---|---|
| literal BR2 | NO-GO (previous audit) |
| literal Gamma | NO-GO (previous audit) |
| literal normalized ambient Gram | NO-GO in this module |
| projective/chiral defect transformation | OPEN |

The ambient radial boundary defect itself tends to zero because the Hermitian
separation collapses.  Dividing by that nonzero separation on each radial
sample reveals the actual kernel mismatch.  Its central limit is strictly
positive, so the global normalized ambient boundary intertwining is false.
This is a no-go for this literal source-matched ambient realization only; it
does not rule out an independently constructed projective/chiral defect
channel.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

/-- The explicit central excess energy of the normalized literal ambient
carrier over the zeroth completed-native moment. -/
def canonicalCompletedC3NormalizedAmbientCentralExcess : ℝ :=
  ‖canonicalCompletedC3NormalizedAmbientResponseState 0
      (by norm_num [operatorHeightParameter])‖ ^ 2 -
    canonicalCompletedNativeLogDerivativeMoment 0

/-- The central excess is strictly positive.  It is the quantitative
obstruction which cannot be removed by the radial separation tending to zero.
-/
theorem canonicalCompletedC3NormalizedAmbientCentralExcess_pos :
    0 < canonicalCompletedC3NormalizedAmbientCentralExcess := by
  unfold canonicalCompletedC3NormalizedAmbientCentralExcess
  exact sub_pos.mpr
    canonicalCompletedC3NormalizedAmbientResponseState_zero_norm_sq_gt_moment_zero

/-- The separation-regularized ambient defect has the concrete nonzero
central excess as its limit. -/
theorem canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_tendsto_centralExcess
    (N : ℕ) (i j : Fin N) :
    Filter.Tendsto
      (fun k : ℕ =>
        canonicalCompletedC3RegularizedAmbientRadialDslopeDefect k N i j)
      Filter.atTop
      (nhds (canonicalCompletedC3NormalizedAmbientCentralExcess : ℂ)) := by
  let hhalf : 0 < (operatorHeightParameter 0).re := by
    norm_num [operatorHeightParameter]
  change Filter.Tendsto
      (fun k : ℕ =>
        canonicalCompletedC3RegularizedAmbientRadialDslopeDefect k N i j)
      Filter.atTop
      (nhds (((‖canonicalCompletedC3NormalizedAmbientResponseState 0 hhalf‖ ^ 2 -
        canonicalCompletedNativeLogDerivativeMoment 0 : ℝ) : ℂ)))
  have hlimit := canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_tendsto
    N i j
  rw [Complex.ofReal_sub, Complex.ofReal_pow]
  rw [inner_self_eq_norm_sq_to_K] at hlimit
  exact hlimit

/-- If the normalized ambient boundary intertwining held globally, every
regularized radial mismatch would vanish exactly.  This is the crucial use of
the nonzero separation on each individual grid entry, not an invalid passage
from the unregularized limit. -/
theorem canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_eq_zero_of_boundaryIntertwining
    (hboundary : CanonicalCompletedC3NormalizedAmbientRadialTiltBoundaryIntertwining)
    (k N : ℕ) (i j : Fin N) :
    canonicalCompletedC3RegularizedAmbientRadialDslopeDefect k N i j = 0 := by
  rw [canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_eq_kernel_sub]
  have hmatrix :=
    canonicalCompletedC3NormalizedAmbientRadialResponseSampleMatrix_eq_dslope
      hboundary k N
  have hentry := congrFun (congrFun hmatrix i) j
  simpa only [canonicalCompletedC3NormalizedAmbientRadialResponseSampleMatrix,
    canonicalCompletedNativeAmbientRadialDslopeSampleMatrix,
    Matrix.of_apply, sub_eq_zero] using hentry

/-- The literal normalized ambient radial boundary intertwining is
impossible.  Choosing the one-point grid forces the regularized mismatch to
be identically zero, contradicting its strictly positive central limit. -/
theorem not_canonicalCompletedC3NormalizedAmbientRadialTiltBoundaryIntertwining :
    ¬ CanonicalCompletedC3NormalizedAmbientRadialTiltBoundaryIntertwining := by
  intro hboundary
  have hzero : Filter.Tendsto
      (fun k : ℕ =>
        canonicalCompletedC3RegularizedAmbientRadialDslopeDefect
          k 1 (0 : Fin 1) (0 : Fin 1))
      Filter.atTop (nhds 0) := by
    convert (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ => (0 : ℂ)) Filter.atTop (nhds 0)) using 1
    funext k
    exact
      canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_eq_zero_of_boundaryIntertwining
        hboundary k 1 0 0
  have hlimit :=
    canonicalCompletedC3RegularizedAmbientRadialDslopeDefect_tendsto_centralExcess
      1 (0 : Fin 1) (0 : Fin 1)
  have hcentral : (canonicalCompletedC3NormalizedAmbientCentralExcess : ℂ) = 0 :=
    tendsto_nhds_unique hlimit hzero
  have hcentralReal : canonicalCompletedC3NormalizedAmbientCentralExcess = 0 := by
    exact_mod_cast hcentral
  have hpositive := canonicalCompletedC3NormalizedAmbientCentralExcess_pos
  linarith

/-- Equivalent explicit no-go spelling, useful for downstream callers that
prefer a false proposition over negation. -/
theorem canonicalCompletedC3NormalizedAmbientRadialTiltBoundaryIntertwining_false :
    CanonicalCompletedC3NormalizedAmbientRadialTiltBoundaryIntertwining → False :=
  not_canonicalCompletedC3NormalizedAmbientRadialTiltBoundaryIntertwining

end

end CarrySelfAdjointOperator
