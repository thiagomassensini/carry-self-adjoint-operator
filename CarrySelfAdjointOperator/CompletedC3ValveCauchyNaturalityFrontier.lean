import CarrySelfAdjointOperator.CompletedC3ValveGreenNaturality
import CarrySelfAdjointOperator.CanonicalC3GlobalCameraBoundaryBridge
import CarrySelfAdjointOperator.CanonicalCompletedC3NormalizedGammaSewing
import Mathlib.Tactic

/-!
# C3 Cauchy scalarization as same-state valve naturality

The historical final interface was phrased as equality between the completed
TFVD Wronskian and the Gamma Cauchy skew.  The preceding naturality files have
identified both sides as boundary forms of two canonical projections of the
same cutoff-one completed C3 state.

This module proves that these are not two different remaining problems:
`CanonicalCompletedC3EnrichedTfvdCauchyTraceCompatibility` is exactly diagonal
same-structured-state boundary compatibility.  Combining the pre-existing
`..._iff_scalarization` theorem then rewrites the old scalarization frontier as
one naturality statement for the canonical C3 source locus.

No new analytic identity is assumed or hidden.  This file only changes the
logical coordinates of the final gate after all source/value/log-jet/Green/
Gamma identifications have been made explicit.
-/

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- Diagonal same-state naturality on the canonical completed C3 source locus. -/
def CanonicalCompletedC3DiagonalSameStructuredBoundaryNaturality : Prop :=
  ∀ (z : ℂ), operatorHeightParameter z ∈ genuineCriticalStrip →
    ∀ hz : z.im ≠ 0,
      CanonicalCompletedC3SameStructuredBoundaryCompatibility z z hz hz

/-- The enriched TFVD completed Wronskian is the scalar Green form of the
same structured state on the open strip. -/
theorem canonicalCompletedC3EnrichedWronskian_eq_structuredScalarGreenForm
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedGreenWronskian
        canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
        canonicalCompletedC3EnrichedTfvdBoundaryCompanion z z =
      greenForm (𝕜 := ℂ)
        (canonicalCompletedC3StructuredScalarBoundaryPair z)
        (canonicalCompletedC3StructuredScalarBoundaryPair z) := by
  rw [canonicalCompletedC3StructuredScalarBoundaryPair_eq_canonical hs]
  rw [← completedC3Wronskian_eq_scalarBoundaryGreenForm z z]
  rw [canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout_eq_characteristic
      hs,
    canonicalCompletedC3EnrichedTfvdBoundaryCompanion_eq_completedNativeOperatorBoundaryCompanion
      hs]

/-- The diagonal Gamma Cauchy boundary measure is the Gamma Green form of the
other canonical projection of the same structured state. -/
theorem canonicalCompletedC3CauchySkew_eq_structuredGammaGreenForm
    (z : ℂ) (hz : z.im ≠ 0) :
    (-(2 : ℂ) * Complex.I) *
        (completedGammaCauchySkew canonicalCompletedC3SixCameraSource z hz : ℂ) =
      greenForm (𝕜 := ℂ)
        (canonicalCompletedC3StructuredGammaBoundaryState z hz)
        (canonicalCompletedC3StructuredGammaBoundaryState z hz) := by
  rw [canonicalCompletedC3StructuredGammaBoundaryState_eq_canonical]
  rw [← canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_boundaryGreenForm]
  exact (canonicalCompletedC3PolarizedGammaBoundaryReadout_diagonal_eq_cauchySkew
    z hz).symm

/-- The old enriched-TFVD/Cauchy compatibility is exactly the statement that
the two boundary forms of the same structured C3 state agree on the diagonal. -/
theorem canonicalCompletedC3EnrichedTfvdCauchyTraceCompatibility_iff_sameStructuredNaturality :
    CanonicalCompletedC3EnrichedTfvdCauchyTraceCompatibility ↔
      CanonicalCompletedC3DiagonalSameStructuredBoundaryNaturality := by
  constructor
  · intro htrace z hs hz
    unfold CanonicalCompletedC3SameStructuredBoundaryCompatibility
    rw [← canonicalCompletedC3CauchySkew_eq_structuredGammaGreenForm z hz,
      ← canonicalCompletedC3EnrichedWronskian_eq_structuredScalarGreenForm hs]
    exact (htrace z hs hz).symm
  · intro hnatural z hs hz
    have h := hnatural z hs hz
    unfold CanonicalCompletedC3SameStructuredBoundaryCompatibility at h
    rw [← canonicalCompletedC3CauchySkew_eq_structuredGammaGreenForm z hz,
      ← canonicalCompletedC3EnrichedWronskian_eq_structuredScalarGreenForm hs]
      at h
    exact h.symm

/-- Consequently the historical Gamma Cauchy strip scalarization frontier is
literally the same-state boundary naturality frontier. -/
theorem canonicalCompletedC3GammaCauchyStripScalarization_iff_sameStructuredNaturality :
    CanonicalCompletedC3GammaCauchyStripScalarization ↔
      CanonicalCompletedC3DiagonalSameStructuredBoundaryNaturality := by
  rw [← canonicalCompletedC3EnrichedTfvdCauchyTraceCompatibility_iff_scalarization,
    canonicalCompletedC3EnrichedTfvdCauchyTraceCompatibility_iff_sameStructuredNaturality]

/-- Valve-enriched spelling of the final frontier.  The preceding files prove
that, on this same source locus, the ordinary/log-jet coordinates are the
actual additive valve curvatures, the Cp log-block sum becomes a product under
the projective valve, and the reconstructed Green port is the Gamma source.
Thus no additional carrier remains to be constructed; the unresolved theorem
is preservation of the boundary Green form between these two canonical
charts. -/
def CanonicalCompletedC3ValveBoundaryNaturalityFrontier : Prop :=
  CanonicalCompletedC3DiagonalSameStructuredBoundaryNaturality

/-- Naming the frontier through the valve layer changes no logical strength. -/
theorem canonicalCompletedC3ValveBoundaryNaturalityFrontier_iff_scalarization :
    CanonicalCompletedC3ValveBoundaryNaturalityFrontier ↔
      CanonicalCompletedC3GammaCauchyStripScalarization := by
  exact
    canonicalCompletedC3GammaCauchyStripScalarization_iff_sameStructuredNaturality.symm

end

end CarrySelfAdjointOperator
