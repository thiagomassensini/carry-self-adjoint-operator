import CarrySelfAdjointOperator.BoundaryCompletedTransport
import CarrySelfAdjointOperator.CompletedNativeTfvdCoefficientJets
import Mathlib.Tactic

/-!
# TFVD as boundary-completed reconstruction

The exact weighted TFVD identity is not a cutoff-shift identity.  It is the
static sister of the cutoff ledger: a vertical state is analysed into a
weighted second-difference channel and a two-coordinate boundary trace, then
reconstructed exactly by Green plus affine return.

This module presents that existing identity through the common
`boundaryAnalysis` / `boundarySynthesis` vocabulary.  It intentionally does
not identify its internal vertical shift with `U_cut` on completion tails.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- TFVD analysis retains both channels which are necessary for lossless
reconstruction: the weighted centered bracket and its boundary trace. -/
def carryWeightedVerticalTfvdBoundaryAnalysis (q : ℝ) :
    CarryVerticalL2 →ₗ[ℂ] ((ℂ × ℂ) × CarryVerticalL2) :=
  boundaryAnalysis
    (carryWeightedVerticalTrace q).toLinearMap
    (carryWeightedVerticalCenteredBracket q).toLinearMap

/-- TFVD synthesis adds the affine boundary return to the Green reconstruction
of the weighted centered bracket. -/
def carryWeightedVerticalTfvdBoundarySynthesis
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ((ℂ × ℂ) × CarryVerticalL2) →ₗ[ℂ] CarryVerticalL2 :=
  boundarySynthesis
    (carryWeightedVerticalReturn q hq0 hq1).toLinearMap
    (carryVerticalL2WeightedGreen q).toLinearMap

/-- The complete weighted TFVD is exactly a boundary reconstruction in the
common capstone language. -/
theorem carryWeightedVerticalTfvd_isBoundaryReconstruction
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    IsBoundaryReconstruction
      (carryWeightedVerticalReturn q hqpos.le hq1).toLinearMap
      (carryVerticalL2WeightedGreen q).toLinearMap
      (carryWeightedVerticalTrace q).toLinearMap
      (carryWeightedVerticalCenteredBracket q).toLinearMap := by
  apply LinearMap.ext
  intro state
  ext n
  simpa [LinearMap.add_apply, LinearMap.comp_apply, add_comm] using
    carryWeightedVerticalTfvd_apply q hqpos hq1 state n

/-- Analysis followed by synthesis is literally the identity on the whole
vertical carrier.  Hence bracket plus trace is lossless in the state direction.
-/
theorem carryWeightedVerticalTfvdBoundarySynthesis_comp_analysis
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    (carryWeightedVerticalTfvdBoundarySynthesis q hqpos.le hq1).comp
        (carryWeightedVerticalTfvdBoundaryAnalysis q) =
      LinearMap.id := by
  exact (isBoundaryReconstruction_iff_synthesis_comp_analysis_eq_id
    (carryWeightedVerticalReturn q hqpos.le hq1).toLinearMap
    (carryVerticalL2WeightedGreen q).toLinearMap
    (carryWeightedVerticalTrace q).toLinearMap
    (carryWeightedVerticalCenteredBracket q).toLinearMap).mp
      (carryWeightedVerticalTfvd_isBoundaryReconstruction q hqpos hq1)

/-- The TFVD analysis is injective: neither the weighted curvature nor the
boundary trace may be discarded before reconstruction. -/
theorem carryWeightedVerticalTfvdBoundaryAnalysis_injective
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    Function.Injective (carryWeightedVerticalTfvdBoundaryAnalysis q) := by
  exact boundaryAnalysis_injective_of_reconstruction
    (carryWeightedVerticalReturn q hqpos.le hq1).toLinearMap
    (carryVerticalL2WeightedGreen q).toLinearMap
    (carryWeightedVerticalTrace q).toLinearMap
    (carryWeightedVerticalCenteredBracket q).toLinearMap
    (carryWeightedVerticalTfvd_isBoundaryReconstruction q hqpos hq1)

/-- The finite coefficient construction is the restriction of the same
Green-plus-boundary reconstruction to a finite synthesized prefix.  This is
the concrete bridge from finite all-order coefficient jets into the TFVD
instance; it contains no moment or positivity premise. -/
theorem finiteSlopeCoefficient_tfvdBoundaryReconstruction
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (N : ℕ) (coeff : Fin N → ℂ) :
    finiteWeightedSlopeGreenResponseLinearMap q N coeff +
        finiteWeightedSlopeBoundaryReturnLinearMap q hqpos.le hq1 N coeff =
      finiteSlopeCoefficientSynthesisLinearMap N coeff :=
  finiteWeightedSlopeGreenResponse_add_boundaryReturn q hqpos hq1 N coeff

end

end CarrySelfAdjointOperator
