import CarrySelfAdjointOperator.ReflectedScalarBoundaryTrace
import Mathlib.Tactic

/-!
# Completed TFVD boundary-trace reduction

This module combines two already separated mechanisms:

1. scalar synthesis contributes the explicit ordered cross-coordinate
   provenance;
2. the enriched TFVD boundary differs from its Green form by an explicit
   Green provenance channel.

Therefore the scalar Wronskian equals the Green form exactly when those two
provenance channels cancel. The theorem is stated directly for the existing
`FiniteC3EnrichedTfvdPairTransportData` carrier and an arbitrarily fine finite
local coordinate index.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk

/-- Exact decomposition of the synthesized scalar trace into Green form,
retained Green provenance, and synthesis cross provenance. -/
theorem completedTfvdScalarBoundaryTrace_eq_green_add_provenance
    {ι : Type*} [Fintype ι]
    (M : ℕ) (data : FiniteC3EnrichedTfvdPairTransportData M)
    (legs : ReflectedBoundarySynthesisData ι)
    (greenFormValue greenProvenance : ℂ)
    (hleft : ∑ i : ι, legs.left i =
      (starRingEnd ℂ) data.logJetReadout)
    (hright : ∑ i : ι, legs.right i =
      (starRingEnd ℂ) data.valueReadout)
    (hjetLeft : ∑ i : ι, legs.jetLeft i = data.logJetReadout)
    (hjetRight : ∑ i : ι, legs.jetRight i = data.valueReadout)
    (hlocal :
      (∑ i : ι,
        sameSEdgeBoundaryWedge
          (legs.left i) (legs.right i)
          (legs.jetLeft i) (legs.jetRight i)) =
        finiteC3EnrichedTfvdPairBoundaryForm M data)
    (hgreen :
      finiteC3EnrichedTfvdPairBoundaryForm M data - greenProvenance =
        greenFormValue) :
    scalarBoundaryWedge data.valueReadout data.logJetReadout =
      greenFormValue +
        (greenProvenance +
          twoLegBoundaryCrossProvenance
            legs.left legs.right legs.jetLeft legs.jetRight) := by
  rw [scalarBoundaryWedge_eq_enrichedTfvdBoundary_add_crossProvenance
    M data legs hleft hright hjetLeft hjetRight hlocal]
  linear_combination hgreen

/-- Exact residual criterion for the completed boundary seam. No information
is discarded: scalar trace equals the Green form iff Green provenance and
synthesis cross provenance cancel. -/
theorem completedTfvdScalarBoundaryTrace_eq_green_iff_provenance_cancel
    {ι : Type*} [Fintype ι]
    (M : ℕ) (data : FiniteC3EnrichedTfvdPairTransportData M)
    (legs : ReflectedBoundarySynthesisData ι)
    (greenFormValue greenProvenance : ℂ)
    (hleft : ∑ i : ι, legs.left i =
      (starRingEnd ℂ) data.logJetReadout)
    (hright : ∑ i : ι, legs.right i =
      (starRingEnd ℂ) data.valueReadout)
    (hjetLeft : ∑ i : ι, legs.jetLeft i = data.logJetReadout)
    (hjetRight : ∑ i : ι, legs.jetRight i = data.valueReadout)
    (hlocal :
      (∑ i : ι,
        sameSEdgeBoundaryWedge
          (legs.left i) (legs.right i)
          (legs.jetLeft i) (legs.jetRight i)) =
        finiteC3EnrichedTfvdPairBoundaryForm M data)
    (hgreen :
      finiteC3EnrichedTfvdPairBoundaryForm M data - greenProvenance =
        greenFormValue) :
    scalarBoundaryWedge data.valueReadout data.logJetReadout =
        greenFormValue ↔
      greenProvenance +
          twoLegBoundaryCrossProvenance
            legs.left legs.right legs.jetLeft legs.jetRight = 0 := by
  rw [completedTfvdScalarBoundaryTrace_eq_green_add_provenance
    M data legs greenFormValue greenProvenance
      hleft hright hjetLeft hjetRight hlocal hgreen]
  constructor
  · intro h
    apply add_left_cancel (a := greenFormValue)
    simpa using h
  · intro h
    rw [h, add_zero]

end

end CarrySelfAdjointOperator
