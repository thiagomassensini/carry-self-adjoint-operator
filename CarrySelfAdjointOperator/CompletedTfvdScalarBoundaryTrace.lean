import CarrySelfAdjointOperator.ScalarBoundaryCrossProvenance
import NativeCarryC3Crosswalk.EnrichedTfvdPairTransport
import Mathlib.Tactic

/-!
# Scalar trace of an enriched TFVD pair

The enriched TFVD transport retains a synthesized value readout, a synthesized
log-jet readout, and the local same-parameter boundary cells from which the C3
Green form is built.  This file proves the exact algebraic relation between
those two levels.

Once local value and log-jet coordinates synthesize the two scalar readouts,
and each retained boundary cell is their local scalar wedge, the global scalar
Wronskian equals

`local TFVD boundary + cross-block scalar provenance`.

Combining this with any existing identity

`local TFVD boundary - Green provenance = Green form`

shows that scalar Wronskian equals Green form exactly when the retained Green
provenance and the newly exposed cross-block provenance cancel.  Thus the
remaining boundary seam is reduced to a concrete cancellation statement; no
positivity, zero hypothesis, or operator realization is inserted.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

open NativeCarryC3Crosswalk

/-- Abstract synthesis data for the local coordinates retained by one enriched
TFVD pair transport. -/
structure EnrichedTfvdScalarSynthesisData (M : ℕ) where
  valueCell : Fin M → ℂ
  logJetCell : Fin M → ℂ

/-- Exact trace formula for an arbitrary enriched TFVD transport data object. -/
theorem finiteC3EnrichedTfvdPair_scalarBoundaryTrace
    (M : ℕ) (data : FiniteC3EnrichedTfvdPairTransportData M)
    (cells : EnrichedTfvdScalarSynthesisData M)
    (hvalue : data.valueReadout = ∑ m : Fin M, cells.valueCell m)
    (hlogJet : data.logJetReadout = ∑ m : Fin M, cells.logJetCell m)
    (hcell : ∀ m : Fin M,
      (data.boundaryCells m).total =
        scalarBoundaryWedge (cells.valueCell m) (cells.logJetCell m)) :
    scalarBoundaryWedge data.valueReadout data.logJetReadout =
      finiteC3EnrichedTfvdPairBoundaryForm M data +
        scalarBoundaryCrossProvenance cells.valueCell cells.logJetCell := by
  rw [hvalue, hlogJet,
    scalarBoundaryWedge_sum_eq_local_add_crossProvenance]
  congr 1
  unfold finiteC3EnrichedTfvdPairBoundaryForm
  apply Finset.sum_congr rfl
  intro m _hm
  exact (hcell m).symm

/-- If the retained TFVD boundary differs from a Green form by an explicit
provenance channel, then the synthesized scalar trace differs from that Green
form by exactly Green provenance plus cross-block synthesis provenance. -/
theorem finiteC3EnrichedTfvdPair_scalarBoundaryTrace_eq_green_add_provenance
    (M : ℕ) (data : FiniteC3EnrichedTfvdPairTransportData M)
    (cells : EnrichedTfvdScalarSynthesisData M)
    (greenFormValue greenProvenance : ℂ)
    (hvalue : data.valueReadout = ∑ m : Fin M, cells.valueCell m)
    (hlogJet : data.logJetReadout = ∑ m : Fin M, cells.logJetCell m)
    (hcell : ∀ m : Fin M,
      (data.boundaryCells m).total =
        scalarBoundaryWedge (cells.valueCell m) (cells.logJetCell m))
    (hgreen :
      finiteC3EnrichedTfvdPairBoundaryForm M data - greenProvenance =
        greenFormValue) :
    scalarBoundaryWedge data.valueReadout data.logJetReadout =
      greenFormValue +
        (greenProvenance +
          scalarBoundaryCrossProvenance cells.valueCell cells.logJetCell) := by
  rw [finiteC3EnrichedTfvdPair_scalarBoundaryTrace
    M data cells hvalue hlogJet hcell]
  linear_combination hgreen

/-- Exact residual criterion for the boundary seam.  No information has been
lost: scalar trace equals the Green form iff the two explicit provenance
channels cancel. -/
theorem finiteC3EnrichedTfvdPair_scalarBoundaryTrace_eq_green_iff
    (M : ℕ) (data : FiniteC3EnrichedTfvdPairTransportData M)
    (cells : EnrichedTfvdScalarSynthesisData M)
    (greenFormValue greenProvenance : ℂ)
    (hvalue : data.valueReadout = ∑ m : Fin M, cells.valueCell m)
    (hlogJet : data.logJetReadout = ∑ m : Fin M, cells.logJetCell m)
    (hcell : ∀ m : Fin M,
      (data.boundaryCells m).total =
        scalarBoundaryWedge (cells.valueCell m) (cells.logJetCell m))
    (hgreen :
      finiteC3EnrichedTfvdPairBoundaryForm M data - greenProvenance =
        greenFormValue) :
    scalarBoundaryWedge data.valueReadout data.logJetReadout =
        greenFormValue ↔
      greenProvenance +
          scalarBoundaryCrossProvenance cells.valueCell cells.logJetCell = 0 := by
  rw [finiteC3EnrichedTfvdPair_scalarBoundaryTrace_eq_green_add_provenance
    M data cells greenFormValue greenProvenance
      hvalue hlogJet hcell hgreen]
  constructor
  · intro h
    exact add_left_cancel h
  · intro h
    rw [h, add_zero]

end

end CarrySelfAdjointOperator
