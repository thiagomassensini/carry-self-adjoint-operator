import CarrySelfAdjointOperator.ScalarBoundaryCrossProvenance
import NativeCarryC3Crosswalk.EnrichedTfvdPairTransport
import Mathlib.Tactic

/-!
# Scalar trace of an enriched TFVD pair

The enriched TFVD transport retains a synthesized value readout, a synthesized
log-jet readout, and local same-parameter boundary cells.  This module proves
the exact algebraic relation between those two levels.

Once local value/log-jet coordinates synthesize the scalar readouts and each
retained boundary cell is their local wedge, the global scalar Wronskian is

`local TFVD boundary + cross-block scalar provenance`.

If the local boundary minus its explicit Green provenance is a Green form,
then scalar Wronskian equals that Green form exactly when Green provenance and
cross-block synthesis provenance cancel.  No positivity, zero hypothesis,
operator realization, or confinement certificate is introduced.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

open NativeCarryC3Crosswalk

/-- Local scalar coordinates whose sums produce the readouts of an enriched
TFVD pair. -/
structure EnrichedTfvdScalarSynthesisData (M : ℕ) where
  valueCell : Fin M → ℂ
  logJetCell : Fin M → ℂ

/-- Exact scalar trace formula for an arbitrary enriched TFVD transport data
object. -/
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

/-- Substituting a provenance-resolved Green identity yields the exact scalar
boundary decomposition. -/
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

/-- Exact residual criterion for the boundary seam.  Scalar trace equals the
Green form iff the two explicit provenance channels cancel. -/
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
    apply add_left_cancel (a := greenFormValue)
    simpa using h
  · intro h
    rw [h, add_zero]

end

end CarrySelfAdjointOperator
