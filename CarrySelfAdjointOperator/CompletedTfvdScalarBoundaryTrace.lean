import CarrySelfAdjointOperator.ScalarBoundaryCrossProvenance
import NativeCarryC3Crosswalk.EnrichedTfvdPairTransport
import Mathlib.Tactic

/-!
# Scalar trace of an enriched TFVD pair

The enriched TFVD transport retains a synthesized value readout, a synthesized
log-jet readout, and a local same-parameter boundary.  The local coordinates
may live on any finite provenance-labelled index, finer than the C3 block
index when necessary.

If those local coordinates synthesize the two scalar readouts and their local
wedges sum to the retained TFVD boundary, then

`global scalar boundary = local TFVD boundary + cross provenance`.

Combining this with `local boundary - Green provenance = Green form` reduces
the remaining scalar seam to one concrete cancellation between two explicit
provenance channels.  No positivity, zero hypothesis, operator realization,
or confinement certificate is introduced.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

open NativeCarryC3Crosswalk

/-- Arbitrarily fine local scalar coordinates whose sums produce the two
readouts of an enriched TFVD pair. -/
structure EnrichedTfvdScalarSynthesisData (ι : Type*) where
  valueCell : ι → ℂ
  logJetCell : ι → ℂ

/-- Exact scalar trace formula.  The local index `ι` can retain every
block/residue/edge coordinate required by the existing C3 ledger. -/
theorem finiteC3EnrichedTfvdPair_scalarBoundaryTrace
    {ι : Type*} [Fintype ι]
    (M : ℕ) (data : FiniteC3EnrichedTfvdPairTransportData M)
    (cells : EnrichedTfvdScalarSynthesisData ι)
    (hvalue : data.valueReadout = ∑ i : ι, cells.valueCell i)
    (hlogJet : data.logJetReadout = ∑ i : ι, cells.logJetCell i)
    (hlocal :
      (∑ i : ι,
        scalarBoundaryWedge (cells.valueCell i) (cells.logJetCell i)) =
          finiteC3EnrichedTfvdPairBoundaryForm M data) :
    scalarBoundaryWedge data.valueReadout data.logJetReadout =
      finiteC3EnrichedTfvdPairBoundaryForm M data +
        scalarBoundaryCrossProvenance cells.valueCell cells.logJetCell := by
  rw [hvalue, hlogJet,
    scalarBoundaryWedge_sum_eq_local_add_crossProvenance,
    hlocal]

/-- Substituting a provenance-resolved Green identity gives the complete
scalar-boundary decomposition. -/
theorem finiteC3EnrichedTfvdPair_scalarBoundaryTrace_eq_green_add_provenance
    {ι : Type*} [Fintype ι]
    (M : ℕ) (data : FiniteC3EnrichedTfvdPairTransportData M)
    (cells : EnrichedTfvdScalarSynthesisData ι)
    (greenFormValue greenProvenance : ℂ)
    (hvalue : data.valueReadout = ∑ i : ι, cells.valueCell i)
    (hlogJet : data.logJetReadout = ∑ i : ι, cells.logJetCell i)
    (hlocal :
      (∑ i : ι,
        scalarBoundaryWedge (cells.valueCell i) (cells.logJetCell i)) =
          finiteC3EnrichedTfvdPairBoundaryForm M data)
    (hgreen :
      finiteC3EnrichedTfvdPairBoundaryForm M data - greenProvenance =
        greenFormValue) :
    scalarBoundaryWedge data.valueReadout data.logJetReadout =
      greenFormValue +
        (greenProvenance +
          scalarBoundaryCrossProvenance cells.valueCell cells.logJetCell) := by
  rw [finiteC3EnrichedTfvdPair_scalarBoundaryTrace
    M data cells hvalue hlogJet hlocal]
  linear_combination hgreen

/-- Exact residual criterion for the boundary seam.  Scalar trace equals the
Green form iff the explicit Green provenance and synthesis-cross provenance
cancel. -/
theorem finiteC3EnrichedTfvdPair_scalarBoundaryTrace_eq_green_iff
    {ι : Type*} [Fintype ι]
    (M : ℕ) (data : FiniteC3EnrichedTfvdPairTransportData M)
    (cells : EnrichedTfvdScalarSynthesisData ι)
    (greenFormValue greenProvenance : ℂ)
    (hvalue : data.valueReadout = ∑ i : ι, cells.valueCell i)
    (hlogJet : data.logJetReadout = ∑ i : ι, cells.logJetCell i)
    (hlocal :
      (∑ i : ι,
        scalarBoundaryWedge (cells.valueCell i) (cells.logJetCell i)) =
          finiteC3EnrichedTfvdPairBoundaryForm M data)
    (hgreen :
      finiteC3EnrichedTfvdPairBoundaryForm M data - greenProvenance =
        greenFormValue) :
    scalarBoundaryWedge data.valueReadout data.logJetReadout =
        greenFormValue ↔
      greenProvenance +
          scalarBoundaryCrossProvenance cells.valueCell cells.logJetCell = 0 := by
  rw [finiteC3EnrichedTfvdPair_scalarBoundaryTrace_eq_green_add_provenance
    M data cells greenFormValue greenProvenance
      hvalue hlogJet hlocal hgreen]
  constructor
  · intro h
    apply add_left_cancel (a := greenFormValue)
    simpa using h
  · intro h
    rw [h, add_zero]

end

end CarrySelfAdjointOperator
