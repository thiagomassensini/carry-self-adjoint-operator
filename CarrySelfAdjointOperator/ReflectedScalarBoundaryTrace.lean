import CarrySelfAdjointOperator.ScalarBoundaryCrossProvenance
import CarrySelfAdjointOperator.TwoLegBoundaryCrossProvenance
import NativeCarryC3Crosswalk.EnrichedTfvdPairTransport
import Mathlib.Tactic

/-!
# Reflected scalar boundary trace

The scalar diagonal Wronskian

`conj(value) * logJet - conj(logJet) * value`

is exactly the native four-leg same-edge boundary under the canonical
reflection assignment

* `left = conj(logJet)`;
* `right = conj(value)`;
* `jetLeft = logJet`;
* `jetRight = value`.

This module isolates the four synthesis equalities that a concrete completed
TFVD ledger must supply. No Green identity, positivity statement, or spectral
claim is inserted into those equalities.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk

/-- Scalar wedge is definitionally the reflected four-leg boundary. -/
theorem scalarBoundaryWedge_eq_reflectedSameSEdgeBoundary
    (value logJet : ℂ) :
    scalarBoundaryWedge value logJet =
      sameSEdgeBoundaryWedge
        ((starRingEnd ℂ) logJet)
        ((starRingEnd ℂ) value)
        logJet value := by
  rfl

/-- Four local legs retained before scalar synthesis. -/
structure ReflectedBoundarySynthesisData (ι : Type*) where
  left : ι → ℂ
  right : ι → ℂ
  jetLeft : ι → ℂ
  jetRight : ι → ℂ

/-- Once the four local sums recover the reflected scalar legs, the scalar
Wronskian is the sum of local same-edge boundaries plus exact cross
provenance. -/
theorem scalarBoundaryWedge_eq_localTwoLeg_add_crossProvenance
    {ι : Type*} [Fintype ι]
    (value logJet : ℂ)
    (legs : ReflectedBoundarySynthesisData ι)
    (hleft : ∑ i : ι, legs.left i = (starRingEnd ℂ) logJet)
    (hright : ∑ i : ι, legs.right i = (starRingEnd ℂ) value)
    (hjetLeft : ∑ i : ι, legs.jetLeft i = logJet)
    (hjetRight : ∑ i : ι, legs.jetRight i = value) :
    scalarBoundaryWedge value logJet =
      (∑ i : ι,
        sameSEdgeBoundaryWedge
          (legs.left i) (legs.right i)
          (legs.jetLeft i) (legs.jetRight i)) +
        twoLegBoundaryCrossProvenance
          legs.left legs.right legs.jetLeft legs.jetRight := by
  rw [scalarBoundaryWedge_eq_reflectedSameSEdgeBoundary,
    ← hleft, ← hright, ← hjetLeft, ← hjetRight]
  exact sameSEdgeBoundaryWedge_sum_eq_local_add_crossProvenance
    legs.left legs.right legs.jetLeft legs.jetRight

/-- Adapter from the reflected local ledger to an existing enriched TFVD pair
boundary form. -/
theorem scalarBoundaryWedge_eq_enrichedTfvdBoundary_add_crossProvenance
    {ι : Type*} [Fintype ι]
    (M : ℕ) (data : FiniteC3EnrichedTfvdPairTransportData M)
    (legs : ReflectedBoundarySynthesisData ι)
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
        finiteC3EnrichedTfvdPairBoundaryForm M data) :
    scalarBoundaryWedge data.valueReadout data.logJetReadout =
      finiteC3EnrichedTfvdPairBoundaryForm M data +
        twoLegBoundaryCrossProvenance
          legs.left legs.right legs.jetLeft legs.jetRight := by
  rw [scalarBoundaryWedge_eq_localTwoLeg_add_crossProvenance
    data.valueReadout data.logJetReadout legs
      hleft hright hjetLeft hjetRight,
    hlocal]

end

end CarrySelfAdjointOperator
