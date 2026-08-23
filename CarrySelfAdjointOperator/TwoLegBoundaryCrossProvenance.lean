import NativeCarryC3Crosswalk.EnrichedTfvdPairTransport
import Mathlib.Tactic

/-!
# Cross provenance for the four-leg TFVD boundary

The native same-edge boundary has four scalar legs:

`right * jetLeft - left * jetRight`.

After global synthesis, each product of sums contains every ordered pair of
local coordinates. The retained cellwise TFVD boundary contains the diagonal
pairs. This module exposes all remaining ordered cross pairs at exactly the
arity used by the enriched TFVD transport.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

open CPFormal.Analytic.Cp

/-- One ordered local pair in the four-leg synthesized boundary. -/
def twoLegBoundaryPairCell
    {ι : Type*}
    (left right jetLeft jetRight : ι → ℂ) (i j : ι) : ℂ :=
  right i * jetLeft j - left i * jetRight j

/-- Complete ordered-pair ledger of the four-leg boundary. -/
def twoLegBoundaryPairwiseLedger
    {ι : Type*} [Fintype ι]
    (left right jetLeft jetRight : ι → ℂ) : ℂ :=
  ∑ i : ι, ∑ j : ι,
    twoLegBoundaryPairCell left right jetLeft jetRight i j

/-- Cross-coordinate provenance after removing the diagonal same-edge
boundaries from the complete pairwise ledger. -/
def twoLegBoundaryCrossProvenance
    {ι : Type*} [Fintype ι]
    (left right jetLeft jetRight : ι → ℂ) : ℂ :=
  twoLegBoundaryPairwiseLedger left right jetLeft jetRight -
    ∑ i : ι,
      sameSEdgeBoundaryWedge
        (left i) (right i) (jetLeft i) (jetRight i)

/-- The same-edge boundary of the four synthesized sums is the complete
ordered-pair ledger. -/
theorem sameSEdgeBoundaryWedge_sum_eq_pairwiseLedger
    {ι : Type*} [Fintype ι]
    (left right jetLeft jetRight : ι → ℂ) :
    sameSEdgeBoundaryWedge
        (∑ i : ι, left i) (∑ i : ι, right i)
        (∑ i : ι, jetLeft i) (∑ i : ι, jetRight i) =
      twoLegBoundaryPairwiseLedger left right jetLeft jetRight := by
  classical
  simp [sameSEdgeBoundaryWedge, twoLegBoundaryPairwiseLedger,
    twoLegBoundaryPairCell, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_sub_distrib]
  congr 1 <;> exact Finset.sum_comm

/-- Four-leg global synthesis equals the sum of local same-edge boundaries
plus explicit cross provenance. -/
theorem sameSEdgeBoundaryWedge_sum_eq_local_add_crossProvenance
    {ι : Type*} [Fintype ι]
    (left right jetLeft jetRight : ι → ℂ) :
    sameSEdgeBoundaryWedge
        (∑ i : ι, left i) (∑ i : ι, right i)
        (∑ i : ι, jetLeft i) (∑ i : ι, jetRight i) =
      (∑ i : ι,
        sameSEdgeBoundaryWedge
          (left i) (right i) (jetLeft i) (jetRight i)) +
        twoLegBoundaryCrossProvenance left right jetLeft jetRight := by
  rw [sameSEdgeBoundaryWedge_sum_eq_pairwiseLedger]
  unfold twoLegBoundaryCrossProvenance
  ring

end

end CarrySelfAdjointOperator
