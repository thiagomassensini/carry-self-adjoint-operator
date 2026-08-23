import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Scalar boundary cross provenance

A synthesized scalar value is a sum of local values, and its synthesized
log-jet is a sum of local log-jets.  Their scalar Green wedge therefore
contains both the diagonal cell wedges and all ordered cross-block pairings.

This module exposes those cross terms canonically from the full pairwise local
ledger.  No analytic input, zero hypothesis, positivity premise, target
spectrum, or selected inverse is used.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

/-- Scalar same-parameter Green wedge of a value and its log jet. -/
def scalarBoundaryWedge (value logJet : ℂ) : ℂ :=
  (starRingEnd ℂ) value * logJet -
    (starRingEnd ℂ) logJet * value

/-- One ordered local pair in the synthesized scalar wedge. -/
def scalarBoundaryPairCell
    {ι : Type*} (value logJet : ι → ℂ) (i j : ι) : ℂ :=
  (starRingEnd ℂ) (value i) * logJet j -
    (starRingEnd ℂ) (logJet i) * value j

/-- Complete ordered-pair expansion of the synthesized scalar boundary. -/
def scalarBoundaryPairwiseLedger
    {ι : Type*} [Fintype ι]
    (value logJet : ι → ℂ) : ℂ :=
  ∑ i : ι, ∑ j : ι, scalarBoundaryPairCell value logJet i j

/-- Cross-block synthesis provenance, obtained from the complete ordered-pair
ledger after removing its diagonal cell wedges. -/
def scalarBoundaryCrossProvenance
    {ι : Type*} [Fintype ι]
    (value logJet : ι → ℂ) : ℂ :=
  scalarBoundaryPairwiseLedger value logJet -
    ∑ i : ι, scalarBoundaryWedge (value i) (logJet i)

/-- Expanding the two synthesized sums produces exactly the ordered-pair
ledger. -/
theorem scalarBoundaryWedge_sum_eq_pairwiseLedger
    {ι : Type*} [Fintype ι]
    (value logJet : ι → ℂ) :
    scalarBoundaryWedge (∑ i : ι, value i) (∑ i : ι, logJet i) =
      scalarBoundaryPairwiseLedger value logJet := by
  classical
  simp [scalarBoundaryWedge, scalarBoundaryPairwiseLedger,
    scalarBoundaryPairCell, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_sub_distrib]

/-- Global scalar boundary equals the sum of local cell boundaries plus the
explicit cross-block provenance. -/
theorem scalarBoundaryWedge_sum_eq_local_add_crossProvenance
    {ι : Type*} [Fintype ι]
    (value logJet : ι → ℂ) :
    scalarBoundaryWedge (∑ i : ι, value i) (∑ i : ι, logJet i) =
      (∑ i : ι, scalarBoundaryWedge (value i) (logJet i)) +
        scalarBoundaryCrossProvenance value logJet := by
  rw [scalarBoundaryWedge_sum_eq_pairwiseLedger]
  unfold scalarBoundaryCrossProvenance
  ring

/-- Equivalent residual spelling, derived from the pairwise definition rather
than used to define it. -/
theorem scalarBoundaryCrossProvenance_eq_global_sub_local
    {ι : Type*} [Fintype ι]
    (value logJet : ι → ℂ) :
    scalarBoundaryCrossProvenance value logJet =
      scalarBoundaryWedge (∑ i : ι, value i) (∑ i : ι, logJet i) -
        ∑ i : ι, scalarBoundaryWedge (value i) (logJet i) := by
  rw [scalarBoundaryWedge_sum_eq_pairwiseLedger]
  rfl

end

end CarrySelfAdjointOperator
