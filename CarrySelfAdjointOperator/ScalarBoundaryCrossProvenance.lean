import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Scalar boundary cross provenance

A synthesized scalar readout is a sum of local value coordinates, and its
log-jet readout is a sum of local jet coordinates.  The scalar Green
Wronskian of those two sums is therefore not merely the sum of the local
cellwise wedges: it also contains every cross-block pairing.

This module exposes those cross terms as a canonical provenance channel.  No
analytic input, zero hypothesis, positivity premise, or choice of inverse is
used.  In particular, the cross provenance is defined from the complete
pairwise local ledger, not as an unexplained residual against a target
operator identity.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

/-- Scalar same-parameter Green wedge of a value and its log jet. -/
def scalarBoundaryWedge (value logJet : ℂ) : ℂ :=
  (starRingEnd ℂ) value * logJet -
    (starRingEnd ℂ) logJet * value

/-- One ordered pair of local coordinates in the synthesized scalar wedge. -/
def scalarBoundaryPairCell
    {ι : Type*} (value logJet : ι → ℂ) (i j : ι) : ℂ :=
  (starRingEnd ℂ) (value i) * logJet j -
    (starRingEnd ℂ) (logJet i) * value j

/-- Complete ordered-pair expansion of the scalar boundary. -/
def scalarBoundaryPairwiseLedger
    {ι : Type*} [Fintype ι]
    (value logJet : ι → ℂ) : ℂ :=
  ∑ i : ι, ∑ j : ι, scalarBoundaryPairCell value logJet i j

/-- Cross-block provenance of scalar synthesis.  It is formed entirely from
all ordered local pairs after removing the diagonal cell wedges. -/
def scalarBoundaryCrossProvenance
    {ι : Type*} [Fintype ι]
    (value logJet : ι → ℂ) : ℂ :=
  scalarBoundaryPairwiseLedger value logJet -
    ∑ i : ι, scalarBoundaryWedge (value i) (logJet i)

/-- Expanding the two synthesized sums produces exactly the complete ordered
pair ledger. -/
theorem scalarBoundaryWedge_sum_eq_pairwiseLedger
    {ι : Type*} [Fintype ι]
    (value logJet : ι → ℂ) :
    scalarBoundaryWedge (∑ i : ι, value i) (∑ i : ι, logJet i) =
      scalarBoundaryPairwiseLedger value logJet := by
  classical
  simp only [scalarBoundaryWedge, scalarBoundaryPairwiseLedger,
    scalarBoundaryPairCell, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_sub_distrib, map_sum]
  congr 1 <;> exact Finset.sum_comm

/-- Canonical synthesis formula: global scalar boundary equals the sum of
cellwise boundaries plus the explicit cross-block provenance channel. -/
theorem scalarBoundaryWedge_sum_eq_local_add_crossProvenance
    {ι : Type*} [Fintype ι]
    (value logJet : ι → ℂ) :
    scalarBoundaryWedge (∑ i : ι, value i) (∑ i : ι, logJet i) =
      (∑ i : ι, scalarBoundaryWedge (value i) (logJet i)) +
        scalarBoundaryCrossProvenance value logJet := by
  rw [scalarBoundaryWedge_sum_eq_pairwiseLedger]
  unfold scalarBoundaryCrossProvenance
  ring

/-- The cross channel is uniquely determined by the local coordinates and
the synthesized scalar boundary. -/
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
