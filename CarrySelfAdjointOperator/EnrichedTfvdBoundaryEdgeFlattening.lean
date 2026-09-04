import CarrySelfAdjointOperator.TwoLegBoundaryCrossProvenance
import NativeCarryC3Crosswalk.EnrichedTfvdPairTransport
import Mathlib.Tactic

/-!
# Exact edge flattening of the enriched TFVD boundary

Each enriched angular TFVD block decodes to three ordered coordinates
`first`, `second`, and `dormant`. Its retained same-parameter boundary is the
sum of the two actual edges

`first → second` and `second → dormant`.

This module flattens the block/edge index as `Fin M × Fin 2` and proves that
the sum of the resulting four-leg wedges is literally the existing enriched
TFVD pair boundary form. No scalar synthesis or Green cancellation is used.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk

/-- Left value leg of one of the two retained edges in a block. -/
def enrichedTfvdBoundaryEdgeLeft
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (pair : EnrichedTfvdValueLogJetPair)
    (mr : Fin M × Fin 2) : ℂ :=
  let valueEdges :=
    enrichedAngularTfvdDecode kappa (omega mr.1) (pair.value.blocks mr.1)
  Fin.cases valueEdges.first (fun _ => valueEdges.second) mr.2

/-- Right value leg of one of the two retained edges in a block. -/
def enrichedTfvdBoundaryEdgeRight
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (pair : EnrichedTfvdValueLogJetPair)
    (mr : Fin M × Fin 2) : ℂ :=
  let valueEdges :=
    enrichedAngularTfvdDecode kappa (omega mr.1) (pair.value.blocks mr.1)
  Fin.cases valueEdges.second (fun _ => valueEdges.dormant) mr.2

/-- Left log-jet leg of one of the two retained edges in a block. -/
def enrichedTfvdBoundaryEdgeJetLeft
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (pair : EnrichedTfvdValueLogJetPair)
    (mr : Fin M × Fin 2) : ℂ :=
  let jetEdges :=
    enrichedAngularTfvdDecode kappa (omega mr.1) (pair.logJet.blocks mr.1)
  Fin.cases jetEdges.first (fun _ => jetEdges.second) mr.2

/-- Right log-jet leg of one of the two retained edges in a block. -/
def enrichedTfvdBoundaryEdgeJetRight
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (pair : EnrichedTfvdValueLogJetPair)
    (mr : Fin M × Fin 2) : ℂ :=
  let jetEdges :=
    enrichedAngularTfvdDecode kappa (omega mr.1) (pair.logJet.blocks mr.1)
  Fin.cases jetEdges.second (fun _ => jetEdges.dormant) mr.2

/-- The two flattened edges of one block sum to its already-defined boundary
cell total. -/
theorem sum_enrichedTfvdBoundaryEdges_eq_cellTotal
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (pair : EnrichedTfvdValueLogJetPair) (m : Fin M) :
    (∑ r : Fin 2,
      sameSEdgeBoundaryWedge
        (enrichedTfvdBoundaryEdgeLeft M kappa omega pair (m, r))
        (enrichedTfvdBoundaryEdgeRight M kappa omega pair (m, r))
        (enrichedTfvdBoundaryEdgeJetLeft M kappa omega pair (m, r))
        (enrichedTfvdBoundaryEdgeJetRight M kappa omega pair (m, r))) =
      (enrichedTfvdSameSBoundaryCells kappa (omega m)
        (pair.value.blocks m) (pair.logJet.blocks m)).total := by
  simp [enrichedTfvdBoundaryEdgeLeft,
    enrichedTfvdBoundaryEdgeRight,
    enrichedTfvdBoundaryEdgeJetLeft,
    enrichedTfvdBoundaryEdgeJetRight,
    enrichedTfvdSameSBoundaryCells,
    TfvdSameSBoundaryCells.total]

/-- Flattening all blocks and both retained edges recovers literally the
existing finite enriched TFVD boundary form. -/
theorem sum_enrichedTfvdBoundaryEdges_eq_pairBoundaryForm
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ)
    (pair : EnrichedTfvdValueLogJetPair) :
    (∑ mr : Fin M × Fin 2,
      sameSEdgeBoundaryWedge
        (enrichedTfvdBoundaryEdgeLeft M kappa omega pair mr)
        (enrichedTfvdBoundaryEdgeRight M kappa omega pair mr)
        (enrichedTfvdBoundaryEdgeJetLeft M kappa omega pair mr)
        (enrichedTfvdBoundaryEdgeJetRight M kappa omega pair mr)) =
      finiteC3EnrichedTfvdPairBoundaryForm M
        (finiteC3EnrichedTfvdPairTransport M kappa omega s pair) := by
  rw [Fintype.sum_prod_type]
  unfold finiteC3EnrichedTfvdPairBoundaryForm
  apply Finset.sum_congr rfl
  intro m _hm
  simpa [finiteC3EnrichedTfvdPairTransport] using
    (sum_enrichedTfvdBoundaryEdges_eq_cellTotal
      M kappa omega pair m)

end

end CarrySelfAdjointOperator
