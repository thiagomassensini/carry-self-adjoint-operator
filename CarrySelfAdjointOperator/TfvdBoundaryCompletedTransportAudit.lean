import CarrySelfAdjointOperator.TfvdBoundaryCompletedTransport

/-!
# Axiom audit for TFVD boundary reconstruction

The audit covers only the adapter which places the existing weighted TFVD
identity in the generic `trace ⊕ defect` / `return + Green` language.  It does
not assert that TFVD's vertical transport is the cutoff transport of a tail.
-/

namespace CarrySelfAdjointOperator

#print axioms carryWeightedVerticalTfvd_isBoundaryReconstruction
#print axioms carryWeightedVerticalTfvdBoundarySynthesis_comp_analysis
#print axioms carryWeightedVerticalTfvdBoundaryAnalysis_injective
#print axioms finiteSlopeCoefficient_tfvdBoundaryReconstruction

end CarrySelfAdjointOperator
