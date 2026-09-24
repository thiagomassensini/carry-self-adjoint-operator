import CarrySelfAdjointOperator.ProjectiveValveFirstColumnMomentGate
import CarrySelfAdjointOperator.CompletedNativeClockGreenMomentGate
import CarrySelfAdjointOperator.TfvdCausalGramCalibrationAudit

/-!
# Audit: first-column metric gate after the valve and TFVD layers

This audit deliberately prints both sides of the seam:

* `seededClockAtlasCoefficientEquation_iff_boundary` is the concrete case
  where a native coefficient transport has already been proved, hence the
  first column is the only remaining metric gate;
* `carryWeightedVerticalTfvdBoundarySynthesis_comp_analysis` records the
  separate TFVD lossless reconstruction statement;
* `canonicalFiniteNativeCausalGreenBoundaryGram_posDef` records the separate
  finite causal positivity resource.

No line below identifies those three facts with one another. In particular,
the audit contains no all-order causal Gram-shift or causal first-column
calibration theorem because neither has been constructed in the repository.
-/

#print axioms CarrySelfAdjointOperator.hasPolarizedCoefficientVectorEquation_iff_firstColumn_of_transport
#print axioms CarrySelfAdjointOperator.hasNativePolarizedCoefficientVectorEquation_iff_firstColumn_of_transport
#print axioms CarrySelfAdjointOperator.completedNativeRealHPCarrierCertificate_of_firstColumn_and_transport
#print axioms CarrySelfAdjointOperator.C3TraceDynamics.seededClockAtlasCoefficientEquation_iff_boundary
#print axioms CarrySelfAdjointOperator.carryWeightedVerticalTfvdBoundarySynthesis_comp_analysis
#print axioms CarrySelfAdjointOperator.canonicalFiniteNativeCausalGreenBoundaryGram_posDef
