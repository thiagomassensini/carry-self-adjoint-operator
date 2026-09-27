import CarrySelfAdjointOperator.MinimalNativeCarryRepresentationCapstone

/-!
# Audit: minimal native-carry representation capstone

Direct dependencies of `minimalNativeCarryRepresentation`:

* `canonicalBR2CarryAmplitudeRatio_pow_sq_eq_carryMass`;
* `carryWeightedVerticalTfvd_identity`;
* `nativeLogGenerator_isSelfAdjoint`;
* `nativeLogGenerator_basisVector_log`;
* `completedNativeCharacteristic_eq_factor_mul_nativeScalar`.

The three remaining theorems below are intentionally layered consequences:
TFVD energy, conditional finite-height provenance, and the one-gate public
confinement frontier.  No Green-port implementation theorem is used here.
-/

namespace CarrySelfAdjointOperator

#print NativeCarryRepresentationCore
#print MinimalPublicC3ConfinementSeam
#print NativeCarryC3Crosswalk.FiniteC3CompletedGreenWronskianSeam

#check NativeCarryRepresentationCore
#check minimalNativeCarryRepresentation
#check nativeCarryRepresentationCore_reconstruct_apply
#check nativeCarryRepresentationCore_fourChannel
#check nativeCarryRepresentation_camera_to_finiteHeight
#check nativeCarryRepresentation_minimalPublicSeam_to_confinement
#check MinimalPublicC3ConfinementSeam

#print axioms minimalNativeCarryRepresentation
#print axioms nativeCarryRepresentationCore_reconstruct_apply
#print axioms nativeCarryRepresentationCore_fourChannel
#print axioms nativeCarryRepresentation_camera_to_finiteHeight
#print axioms nativeCarryRepresentation_minimalPublicSeam_to_confinement

end CarrySelfAdjointOperator
