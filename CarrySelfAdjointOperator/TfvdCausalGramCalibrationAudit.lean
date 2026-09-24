import CarrySelfAdjointOperator.CompletedNativeCausalCoefficientGram
import CarrySelfAdjointOperator.CompletedNativeTfvdEnrichedLowOrderMomentTest
import CarrySelfAdjointOperator.NativeCausalCenterLegNoGoAudit
import CarrySelfAdjointOperator.BR2CausalBoundaryMetricCalibration
import CarrySelfAdjointOperator.CompletedNativeTfvdRawAllOrderJetBridge

/-!
# Audit: TFVD causal positive Gram versus the native moment Gram

This file records the exact state of the proposed calibration seam.

* The finite causal `Green ⊕ boundary` families are strictly independent and
  have positive-definite complex Gram matrices.
* They are prefix families `Fin N → E`; no theorem in the present graph gives
  their projective Gram compatibility or identifies their first column with
  the completed native moments.
* The currently available fixed-carrier enriched TFVD Taylor family is not a
  substitute: its `(0,0)` Gram entry is formally incompatible with the native
  zeroth moment.
* Likewise, the literal C3 causal response is obstructed even after arbitrary
  two-seed boundary return.

Thus this audit deliberately does **not** assert that a positive TFVD Gram is
already the Hankel Gram.  The remaining constructive target is a completed,
all-order vector family whose Gram satisfies
`HasPolarizedCoefficientVectorEquation`.
-/

namespace CarrySelfAdjointOperator

#print axioms canonicalFiniteNativeCausalGreenBoundaryJet_linearIndependent
#print axioms canonicalFiniteNativeCausalGreenBoundaryGram_posDef

#print axioms not_hasPolarizedCoefficientVectorEquation_enrichedTfvdTaylor
#print axioms not_canonicalBR2CausalGreenResponse_centerLegReadout
#print axioms not_nonempty_canonicalBR2C3BoundaryResponse_momentCertificate

#check canonicalFiniteNativeCausalGreenBoundaryJet
#check canonicalCompletedNativeTfvdEnrichedTaylorRawJet
#check canonicalCompletedTfvdGreenNaimarkRawJet
#check IsCanonicalCompletedTfvdGreenRawJetLimit
#check HasPolarizedCoefficientVectorEquation

end CarrySelfAdjointOperator
