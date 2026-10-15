import CPFormal.Analytic.CpNativeGprePrimeCarryContraction
import CPFormal.Analytic.CpTfvdSeededFiniteBesselConservation
import GreenFrame.Concrete.Analysis.ResidualAnalysis
import CarrySelfAdjointOperator.NativeSourceThetaProjectiveValve
import CarrySelfAdjointOperator.ProjectiveValveFirstColumnMomentGate
import CarrySelfAdjointOperator.NativePhysicalSewingAuditSupport

/-! Executable reuse checks against the ACTUALLY CONSUMED dependency pins.
The source-defined prime-carry contraction has a strict geometric complement.
No identification of this complement with the native moment energy is assumed
or claimed. Newer upstream projection/gluing APIs are audited in their own repo.
-/
namespace CarrySelfAdjointOperator.GeometricReuseAudit
open CPFormal.Analytic.Cp
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- A local audit check, not a new positive metric or moment realization. -/
private theorem verifiedComplementBudget (X : NativeGpreTowerHilbert) :
    (1/12 : ℝ)*‖X‖^2 ≤ ‖X‖^2-‖nativeGprePrimeCarryDefectState X‖^2 := by
  have h := nativeGprePrimeCarryDefectState_norm_sq_le X
  nlinarith

/-- Strictness for every nonzero geometric source, with no moment premise. -/
private theorem verifiedComplementPositive (X : NativeGpreTowerHilbert) (hX : X ≠ 0) :
    0 < ‖X‖^2-‖nativeGprePrimeCarryDefectState X‖^2 := by
  have h := verifiedComplementBudget X
  have hn := pow_pos (norm_pos_iff.mpr hX) 2
  nlinarith

#check verifiedComplementBudget
#print axioms verifiedComplementBudget
#check verifiedComplementPositive
#print axioms verifiedComplementPositive
#check nativeGprePrimeCarryContractionMajorant_tsum
#print axioms nativeGprePrimeCarryContractionMajorant_tsum
#check nativeGprePrimeCarryDefectState_norm_sq_le
#print axioms nativeGprePrimeCarryDefectState_norm_sq_le

#audit_physical_sewing
  verifiedComplementBudget
  verifiedComplementPositive
  nativeGprePrimeCarryContractionMajorant_tsum
  nativeGprePrimeCarryDefectState_norm_sq_le

#check nativeGprePrimeCarryDefectState_realizes
#print axioms nativeGprePrimeCarryDefectState_realizes
#check canonicalProvenanceState_pythagoras_seededTfvdBesselLedger_of_realizesOn
#print axioms canonicalProvenanceState_pythagoras_seededTfvdBesselLedger_of_realizesOn
#check GreenFrame.Concrete.seedResidualAnalysis_norm_sq_bounds
#print axioms GreenFrame.Concrete.seedResidualAnalysis_norm_sq_bounds
#check nativeSourceMomentQuadratic_eq_thetaGreen_integral
#print axioms nativeSourceMomentQuadratic_eq_thetaGreen_integral
#check nativeSourceSchurRemainder_first_odd_eq_theta_balance
#print axioms nativeSourceSchurRemainder_first_odd_eq_theta_balance
#check nativeThetaFirstOddCore_pos
#print axioms nativeThetaFirstOddCore_pos
#check projectiveValveMass_nativeMoments_eq_reciprocal
#print axioms projectiveValveMass_nativeMoments_eq_reciprocal
#check hasNativePolarizedCoefficientVectorEquation_iff_firstColumn_of_transport
#print axioms hasNativePolarizedCoefficientVectorEquation_iff_firstColumn_of_transport

#audit_physical_sewing
  nativeGprePrimeCarryDefectState_realizes
  canonicalProvenanceState_pythagoras_seededTfvdBesselLedger_of_realizesOn
  GreenFrame.Concrete.seedResidualAnalysis_norm_sq_bounds
  nativeSourceMomentQuadratic_eq_thetaGreen_integral
  nativeSourceSchurRemainder_first_odd_eq_theta_balance
  nativeThetaFirstOddCore_pos
  projectiveValveMass_nativeMoments_eq_reciprocal
  hasNativePolarizedCoefficientVectorEquation_iff_firstColumn_of_transport

end
end CarrySelfAdjointOperator.GeometricReuseAudit
