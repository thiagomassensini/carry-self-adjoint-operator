import CarrySelfAdjointOperator.MixedReturnNativeReadout
import CarrySelfAdjointOperator.CompletedNativeJacobiPointSpectrumConverse

/-!
# Exact multibase readout to height point spectrum

This file is a thin, non-circular adapter between the already formalized
six-camera mixed-return characteristic and the already constructed
self-adjoint height operators.

No new spectral operator, positivity hypothesis, zero table, or fitted height
is introduced here.  The only input is exact readout equality with
`completedNativeOperatorCharacteristic`.

The purpose of the small abstract interface is to let later realizations
(minimal multibase/Potapov, boundary/Weyl, or cutoff-limit readouts) reuse the
same spectral theorem once they prove the same exact scalar characteristic
identity on the real height axis.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- A real-height readout is exact when it is literally the already canonical
completed-native operator characteristic on the real axis. -/
def IsExactCompletedNativeHeightReadout (readout : ℝ → ℂ) : Prop :=
  ∀ t : ℝ, readout t = completedNativeOperatorCharacteristic (t : ℂ)

/-- The existing six-camera mixed-return readout is an exact completed-native
height readout at every finite cutoff. -/
theorem mixedReturnCompletedHeightCharacteristic_isExactReadout
    (cutoff : Fin 6 → ℕ) :
    IsExactCompletedNativeHeightReadout
      (mixedReturnCompletedHeightCharacteristic cutoff) := by
  intro t
  exact congrFun (mixedReturnCompletedHeightCharacteristic_eq cutoff) t

namespace CompletedNativeRealHPCarrierCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {jet : (ℕ ⊕ ℕ) → E}

/-- Any exact real-axis realization of the completed-native characteristic
inherits the existing zero-to-point-spectrum theorem for the reduced signed
height operator.  This is the reusable bridge for future multibase
realizations: only the exact readout identity is required here. -/
theorem exactReadout_zero_hasSignedHeightEigenvalue
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {readout : ℝ → ℂ}
    (hreadout : IsExactCompletedNativeHeightReadout readout)
    {t : ℝ} (hzero : readout t = 0) :
    LinearPMap.HasEigenvalue
      certificate.toReducedMaximalSelfAdjointHeightData.selfAdjointData.complexification
      (t : ℂ) := by
  have hchar : completedNativeOperatorCharacteristic (t : ℂ) = 0 := by
    calc
      completedNativeOperatorCharacteristic (t : ℂ) = readout t :=
        (hreadout t).symm
      _ = 0 := hzero
  exact
    certificate.reducedSignedHeightComplexification_hasEigenvalue_of_atomicExtraction
      (ofReal_mem_completedNativeHeightDomain t) hchar

/-- At every nonzero real height, an exact readout vanishes exactly when the
positive Jacobi energy operator has the reciprocal-square point eigenvalue.

This is the converse direction already proved by cyclicity, transported through
an arbitrary exact readout. -/
theorem exactReadout_zero_iff_jacobiEigenvalue_inv_sq
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {readout : ℝ → ℂ}
    (hreadout : IsExactCompletedNativeHeightReadout readout)
    {t : ℝ} (ht : t ≠ 0) :
    readout t = 0 ↔
      LinearPMap.HasEigenvalue
        certificate.completedJacobiEnergySelfAdjointData.complexification
        ((t : ℂ) ^ 2)⁻¹ := by
  rw [hreadout t]
  exact
    (certificate.completedJacobiEnergyComplexification_hasEigenvalue_inv_sq_iff_nativeZero
      ht).symm

/-- Concrete six-camera consequence: a zero of the exact mixed-return
characteristic is a genuine eigenvalue of the reduced signed-height operator
at that same real height. -/
theorem mixedReturnCompletedHeightCharacteristic_zero_hasSignedHeightEigenvalue
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (cutoff : Fin 6 → ℕ) {t : ℝ}
    (hzero : mixedReturnCompletedHeightCharacteristic cutoff t = 0) :
    LinearPMap.HasEigenvalue
      certificate.toReducedMaximalSelfAdjointHeightData.selfAdjointData.complexification
      (t : ℂ) := by
  exact certificate.exactReadout_zero_hasSignedHeightEigenvalue
    (mixedReturnCompletedHeightCharacteristic_isExactReadout cutoff) hzero

/-- Concrete six-camera point-spectrum equivalence in the positive Jacobi
coordinate. -/
theorem mixedReturnCompletedHeightCharacteristic_zero_iff_jacobiEigenvalue_inv_sq
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (cutoff : Fin 6 → ℕ) {t : ℝ} (ht : t ≠ 0) :
    mixedReturnCompletedHeightCharacteristic cutoff t = 0 ↔
      LinearPMap.HasEigenvalue
        certificate.completedJacobiEnergySelfAdjointData.complexification
        ((t : ℂ) ^ 2)⁻¹ := by
  exact certificate.exactReadout_zero_iff_jacobiEigenvalue_inv_sq
    (mixedReturnCompletedHeightCharacteristic_isExactReadout cutoff) ht

end CompletedNativeRealHPCarrierCertificate

end
end CarrySelfAdjointOperator
