import CarrySelfAdjointOperator.MixedReturnHeightSpectrumBridge
import Mathlib.Tactic

/-!
# Zero-equivalent multibase readouts and height point spectrum

This is the spectral handoff immediately upstream of
`MixedReturnHeightSpectrumBridge`.  A physical multibase realization need not
agree literally with `completedNativeOperatorCharacteristic` to preserve the
already constructed signed-height and Jacobi point spectra: it only needs the
same real-axis zero locus.

The interface is deliberately polymorphic in the codomain.  Thus a future
physical characteristic may remain a vector or a matrix until its collective
blindness condition has been proved.  No arbitrary scalarization of the
multibase object is required by this module.  A scalar secular readout is a
special case, and receives the convenient nonvanishing-factor constructor.

This module does not construct a height operator, a Jacobi operator, or an HP
certificate.  It simply transports a zero through the existing spectral
theorems, which continue to require the existing
`CompletedNativeRealHPCarrierCertificate`.

Equality of readouts remains strictly stronger than this interface and must be
used when derivatives, Taylor coefficients, or zero multiplicities matter.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- A real-height readout has the canonical completed-native zero locus when
its vanishing is equivalent, pointwise on the real height axis, to vanishing
of the canonical operator characteristic.

The codomain is intentionally arbitrary apart from possessing zero.  This lets
a physical vector-valued characteristic or a matrix-valued residual be handed
off directly once `readout t = 0` has been proved to express its collective
blindness. -/
def IsZeroEquivalentCompletedNativeHeightReadout
    {A : Type*} [Zero A] (readout : ℝ → A) : Prop :=
  ∀ t : ℝ,
    readout t = 0 ↔ completedNativeOperatorCharacteristic (t : ℂ) = 0

namespace IsZeroEquivalentCompletedNativeHeightReadout

/-- Literal readout equality induces zero equivalence.  This is the bridge
from the pre-existing exact mixed-return API to the weaker spectral handoff. -/
theorem of_exact
    {readout : ℝ → ℂ}
    (hreadout : IsExactCompletedNativeHeightReadout readout) :
    IsZeroEquivalentCompletedNativeHeightReadout readout := by
  intro t
  rw [hreadout t]

/-- A scalar readout differing from the canonical characteristic by a factor
which never vanishes on the real height axis has exactly the same zero locus.

This is the expected constructor for a reduced secular or Potapov readout
after its structural gauge has been shown nonzero.  It asserts equality of
zero sets only; it deliberately makes no claim about zero multiplicities. -/
theorem of_nonvanishing_scalar_factor
    {readout unit : ℝ → ℂ}
    (hunit : ∀ t : ℝ, unit t ≠ 0)
    (hreadout : ∀ t : ℝ,
      readout t = unit t * completedNativeOperatorCharacteristic (t : ℂ)) :
    IsZeroEquivalentCompletedNativeHeightReadout readout := by
  intro t
  constructor
  · intro hzero
    have hproduct :
        unit t * completedNativeOperatorCharacteristic (t : ℂ) = 0 := by
      rw [← hreadout t]
      exact hzero
    exact (mul_eq_zero.mp hproduct).resolve_left (hunit t)
  · intro hzero
    rw [hreadout t, hzero, mul_zero]

/-- A right scalar factor is equivalent to the left-factor form over `ℂ`.
This variant matches factorizations whose canonical characteristic is written
first. -/
theorem of_nonvanishing_scalar_factor_right
    {readout unit : ℝ → ℂ}
    (hunit : ∀ t : ℝ, unit t ≠ 0)
    (hreadout : ∀ t : ℝ,
      readout t = completedNativeOperatorCharacteristic (t : ℂ) * unit t) :
    IsZeroEquivalentCompletedNativeHeightReadout readout := by
  apply of_nonvanishing_scalar_factor hunit
  intro t
  simpa only [mul_comm] using hreadout t

end IsZeroEquivalentCompletedNativeHeightReadout

/-- The existing exact six-camera mixed-return readout also satisfies the
weaker zero-equivalence interface. -/
theorem mixedReturnCompletedHeightCharacteristic_isZeroEquivalentReadout
    (cutoff : Fin 6 → ℕ) :
    IsZeroEquivalentCompletedNativeHeightReadout
      (mixedReturnCompletedHeightCharacteristic cutoff) :=
  IsZeroEquivalentCompletedNativeHeightReadout.of_exact
    (mixedReturnCompletedHeightCharacteristic_isExactReadout cutoff)

namespace CompletedNativeRealHPCarrierCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {jet : (ℕ ⊕ ℕ) → E}

/-- The existing signed-height zero-to-eigenvalue theorem transported through
an arbitrary zero-equivalent physical readout.  The proof only changes the
readout zero into the already canonical characteristic zero. -/
theorem zeroEquivalentReadout_zero_hasSignedHeightEigenvalue
    {A : Type*} [Zero A]
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {readout : ℝ → A}
    (hreadout : IsZeroEquivalentCompletedNativeHeightReadout readout)
    {t : ℝ} (hzero : readout t = 0) :
    LinearPMap.HasEigenvalue
      certificate.toReducedMaximalSelfAdjointHeightData.selfAdjointData.complexification
      (t : ℂ) := by
  exact certificate.reducedSignedHeightComplexification_hasEigenvalue_of_atomicExtraction
    (ofReal_mem_completedNativeHeightDomain t) ((hreadout t).mp hzero)

/-- The existing nonzero-height Jacobi point-spectrum correspondence
transported through any zero-equivalent physical readout. -/
theorem zeroEquivalentReadout_zero_iff_jacobiEigenvalue_inv_sq
    {A : Type*} [Zero A]
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {readout : ℝ → A}
    (hreadout : IsZeroEquivalentCompletedNativeHeightReadout readout)
    {t : ℝ} (ht : t ≠ 0) :
    readout t = 0 ↔
      LinearPMap.HasEigenvalue
        certificate.completedJacobiEnergySelfAdjointData.complexification
        ((t : ℂ) ^ 2)⁻¹ := by
  rw [hreadout t]
  exact
    (certificate.completedJacobiEnergyComplexification_hasEigenvalue_inv_sq_iff_nativeZero
      ht).symm

/-- Concrete zero-equivalent form of the already exact mixed-return
signed-height theorem. -/
theorem mixedReturnCompletedHeightCharacteristic_zero_hasSignedHeightEigenvalue'
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (cutoff : Fin 6 → ℕ) {t : ℝ}
    (hzero : mixedReturnCompletedHeightCharacteristic cutoff t = 0) :
    LinearPMap.HasEigenvalue
      certificate.toReducedMaximalSelfAdjointHeightData.selfAdjointData.complexification
      (t : ℂ) := by
  exact certificate.zeroEquivalentReadout_zero_hasSignedHeightEigenvalue
    (mixedReturnCompletedHeightCharacteristic_isZeroEquivalentReadout cutoff) hzero

/-- Concrete zero-equivalent form of the existing mixed-return/Jacobi
reciprocal-square correspondence. -/
theorem mixedReturnCompletedHeightCharacteristic_zero_iff_jacobiEigenvalue_inv_sq'
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (cutoff : Fin 6 → ℕ) {t : ℝ} (ht : t ≠ 0) :
    mixedReturnCompletedHeightCharacteristic cutoff t = 0 ↔
      LinearPMap.HasEigenvalue
        certificate.completedJacobiEnergySelfAdjointData.complexification
        ((t : ℂ) ^ 2)⁻¹ := by
  exact certificate.zeroEquivalentReadout_zero_iff_jacobiEigenvalue_inv_sq
    (mixedReturnCompletedHeightCharacteristic_isZeroEquivalentReadout cutoff) ht

end CompletedNativeRealHPCarrierCertificate

end
end CarrySelfAdjointOperator
