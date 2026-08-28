import CarrySelfAdjointOperator.CanonicalCompletedC3TfvdResolventDomain
import CarrySelfAdjointOperator.CompletedC3FullWronskianOperatorCarrier
import Mathlib.Tactic

/-!
# Gamma boundary versus the full Wronskian operator carrier

The completed TFVD construction now has two unconditional Hilbert
realizations with different purposes:

* resolvent uniqueness identifies its maximal-domain response with the
  positive Gamma state;
* exact head--tail completion identifies its boundary trace with `(F,-F')`,
  whose Wronskian is represented by the full bounded symplectic operator.

This file places both sides in one literal scalar square.  It neither assumes
nor proves that the positive Gamma boundary equals the completed Wronskian.
Instead it proves that this is exactly the remaining compatibility between
the two already constructed Hilbert readouts.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The independently completed TFVD Wronskian is exactly the readout of the
normalized full bounded operator.  The argument order is chosen to match the
source-varying Gamma boundary convention. -/
theorem canonicalC3BracketTfvdCompletedWronskianReadout_eq_fullOperatorInner
    (M : ℕ) {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalC3BracketTfvdCompletedWronskianReadout M w z =
      inner ℂ
        (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)
        (canonicalCompletedC3FullWronskianOperator
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M w)) := by
  rw [canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime
      M hwStrip hzStrip]
  exact completedGreenWronskian_eq_normalizedFullOperatorInner
    M hwStrip hzStrip

/-- The concrete TFVD maximal-domain boundary equals the positive Gamma
boundary by resolvent uniqueness.  Consequently its equality with the full
operator readout is precisely the raw Gamma--Wronskian sewing, with no
candidate or vector defect left in the statement. -/
theorem canonicalCompletedC3TfvdDomainBoundary_eq_fullOperatorInner_iff
    (M : ℕ) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3CandidateResolventBoundaryReadout z w
          (canonicalCompletedC3TfvdResolventDomainVector z hz)
          (canonicalCompletedC3TfvdResolventDomainVector w hw) =
        inner ℂ
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)
          (canonicalCompletedC3FullWronskianOperator
            (canonicalCompletedC3NormalizedFullWronskianOperatorState M w)) ↔
      canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z := by
  have hcompanion :
      completedNativeOperatorBoundaryCompanion =
        (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u) := by
    funext u
    exact completedNativeOperatorBoundaryCompanion_eq_neg_deriv u
  rw [canonicalCompletedC3TfvdDomainBoundaryReadout_eq_gammaBoundaryReadout,
    hcompanion]
  exact iff_of_eq (congrArg
    (fun value : ℂ =>
      canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw = value)
    (completedGreenWronskian_eq_normalizedFullOperatorInner
      M hwStrip hzStrip).symm)

/-- The raw scalar defect is literally the difference between the positive
Gamma boundary readout and the full bounded-operator readout. -/
theorem canonicalCompletedC3RawGammaWronskianDefect_eq_sub_fullOperatorInner
    (M : ℕ) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawGammaWronskianDefect z w hz hw =
      canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
        inner ℂ
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)
          (canonicalCompletedC3FullWronskianOperator
            (canonicalCompletedC3NormalizedFullWronskianOperatorState M w)) := by
  have hcompanion :
      completedNativeOperatorBoundaryCompanion =
        (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u) := by
    funext u
    exact completedNativeOperatorBoundaryCompanion_eq_neg_deriv u
  unfold canonicalCompletedC3RawGammaWronskianDefect
  rw [hcompanion,
    completedGreenWronskian_eq_normalizedFullOperatorInner
      M hwStrip hzStrip]

/-- The positive Gamma Gram realizes the completed-native divided-slope
kernel exactly when its boundary agrees with the full Hilbert-operator
Wronskian.  This is the operatorial spelling of the remaining sewing gate. -/
theorem canonicalCompletedC3NormalizedGammaKernel_eq_dslope_iff_fullOperatorInner
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3NormalizedPolarizedGammaKernel z w hz hw =
        canonicalCompletedNativePolarizedDslopeKernel z w ↔
      canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw =
        inner ℂ
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)
          (canonicalCompletedC3FullWronskianOperator
            (canonicalCompletedC3NormalizedFullWronskianOperatorState M w)) := by
  have hcompanion :
      completedNativeOperatorBoundaryCompanion =
        (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u) := by
    funext u
    exact completedNativeOperatorBoundaryCompanion_eq_neg_deriv u
  rw [canonicalCompletedC3NormalizedPolarizedGammaKernel_eq_dslope_iff_rawWronskian
      M z w hz hw hzStrip hwStrip hzF hwF hsep,
    hcompanion,
    completedGreenWronskian_eq_normalizedFullOperatorInner
      M hwStrip hzStrip]

/-- At a hypothetical off-axis characteristic zero, the two concrete Hilbert
readouts cannot agree: the full Wronskian operator readout vanishes while the
positive Gamma boundary readout is nonzero.  This confirms that closing the
last square globally is already a confinement-strength statement. -/
theorem canonicalCompletedC3GammaBoundary_ne_fullOperatorInner_of_characteristicZero
    (M : ℕ) {z : ℂ} (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    canonicalCompletedC3PolarizedGammaBoundaryReadout z z hz hz ≠
      inner ℂ
        (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)
        (canonicalCompletedC3FullWronskianOperator
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)) := by
  rw [← canonicalC3BracketTfvdCompletedWronskianReadout_eq_fullOperatorInner
    M hzStrip hzStrip]
  rw [← canonicalCompletedC3TfvdDomainBoundaryReadout_eq_gammaBoundaryReadout]
  exact
    canonicalCompletedC3TfvdDomainBoundary_ne_tfvdWronskian_of_characteristicZero
      M hz hzStrip hzero

end

end CarrySelfAdjointOperator
