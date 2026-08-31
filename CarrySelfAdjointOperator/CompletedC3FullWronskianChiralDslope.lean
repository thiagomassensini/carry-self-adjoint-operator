import CarrySelfAdjointOperator.CompletedC3FullWronskianPolarization
import CarrySelfAdjointOperator.CanonicalCompletedC3GammaLedgerNumerator
import Mathlib.Tactic

/-!
# Chiral quotient for the completed-native dslope

The full Wronskian carrier contains the completed logarithmic response as a
signed difference of two positive chiral Gram kernels.  This module divides
that exact balance only by the intrinsic spectral separation and identifies
the result with the canonical polarized `dslope`.

No positivity, zero-set, Stieltjes, Jacobi, or confinement hypothesis is used.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The normalized chiral difference is exactly the Hermitian-polarized
numerator of the completed logarithmic response. -/
theorem canonicalCompletedC3FullWronskianChiralDifference_eq_polarizedResponseNumerator
    (M : ℕ) {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0) :
    Complex.I *
        (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
            M z w -
          canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
            M z w) =
      canonicalCompletedNativePolarizedResponseNumerator z w := by
  rw [← canonicalCompletedC3NormalizedFullWronskianKernel_div_eq_chiralDifference
    M hzF hwF]
  rw [canonicalCompletedC3NormalizedFullWronskianOperatorKernel_eq_completed
    M hzStrip hwStrip]
  have hcompanion :
      (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u) =
        completedNativeOperatorBoundaryCompanion := by
    funext u
    exact (completedNativeOperatorBoundaryCompanion_eq_neg_deriv u).symm
  rw [hcompanion]
  rw [completedGreenWronskian_eq_normalizedResponse_cross_mul
    completedNativeOperatorCharacteristic
    completedNativeOperatorBoundaryCompanion w z hwF hzF]
  unfold canonicalCompletedNativePolarizedResponseNumerator
  have hstarZ :
      (starRingEnd ℂ) (completedNativeOperatorCharacteristic z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hzF
  field_simp [hwF, hstarZ]

/-- Division-free final form: the signed chiral balance is the spectral
separation times the canonical polarized `dslope`. -/
theorem canonicalCompletedC3FullWronskianChiralDifference_eq_separation_mul_dslope
    (M : ℕ) {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    Complex.I *
        (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
            M z w -
          canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
            M z w) =
      (w - conj z) * canonicalCompletedNativePolarizedDslopeKernel z w := by
  rw [canonicalCompletedC3FullWronskianChiralDifference_eq_polarizedResponseNumerator
      M hzStrip hwStrip hzF hwF,
    canonicalCompletedNativePolarizedResponseNumerator_eq_mul_dslope
      hzStrip hsep]

/-- Away from collision, the canonical polarized `dslope` is literally the
spectral-separation quotient of the signed difference of two positive Gram
kernels. -/
theorem canonicalCompletedNativePolarizedDslopeKernel_eq_chiralDifference_div
    (M : ℕ) {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedNativePolarizedDslopeKernel z w =
      Complex.I *
          (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
              M z w -
            canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
              M z w) /
        (w - conj z) := by
  apply (eq_div_iff (sub_ne_zero.mpr hsep)).2
  rw [mul_comm]
  exact
    (canonicalCompletedC3FullWronskianChiralDifference_eq_separation_mul_dslope
      M hzStrip hwStrip hzF hwF hsep).symm

end

end CarrySelfAdjointOperator
