import CarrySelfAdjointOperator.CompletedNativeCentralCarryAtlasEnergy
import CarrySelfAdjointOperator.CompletedC3FullWronskianChiralDslope
import CarrySelfAdjointOperator.CanonicalCompletedC3NormalizedGammaSewing
import Mathlib.Tactic

/-!
# Crossed chart form of the completed chiral balance

The compatible Poisson graph realizes the positive raw C3 Gram, including its
causal boundary return.  The completed logarithmic response contains two
additional product channels: the xi completion factor and the C3 chart
factor.  This module keeps those factors explicit and proves the exact
division-free identity connecting them to the full chiral balance.

No positivity, zero-set, Stieltjes, Jacobi, or confinement premise is used.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- After restoring the characteristic and chart weights, the normalized
signed chiral balance is exactly the xi-weighted raw C3 Wronskian plus the
independently retained archimedean/chart product channel. -/
theorem canonicalCompletedC3FullChiralBalance_crossedChartIdentity
    (M : ℕ) {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0) :
    mixedHermitianWeight canonicalC3ChartFactorHeight w z *
        canonicalCompletedC3GammaCharacteristicWeight z w *
        (Complex.I *
          (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
              M z w -
            canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
              M z w)) =
      mixedHermitianWeight nativeXiCompletionFactor w z *
          canonicalCompletedC3RawHeightMixedWronskian w z +
        canonicalCompletedC3ArchimedeanChartMixedChannel w z := by
  have hchiral :=
    canonicalCompletedC3FullWronskianChiralDifference_eq_polarizedResponseNumerator
      M hzStrip hwStrip hzF hwF
  have hwron := completedGreenWronskian_eq_normalizedResponse_cross_mul
    completedNativeOperatorCharacteristic
    completedNativeOperatorBoundaryCompanion w z hwF hzF
  change
    completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion w z =
      canonicalCompletedC3GammaCharacteristicWeight z w *
        canonicalCompletedNativePolarizedResponseNumerator z w at hwron
  have hcompanion :
      (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u) =
        completedNativeOperatorBoundaryCompanion := by
    funext u
    exact (completedNativeOperatorBoundaryCompanion_eq_neg_deriv u).symm
  have hcross := completedFNegFPrimeWronskian_crossedChartIdentity
    (z := w) (w := z) hwStrip hzStrip
  rw [hcompanion] at hcross
  calc
    mixedHermitianWeight canonicalC3ChartFactorHeight w z *
          canonicalCompletedC3GammaCharacteristicWeight z w *
          (Complex.I *
            (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
                M z w -
              canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
                M z w)) =
        mixedHermitianWeight canonicalC3ChartFactorHeight w z *
          canonicalCompletedC3GammaCharacteristicWeight z w *
            canonicalCompletedNativePolarizedResponseNumerator z w := by
              rw [hchiral]
    _ = mixedHermitianWeight canonicalC3ChartFactorHeight w z *
          completedGreenWronskian
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion w z := by
              rw [hwron]
              ring
    _ = _ := hcross

/-- Away from Hermitian collision, the same identity places the completed
`dslope` directly in the crossed raw-plus-archimedean ledger.  The spectral
separation is retained, so no division near a zero occurs. -/
theorem canonicalCompletedC3Dslope_crossedChartIdentity
    (M : ℕ) {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    mixedHermitianWeight canonicalC3ChartFactorHeight w z *
        canonicalCompletedC3GammaCharacteristicWeight z w *
        ((w - conj z) * canonicalCompletedNativePolarizedDslopeKernel z w) =
      mixedHermitianWeight nativeXiCompletionFactor w z *
          canonicalCompletedC3RawHeightMixedWronskian w z +
        canonicalCompletedC3ArchimedeanChartMixedChannel w z := by
  rw [←
    canonicalCompletedC3FullWronskianChiralDifference_eq_separation_mul_dslope
      M hzStrip hwStrip hzF hwF hsep]
  exact canonicalCompletedC3FullChiralBalance_crossedChartIdentity
    M hzStrip hwStrip hzF hwF

end

end CarrySelfAdjointOperator
