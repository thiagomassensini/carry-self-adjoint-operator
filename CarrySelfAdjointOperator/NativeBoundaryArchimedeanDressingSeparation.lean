import CarrySelfAdjointOperator.CompletedNativeCancellationBoundarySewing
import CarrySelfAdjointOperator.CompletedNativeProductMomentCenter
import CarrySelfAdjointOperator.CompletedC3SameStructuredBoundaryState
import CarrySelfAdjointOperator.CompletedC3CentralLedgerChannelDerivative
import CarrySelfAdjointOperator.CanonicalC3GlobalCameraBoundaryBridge
import Mathlib.Tactic

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- The scalar chart before the archimedean xi dressing.  Its first
coordinate is the negative derivative (the Green companion), and its second
coordinate is the native scalar itself. -/
def canonicalNativeUndressedScalarBoundaryPair (z : ℂ) : ℂ × ℂ :=
  (nativeHeightScalarBoundaryCompanion z, nativeHeightScalar z)

/-- The triangular boundary-chart map induced by multiplication by the
archimedean completion factor. -/
def nativeArchimedeanBoundaryDressing (z : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (nativeXiCompletionFactor z * p.1 +
      nativeXiCompletionBoundaryCompanion z * p.2,
    nativeXiCompletionFactor z * p.2)

/-- The native pair is exactly the negative-derivative/value pair of the
undressed scalar. -/
theorem canonicalNativeUndressedScalarBoundaryPair_eq_negDeriv (z : ℂ) :
    canonicalNativeUndressedScalarBoundaryPair z =
      (-deriv nativeHeightScalar z, nativeHeightScalar z) := by
  rfl

/-- The completed characteristic is exactly the archimedean factor times the
undressed native scalar. -/
theorem completedNativeOperatorCharacteristic_eq_nativeXiCompletionFactor_mul_nativeHeightScalar
    (z : ℂ) :
    completedNativeOperatorCharacteristic z =
      nativeXiCompletionFactor z * nativeHeightScalar z := by
  rfl

/-- The dressed image of the native pair is the product companion/value pair. -/
theorem nativeArchimedeanBoundaryDressing_nativePair_eq_productPair (z : ℂ) :
    nativeArchimedeanBoundaryDressing z
        (canonicalNativeUndressedScalarBoundaryPair z) =
      (productBoundaryCompanion
        nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion
        nativeHeightScalar nativeHeightScalarBoundaryCompanion z,
       nativeXiCompletionFactor z * nativeHeightScalar z) := by
  apply Prod.ext
  · simp [nativeArchimedeanBoundaryDressing,
      canonicalNativeUndressedScalarBoundaryPair,
      productBoundaryCompanion]
    ring
  · rfl

/-- On the genuine strip the completed scalar pair is the triangular dressing
of the undressed native pair. -/
theorem canonicalCompletedC3ScalarBoundaryPair_eq_nativeArchimedeanBoundaryDressing
    {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3ScalarBoundaryPair z =
      nativeArchimedeanBoundaryDressing z
        (canonicalNativeUndressedScalarBoundaryPair z) := by
  unfold canonicalCompletedC3ScalarBoundaryPair
    nativeArchimedeanBoundaryDressing
    canonicalNativeUndressedScalarBoundaryPair
  apply Prod.ext
  · rw [completedNativeOperatorBoundaryCompanion_eq_product hz]
    simp only [productBoundaryCompanion]
    ring
  · simp only [completedNativeOperatorCharacteristic, nativeHeightScalar]

/-- The undressed native pair is the normalized TFVD value/log-jet trace. -/
theorem canonicalNativeUndressedScalarBoundaryPair_eq_normalizedTfvdTrace
    {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalNativeUndressedScalarBoundaryPair z =
      (canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout z,
        canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout z) := by
  unfold canonicalNativeUndressedScalarBoundaryPair
  rw [canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout_eq_nativeCompanion
      hz,
    canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar
      hz]

/-- The Green form of the undressed native scalar boundary chart. -/
def canonicalNativeUndressedGreenForm (z w : ℂ) : ℂ :=
  greenForm (𝕜 := ℂ)
    (canonicalNativeUndressedScalarBoundaryPair z)
    (canonicalNativeUndressedScalarBoundaryPair w)

/-- Product-factor correction to the Green form of the undressed chart. -/
def canonicalArchimedeanBoundaryGreenCorrection (z w : ℂ) : ℂ :=
  ((starRingEnd ℂ) (nativeXiCompletionFactor z) *
      nativeXiCompletionBoundaryCompanion w -
    (starRingEnd ℂ) (nativeXiCompletionBoundaryCompanion z) *
      nativeXiCompletionFactor w) *
    ((starRingEnd ℂ) (nativeHeightScalar z) *
      nativeHeightScalar w)

/-- The native Green form is the scalar Wronskian of the undressed scalar. -/
theorem canonicalNativeUndressedGreenForm_eq_nativeWronskian (z w : ℂ) :
    canonicalNativeUndressedGreenForm z w =
      completedGreenWronskian
        nativeHeightScalar nativeHeightScalarBoundaryCompanion w z := by
  simpa [canonicalNativeUndressedGreenForm,
    canonicalNativeUndressedScalarBoundaryPair] using
    (completedGreenWronskian_eq_scalarGreenForm
      nativeHeightScalar nativeHeightScalarBoundaryCompanion w z).symm

/-- Exact Green-form product rule for the dressed scalar boundary chart. -/
theorem canonicalCompletedC3ScalarGreenForm_eq_scaledNative_add_archimedeanCorrection
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    greenForm (𝕜 := ℂ)
        (canonicalCompletedC3ScalarBoundaryPair z)
        (canonicalCompletedC3ScalarBoundaryPair w) =
      (starRingEnd ℂ) (nativeXiCompletionFactor z) *
          nativeXiCompletionFactor w *
          canonicalNativeUndressedGreenForm z w +
        canonicalArchimedeanBoundaryGreenCorrection z w := by
  rw [canonicalCompletedC3ScalarBoundaryPair_eq_nativeArchimedeanBoundaryDressing hz,
    canonicalCompletedC3ScalarBoundaryPair_eq_nativeArchimedeanBoundaryDressing hw]
  calc
    greenForm (𝕜 := ℂ)
        (nativeArchimedeanBoundaryDressing z
          (canonicalNativeUndressedScalarBoundaryPair z))
        (nativeArchimedeanBoundaryDressing w
          (canonicalNativeUndressedScalarBoundaryPair w)) =
      completedGreenWronskian
        (fun u ↦ nativeXiCompletionFactor u * nativeHeightScalar u)
        (productBoundaryCompanion
          nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion
          nativeHeightScalar nativeHeightScalarBoundaryCompanion)
        w z := by
          rw [nativeArchimedeanBoundaryDressing_nativePair_eq_productPair,
            nativeArchimedeanBoundaryDressing_nativePair_eq_productPair]
          simpa using
            (completedGreenWronskian_eq_scalarGreenForm
              (fun u ↦ nativeXiCompletionFactor u * nativeHeightScalar u)
              (productBoundaryCompanion
                nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion
                nativeHeightScalar nativeHeightScalarBoundaryCompanion)
              w z).symm
    _ = nativeHeightScalar w *
          (starRingEnd ℂ) (nativeHeightScalar z) *
          completedGreenWronskian
            nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion w z +
        nativeXiCompletionFactor w *
          (starRingEnd ℂ) (nativeXiCompletionFactor z) *
          completedGreenWronskian
            nativeHeightScalar nativeHeightScalarBoundaryCompanion w z := by
          exact completedGreenWronskian_mul
            nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion
            nativeHeightScalar nativeHeightScalarBoundaryCompanion w z
    _ = (starRingEnd ℂ) (nativeXiCompletionFactor z) *
          nativeXiCompletionFactor w *
          canonicalNativeUndressedGreenForm z w +
        canonicalArchimedeanBoundaryGreenCorrection z w := by
          rw [canonicalNativeUndressedGreenForm_eq_nativeWronskian]
          unfold canonicalArchimedeanBoundaryGreenCorrection
          simp only [completedGreenWronskian]
          ring

/-- The full change of Green form from the native chart to the dressed chart.
It includes both the scalar rescaling of the native channel and the
completion-jet cross correction. -/
def canonicalArchimedeanBoundaryGreenTransportCorrection
    (z w : ℂ) : ℂ :=
  ((starRingEnd ℂ) (nativeXiCompletionFactor z) *
      nativeXiCompletionFactor w - 1) *
      canonicalNativeUndressedGreenForm z w +
    canonicalArchimedeanBoundaryGreenCorrection z w

/-- The dressed scalar Green form is the native form plus the complete
archimedean transport correction. -/
theorem canonicalCompletedC3ScalarGreenForm_eq_native_add_archimedeanTransportCorrection
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    greenForm (𝕜 := ℂ)
        (canonicalCompletedC3ScalarBoundaryPair z)
        (canonicalCompletedC3ScalarBoundaryPair w) =
      canonicalNativeUndressedGreenForm z w +
        canonicalArchimedeanBoundaryGreenTransportCorrection z w := by
  rw [canonicalCompletedC3ScalarGreenForm_eq_scaledNative_add_archimedeanCorrection
    hz hw]
  unfold canonicalArchimedeanBoundaryGreenTransportCorrection
  ring

/-- The same correction written with ordinary derivatives of the completion
factor. -/
theorem canonicalArchimedeanBoundaryGreenCorrection_eq_derivative
    (z w : ℂ) :
    canonicalArchimedeanBoundaryGreenCorrection z w =
      ((starRingEnd ℂ) (deriv nativeXiCompletionFactor z) *
          nativeXiCompletionFactor w -
        (starRingEnd ℂ) (nativeXiCompletionFactor z) *
          deriv nativeXiCompletionFactor w) *
        ((starRingEnd ℂ) (nativeHeightScalar z) *
          nativeHeightScalar w) := by
  unfold canonicalArchimedeanBoundaryGreenCorrection
    nativeXiCompletionBoundaryCompanion
  simp only [map_neg]
  ring

/-- Difference between the actual Gamma boundary form and the scaled native
undressed form.  The factor is retained because a triangular dressing does
not preserve the Green form. -/
def canonicalC3NativeBoundaryGreenMismatch
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  greenForm (𝕜 := ℂ)
      (canonicalCompletedC3GammaBoundaryState z hz)
      (canonicalCompletedC3GammaBoundaryState w hw) -
    (starRingEnd ℂ) (nativeXiCompletionFactor z) *
      nativeXiCompletionFactor w *
      canonicalNativeUndressedGreenForm z w

/-- Difference between the actual Gamma boundary form and the undressed native
Green form.  This is the intrinsic boundary-chart residual. -/
def canonicalC3GammaNativeUndressedBoundaryGreenMismatch
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  greenForm (𝕜 := ℂ)
      (canonicalCompletedC3GammaBoundaryState z hz)
      (canonicalCompletedC3GammaBoundaryState w hw) -
    canonicalNativeUndressedGreenForm z w

/-- The raw Gamma--Wronskian defect decomposes into the intrinsic Gamma versus
native residual and the full archimedean chart-transport correction. -/
theorem canonicalCompletedC3RawGammaWronskianDefect_eq_gammaNativeMismatch_sub_archimedeanTransportCorrection
    {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawGammaWronskianDefect z w hz hw =
      canonicalC3GammaNativeUndressedBoundaryGreenMismatch z w hz hw -
        canonicalArchimedeanBoundaryGreenTransportCorrection z w := by
  rw [canonicalCompletedC3RawGammaWronskianDefect_eq_boundaryGreenForm_sub,
    canonicalCompletedC3ScalarGreenForm_eq_native_add_archimedeanTransportCorrection
      hzStrip hwStrip]
  unfold canonicalC3GammaNativeUndressedBoundaryGreenMismatch
  ring

/-- The existing raw Gamma--Wronskian defect also decomposes relative to the
scaled native chart, isolating only the completion-jet cross channel. -/
theorem canonicalCompletedC3RawGammaWronskianDefect_eq_nativeMismatch_sub_archimedeanCorrection
    {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawGammaWronskianDefect z w hz hw =
      canonicalC3NativeBoundaryGreenMismatch z w hz hw -
        canonicalArchimedeanBoundaryGreenCorrection z w := by
  rw [canonicalCompletedC3RawGammaWronskianDefect_eq_boundaryGreenForm_sub,
    canonicalCompletedC3ScalarGreenForm_eq_scaledNative_add_archimedeanCorrection
      hzStrip hwStrip]
  unfold canonicalC3NativeBoundaryGreenMismatch
  ring

/-- The Gamma/native mismatch vanishes exactly when the Gamma form is the
scaled native form. -/
theorem canonicalC3NativeBoundaryGreenMismatch_eq_zero_iff
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalC3NativeBoundaryGreenMismatch z w hz hw = 0 ↔
      greenForm (𝕜 := ℂ)
          (canonicalCompletedC3GammaBoundaryState z hz)
          (canonicalCompletedC3GammaBoundaryState w hw) =
        (starRingEnd ℂ) (nativeXiCompletionFactor z) *
          nativeXiCompletionFactor w *
          canonicalNativeUndressedGreenForm z w := by
  unfold canonicalC3NativeBoundaryGreenMismatch
  exact sub_eq_zero

/-- The completed log derivative separates into the native and
archimedean logarithmic derivatives. -/
theorem completedNativeLogDerivative_eq_native_add_archimedean
    {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hA : nativeXiCompletionFactor z ≠ 0)
    (hN : nativeHeightScalar z ≠ 0) :
    -deriv completedNativeOperatorCharacteristic z /
          completedNativeOperatorCharacteristic z =
      -deriv nativeHeightScalar z / nativeHeightScalar z +
        -deriv nativeXiCompletionFactor z / nativeXiCompletionFactor z := by
  have hsNative : operatorHeightParameter z ∈ nativeScalarDomain :=
    ⟨by linarith [hz.1], hz.2⟩
  have hmul :=
    ((nativeXiCompletionFactor_differentiableAt hz).hasDerivAt.mul
      (nativeHeightScalar_differentiableAt hsNative).hasDerivAt).deriv
  change deriv completedNativeOperatorCharacteristic z =
      deriv nativeXiCompletionFactor z * nativeHeightScalar z +
        nativeXiCompletionFactor z * deriv nativeHeightScalar z at hmul
  change
    -deriv completedNativeOperatorCharacteristic z /
        (nativeXiCompletionFactor z * nativeHeightScalar z) =
      -deriv nativeHeightScalar z / nativeHeightScalar z +
        -deriv nativeXiCompletionFactor z / nativeXiCompletionFactor z
  rw [hmul]
  field_simp [hA, hN]
  ring

end

end CarrySelfAdjointOperator
