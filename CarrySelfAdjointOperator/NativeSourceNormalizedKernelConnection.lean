import CarrySelfAdjointOperator.NativeGammaCoupledCompletionObstruction

/-! Value normalization and the completion connection.
An inner product of vectors normalized by their own scalar readout is blind
to a common scalar dressing. The actual value-normalized native Green readout
is not: its two-input correction is the skew completion connection, nonzero
at the center. These are different readouts, not an asserted positive Gram. -/
namespace CarrySelfAdjointOperator.SourceKernelCalibration
open CPFormal.Analytic.Cp NativeCarrySpectralWeyl.Boundary
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

section ScalarDressing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def readoutNormalizedState (ell : E →ₗ[ℂ] ℂ) (v : E) : E := (ell v)⁻¹ • v

/-- Exact scalar-gauge invariance, even when the readout is zero (total inverse).
No inverse is used to construct a moment-fitting input. -/
theorem readoutNormalizedState_smul (ell : E →ₗ[ℂ] ℂ) (v : E)
    (a : ℂ) (ha : a ≠ 0) :
    readoutNormalizedState ell (a • v) = readoutNormalizedState ell v := by
  simp [readoutNormalizedState, map_smul, smul_smul, mul_inv_rev, ha]

theorem readoutNormalizedGram_dressing_invariant (ell : E →ₗ[ℂ] ℂ)
    (v w : E) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    inner ℂ (readoutNormalizedState ell (a • v))
        (readoutNormalizedState ell (b • w)) =
      inner ℂ (readoutNormalizedState ell v) (readoutNormalizedState ell w) := by
  rw [readoutNormalizedState_smul ell v a ha,
    readoutNormalizedState_smul ell w b hb]
end ScalarDressing

/-- Negative logarithmic derivative of the actual completion factor. -/
def completionConnection (z : ℂ) : ℂ :=
  nativeXiCompletionBoundaryCompanion z / nativeXiCompletionFactor z

def undressedValueNormalizedGreen (z w : ℂ) : ℂ :=
  canonicalNativeUndressedGreenForm z w /
    (conj (nativeHeightScalar z)*nativeHeightScalar w)

def completedValueNormalizedGreen (z w : ℂ) : ℂ :=
  greenForm (𝕜 := ℂ) (canonicalCompletedC3ScalarBoundaryPair z)
      (canonicalCompletedC3ScalarBoundaryPair w) /
    (conj (completedNativeOperatorCharacteristic z)*completedNativeOperatorCharacteristic w)

/-- Dividing by the actual source values retains the completion correction. -/
theorem valueNormalizedGreen_discrepancy (z w : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hAz : nativeXiCompletionFactor z ≠ 0) (hAw : nativeXiCompletionFactor w ≠ 0)
    (hNz : nativeHeightScalar z ≠ 0) (hNw : nativeHeightScalar w ≠ 0) :
    completedValueNormalizedGreen z w-undressedValueNormalizedGreen z w =
      canonicalArchimedeanBoundaryGreenCorrection z w /
        (conj (completedNativeOperatorCharacteristic z)*completedNativeOperatorCharacteristic w) := by
  unfold completedValueNormalizedGreen undressedValueNormalizedGreen
  rw [canonicalCompletedC3ScalarGreenForm_eq_scaledNative_add_archimedeanCorrection hz hw]
  change (_+_)/(conj (nativeXiCompletionFactor z*nativeHeightScalar z)*
      (nativeXiCompletionFactor w*nativeHeightScalar w)) - _ =
    _/(conj (nativeXiCompletionFactor z*nativeHeightScalar z)*
      (nativeXiCompletionFactor w*nativeHeightScalar w))
  simp only [map_mul]
  have hAzc : conj (nativeXiCompletionFactor z) ≠ 0 := by simpa using hAz
  have hNzc : conj (nativeHeightScalar z) ≠ 0 := by simpa using hNz
  field_simp
  ring

/-- Exact connection law on two independent inputs, with unchanged factors. -/
theorem valueNormalizedGreen_connection (z w : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hAz : nativeXiCompletionFactor z ≠ 0) (hAw : nativeXiCompletionFactor w ≠ 0)
    (hNz : nativeHeightScalar z ≠ 0) (hNw : nativeHeightScalar w ≠ 0) :
    completedValueNormalizedGreen z w-undressedValueNormalizedGreen z w =
      completionConnection w-conj (completionConnection z) := by
  rw [valueNormalizedGreen_discrepancy z w hz hw hAz hAw hNz hNw]
  unfold canonicalArchimedeanBoundaryGreenCorrection completionConnection
  change _/(conj (nativeXiCompletionFactor z*nativeHeightScalar z)*
      (nativeXiCompletionFactor w*nativeHeightScalar w)) = _
  simp only [map_mul, map_div₀]
  have hAzc : conj (nativeXiCompletionFactor z) ≠ 0 := by simpa using hAz
  have hNzc : conj (nativeHeightScalar z) ≠ 0 := by simpa using hNz
  field_simp

/-- The correction is effective for the actual native/completed source. -/
theorem valueNormalizedGreen_center_discrepancy_ne_zero :
    completedValueNormalizedGreen 0 0-undressedValueNormalizedGreen 0 0 ≠ 0 := by
  have hs : operatorHeightParameter 0 ∈ genuineCriticalStrip := by
    norm_num [operatorHeightParameter, genuineCriticalStrip]
  have hA := nativeXiCompletionFactor_ne_zero zero_mem_completedNativeHeightDomain
  rw [valueNormalizedGreen_discrepancy 0 0 hs hs hA hA
    nativeHeightScalar_zero_ne_zero nativeHeightScalar_zero_ne_zero]
  exact div_ne_zero
    GammaMaterialSewing.nativeArchimedean_centerCorrection_cancel_nontrivially.1
    (mul_ne_zero (by simpa using completedNativeOperatorCharacteristic_zero_ne_zero)
      completedNativeOperatorCharacteristic_zero_ne_zero)

theorem completionConnection_center_skew_ne_zero :
    completionConnection 0-conj (completionConnection 0) ≠ 0 := by
  have hs : operatorHeightParameter 0 ∈ genuineCriticalStrip := by
    norm_num [operatorHeightParameter, genuineCriticalStrip]
  have hA := nativeXiCompletionFactor_ne_zero zero_mem_completedNativeHeightDomain
  rw [← valueNormalizedGreen_connection 0 0 hs hs hA hA
    nativeHeightScalar_zero_ne_zero nativeHeightScalar_zero_ne_zero]
  exact valueNormalizedGreen_center_discrepancy_ne_zero

/-- The same mandatory correction after the prescribed Green division. At
w = conj z this uses the total inverse; the native diagonal value requires
the removable-limit theorem and is not defined by this quotient. -/
theorem dividedGreen_connection_correction (z w : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hAz : nativeXiCompletionFactor z ≠ 0) (hAw : nativeXiCompletionFactor w ≠ 0)
    (hNz : nativeHeightScalar z ≠ 0) (hNw : nativeHeightScalar w ≠ 0) :
    completedValueNormalizedGreen z w / (2*(w-conj z)) -
        undressedValueNormalizedGreen z w / (2*(w-conj z)) =
      (completionConnection w-conj (completionConnection z)) / (2*(w-conj z)) := by
  rw [← sub_div, valueNormalizedGreen_connection z w hz hw hAz hAw hNz hNw]

end
end CarrySelfAdjointOperator.SourceKernelCalibration
