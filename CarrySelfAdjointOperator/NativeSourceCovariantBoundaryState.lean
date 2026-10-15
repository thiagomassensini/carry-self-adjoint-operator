import CarrySelfAdjointOperator.NativeSourceNormalizedKernelConnection
import CarrySelfAdjointOperator.NativePrimeCarryKernelCalibration
import CarrySelfAdjointOperator.CompletedC3FullWronskianCentralChiralEnergy

/-! The actual completed value/companion state retains the completion
connection after normalization. Its standard Gram is explicitly computed,
including all four companion crossings. The unit value coordinate rules out
using this unchanged state as the zeroth moment vector under an isometry. -/
namespace CarrySelfAdjointOperator.SourceKernelCalibration
open CPFormal.Analytic.Cp
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def nativeConnection (z : ℂ) : ℂ :=
  nativeHeightScalarBoundaryCompanion z / nativeHeightScalar z

def completedConnection (z : ℂ) : ℂ :=
  completedNativeOperatorBoundaryCompanion z / completedNativeOperatorCharacteristic z

/-- Normalization of the original pair, independent of any target moment. -/
def completedConnectionState (z : ℂ) : WithLp 2 (ℂ × ℂ) :=
  WithLp.toLp 2 (completedConnection z, 1)

theorem completedConnection_eq_sum (z : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hA : nativeXiCompletionFactor z ≠ 0) (hN : nativeHeightScalar z ≠ 0) :
    completedConnection z = nativeConnection z+completionConnection z := by
  unfold completedConnection nativeConnection completionConnection
  rw [completedNativeOperatorBoundaryCompanion_eq_product hz]
  change (nativeXiCompletionBoundaryCompanion z*nativeHeightScalar z +
    nativeXiCompletionFactor z*nativeHeightScalarBoundaryCompanion z) /
    (nativeXiCompletionFactor z*nativeHeightScalar z) = _
  field_simp
  ring

/-- Real source normalization, not a postulated positive kernel. -/
theorem completedConnectionState_eq_normalized_pair (z : ℂ)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    completedConnectionState z = (completedNativeOperatorCharacteristic z)⁻¹ •
      WithLp.toLp 2 (canonicalCompletedC3ScalarBoundaryPair z) := by
  apply WithLp.ofLp_injective
  ext <;> simp [completedConnectionState, completedConnection,
    canonicalCompletedC3ScalarBoundaryPair, div_eq_mul_inv, hF, mul_comm]

/-- The full Gram retains native, completion, and BOTH ordered cross terms. -/
theorem completedConnectionState_polarized_gram (z w : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hAz : nativeXiCompletionFactor z ≠ 0) (hAw : nativeXiCompletionFactor w ≠ 0)
    (hNz : nativeHeightScalar z ≠ 0) (hNw : nativeHeightScalar w ≠ 0) :
    inner ℂ (completedConnectionState z) (completedConnectionState w) =
      1 + conj (nativeConnection z)*nativeConnection w +
        conj (completionConnection z)*completionConnection w +
        conj (nativeConnection z)*completionConnection w +
        conj (completionConnection z)*nativeConnection w := by
  rw [WithLp.prod_inner_apply]
  simp only [completedConnectionState, RCLike.inner_apply, WithLp.ofLp_toLp,
    map_one, mul_one]
  rw [completedConnection_eq_sum z hz hAz hNz,
    completedConnection_eq_sum w hw hAw hNw]
  simp only [map_add]
  ring

theorem completedConnection_zero : completedConnection 0 = 0 := by
  have hd := deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
    completedNativeOperatorCharacteristic_eventually_even
  simp [completedConnection, completedNativeOperatorBoundaryCompanion, hd]

/-- The completion and native connection cancel at the center. -/
theorem native_completion_connections_center_cancel :
    nativeConnection 0+completionConnection 0 = 0 := by
  have hA := nativeXiCompletionFactor_ne_zero zero_mem_completedNativeHeightDomain
  rw [← completedConnection_eq_sum 0 zero_mem_completedNativeHeightDomain hA
    nativeHeightScalar_zero_ne_zero, completedConnection_zero]

theorem completedConnectionState_center_norm_sq :
    ‖completedConnectionState 0‖^2 = 1 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp [completedConnectionState, completedConnection_zero]

/-- Full pair normalization has retained the connection, but its standard
Hilbert state still has the wrong central energy for the moment problem. -/
theorem completedConnectionState_isometric_transport_noGo
    (L : WithLp 2 (ℂ × ℂ) →ₗᵢ[ℝ] NativeGpreTowerHilbert) :
    complementKernel (L (completedConnectionState 0)) (L (completedConnectionState 0)) ≠
      canonicalCompletedNativeLogDerivativeMoment 0 :=
  raw_unit_state_isometric_transport_noGo L _
    (by rw [completedConnectionState_center_norm_sq])

/-- Source-derived first jet; no scalar is selected to fit a target norm. -/
def completedConnectionTangent : WithLp 2 (ℂ × ℂ) :=
  WithLp.toLp 2 (deriv completedConnection 0, 0)

theorem completedConnection_hasDerivAt_center :
    HasDerivAt completedConnection
      (2*(canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) 0 := by
  have heq : completedConnection = fun z => (2 : ℂ)*
      completedGreenNormalizedResponse completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z := by
    funext z
    simp only [completedConnection, completedGreenNormalizedResponse, div_eq_mul_inv,
      mul_inv_rev]
    ring
  rw [heq]
  exact completedNativeGreenNormalizedResponse_hasDerivAt_h0.const_mul (2 : ℂ)

theorem completedConnectionTangent_norm_sq :
    ‖completedConnectionTangent‖^2 =
      4*(canonicalCompletedNativeLogDerivativeMoment 0)^2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖deriv completedConnection 0‖^2+‖(0 : ℂ)‖^2 = _
  rw [completedConnection_hasDerivAt_center.deriv]
  norm_num [mul_pow, sq_abs]

/-- The tangent fails on the other side: even its TOTAL standard energy is
strictly below h₀. Thus contraction cannot turn it into the zeroth moment. -/
theorem completedConnectionTangent_isometric_transport_noGo
    (L : WithLp 2 (ℂ × ℂ) →ₗᵢ[ℝ] NativeGpreTowerHilbert) :
    complementKernel (L completedConnectionTangent) (L completedConnectionTangent) <
      canonicalCompletedNativeLogDerivativeMoment 0 := by
  have hp := canonicalCompletedNativeLogDerivativeMoment_zero_pos
  have hu := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  have he : ‖L completedConnectionTangent‖^2 =
      4*(canonicalCompletedNativeLogDerivativeMoment 0)^2 := by
    rw [L.norm_map, completedConnectionTangent_norm_sq]
  rw [complementKernel_self]
  have hsmall : 4*(canonicalCompletedNativeLogDerivativeMoment 0)^2 <
      canonicalCompletedNativeLogDerivativeMoment 0 := by
    nlinarith
  rw [he]
  nlinarith [sq_nonneg ‖nativeGprePrimeCarryDefectState (L completedConnectionTangent)‖]

end
end CarrySelfAdjointOperator.SourceKernelCalibration
