import CarrySelfAdjointOperator.CompletedC3RawSpectralTraceTransport

/-!
# Completed C3 Green--Wronskian readout on one separated state

The finite enriched C3 ledger retains its radial Green, Wronskian-skew,
off-diagonal, and seam channels until the channel-local final readout.  This
file states its completed limit directly in the canonical trace coordinates
`(F, -F')`.

The last theorem records the exact frontier that must not be hidden in this
rephrasing: replacing the complete separated-ledger readout by the positive
radial Green limit at a Genuine zero is equivalent to critical-line
confinement at that point.
-/

open scoped Topology

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section

/-- The boundary pair extracted from the tail-completed enriched TFVD state.
The companion and value remain separate coordinates of one pair. -/
def canonicalCompletedC3FNegFPrimeGreenBoundaryState (z : ℂ) : ℂ × ℂ :=
  (canonicalCompletedC3EnrichedTfvdBoundaryCompanion z,
    canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout z)

/-- On the centered-height strip, the boundary state is literally
`(-F', F)`. -/
theorem canonicalCompletedC3FNegFPrimeGreenBoundaryState_eq
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3FNegFPrimeGreenBoundaryState z =
      (-deriv completedNativeOperatorCharacteristic z,
        completedNativeOperatorCharacteristic z) := by
  unfold canonicalCompletedC3FNegFPrimeGreenBoundaryState
  apply Prod.ext
  · rw [
      canonicalCompletedC3EnrichedTfvdBoundaryCompanion_eq_completedNativeOperatorBoundaryCompanion
        hs,
      completedNativeOperatorBoundaryCompanion_eq_neg_deriv]
  · exact
      canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout_eq_characteristic
        hs

/-- The algebraic Green form of the same completed boundary state is exactly
the Wronskian of `(F, -F')`; no real-part projection is used. -/
theorem greenForm_canonicalCompletedC3FNegFPrimeBoundaryState_eq_wronskian
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    NativeCarrySpectralWeyl.Boundary.greenForm (𝕜 := ℂ)
        (canonicalCompletedC3FNegFPrimeGreenBoundaryState w)
        (canonicalCompletedC3FNegFPrimeGreenBoundaryState z) =
      completedGreenWronskian
        completedNativeOperatorCharacteristic
        (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
        z w := by
  rw [canonicalCompletedC3FNegFPrimeGreenBoundaryState_eq hz,
    canonicalCompletedC3FNegFPrimeGreenBoundaryState_eq hw]
  simp [NativeCarrySpectralWeyl.Boundary.greenForm,
    completedGreenWronskian]

/-- Completion of the full four-channel C3 ledger gives the Green form of
the single boundary state `(-F', F)`.  Radial, skew, off-diagonal, and seam
coordinates stay separated at every finite cutoff and are combined only by
their channel-local final readout. -/
theorem finalScalarReadout_tendsto_greenForm_F_negFprime
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ =>
        canonicalCompletedC3FinalScalarReadout
          (canonicalCompletedC3FiniteEnrichedSeparatedBoundaryChannels M z))
      atTop
      (nhds
        (NativeCarrySpectralWeyl.Boundary.greenForm (𝕜 := ℂ)
          (canonicalCompletedC3FNegFPrimeGreenBoundaryState z)
          (canonicalCompletedC3FNegFPrimeGreenBoundaryState z))) := by
  have hlimit := finalScalarReadout_tendsto_completedWronskian hs
  have hgreen :=
    greenForm_canonicalCompletedC3FNegFPrimeBoundaryState_eq_wronskian hs hs
  have htrace :
      completedGreenWronskian
          canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
          canonicalCompletedC3EnrichedTfvdBoundaryCompanion z z =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
          z z := by
    simp only [completedGreenWronskian,
      canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout_eq_characteristic
        hs,
      canonicalCompletedC3EnrichedTfvdBoundaryCompanion_eq_completedNativeOperatorBoundaryCompanion
        hs,
      completedNativeOperatorBoundaryCompanion_eq_neg_deriv]
  rw [htrace, ← hgreen] at hlimit
  exact hlimit

/-- At a Genuine zero, identifying the independently completed positive
radial Green limit with the completed `(F, -F')` Wronskian is equivalent to
the critical-line conclusion at that point.  This is the precise remaining
positive-Green frontier; it is not discharged by the separated-ledger limit
above. -/
theorem normalizedGreenLimit_eq_F_negFprimeWronskian_at_genuineZero_iff
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    canonicalCompletedC3NormalizedGreenLimitTrace s =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
          (centeredHeightParameter s) (centeredHeightParameter s) ↔
      s.re = (1 : ℝ) / 2 := by
  have hzStrip :
      operatorHeightParameter (centeredHeightParameter s) ∈
        genuineCriticalStrip := by
    simpa using hs
  have hwronskian :
      completedGreenWronskian
          completedNativeOperatorCharacteristic
          (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
          (centeredHeightParameter s) (centeredHeightParameter s) = 0 := by
    have htfvd :=
      canonicalCompletedC3EnrichedTfvdWronskian_eq_zero_of_genuine_zero
        hs hzero
    simpa only [completedGreenWronskian,
      canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout_eq_characteristic
        hzStrip,
      canonicalCompletedC3EnrichedTfvdBoundaryCompanion_eq_completedNativeOperatorBoundaryCompanion
        hzStrip,
      completedNativeOperatorBoundaryCompanion_eq_neg_deriv] using htfvd
  constructor
  · intro hidentity
    by_contra hoff
    apply canonicalCompletedC3NormalizedGreenLimitTrace_ne_zero hs hoff
    rw [hidentity, hwronskian]
  · intro hre
    rw [hwronskian,
      canonicalCompletedC3NormalizedGreenLimitTrace_eq_energy]
    have him : (centeredHeightParameter s).im = 0 := by
      rw [centeredHeightParameter_im]
      linarith
    have hfixed :
        centeredHeightParameter s =
          (starRingEnd ℂ) (centeredHeightParameter s) :=
      (Complex.conj_eq_iff_im.mpr him).symm
    have hsub :
        centeredHeightParameter s -
            (starRingEnd ℂ) (centeredHeightParameter s) = 0 :=
      sub_eq_zero.mpr hfixed
    rw [hsub, zero_mul]

end

end CarrySelfAdjointOperator
