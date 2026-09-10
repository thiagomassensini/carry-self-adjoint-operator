import CarrySelfAdjointOperator.BR2GreenFrameDslopeLimitBridge
import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration

/-!
# Completed native camera/TFVD Green-frame defect crosswalk

This module audits the first component of the proposed C2-to-BR2 vector
identification.  The existing Green-frame bridge reduces the all-order gate
to equality of the normalized native limit jet with the BR2 projective jet.
Before comparing higher coordinates, its even order-zero component must be
anchored.

That anchor is impossible for every normalized state whose real-axis kernel is
the native `dslope` kernel.  The BR2 source has an exclusive center pivot
`-2`, hence its vertical state has norm at least `2`.  On the other hand, the
kernel identity at the diagonal identifies the squared norm of any normalized
state at the origin with the native moment `h₀`, and the already proved native
calibration gives `h₀ < 1/16`.

Thus this is an exact order-zero obstruction, rather than a scalar phase or a
missing higher-jet crosswalk.  The result applies to the concrete C2 pair
`(base,radius) = (2,1)` and, in fact, to every supported BR2 pair.  It does
not identify the C2 positive three-channel carrier with the `CarryVerticalL2`
state argument of the abstract Green-frame bridge; the fixed positive-carrier
sewing no-go is recorded separately in
`CompletedC3KernelMetricCalibration.lean`.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter
open FiniteNativeCarryOperator.Camera

noncomputable section

/-! ## The center pivot gives a norm floor -/

/-- Every supported BR2 vertical bracket has a center coordinate of modulus
`2`, so its `CarryVerticalL2` norm is at least `2`. -/
theorem br2CameraBracketVerticalState_norm_ge_two
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    (2 : ℝ) ≤ ‖br2CameraBracketVerticalState base radius 0‖ := by
  have hcoord := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (br2CameraBracketVerticalState base radius 0) (alignedCenter base 0)
  rw [br2CameraBracketVerticalState_apply_alignedCenter
    hbase hradius 0 0] at hcoord
  norm_num at hcoord ⊢
  exact hcoord

/-! ## The order-zero anchor is impossible -/

/-- A normalized native-kernel state cannot equal a supported BR2 order-zero
bracket.  The diagonal kernel identity forces its norm square to be `h₀`,
whereas the BR2 center pivot forces a norm square at least `4`. -/
theorem canonicalCompletedNativeGreenFrame_evenZero_anchor_impossible
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    {state : ℂ → CarryVerticalL2}
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    ¬ normalizedCompletedGreenState
        completedNativeOperatorCharacteristic state 0 =
      br2CameraBracketVerticalState base radius 0 := by
  intro hanchor
  have hdiag := hkernel 0 0
    completedNativeOperatorCharacteristic_zero_ne_zero
    completedNativeOperatorCharacteristic_zero_ne_zero
  simp only [Complex.ofReal_zero, dslope_same,
    completedNativeGreenNormalizedResponse_hasDerivAt_h0.deriv] at hdiag
  rw [hanchor] at hdiag
  rw [inner_self_eq_norm_sq_to_K] at hdiag
  have hdiagProd : ‖br2CameraBracketVerticalState base radius 0‖ *
      ‖br2CameraBracketVerticalState base radius 0‖ =
      canonicalCompletedNativeLogDerivativeMoment 0 := by
    have hdiag' := congrArg Complex.re hdiag
    simp [pow_two, Complex.mul_re] at hdiag'
    exact hdiag'
  have hnorm := br2CameraBracketVerticalState_norm_ge_two hbase hradius
  have hmoment := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  nlinarith [sq_nonneg (‖br2CameraBracketVerticalState base radius 0‖ - 2)]

/-- The analyzed finite forward-difference defect at even order zero converges
to an explicit nonzero vector.  The displayed limit is the normalized native
state at the origin minus the BR2 Green-frame state; no residual channel is
discarded. -/
theorem canonicalCompletedNativeGreenFrame_evenZero_defect_tendsto_explicit
    {base radius : ℕ}
    {state : ℂ → CarryVerticalL2}
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    Tendsto
        (fun k ↦ canonicalCompletedGreenFrameAnalysisCLM
            (completedGreenForwardDifferenceParityJet
              (normalizedCompletedGreenState
                completedNativeOperatorCharacteristic state) k (Sum.inl 0)) -
          br2CameraBracketGreenFrameParityJet base radius (Sum.inl 0))
        atTop
        (nhds
          (canonicalCompletedGreenFrameAnalysisCLM
              (normalizedCompletedGreenState
                completedNativeOperatorCharacteristic state 0) -
            br2CameraBracketGreenFrameParityJet base radius (Sum.inl 0))) := by
  have ht :=
    (canonicalCompletedGreenFrame_forwardDifference_tendsto_dslope
      state hkernel (Sum.inl 0)).sub_const
      (br2CameraBracketGreenFrameParityJet base radius (Sum.inl 0))
  rw [canonicalCompletedNativeGreenFrameDslopeJet_inl_zero] at ht
  exact ht

/-- The explicit order-zero limit above is nonzero for every supported BR2
pair.  Faithfulness of the Green analysis reduces a zero difference to the
impossible anchor. -/
theorem canonicalCompletedNativeGreenFrame_evenZero_defect_limit_ne_zero
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    {state : ℂ → CarryVerticalL2}
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    canonicalCompletedGreenFrameAnalysisCLM
          (normalizedCompletedGreenState
            completedNativeOperatorCharacteristic state 0) -
        br2CameraBracketGreenFrameParityJet base radius (Sum.inl 0) ≠ 0 := by
  intro hzero
  have hanal := sub_eq_zero.mp hzero
  apply canonicalCompletedNativeGreenFrame_evenZero_anchor_impossible
    hbase hradius hkernel
  apply canonicalCompletedGreenFrameAnalysisCLM_injective at hanal
  simpa [br2CameraBracketGreenFrameParityJet,
    br2CameraBracketProjectiveHilbertParityJet] using hanal

/-- Consequently the order-zero vector defect cannot tend to zero.  This is
the exact first obstruction to the all-order BR2 sewing gate. -/
theorem canonicalCompletedNativeGreenFrame_evenZero_defect_not_tendsto_zero
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    {state : ℂ → CarryVerticalL2}
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    ¬ Tendsto
        (fun k ↦ canonicalCompletedGreenFrameAnalysisCLM
            (completedGreenForwardDifferenceParityJet
              (normalizedCompletedGreenState
                completedNativeOperatorCharacteristic state) k (Sum.inl 0)) -
          br2CameraBracketGreenFrameParityJet base radius (Sum.inl 0))
        atTop (nhds 0) := by
  intro h
  exact (canonicalCompletedNativeGreenFrame_evenZero_anchor_impossible
    hbase hradius hkernel)
      ((canonicalCompletedNativeGreenFrame_evenZero_defect_tendsto_zero_iff_anchor
        state hkernel base radius).mp h)

/-- No normalized native-kernel state can satisfy the full BR2 Green-frame
vector identification once its order-zero component is included. -/
theorem canonicalCompletedNativeGreenFrameDslopeJet_ne_br2_of_kernel
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    {state : ℂ → CarryVerticalL2}
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    ¬ canonicalCompletedNativeGreenFrameDslopeJet state hkernel =
        br2CameraBracketGreenFrameParityJet base radius := by
  intro heq
  have hanal := congrFun heq (Sum.inl 0)
  rw [canonicalCompletedNativeGreenFrameDslopeJet_inl_zero] at hanal
  apply canonicalCompletedNativeGreenFrame_evenZero_anchor_impossible
    hbase hradius hkernel
  apply canonicalCompletedGreenFrameAnalysisCLM_injective at hanal
  simpa [br2CameraBracketGreenFrameParityJet,
    br2CameraBracketProjectiveHilbertParityJet] using hanal

/-! ## Canonical C2 specialization -/

/-- The C2 literal camera is a supported BR2 camera. -/
theorem c2CanonicalBase_isSupported : IsSupported 2 := by
  norm_num [IsSupported]

/-- Radius one is the canonical C2 centered-bracket radius. -/
theorem c2CanonicalRadius_one_mem : (1 : ℕ) ∈ radiusSet 2 := by
  norm_num [radiusSet, halfRange]

@[simp] theorem c2CanonicalNativeGreenFrame_evenZero_anchor_impossible
    {state : ℂ → CarryVerticalL2}
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    ¬ normalizedCompletedGreenState
        completedNativeOperatorCharacteristic state 0 =
      br2CameraBracketVerticalState 2 1 0 :=
  canonicalCompletedNativeGreenFrame_evenZero_anchor_impossible
    c2CanonicalBase_isSupported c2CanonicalRadius_one_mem hkernel

theorem c2CanonicalNativeGreenFrameDslopeJet_ne_br2_of_kernel
    {state : ℂ → CarryVerticalL2}
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    ¬ canonicalCompletedNativeGreenFrameDslopeJet state hkernel =
        br2CameraBracketGreenFrameParityJet 2 1 :=
  canonicalCompletedNativeGreenFrameDslopeJet_ne_br2_of_kernel
    c2CanonicalBase_isSupported c2CanonicalRadius_one_mem hkernel

theorem c2CanonicalNativeGreenFrame_evenZero_defect_not_tendsto_zero
    {state : ℂ → CarryVerticalL2}
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    ¬ Tendsto
        (fun k ↦ canonicalCompletedGreenFrameAnalysisCLM
            (completedGreenForwardDifferenceParityJet
              (normalizedCompletedGreenState
                completedNativeOperatorCharacteristic state) k (Sum.inl 0)) -
          br2CameraBracketGreenFrameParityJet 2 1 (Sum.inl 0))
        atTop (nhds 0) :=
  canonicalCompletedNativeGreenFrame_evenZero_defect_not_tendsto_zero
    c2CanonicalBase_isSupported c2CanonicalRadius_one_mem hkernel

end

end CarrySelfAdjointOperator
