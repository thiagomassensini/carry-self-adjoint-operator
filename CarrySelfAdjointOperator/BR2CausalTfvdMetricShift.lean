import CarrySelfAdjointOperator.BR2CausalShiftDefect
import CarrySelfAdjointOperator.CarryTfvdTraceMetricKernel
import CarrySelfAdjointOperator.C3ProjectiveHilbertRBBridge

/-!
# The existing bracket-plus-trace metric on the actual causal C3 responses

The trace is retained and computed. For these zero-seed responses it vanishes,
so the exact metric readout recovers the literal source Gram. Its first shift
defect is exactly -6. This does not exclude other completed trace families.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp FiniteNativeCarryOperator.Camera NativeCarrySpectralWeyl.Camera
open scoped InnerProductSpace lp

noncomputable section
set_option autoImplicit false

/-- The two incoming coordinates of the existing causal C3 response vanish. -/
theorem br2C3CausalResponse_head_zero
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    br2CameraBracketCausalGreenResponse q 3 1 n 0 = 0 ∧
      br2CameraBracketCausalGreenResponse q 3 1 n 1 = 0 := by
  have h0 : br2CameraBracketVerticalState 3 1 n 0 = 0 := by
    simp [br2CameraBracketVerticalState, lp.single_apply, Pi.single_apply]
    omega
  have h1 : br2CameraBracketVerticalState 3 1 n 1 = 0 := by
    simp [br2CameraBracketVerticalState, lp.single_apply, Pi.single_apply]
    omega
  constructor
  · rw [br2CameraBracketCausalGreenResponse_apply q hq0 hq1]
    simp
  · rw [br2CameraBracketCausalGreenResponse_apply q hq0 hq1]
    simp [Finset.sum_range_succ, h0, h1]

/-- The trace is evaluated, rather than omitted from the metric. -/
theorem br2C3CausalResponse_trace_zero
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    carryWeightedVerticalTrace q (br2CameraBracketCausalGreenResponse q 3 1 n) = 0 := by
  have h := br2C3CausalResponse_head_zero q hq0 hq1 n
  simp [carryWeightedVerticalTrace_apply, h.1, h.2]

/-- The full existing TFVD metric transports the causal responses exactly
to the Gram of their incidence sources, for arbitrary crossed indices. -/
theorem br2C3CausalTfvdMetric_inner_eq_source
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (i j : ℕ) :
    inner ℂ (carryTfvdMetricState q (br2CameraBracketCausalGreenResponse q 3 1 i))
        (carryTfvdMetricState q (br2CameraBracketCausalGreenResponse q 3 1 j)) =
      inner ℂ (br2CameraBracketVerticalState 3 1 i)
        (br2CameraBracketVerticalState 3 1 j) := by
  have hbase : IsSupported 3 := by norm_num [IsSupported]
  have hradius : (1 : ℕ) ∈ radiusSet 3 := by norm_num [mem_radiusSet_iff]
  rw [carryTfvdMetricState_inner,
    carryTfvdCausalSecondDifference_inner_eq_bracket_add_trace,
    carryWeightedVerticalCenteredBracket_br2CausalGreenResponse q hqpos hq1 hbase hradius,
    carryWeightedVerticalCenteredBracket_br2CausalGreenResponse q hqpos hq1 hbase hradius,
    br2C3CausalResponse_trace_zero q hqpos.le hq1,
    br2C3CausalResponse_trace_zero q hqpos.le hq1]
  simp [carryTfvdTraceMetric]

/-- The first shift defect in that retained bracket-plus-trace metric is
exactly -6. The raw Gram entries are reused from the projective frontier. -/
theorem br2C3CausalTfvdMetric_firstShiftDefect_eq_neg_six
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    let v := fun n => carryTfvdMetricState q (br2CameraBracketCausalGreenResponse q 3 1 n)
    inner ℂ (v 0) (v 2) - inner ℂ (v 1) (v 1) = -6 := by
  dsimp only
  rw [br2C3CausalTfvdMetric_inner_eq_source q hqpos hq1,
    br2C3CausalTfvdMetric_inner_eq_source q hqpos hq1]
  have h02 := ProjectiveValve.c3_rawCoefficient_zero_two
  have h11 := ProjectiveValve.c3_rawCoefficient_one_one
  simp only [ProjectiveValve.projectiveIncidenceCoefficient,
    ProjectiveValve.projectiveIncidenceRawJet_coreToHilbert] at h02 h11
  rw [h02, h11]
  norm_num

/-- The existing projective Hilbert/RB recovery preserves the original
pairing, hence it transports the same strict defect on this causal family. -/
theorem br2C3CausalProjectiveReturn_firstShiftDefect_neg
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    let data := fun n => nativeGpreTfvdProjectiveHilbertRealization q
      (br2CameraBracketCausalGreenResponse q 3 1 n)
    (nativeGpreTfvdProjectivePulledBackInner q hqpos.le hq1 (data 0) (data 2) -
      nativeGpreTfvdProjectivePulledBackInner q hqpos.le hq1 (data 1) (data 1)).re < 0 := by
  dsimp only
  rw [nativeGpreTfvdProjectivePulledBackInner_realization q hqpos hq1,
    nativeGpreTfvdProjectivePulledBackInner_realization q hqpos hq1]
  exact br2C3CausalResponse_firstShiftDefect_neg q hqpos hq1

end
end CarrySelfAdjointOperator
