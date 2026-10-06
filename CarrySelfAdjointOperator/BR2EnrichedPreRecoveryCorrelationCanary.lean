import CarrySelfAdjointOperator.CompletedNativeTfvdPreRecoveryIncidenceAudit
import CPFormal.Analytic.CpNativeGpreTfvdCommutatorTowerSource

/-!
# A concrete correlation retained by enriched BR2 pre-recovery analysis

The bracket coordinates of C3 orders zero and two are orthogonal. Their
causal states nonetheless share an active native value-provenance coordinate.
This file tests that coordinate before any camera synthesis or readout. It
does not define a six-role lift, a camera promotion, or a visible target Gram.
-/

open scoped InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open FiniteNativeCarryOperator.Camera

noncomputable section

/-- An existing active Cp context: prime two, arithmetic time one, analytic
edge four. Its positive native provenance cell is ten, not edge four. -/
def br2EnrichedCorrelationContext : NativeGpreBoundaryContext :=
  nativeGpreCanonicalActiveCommutatorContext ⟨2, Nat.prime_two⟩ 1 4

/-- The atlas retains this genuine native coordinate before compression. -/
def br2EnrichedCorrelationAtlas : Finset NativeGpreBoundaryContext :=
  {br2EnrichedCorrelationContext}

@[simp] theorem br2EnrichedCorrelationContext_cell :
    br2EnrichedCorrelationContext.cell = 10 := rfl

/-- The tested provenance coordinate is the geometric right leg of the
second even C3 bracket, not a parity/source-role relabeling. -/
theorem br2EnrichedCorrelationContext_cell_eq_second_even_right_leg :
    br2EnrichedCorrelationContext.cell = alignedCenter 3 2 + 1 := by
  norm_num [br2EnrichedCorrelationContext_cell, alignedCenter]

/-- The context's value coefficient is active by the existing native tower
result, independently of the BR2 vectors and all target moments. -/
theorem br2EnrichedCorrelationContext_valueCoefficient_ne_zero :
    nativeGpreTowerCoordinateCoefficient
      (br2EnrichedCorrelationContext.withRole .value) ≠ 0 :=
  nativeGpreCanonicalActiveCommutatorContext_active ⟨2, Nat.prime_two⟩ 1 4

/-- Expose the complete analyzed causal state, rather than only its bracket
projection. All TFVD traces and both provenance roles remain present. -/
theorem br2CausalTfvdPreRecoveryIncidenceState_eq_fullAnalysis
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    {base radius : ℕ} (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) (index : ℕ) :
    br2CausalTfvdPreRecoveryIncidenceState q S base radius index =
      nativeGpreFiniteTfvdAnalysis q S
        (br2CameraBracketCausalGreenResponse q base radius index) := by
  unfold br2CausalTfvdPreRecoveryIncidenceState br2CausalTfvdPreRecoveryIncidenceMap
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    LinearMap.restrictScalars_apply]
  rw [br2CameraBracketCausalGreenResponseMap_cameraBracketIncidence
    q hbase hradius index]

/-- On the causal prototype, the complete enriched datum is recoverable
from its bracket by the existing Green map followed by full analysis. The
nonzero coordinate pairing does not assert extra independent source data. -/
theorem br2CausalTfvdPreRecoveryIncidenceState_eq_analysisGreenBracket
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {base radius : ℕ} (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) (index : ℕ) :
    br2CausalTfvdPreRecoveryIncidenceState q S base radius index =
      nativeGpreFiniteTfvdAnalysis q S
        (carryVerticalL2WeightedGreen q
          (nativeGpreFiniteTfvdAnalysisBracketProjection S
            (br2CausalTfvdPreRecoveryIncidenceState q S base radius index))) := by
  rw [br2CausalTfvdPreRecoveryIncidenceState_bracket_eq
    q hqpos hq1 S hbase hradius index]
  exact br2CausalTfvdPreRecoveryIncidenceState_eq_fullAnalysis
    q S hbase hradius index

/-- The retained value-role coordinate is the literal active native tower
lift of the causal state. It is not a new scalar response. -/
theorem br2CausalTfvdPreRecoveryIncidenceState_value_apply
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    {base radius : ℕ} (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) (index : ℕ) (c : ↥S) :
    (br2CausalTfvdPreRecoveryIncidenceState q S base radius index).2.1 c =
      br2CameraBracketCausalGreenResponse q base radius index c.1.cell *
        (nativeGpreTowerCoordinateCoefficient (c.1.withRole .value) : ℂ) := by
  rw [br2CausalTfvdPreRecoveryIncidenceState_eq_fullAnalysis q S hbase hradius]
  exact nativeGpreFiniteContinuousBoundaryRoleLift_apply .value S _ c

/-- The causal BR2 prototype retains its TFVD trace, but that trace is
zero. A global unit Dirichlet seed must not be inferred from this prototype. -/
theorem br2CausalTfvdPreRecoveryIncidenceState_trace_eq_zero
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {base radius : ℕ} (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) (index : ℕ) :
    nativeGpreFiniteTfvdAnalysisTraceProjection S
      (br2CausalTfvdPreRecoveryIncidenceState q S base radius index) = (0, 0) := by
  rw [br2CausalTfvdPreRecoveryIncidenceState_eq_fullAnalysis q S hbase hradius]
  change carryWeightedVerticalTrace q
    (br2CameraBracketCausalGreenResponse q base radius index) = (0, 0)
  have hx0 : br2CameraBracketCausalGreenResponse q base radius index 0 = 0 := by
    rw [br2CameraBracketCausalGreenResponse_apply q hq0 hq1]
    simp [carryWeightedVerticalGreenKernel]
  have hx1 : br2CameraBracketCausalGreenResponse q base radius index 1 = 0 := by
    rw [br2CameraBracketCausalGreenResponse_apply q hq0 hq1]
    simp [Finset.sum_range_succ, carryWeightedVerticalGreenKernel,
      br2CameraBracketVerticalState_zero hbase hradius]
  rw [carryWeightedVerticalTrace_apply, hx0, hx1]
  simp

/-- Exact rational canary at one admissible TFVD parameter. The parameter
one-half is not adjusted to a target coefficient. -/
theorem br2CausalGreenResponse_C3_zero_two_at_ten :
    br2CameraBracketCausalGreenResponse (1 / 2) 3 1 0 10 = (1 / 64 : ℂ) ∧
      br2CameraBracketCausalGreenResponse (1 / 2) 3 1 2 10 = (-1 / 2 : ℂ) := by
  constructor <;>
    rw [br2CameraBracketCausalGreenResponse_apply _ (by norm_num) (by norm_num)] <;>
    norm_num [Finset.sum_range_succ, carryWeightedVerticalGreenKernel,
      br2CameraBracketVerticalState, alignedCenter, lp.single_apply]

/-- The two enriched value coordinates have a nontrivial polarized pairing.
The native tower coefficient remains explicit; it is not fitted to h-one. -/
theorem br2EnrichedPreRecovery_value02_pairing_eq :
    let c : ↥br2EnrichedCorrelationAtlas :=
      ⟨br2EnrichedCorrelationContext, Finset.mem_singleton_self _⟩
    inner ℂ
      ((br2CausalTfvdPreRecoveryIncidenceState
        (1 / 2) br2EnrichedCorrelationAtlas 3 1 0).2.1 c)
      ((br2CausalTfvdPreRecoveryIncidenceState
        (1 / 2) br2EnrichedCorrelationAtlas 3 1 2).2.1 c) =
      -(nativeGpreTowerCoordinateCoefficient
        (br2EnrichedCorrelationContext.withRole .value) : ℂ) ^ 2 / 128 := by
  dsimp only
  have hbase : IsSupported 3 := by norm_num [IsSupported]
  have hradius : (1 : ℕ) ∈ radiusSet 3 := by norm_num [radiusSet, halfRange]
  rw [br2CausalTfvdPreRecoveryIncidenceState_value_apply _ _ hbase hradius,
    br2CausalTfvdPreRecoveryIncidenceState_value_apply _ _ hbase hradius]
  simp only [br2EnrichedCorrelationContext_cell]
  rw [br2CausalGreenResponse_C3_zero_two_at_ten.1,
    br2CausalGreenResponse_C3_zero_two_at_ten.2]
  simp only [RCLike.inner_apply, map_mul, map_div₀, map_one, map_ofNat,
    Complex.conj_ofReal]
  ring

/-- Actual enriched C3 data are not pairwise orthogonal in all their
provenance coordinates. This says nothing yet about the visible camera Gram. -/
theorem br2EnrichedPreRecovery_value02_pairing_ne_zero :
    let c : ↥br2EnrichedCorrelationAtlas :=
      ⟨br2EnrichedCorrelationContext, Finset.mem_singleton_self _⟩
    inner ℂ
      ((br2CausalTfvdPreRecoveryIncidenceState
        (1 / 2) br2EnrichedCorrelationAtlas 3 1 0).2.1 c)
      ((br2CausalTfvdPreRecoveryIncidenceState
        (1 / 2) br2EnrichedCorrelationAtlas 3 1 2).2.1 c) ≠ 0 := by
  dsimp only
  rw [br2EnrichedPreRecovery_value02_pairing_eq]
  have ha : (nativeGpreTowerCoordinateCoefficient
      (br2EnrichedCorrelationContext.withRole .value) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr br2EnrichedCorrelationContext_valueCoefficient_ne_zero
  exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 ha)) (by norm_num)

end

end CarrySelfAdjointOperator
