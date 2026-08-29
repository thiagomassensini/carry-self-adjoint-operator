import CarrySelfAdjointOperator.CompletedC3GlobalGreenOperatorCarrier
import CarrySelfAdjointOperator.CompletedC3EnrichedSymplecticNoLeakBridge
import CarrySelfAdjointOperator.CompletedNativeTfvdWronskianMoments
import Mathlib.Tactic

/-!
# Operator carrier for the full completed Wronskian

The permanent one-point C3 carrier already retains the value/log-jet head and
tail channels separately.  This module packages their completed projections
as a continuous boundary-trace readout and combines that raw C3 Wronskian with
the archimedean/chart operator block.

The resulting bounded operator realizes the chart-weighted Wronskian of the
actual completed pair `(F, -F')` at every cutoff.  This construction does not
identify the radial Green candidate with the full ledger and does not assume a
moment kernel, positivity, a zero, or spectral data.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-! ## Continuous completed-trace projection -/

/-- Continuous projection from the permanent one-point carrier to its four
separated scalar trace coordinates. -/
def canonicalCompletedC3OnePointTraceCoordinates :
    CanonicalCompletedC3AllCutoffOnePointHilbert →L[ℝ]
      CanonicalCompletedC3AllCutoffOnePointTraceHilbert :=
  (WithLp.sndL 2 ℝ
      RealifiedNaimarkComplexification
      CanonicalCompletedC3AllCutoffOnePointTraceHilbert).comp
    ((WithLp.sndL 2 ℝ
        RealifiedNaimarkComplexification
        (WithLp 2
          (RealifiedNaimarkComplexification ×
            CanonicalCompletedC3AllCutoffOnePointTraceHilbert))).comp
      (WithLp.sndL 2 ℝ
        RealifiedNaimarkComplexification
        (WithLp 2
          (RealifiedNaimarkComplexification ×
            WithLp 2
              (RealifiedNaimarkComplexification ×
                CanonicalCompletedC3AllCutoffOnePointTraceHilbert)))))

/-- Value-head coordinate as a bounded scalar readout. -/
def canonicalCompletedC3OnePointValueHeadReadout :
    CanonicalCompletedC3AllCutoffOnePointHilbert →L[ℝ] ℂ :=
  (WithLp.fstL 2 ℝ ℂ
      (WithLp 2 (ℂ × WithLp 2 (ℂ × ℂ)))).comp
    canonicalCompletedC3OnePointTraceCoordinates

/-- Log-jet-head coordinate as a bounded scalar readout. -/
def canonicalCompletedC3OnePointLogJetHeadReadout :
    CanonicalCompletedC3AllCutoffOnePointHilbert →L[ℝ] ℂ :=
  (WithLp.fstL 2 ℝ ℂ (WithLp 2 (ℂ × ℂ))).comp
    ((WithLp.sndL 2 ℝ ℂ
        (WithLp 2 (ℂ × WithLp 2 (ℂ × ℂ)))).comp
      canonicalCompletedC3OnePointTraceCoordinates)

/-- Value-tail coordinate as a bounded scalar readout. -/
def canonicalCompletedC3OnePointValueTailReadout :
    CanonicalCompletedC3AllCutoffOnePointHilbert →L[ℝ] ℂ :=
  (WithLp.fstL 2 ℝ ℂ ℂ).comp
    ((WithLp.sndL 2 ℝ ℂ (WithLp 2 (ℂ × ℂ))).comp
      ((WithLp.sndL 2 ℝ ℂ
          (WithLp 2 (ℂ × WithLp 2 (ℂ × ℂ)))).comp
        canonicalCompletedC3OnePointTraceCoordinates))

/-- Log-jet-tail coordinate as a bounded scalar readout. -/
def canonicalCompletedC3OnePointLogJetTailReadout :
    CanonicalCompletedC3AllCutoffOnePointHilbert →L[ℝ] ℂ :=
  (WithLp.sndL 2 ℝ ℂ ℂ).comp
    ((WithLp.sndL 2 ℝ ℂ (WithLp 2 (ℂ × ℂ))).comp
      ((WithLp.sndL 2 ℝ ℂ
          (WithLp 2 (ℂ × WithLp 2 (ℂ × ℂ)))).comp
        canonicalCompletedC3OnePointTraceCoordinates))

/-- Multiplication by `i`, regarded as a bounded real-linear map on `ℂ`. -/
def canonicalCompletedC3ComplexIMulReal : ℂ →L[ℝ] ℂ :=
  (((Complex.I : ℂ) • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ)

/-- Continuous completed trace `(companion, value)` obtained only after the
four head/tail channels have remained separate.  The map is real-linear
because the permanent Naimark coordinates are explicitly realified. -/
def canonicalCompletedC3OnePointCompletedTraceProjection :
    CanonicalCompletedC3AllCutoffOnePointHilbert →L[ℝ]
      CompletedScalarBoundaryTraceCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm.toContinuousLinearMap.comp
    ((canonicalCompletedC3ComplexIMulReal.comp
        (canonicalCompletedC3OnePointLogJetHeadReadout +
          canonicalCompletedC3OnePointLogJetTailReadout)).prod
      (canonicalCompletedC3OnePointValueHeadReadout +
        canonicalCompletedC3OnePointValueTailReadout))

@[simp] theorem canonicalCompletedC3OnePointCompletedTraceProjection_apply
    (state : CanonicalCompletedC3AllCutoffOnePointHilbert) :
    canonicalCompletedC3OnePointCompletedTraceProjection state =
      WithLp.toLp 2
        (state.completedCompanion, state.completedValue) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  all_goals
    simp [canonicalCompletedC3OnePointCompletedTraceProjection,
      canonicalCompletedC3OnePointValueHeadReadout,
      canonicalCompletedC3OnePointLogJetHeadReadout,
      canonicalCompletedC3OnePointValueTailReadout,
      canonicalCompletedC3OnePointLogJetTailReadout,
      canonicalCompletedC3ComplexIMulReal,
      canonicalCompletedC3OnePointTraceCoordinates,
      CanonicalCompletedC3AllCutoffOnePointHilbert.completedCompanion,
      CanonicalCompletedC3AllCutoffOnePointHilbert.completedValue,
      CanonicalCompletedC3AllCutoffOnePointHilbert.valueHead,
      CanonicalCompletedC3AllCutoffOnePointHilbert.logJetHead,
      CanonicalCompletedC3AllCutoffOnePointHilbert.valueTail,
      CanonicalCompletedC3AllCutoffOnePointHilbert.logJetTail]
  ring

/-- On the canonical cutoff state, the continuous projection is exactly the
raw completed C3 boundary trace. -/
theorem canonicalCompletedC3OnePointCompletedTraceProjection_state_eq
    (M : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3OnePointCompletedTraceProjection
        (canonicalCompletedC3AllCutoffOnePointState M z) =
      completedScalarBoundaryTraceState
        canonicalCompletedC3RawHeightValue
        canonicalCompletedC3RawHeightCompanion z := by
  rw [canonicalCompletedC3OnePointCompletedTraceProjection_apply,
    canonicalCompletedC3AllCutoffOnePointState_completedCompanion_eq M hz,
    canonicalCompletedC3AllCutoffOnePointState_completedValue_eq M hz]
  rfl

/-! ## Completed enriched one-point state -/

/-- The actual all-cutoff limit of the enriched TFVD state.  The direct,
reflected, and quarter-turned Naimark vectors remain present, while each of
the four boundary traces is completed independently. -/
def canonicalCompletedC3CompletedOnePointState
    (z : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    CanonicalCompletedC3AllCutoffOnePointHilbert :=
  WithLp.toLp 2
    (completedC3SymplecticNaimarkState
        (operatorHeightParameter z) hz.1,
      WithLp.toLp 2
        (completedC3SymplecticNaimarkState
            (reflectedParameter (operatorHeightParameter z))
            (by
              simpa [reflectedParameter] using sub_pos.mpr hz.2),
          WithLp.toLp 2
            (completedC3QuarterTurnSymplecticNaimarkState
                (reflectedParameter (operatorHeightParameter z))
                (by
                  simpa [reflectedParameter] using sub_pos.mpr hz.2),
              WithLp.toLp 2
                (bracketedDirichletChart 3 (operatorHeightParameter z),
                  WithLp.toLp 2
                    (canonicalCompletedC3EnrichedTfvdLogJetTailReadout
                        (operatorHeightParameter z),
                      WithLp.toLp 2 (0, 0))))))

/-- The permanent cutoff states converge as vectors to the completed
enriched TFVD state.  This combines the three Naimark vector limits with the
four separate head/tail limits; no scalar readout is used in the proof. -/
theorem canonicalCompletedC3AllCutoffOnePointState_tendsto_completed
    {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    Filter.Tendsto
      (fun M : ℕ => canonicalCompletedC3AllCutoffOnePointState M z)
      Filter.atTop
      (nhds (canonicalCompletedC3CompletedOnePointState z hz)) := by
  have hreflected :
      0 < (reflectedParameter (operatorHeightParameter z)).re := by
    simpa [reflectedParameter] using sub_pos.mpr hz.2
  have hdirect :=
    canonicalC3AllCutoffGenuineSymplecticNaimarkRealization_tendsto hz.1
  have hreflectedState :=
    canonicalC3AllCutoffGenuineSymplecticNaimarkRealization_tendsto
      hreflected
  have hquarterTurn :=
    canonicalC3AllCutoffGenuineQuarterTurnSymplecticNaimarkRealization_tendsto
      hreflected
  have hvalueHead :=
    finiteBracketedDirichletChart_tendsto
      3 (by norm_num) (s := operatorHeightParameter z) (by linarith [hz.1])
  have hlogJetHead :=
    finiteCanonicalLogBracketChart_tendsto_completed hz.1
  have hvalueTail :=
    realCpBracketCutoffTail_tendsto_zero
      3 (by norm_num) (s := operatorHeightParameter z) (by linarith [hz.1])
  have hlogJetTail := canonicalC3LogJetCutoffTail_tendsto_zero hz.1
  have htailPair := hvalueTail.prodMk_nhds hlogJetTail
  have htail :=
    (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp htailPair
  have hlogJetPair := hlogJetHead.prodMk_nhds htail
  have hlogJet :=
    (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp hlogJetPair
  have hvaluePair := hvalueHead.prodMk_nhds hlogJet
  have htrace :=
    (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp hvaluePair
  have hquarterPair := hquarterTurn.prodMk_nhds htrace
  have hquarter :=
    (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp hquarterPair
  have hreflectedPair := hreflectedState.prodMk_nhds hquarter
  have hreflectedBlock :=
    (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp
      hreflectedPair
  have hfullPair := hdirect.prodMk_nhds hreflectedBlock
  have hfull :=
    (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp hfullPair
  unfold canonicalCompletedC3AllCutoffOnePointState
    canonicalCompletedC3CompletedOnePointState
  convert hfull using 1
  funext M
  rfl

/-- The completed trace projection of the vector limit is the exact raw
value/log-jet boundary pair. -/
theorem canonicalCompletedC3OnePointCompletedTraceProjection_completed_eq
    {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3OnePointCompletedTraceProjection
        (canonicalCompletedC3CompletedOnePointState z hz) =
      completedScalarBoundaryTraceState
        canonicalCompletedC3RawHeightValue
        canonicalCompletedC3RawHeightCompanion z := by
  have hlimit :=
    canonicalCompletedC3OnePointCompletedTraceProjection.continuous.continuousAt.tendsto.comp
      (canonicalCompletedC3AllCutoffOnePointState_tendsto_completed hz)
  have hcanonical : Filter.Tendsto
      (fun M : ℕ =>
        canonicalCompletedC3OnePointCompletedTraceProjection
          (canonicalCompletedC3AllCutoffOnePointState M z))
      Filter.atTop
      (nhds
        (completedScalarBoundaryTraceState
          canonicalCompletedC3RawHeightValue
          canonicalCompletedC3RawHeightCompanion z)) := by
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun M => ?_)
    exact
      (canonicalCompletedC3OnePointCompletedTraceProjection_state_eq M hz).symm
  exact tendsto_nhds_unique hlimit hcanonical

/-! ## Full direct-sum operator carrier -/

/-- Hilbert carrier of the xi-weighted raw C3 trace and the independently
retained archimedean/chart correction. -/
abbrev CanonicalCompletedC3FullWronskianOperatorCarrier :=
  WithLp 2
    (CompletedScalarBoundaryTraceCarrier ×
      CanonicalCompletedC3ArchimedeanChartOperatorCarrier)

/-- Canonical full state at cutoff `M`.  Its first block is a continuous
projection of the actual enriched one-point state, not a separately postulated
scalar trace. -/
def canonicalCompletedC3FullWronskianOperatorState
    (M : ℕ) (z : ℂ) : CanonicalCompletedC3FullWronskianOperatorCarrier :=
  WithLp.toLp 2
    (nativeXiCompletionFactor z •
        canonicalCompletedC3OnePointCompletedTraceProjection
          (canonicalCompletedC3AllCutoffOnePointState M z),
      canonicalCompletedC3ArchimedeanChartOperatorState z)

/-- Cutoff-free state obtained by applying the same bounded trace projection
to the completed enriched TFVD vector. -/
def canonicalCompletedC3FullWronskianFunctionalState
    (z : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    CanonicalCompletedC3FullWronskianOperatorCarrier :=
  WithLp.toLp 2
    (nativeXiCompletionFactor z •
        canonicalCompletedC3OnePointCompletedTraceProjection
          (canonicalCompletedC3CompletedOnePointState z hz),
      canonicalCompletedC3ArchimedeanChartOperatorState z)

/-- Exact head--tail completion makes every cutoff state equal to the
cutoff-free functional state after the bounded trace projection. -/
theorem canonicalCompletedC3FullWronskianOperatorState_eq_functionalState
    (M : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3FullWronskianOperatorState M z =
      canonicalCompletedC3FullWronskianFunctionalState z hz := by
  unfold canonicalCompletedC3FullWronskianOperatorState
    canonicalCompletedC3FullWronskianFunctionalState
  rw [canonicalCompletedC3OnePointCompletedTraceProjection_state_eq M hz,
    canonicalCompletedC3OnePointCompletedTraceProjection_completed_eq hz]

/-- The projected operator states therefore converge to the same canonical
functional state; in fact the sequence is exactly constant. -/
theorem canonicalCompletedC3FullWronskianOperatorState_tendsto_functionalState
    {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    Filter.Tendsto
      (fun M : ℕ => canonicalCompletedC3FullWronskianOperatorState M z)
      Filter.atTop
      (nhds (canonicalCompletedC3FullWronskianFunctionalState z hz)) := by
  refine tendsto_const_nhds.congr'
    (Filter.Eventually.of_forall fun M => ?_)
  exact
    (canonicalCompletedC3FullWronskianOperatorState_eq_functionalState
      M hz).symm

/-- Bounded block operator: the canonical boundary rotation on the raw trace
and the already-proved crossed chart operator on the correction block. -/
def canonicalCompletedC3FullWronskianOperator :
    CanonicalCompletedC3FullWronskianOperatorCarrier →L[ℂ]
      CanonicalCompletedC3FullWronskianOperatorCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ
      CompletedScalarBoundaryTraceCarrier
      CanonicalCompletedC3ArchimedeanChartOperatorCarrier).symm
    |>.toContinuousLinearMap.comp
      ((completedScalarBoundarySymplecticRotation.comp
          (WithLp.fstL 2 ℂ
            CompletedScalarBoundaryTraceCarrier
            CanonicalCompletedC3ArchimedeanChartOperatorCarrier)).prod
        (canonicalCompletedC3ArchimedeanChartOperator.comp
          (WithLp.sndL 2 ℂ
            CompletedScalarBoundaryTraceCarrier
            CanonicalCompletedC3ArchimedeanChartOperatorCarrier)))

@[simp] theorem canonicalCompletedC3FullWronskianOperator_apply
    (state : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    canonicalCompletedC3FullWronskianOperator state = WithLp.toLp 2
      (completedScalarBoundarySymplecticRotation state.fst,
        canonicalCompletedC3ArchimedeanChartOperator state.snd) :=
  rfl

@[simp] theorem canonicalCompletedC3FullWronskianOperator_sq
    (state : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    canonicalCompletedC3FullWronskianOperator
        (canonicalCompletedC3FullWronskianOperator state) = -state := by
  rw [canonicalCompletedC3FullWronskianOperator_apply,
    canonicalCompletedC3FullWronskianOperator_apply]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact completedScalarBoundarySymplecticRotation_sq state.fst
  · exact canonicalCompletedC3ArchimedeanChartOperator_sq state.snd

/-- The cutoff-free symplectic functional on the full trace/chart carrier. -/
def canonicalCompletedC3FullWronskianFunctional
    (stateW stateZ : CanonicalCompletedC3FullWronskianOperatorCarrier) : ℂ :=
  inner ℂ stateW (canonicalCompletedC3FullWronskianOperator stateZ)

/-- The full bounded-operator readout is exactly the chart-weighted completed
Wronskian of `(F,-F')`.  No radial no-leak identification is used. -/
theorem completedFNegFPrimeWronskian_eq_fullOperatorInner
    (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedHermitianWeight canonicalC3ChartFactorHeight z w *
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
          z w =
      inner ℂ
        (canonicalCompletedC3FullWronskianOperatorState M w)
        (canonicalCompletedC3FullWronskianOperator
          (canonicalCompletedC3FullWronskianOperatorState M z)) := by
  rw [canonicalCompletedC3FullWronskianOperator_apply,
    WithLp.prod_inner_apply]
  change
    _ = inner ℂ
        (nativeXiCompletionFactor w •
          canonicalCompletedC3OnePointCompletedTraceProjection
            (canonicalCompletedC3AllCutoffOnePointState M w))
        (completedScalarBoundarySymplecticRotation
          (nativeXiCompletionFactor z •
            canonicalCompletedC3OnePointCompletedTraceProjection
              (canonicalCompletedC3AllCutoffOnePointState M z))) +
      inner ℂ
        (canonicalCompletedC3ArchimedeanChartOperatorState w)
        (canonicalCompletedC3ArchimedeanChartOperator
          (canonicalCompletedC3ArchimedeanChartOperatorState z))
  rw [map_smul, inner_smul_left, inner_smul_right]
  rw [canonicalCompletedC3OnePointCompletedTraceProjection_state_eq M hz,
    canonicalCompletedC3OnePointCompletedTraceProjection_state_eq M hw,
    ← completedGreenWronskian_eq_boundarySymplecticInner,
    ← canonicalCompletedC3ArchimedeanChartMixedChannel_eq_operatorInner]
  rw [completedFNegFPrimeWronskian_crossedChartIdentity hz hw]
  unfold mixedHermitianWeight canonicalCompletedC3RawHeightMixedWronskian
  ring

/-- The completed enriched TFVD limit realizes the chart-weighted
Wronskian through the cutoff-free symplectic functional. -/
theorem completedFNegFPrimeWronskian_eq_fullSymplecticFunctional
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedHermitianWeight canonicalC3ChartFactorHeight z w *
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
          z w =
      canonicalCompletedC3FullWronskianFunctional
        (canonicalCompletedC3FullWronskianFunctionalState w hw)
        (canonicalCompletedC3FullWronskianFunctionalState z hz) := by
  rw [← canonicalCompletedC3FullWronskianOperatorState_eq_functionalState
      0 hw,
    ← canonicalCompletedC3FullWronskianOperatorState_eq_functionalState
      0 hz]
  exact completedFNegFPrimeWronskian_eq_fullOperatorInner 0 hz hw

/-- The full operator realization is cutoff-independent at the scalar readout
level, as forced by exact head--tail completion. -/
theorem canonicalCompletedC3FullWronskianOperatorInner_cutoff_independent
    (M N : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    inner ℂ
        (canonicalCompletedC3FullWronskianOperatorState M w)
        (canonicalCompletedC3FullWronskianOperator
          (canonicalCompletedC3FullWronskianOperatorState M z)) =
      inner ℂ
        (canonicalCompletedC3FullWronskianOperatorState N w)
        (canonicalCompletedC3FullWronskianOperator
          (canonicalCompletedC3FullWronskianOperatorState N z)) := by
  rw [← completedFNegFPrimeWronskian_eq_fullOperatorInner M hz hw,
    ← completedFNegFPrimeWronskian_eq_fullOperatorInner N hz hw]

/-! ## Canonical removal of the chart weight -/

/-- The chart-normalized full state.  Its normalization is canonical and is
used only where the existing strip theorem proves the chart factor nonzero. -/
def canonicalCompletedC3NormalizedFullWronskianOperatorState
    (M : ℕ) (z : ℂ) : CanonicalCompletedC3FullWronskianOperatorCarrier :=
  (canonicalC3ChartFactorHeight z)⁻¹ •
    canonicalCompletedC3FullWronskianOperatorState M z

/-- Canonically chart-normalized cutoff-free functional state. -/
def canonicalCompletedC3NormalizedFullWronskianFunctionalState
    (z : ℂ)
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    CanonicalCompletedC3FullWronskianOperatorCarrier :=
  (canonicalC3ChartFactorHeight z)⁻¹ •
    canonicalCompletedC3FullWronskianFunctionalState z hz

/-- After the canonical chart normalization, the same bounded operator reads
the unweighted completed Wronskian exactly. -/
theorem completedGreenWronskian_eq_normalizedFullOperatorInner
    (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    completedGreenWronskian
        completedNativeOperatorCharacteristic
        (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
        z w =
      inner ℂ
        (canonicalCompletedC3NormalizedFullWronskianOperatorState M w)
        (canonicalCompletedC3FullWronskianOperator
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)) := by
  have hchartZ := canonicalC3ChartFactorHeight_ne_zero hz
  have hchartW := canonicalC3ChartFactorHeight_ne_zero hw
  unfold canonicalCompletedC3NormalizedFullWronskianOperatorState
  rw [map_smul, inner_smul_left, inner_smul_right,
    ← completedFNegFPrimeWronskian_eq_fullOperatorInner M hz hw]
  unfold mixedHermitianWeight
  simp only [map_inv₀]
  field_simp [hchartZ, hchartW]

/-- After the canonical chart normalization, the cutoff-free symplectic
functional is exactly the unweighted completed Wronskian. -/
theorem completedGreenWronskian_eq_normalizedFullSymplecticFunctional
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    completedGreenWronskian
        completedNativeOperatorCharacteristic
        (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
        z w =
      canonicalCompletedC3FullWronskianFunctional
        (canonicalCompletedC3NormalizedFullWronskianFunctionalState w hw)
        (canonicalCompletedC3NormalizedFullWronskianFunctionalState z hz) := by
  unfold canonicalCompletedC3NormalizedFullWronskianFunctionalState
  rw [← canonicalCompletedC3FullWronskianOperatorState_eq_functionalState
      0 hw,
    ← canonicalCompletedC3FullWronskianOperatorState_eq_functionalState
      0 hz]
  simpa [canonicalCompletedC3FullWronskianFunctional,
    canonicalCompletedC3NormalizedFullWronskianOperatorState] using
      (completedGreenWronskian_eq_normalizedFullOperatorInner 0 hz hw)

/-- Scalar kernel represented by the normalized full state. -/
def canonicalCompletedC3NormalizedFullWronskianOperatorKernel
    (M : ℕ) (w z : ℂ) : ℂ :=
  inner ℂ
    (canonicalCompletedC3NormalizedFullWronskianOperatorState M w)
    (canonicalCompletedC3FullWronskianOperator
      (canonicalCompletedC3NormalizedFullWronskianOperatorState M z))

/-- On the natural completed domain, the normalized operator kernel is the
unweighted completed Wronskian. -/
theorem canonicalCompletedC3NormalizedFullWronskianOperatorKernel_eq_completed
    (M : ℕ) {w z : ℂ}
    (hw : w ∈ completedNativeHeightDomain)
    (hz : z ∈ completedNativeHeightDomain) :
    canonicalCompletedC3NormalizedFullWronskianOperatorKernel M w z =
      completedGreenWronskian
        completedNativeOperatorCharacteristic
        (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
        z w := by
  exact (completedGreenWronskian_eq_normalizedFullOperatorInner M hz hw).symm

/-! ## Center response and canonical moments -/

/-- Center-pinned normalized response read solely from the full operator
carrier. -/
def canonicalCompletedC3FullOperatorNormalizedResponse
    (M : ℕ) (z : ℂ) : ℂ :=
  canonicalCompletedC3NormalizedFullWronskianOperatorKernel M 0 z /
    ((2 : ℂ) * completedNativeOperatorCharacteristic z *
      (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0))

/-- Near the centered origin, the operator-carrier response is exactly the
canonical completed normalized response. -/
theorem canonicalCompletedC3FullOperatorNormalizedResponse_eventuallyEq_completed
    (M : ℕ) :
    canonicalCompletedC3FullOperatorNormalizedResponse M =ᶠ[nhds 0]
      completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion := by
  have hdomain : completedNativeHeightDomain ∈ nhds (0 : ℂ) :=
    isOpen_completedNativeHeightDomain.mem_nhds
      zero_mem_completedNativeHeightDomain
  have hnonzero : ∀ᶠ z in nhds (0 : ℂ),
      completedNativeOperatorCharacteristic z ≠ 0 :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero
  have hcenterStar :
      (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2
      completedNativeOperatorCharacteristic_zero_ne_zero
  filter_upwards [hdomain, hnonzero] with z hzDomain hzNonzero
  rw [canonicalCompletedC3FullOperatorNormalizedResponse,
    canonicalCompletedC3NormalizedFullWronskianOperatorKernel_eq_completed
      M zero_mem_completedNativeHeightDomain hzDomain]
  have hderivZero : deriv completedNativeOperatorCharacteristic 0 = 0 :=
    deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
      completedNativeOperatorCharacteristic_eventually_even
  unfold completedGreenWronskian completedGreenNormalizedResponse
  dsimp only
  rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv]
  rw [hderivZero]
  simp only [map_zero, neg_zero, mul_zero, sub_zero]
  field_simp [hzNonzero, hcenterStar]

/-- Taylor coefficient of the response extracted from the full operator
carrier. -/
def canonicalCompletedC3FullOperatorResponseTaylorCoefficient
    (M order : ℕ) : ℂ :=
  iteratedDeriv order
      (canonicalCompletedC3FullOperatorNormalizedResponse M) 0 /
    order.factorial

/-- Every response coefficient of the full operator carrier is the canonical
completed response coefficient. -/
theorem canonicalCompletedC3FullOperatorResponseTaylorCoefficient_eq_completed
    (M order : ℕ) :
    canonicalCompletedC3FullOperatorResponseTaylorCoefficient M order =
      completedNativeGreenResponseTaylorCoefficient order := by
  unfold canonicalCompletedC3FullOperatorResponseTaylorCoefficient
    completedNativeGreenResponseTaylorCoefficient
  rw [Filter.EventuallyEq.iteratedDeriv_eq order
    (canonicalCompletedC3FullOperatorNormalizedResponse_eventuallyEq_completed M)]

/-- Real moment sequence read from the odd Taylor coefficients of the full
operator-carrier response. -/
def canonicalCompletedC3FullOperatorMoment (M n : ℕ) : ℝ :=
  (canonicalCompletedC3FullOperatorResponseTaylorCoefficient
    M (2 * n + 1)).re

/-- The full Hilbert-operator carrier produces exactly the canonical native
moment at every order and every cutoff. -/
theorem canonicalCompletedC3FullOperatorMoment_eq_canonical
    (M n : ℕ) :
    canonicalCompletedC3FullOperatorMoment M n =
      canonicalCompletedNativeLogDerivativeMoment n := by
  rw [canonicalCompletedC3FullOperatorMoment,
    canonicalCompletedC3FullOperatorResponseTaylorCoefficient_eq_completed,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]
  simp

/-- Hence the operator-carrier moments satisfy the exact division-free native
moment recurrence. -/
theorem canonicalCompletedC3FullOperatorMoment_isMomentSequence (M : ℕ) :
    IsCompletedNativeLogDerivativeMomentSequence
      (canonicalCompletedC3FullOperatorMoment M) := by
  have heq : canonicalCompletedC3FullOperatorMoment M =
      canonicalCompletedNativeLogDerivativeMoment := by
    funext n
    exact canonicalCompletedC3FullOperatorMoment_eq_canonical M n
  rw [heq]
  exact canonicalCompletedNativeLogDerivativeMoment_isMomentSequence

/-! ## Exact operator kernel and its jets -/

/-- Scalar kernel represented by the full bounded operator at cutoff `M`. -/
def canonicalCompletedC3FullWronskianOperatorKernel
    (M : ℕ) (w z : ℂ) : ℂ :=
  inner ℂ
    (canonicalCompletedC3FullWronskianOperatorState M w)
    (canonicalCompletedC3FullWronskianOperator
      (canonicalCompletedC3FullWronskianOperatorState M z))

/-- On the natural completed domain, the operator kernel is the exact
chart-weighted Wronskian of the completed native characteristic. -/
theorem canonicalCompletedC3FullWronskianOperatorKernel_eq_completed
    (M : ℕ) {w z : ℂ}
    (hw : w ∈ completedNativeHeightDomain)
    (hz : z ∈ completedNativeHeightDomain) :
    canonicalCompletedC3FullWronskianOperatorKernel M w z =
      mixedHermitianWeight canonicalC3ChartFactorHeight z w *
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
          z w := by
  exact (completedFNegFPrimeWronskian_eq_fullOperatorInner M hz hw).symm

/-- Every finite pair of jets of the full state is exactly the corresponding
forward difference of its operator kernel.  This is a vector identity and
does not invoke moments or positivity. -/
theorem canonicalCompletedC3FullWronskianOperatorJets_eq_kernelForwardDifference
    (M : ℕ) (h : ℂ) (p q : ℕ) :
    inner ℂ
        (completedGreenForwardDifferenceJet
          (canonicalCompletedC3FullWronskianOperatorState M) h p)
        (canonicalCompletedC3FullWronskianOperator
          (completedGreenForwardDifferenceJet
            (canonicalCompletedC3FullWronskianOperatorState M) h q)) =
      completedGreenKernelForwardDifference
        (canonicalCompletedC3FullWronskianOperatorKernel M) h p q := by
  exact inner_completedGreenForwardDifferenceJet_operator_eq_kernel
    canonicalCompletedC3FullWronskianOperator
    (canonicalCompletedC3FullWronskianOperatorState M)
    (canonicalCompletedC3FullWronskianOperatorState M) h p q

/-- The chart-normalized vector jets likewise realize exactly the forward
difference of the unweighted operator kernel. -/
theorem canonicalCompletedC3NormalizedFullWronskianOperatorJets_eq_kernelForwardDifference
    (M : ℕ) (h : ℂ) (p q : ℕ) :
    inner ℂ
        (completedGreenForwardDifferenceJet
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M) h p)
        (canonicalCompletedC3FullWronskianOperator
          (completedGreenForwardDifferenceJet
            (canonicalCompletedC3NormalizedFullWronskianOperatorState M)
            h q)) =
      completedGreenKernelForwardDifference
        (canonicalCompletedC3NormalizedFullWronskianOperatorKernel M)
        h p q := by
  exact inner_completedGreenForwardDifferenceJet_operator_eq_kernel
    canonicalCompletedC3FullWronskianOperator
    (canonicalCompletedC3NormalizedFullWronskianOperatorState M)
    (canonicalCompletedC3NormalizedFullWronskianOperatorState M) h p q

end

end CarrySelfAdjointOperator
