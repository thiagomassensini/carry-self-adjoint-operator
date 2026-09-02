import CarrySelfAdjointOperator.CompletedC3ExistingRawSymplecticCarrierAudit
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic

/-!
# Tangent audit of the completed C3 symplectic crossing

This file identifies the already proved central variation `h₀` before any
positive interpretation.  The unnormalized numerator is the fixed full
Wronskian operator paired between the central response and the real source
curve.  Its derivative is the value of one fixed continuous linear
functional on the real source tangent.

No new carrier, boundary pencil, symplectic operator, Gram realization,
positivity claim, clock quotient, theta representation, zero hypothesis,
confinement statement, higher moment, or all-order construction is added.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-! ## Unnormalized collision numerator and its existing denominator -/

/-- The unnormalized full-operator crossing on the real collision line. -/
def canonicalCompletedC3FullOperatorRealCollisionNumerator
    (M : ℕ) (t : ℝ) : ℂ :=
  inner ℂ
    (canonicalCompletedC3FullWronskianOperatorState M 0)
    (canonicalCompletedC3FullWronskianOperator
      (canonicalCompletedC3FullWronskianOperatorState M (t : ℂ)))

/-- The normalization already used by the channel-complete central ledger.
It is cutoff-independent; the parameter `M` belongs only to the numerator. -/
def canonicalCompletedC3FullOperatorRealCollisionNormalization
    (t : ℝ) : ℂ :=
  canonicalCompletedC3FixedCenterLedgerNormalization (t : ℂ)

/-- The quotient of the unnormalized operator crossing by the old ledger
normalization. -/
def canonicalCompletedC3FullOperatorRealCollisionQuotient
    (M : ℕ) (t : ℝ) : ℂ :=
  canonicalCompletedC3FullOperatorRealCollisionNumerator M t /
    canonicalCompletedC3FullOperatorRealCollisionNormalization t

@[simp] theorem canonicalCompletedC3FullOperatorRealCollisionNumerator_zero
    (M : ℕ) :
    canonicalCompletedC3FullOperatorRealCollisionNumerator M 0 = 0 := by
  exact canonicalCompletedC3FullWronskianOperator_center_collision M

/-- The unnormalized quotient is pointwise the total symplectic branch
already isolated by the collision audit. -/
theorem canonicalCompletedC3FullOperatorRealCollisionQuotient_eq_total
    (M : ℕ) (t : ℝ) :
    canonicalCompletedC3FullOperatorRealCollisionQuotient M t =
      canonicalCompletedC3FixedCenterTotalSymplecticRealBranch t := by
  have ht : operatorHeightParameter (t : ℂ) ∈ genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter]
  unfold canonicalCompletedC3FullOperatorRealCollisionQuotient
    canonicalCompletedC3FullOperatorRealCollisionNumerator
    canonicalCompletedC3FullOperatorRealCollisionNormalization
    canonicalCompletedC3FixedCenterTotalSymplecticRealBranch
  rw [canonicalCompletedC3FullWronskianOperator_inner_eq_raw_add_archimedean,
    canonicalCompletedC3RawWronskianOperator_inner_eq M ht
      zero_mem_completedNativeHeightDomain,
    ← canonicalCompletedC3ArchimedeanChartMixedChannel_eq_operatorInner,
    canonicalCompletedC3FixedCenterGlobalOperatorRealBranch_eq_archimedean]
  unfold canonicalCompletedC3FixedCenterRawWronskianBranch
    canonicalCompletedC3FixedCenterArchimedeanBranch
  ring

/-- The same quotient is the full-operator normalized response introduced in
the existing raw-carrier audit. -/
theorem canonicalCompletedC3FullOperatorRealCollisionQuotient_eq_existing
    (M : ℕ) (t : ℝ) :
    canonicalCompletedC3FullOperatorRealCollisionQuotient M t =
      canonicalCompletedC3FullOperatorFixedCenterRealBranch M t := by
  rw [canonicalCompletedC3FullOperatorRealCollisionQuotient_eq_total,
    canonicalCompletedC3FullOperatorFixedCenterRealBranch_eq_total]

/-! ## A differentiable representative of the already existing source -/

/-- Product expression for the raw C3 value on the open strip.  It is named
only to expose differentiability of the old trace state. -/
def canonicalCompletedC3RawAnalyticValue (z : ℂ) : ℂ :=
  canonicalC3ChartFactorHeight z * nativeHeightScalar z

/-- Product-rule companion of the same raw value. -/
def canonicalCompletedC3RawAnalyticCompanion (z : ℂ) : ℂ :=
  productBoundaryCompanion
    canonicalC3ChartFactorHeight canonicalC3ChartFactorHeightCompanion
    nativeHeightScalar nativeHeightScalarBoundaryCompanion z

theorem canonicalCompletedC3RawHeightValue_eq_analyticValue
    {z : ℂ} (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawHeightValue z =
      canonicalCompletedC3RawAnalyticValue z := by
  rw [canonicalCompletedC3RawHeightValue_eq_chart_mul_normalized hz,
    canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar
      hz]
  rfl

theorem canonicalCompletedC3RawHeightCompanion_eq_analyticCompanion
    {z : ℂ} (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawHeightCompanion z =
      canonicalCompletedC3RawAnalyticCompanion z := by
  rw [canonicalCompletedC3RawHeightCompanion_eq_chartProductCompanion hz]
  unfold canonicalCompletedC3RawAnalyticCompanion productBoundaryCompanion
  rw [
    canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar
      hz,
    canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout_eq_nativeCompanion
      hz]

/-- Strip-local analytic spelling of the old full state.  It has exactly the
same two carrier blocks; no replacement carrier is introduced. -/
def canonicalCompletedC3FullWronskianAnalyticState
    (z : ℂ) : CanonicalCompletedC3FullWronskianOperatorCarrier :=
  let rawTrace := completedScalarBoundaryTraceState
    canonicalCompletedC3RawAnalyticValue
    canonicalCompletedC3RawAnalyticCompanion z
  let nativeTrace := completedScalarBoundaryTraceState
    nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion z
  let chartTrace := completedScalarBoundaryTraceState
    canonicalC3ChartFactorHeight canonicalC3ChartFactorHeightCompanion z
  WithLp.toLp 2
    (nativeXiCompletionFactor z • rawTrace,
      WithLp.toLp 2
        ((nativeHeightScalar z * canonicalC3ChartFactorHeight z) • nativeTrace,
          (nativeHeightScalar z * nativeXiCompletionFactor z) • chartTrace))

/-- On the strip, the cutoff state is exactly its analytic spelling. -/
theorem canonicalCompletedC3FullWronskianOperatorState_eq_analyticState
    (M : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3FullWronskianOperatorState M z =
      canonicalCompletedC3FullWronskianAnalyticState z := by
  unfold canonicalCompletedC3FullWronskianOperatorState
    canonicalCompletedC3FullWronskianAnalyticState
  rw [canonicalCompletedC3OnePointCompletedTraceProjection_state_eq M hz]
  dsimp only
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change nativeXiCompletionFactor z •
        completedScalarBoundaryTraceState
          canonicalCompletedC3RawHeightValue
          canonicalCompletedC3RawHeightCompanion z = _
    unfold completedScalarBoundaryTraceState
    rw [canonicalCompletedC3RawHeightValue_eq_analyticValue hz,
      canonicalCompletedC3RawHeightCompanion_eq_analyticCompanion hz]
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change
        (canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout z *
            canonicalC3ChartFactorHeight z) • _ = _
      rw [canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar
        hz]
    · change
        (canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout z *
            nativeXiCompletionFactor z) • _ = _
      rw [canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar
        hz]

private theorem canonicalC3ChartFactorHeightCompanion_analyticAt_zero :
    AnalyticAt ℂ canonicalC3ChartFactorHeightCompanion 0 := by
  exact (canonicalC3ChartFactorHeight_analyticAt_zero.deriv.neg).congr
    (Filter.Eventually.of_forall fun z =>
      (canonicalC3ChartFactorHeightCompanion_eq_neg_deriv z).symm)

private theorem nativeXiCompletionBoundaryCompanion_analyticAt_zero :
    AnalyticAt ℂ nativeXiCompletionBoundaryCompanion 0 := by
  change AnalyticAt ℂ (fun z => -deriv nativeXiCompletionFactor z) 0
  exact nativeXiCompletionFactor_analyticAt_zero.deriv.neg

private theorem nativeHeightScalarBoundaryCompanion_analyticAt_zero :
    AnalyticAt ℂ nativeHeightScalarBoundaryCompanion 0 := by
  change AnalyticAt ℂ (fun z => -deriv nativeHeightScalar z) 0
  exact nativeHeightScalar_analyticAt_zero.deriv.neg

private theorem canonicalCompletedC3RawAnalyticValue_analyticAt_zero :
    AnalyticAt ℂ canonicalCompletedC3RawAnalyticValue 0 := by
  exact canonicalC3ChartFactorHeight_analyticAt_zero.mul
    nativeHeightScalar_analyticAt_zero

private theorem canonicalCompletedC3RawAnalyticCompanion_analyticAt_zero :
    AnalyticAt ℂ canonicalCompletedC3RawAnalyticCompanion 0 := by
  unfold canonicalCompletedC3RawAnalyticCompanion productBoundaryCompanion
  exact
    (canonicalC3ChartFactorHeightCompanion_analyticAt_zero.mul
      nativeHeightScalar_analyticAt_zero).add
        (canonicalC3ChartFactorHeight_analyticAt_zero.mul
          nativeHeightScalarBoundaryCompanion_analyticAt_zero)

private theorem canonicalCompletedC3FullWronskianAnalyticState_differentiableAt_zero :
    DifferentiableAt ℂ canonicalCompletedC3FullWronskianAnalyticState 0 := by
  have hA := nativeXiCompletionFactor_analyticAt_zero.differentiableAt
  have hA' := nativeXiCompletionBoundaryCompanion_analyticAt_zero.differentiableAt
  have hG := nativeHeightScalar_analyticAt_zero.differentiableAt
  have hG' := nativeHeightScalarBoundaryCompanion_analyticAt_zero.differentiableAt
  have hC := canonicalC3ChartFactorHeight_analyticAt_zero.differentiableAt
  have hC' := canonicalC3ChartFactorHeightCompanion_analyticAt_zero.differentiableAt
  have hRaw := canonicalCompletedC3RawAnalyticValue_analyticAt_zero.differentiableAt
  have hRaw' :=
    canonicalCompletedC3RawAnalyticCompanion_analyticAt_zero.differentiableAt
  have hRawTrace : DifferentiableAt ℂ
      (fun z => completedScalarBoundaryTraceState
        canonicalCompletedC3RawAnalyticValue
        canonicalCompletedC3RawAnalyticCompanion z) 0 := by
    unfold completedScalarBoundaryTraceState
    exact
      (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).symm.toContinuousLinearMap
        |>.differentiableAt.comp 0 (hRaw'.prodMk hRaw)
  have hNativeTrace : DifferentiableAt ℂ
      (fun z => completedScalarBoundaryTraceState
        nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion z) 0 := by
    unfold completedScalarBoundaryTraceState
    exact
      (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).symm.toContinuousLinearMap
        |>.differentiableAt.comp 0 (hA'.prodMk hA)
  have hChartTrace : DifferentiableAt ℂ
      (fun z => completedScalarBoundaryTraceState
        canonicalC3ChartFactorHeight canonicalC3ChartFactorHeightCompanion z) 0 := by
    unfold completedScalarBoundaryTraceState
    exact
      (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).symm.toContinuousLinearMap
        |>.differentiableAt.comp 0 (hC'.prodMk hC)
  have hRawBlock := hA.smul hRawTrace
  have hNativeBlock := (hG.mul hC).smul hNativeTrace
  have hChartBlock := (hG.mul hA).smul hChartTrace
  have hArch : DifferentiableAt ℂ
      (fun z => WithLp.toLp 2
        ((nativeHeightScalar z * canonicalC3ChartFactorHeight z) •
            completedScalarBoundaryTraceState
              nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion z,
          (nativeHeightScalar z * nativeXiCompletionFactor z) •
            completedScalarBoundaryTraceState
              canonicalC3ChartFactorHeight canonicalC3ChartFactorHeightCompanion z)) 0 := by
    exact
      (WithLp.prodContinuousLinearEquiv 2 ℂ
          CompletedScalarBoundaryTraceCarrier
          CompletedScalarBoundaryTraceCarrier).symm.toContinuousLinearMap
        |>.differentiableAt.comp 0 (hNativeBlock.prodMk hChartBlock)
  unfold canonicalCompletedC3FullWronskianAnalyticState
  dsimp only
  exact
    (WithLp.prodContinuousLinearEquiv 2 ℂ
        CompletedScalarBoundaryTraceCarrier
        CanonicalCompletedC3ArchimedeanChartOperatorCarrier).symm.toContinuousLinearMap
      |>.differentiableAt.comp 0 (hRawBlock.prodMk hArch)

/-! ## The real source tangent and the fixed crossing functional -/

/-- The old full state, restricted to the real collision line, is
differentiable at the center. -/
theorem canonicalCompletedC3FullWronskianOperatorRealSource_differentiableAt_zero
    (M : ℕ) :
    DifferentiableAt ℝ
      (fun t : ℝ =>
        canonicalCompletedC3FullWronskianOperatorState M (t : ℂ)) 0 := by
  rw [show (fun t : ℝ =>
      canonicalCompletedC3FullWronskianOperatorState M (t : ℂ)) =
      fun t : ℝ => canonicalCompletedC3FullWronskianAnalyticState (t : ℂ) by
    funext t
    exact canonicalCompletedC3FullWronskianOperatorState_eq_analyticState M
      (ofReal_mem_completedNativeHeightDomain t)]
  have hA : DifferentiableAt ℝ
      (fun t : ℝ => nativeXiCompletionFactor (t : ℂ)) 0 :=
    nativeXiCompletionFactor_analyticAt_zero.differentiableAt.hasDerivAt
      |>.comp_ofReal.differentiableAt
  have hA' : DifferentiableAt ℝ
      (fun t : ℝ => nativeXiCompletionBoundaryCompanion (t : ℂ)) 0 :=
    nativeXiCompletionBoundaryCompanion_analyticAt_zero.differentiableAt.hasDerivAt
      |>.comp_ofReal.differentiableAt
  have hG : DifferentiableAt ℝ
      (fun t : ℝ => nativeHeightScalar (t : ℂ)) 0 :=
    nativeHeightScalar_analyticAt_zero.differentiableAt.hasDerivAt
      |>.comp_ofReal.differentiableAt
  have hG' : DifferentiableAt ℝ
      (fun t : ℝ => nativeHeightScalarBoundaryCompanion (t : ℂ)) 0 :=
    nativeHeightScalarBoundaryCompanion_analyticAt_zero.differentiableAt.hasDerivAt
      |>.comp_ofReal.differentiableAt
  have hC : DifferentiableAt ℝ
      (fun t : ℝ => canonicalC3ChartFactorHeight (t : ℂ)) 0 :=
    canonicalC3ChartFactorHeight_analyticAt_zero.differentiableAt.hasDerivAt
      |>.comp_ofReal.differentiableAt
  have hC' : DifferentiableAt ℝ
      (fun t : ℝ => canonicalC3ChartFactorHeightCompanion (t : ℂ)) 0 :=
    canonicalC3ChartFactorHeightCompanion_analyticAt_zero.differentiableAt.hasDerivAt
      |>.comp_ofReal.differentiableAt
  have hRaw : DifferentiableAt ℝ
      (fun t : ℝ => canonicalCompletedC3RawAnalyticValue (t : ℂ)) 0 :=
    canonicalCompletedC3RawAnalyticValue_analyticAt_zero.differentiableAt.hasDerivAt
      |>.comp_ofReal.differentiableAt
  have hRaw' : DifferentiableAt ℝ
      (fun t : ℝ => canonicalCompletedC3RawAnalyticCompanion (t : ℂ)) 0 :=
    canonicalCompletedC3RawAnalyticCompanion_analyticAt_zero.differentiableAt.hasDerivAt
      |>.comp_ofReal.differentiableAt
  have hRawTrace : DifferentiableAt ℝ
      (fun t : ℝ => completedScalarBoundaryTraceState
        canonicalCompletedC3RawAnalyticValue
        canonicalCompletedC3RawAnalyticCompanion (t : ℂ)) 0 := by
    unfold completedScalarBoundaryTraceState
    exact
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm.toContinuousLinearMap
        |>.differentiableAt.comp 0 (hRaw'.prodMk hRaw)
  have hNativeTrace : DifferentiableAt ℝ
      (fun t : ℝ => completedScalarBoundaryTraceState
        nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion (t : ℂ)) 0 := by
    unfold completedScalarBoundaryTraceState
    exact
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm.toContinuousLinearMap
        |>.differentiableAt.comp 0 (hA'.prodMk hA)
  have hChartTrace : DifferentiableAt ℝ
      (fun t : ℝ => completedScalarBoundaryTraceState
        canonicalC3ChartFactorHeight canonicalC3ChartFactorHeightCompanion
          (t : ℂ)) 0 := by
    unfold completedScalarBoundaryTraceState
    exact
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm.toContinuousLinearMap
        |>.differentiableAt.comp 0 (hC'.prodMk hC)
  have hRawBlock := hA.smul hRawTrace
  have hNativeBlock := (hG.mul hC).smul hNativeTrace
  have hChartBlock := (hG.mul hA).smul hChartTrace
  have hArch : DifferentiableAt ℝ
      (fun t : ℝ => WithLp.toLp 2
        ((nativeHeightScalar (t : ℂ) * canonicalC3ChartFactorHeight (t : ℂ)) •
            completedScalarBoundaryTraceState
              nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion (t : ℂ),
          (nativeHeightScalar (t : ℂ) * nativeXiCompletionFactor (t : ℂ)) •
            completedScalarBoundaryTraceState
              canonicalC3ChartFactorHeight canonicalC3ChartFactorHeightCompanion
                (t : ℂ))) 0 := by
    exact
      (WithLp.prodContinuousLinearEquiv 2 ℝ
          CompletedScalarBoundaryTraceCarrier
          CompletedScalarBoundaryTraceCarrier).symm.toContinuousLinearMap
        |>.differentiableAt.comp 0 (hNativeBlock.prodMk hChartBlock)
  unfold canonicalCompletedC3FullWronskianAnalyticState
  dsimp only
  exact
    (WithLp.prodContinuousLinearEquiv 2 ℝ
        CompletedScalarBoundaryTraceCarrier
        CanonicalCompletedC3ArchimedeanChartOperatorCarrier).symm.toContinuousLinearMap
      |>.differentiableAt.comp 0 (hRawBlock.prodMk hArch)

/-- The actual real tangent of the already existing source curve.  This is a
derivative in the underlying real Banach space, so no complex-linearity of
the enriched source construction is asserted. -/
def canonicalCompletedC3FullWronskianOperatorRealSourceTangent
    (M : ℕ) : CanonicalCompletedC3FullWronskianOperatorCarrier :=
  deriv
    (fun t : ℝ =>
      canonicalCompletedC3FullWronskianOperatorState M (t : ℂ)) 0

/-- The raw component of the real source tangent. -/
def canonicalCompletedC3FullWronskianOperatorRawSourceTangent
    (M : ℕ) : CompletedScalarBoundaryTraceCarrier :=
  (canonicalCompletedC3FullWronskianOperatorRealSourceTangent M).fst

/-- The archimedean/chart component of the real source tangent. -/
def canonicalCompletedC3FullWronskianOperatorArchimedeanSourceTangent
    (M : ℕ) : CanonicalCompletedC3ArchimedeanChartOperatorCarrier :=
  (canonicalCompletedC3FullWronskianOperatorRealSourceTangent M).snd

/-- Fixing the response at the center turns the full symplectic pairing into
one continuous complex-linear functional of the source leg. -/
def canonicalCompletedC3FullOperatorCentralCrossingFunctional
    (M : ℕ) :
    CanonicalCompletedC3FullWronskianOperatorCarrier →L[ℂ] ℂ :=
  (innerSL ℂ (canonicalCompletedC3FullWronskianOperatorState M 0)).comp
    canonicalCompletedC3FullWronskianOperator

@[simp] theorem canonicalCompletedC3FullOperatorCentralCrossingFunctional_apply
    (M : ℕ) (v : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    canonicalCompletedC3FullOperatorCentralCrossingFunctional M v =
      inner ℂ
        (canonicalCompletedC3FullWronskianOperatorState M 0)
        (canonicalCompletedC3FullWronskianOperator v) := by
  rfl

theorem canonicalCompletedC3FullOperatorRealCollisionNumerator_eq_functional
    (M : ℕ) (t : ℝ) :
    canonicalCompletedC3FullOperatorRealCollisionNumerator M t =
      canonicalCompletedC3FullOperatorCentralCrossingFunctional M
        (canonicalCompletedC3FullWronskianOperatorState M (t : ℂ)) := by
  rfl

/-- Differentiating the numerator differentiates only its source leg: the
central response and the full symplectic operator stay fixed. -/
theorem deriv_canonicalCompletedC3FullOperatorRealCollisionNumerator_zero
    (M : ℕ) :
    deriv (canonicalCompletedC3FullOperatorRealCollisionNumerator M) 0 =
      canonicalCompletedC3FullOperatorCentralCrossingFunctional M
        (canonicalCompletedC3FullWronskianOperatorRealSourceTangent M) := by
  let source : ℝ → CanonicalCompletedC3FullWronskianOperatorCarrier :=
    fun t => canonicalCompletedC3FullWronskianOperatorState M (t : ℂ)
  let crossing :
      CanonicalCompletedC3FullWronskianOperatorCarrier →L[ℝ] ℂ :=
    (canonicalCompletedC3FullOperatorCentralCrossingFunctional M).restrictScalars ℝ
  have hsource : DifferentiableAt ℝ source 0 := by
    exact canonicalCompletedC3FullWronskianOperatorRealSource_differentiableAt_zero M
  have hconstant : DifferentiableAt ℝ (fun _ : ℝ => crossing) 0 :=
    differentiableAt_const crossing
  have hderiv := deriv_clm_apply hconstant hsource
  rw [show canonicalCompletedC3FullOperatorRealCollisionNumerator M =
      fun t => crossing (source t) by
    funext t
    rfl]
  change deriv (fun t => crossing (source t)) 0 = crossing (deriv source 0)
  simpa only [deriv_const, zero_apply, zero_add] using hderiv

/-- The tangent crossing is exactly the sum of the raw trace rotation and
the archimedean/chart rotation.  Both summands use blocks which already
belonged to the full carrier. -/
theorem canonicalCompletedC3FullOperatorCentralCrossingFunctional_tangent_eq_blocks
    (M : ℕ) :
    canonicalCompletedC3FullOperatorCentralCrossingFunctional M
        (canonicalCompletedC3FullWronskianOperatorRealSourceTangent M) =
      inner ℂ
          (canonicalCompletedC3RawWronskianOperatorState M 0)
          (completedScalarBoundarySymplecticRotation
            (canonicalCompletedC3FullWronskianOperatorRawSourceTangent M)) +
        inner ℂ
          (canonicalCompletedC3ArchimedeanChartOperatorState 0)
          (canonicalCompletedC3ArchimedeanChartOperator
            (canonicalCompletedC3FullWronskianOperatorArchimedeanSourceTangent M)) := by
  rw [canonicalCompletedC3FullOperatorCentralCrossingFunctional_apply,
    canonicalCompletedC3FullWronskianOperator_apply,
    WithLp.prod_inner_apply]
  rfl

/-! ## Removing the normalization at a zero numerator -/

theorem canonicalCompletedC3FullOperatorRealCollisionNumerator_differentiableAt_zero
    (M : ℕ) :
    DifferentiableAt ℝ
      (canonicalCompletedC3FullOperatorRealCollisionNumerator M) 0 := by
  rw [show canonicalCompletedC3FullOperatorRealCollisionNumerator M =
      fun t : ℝ =>
        ((canonicalCompletedC3FullOperatorCentralCrossingFunctional M).restrictScalars ℝ)
          (canonicalCompletedC3FullWronskianOperatorState M (t : ℂ)) by
    funext t
    rfl]
  exact
    ((canonicalCompletedC3FullOperatorCentralCrossingFunctional M).restrictScalars ℝ)
      |>.differentiableAt.comp 0
        (canonicalCompletedC3FullWronskianOperatorRealSource_differentiableAt_zero M)

theorem canonicalCompletedC3FullOperatorRealCollisionNormalization_zero_ne_zero :
    canonicalCompletedC3FullOperatorRealCollisionNormalization 0 ≠ 0 := by
  unfold canonicalCompletedC3FullOperatorRealCollisionNormalization
    canonicalCompletedC3FixedCenterLedgerNormalization
  apply mul_ne_zero
  · exact mixedHermitianWeight_canonicalC3ChartFactorHeight_ne_zero
      zero_mem_completedNativeHeightDomain zero_mem_completedNativeHeightDomain
  · apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · simpa using completedNativeOperatorCharacteristic_zero_ne_zero
    · exact completedNativeOperatorCharacteristic_zero_ne_zero

theorem canonicalCompletedC3FullOperatorRealCollisionNormalization_differentiableAt_zero :
    DifferentiableAt ℝ
      canonicalCompletedC3FullOperatorRealCollisionNormalization 0 := by
  have hchart : DifferentiableAt ℝ
      (fun t : ℝ => canonicalC3ChartFactorHeight (t : ℂ)) 0 :=
    canonicalC3ChartFactorHeight_analyticAt_zero.differentiableAt.hasDerivAt
      |>.comp_ofReal.differentiableAt
  have hcharacteristic : DifferentiableAt ℝ
      (fun t : ℝ => completedNativeOperatorCharacteristic (t : ℂ)) 0 :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.hasDerivAt
      |>.comp_ofReal.differentiableAt
  unfold canonicalCompletedC3FullOperatorRealCollisionNormalization
    canonicalCompletedC3FixedCenterLedgerNormalization mixedHermitianWeight
  fun_prop

/-- Because the unnormalized crossing vanishes at collision, differentiating
the normalized branch introduces only the central value of the denominator;
the derivative of the denominator drops out. -/
theorem deriv_canonicalCompletedC3FullOperatorRealCollisionQuotient_zero
    (M : ℕ) :
    deriv (canonicalCompletedC3FullOperatorRealCollisionQuotient M) 0 =
      deriv (canonicalCompletedC3FullOperatorRealCollisionNumerator M) 0 /
        canonicalCompletedC3FullOperatorRealCollisionNormalization 0 := by
  unfold canonicalCompletedC3FullOperatorRealCollisionQuotient
  change deriv
      (canonicalCompletedC3FullOperatorRealCollisionNumerator M /
        canonicalCompletedC3FullOperatorRealCollisionNormalization) 0 = _
  rw [deriv_div
    (canonicalCompletedC3FullOperatorRealCollisionNumerator_differentiableAt_zero M)
    canonicalCompletedC3FullOperatorRealCollisionNormalization_differentiableAt_zero
    canonicalCompletedC3FullOperatorRealCollisionNormalization_zero_ne_zero,
    canonicalCompletedC3FullOperatorRealCollisionNumerator_zero]
  field_simp [canonicalCompletedC3FullOperatorRealCollisionNormalization_zero_ne_zero]
  ring

/-! ## Structural form of the first completed collision variation -/

/-- The old theorem `B_total'(0) = h₀`, with the quotient rule removed, says
precisely that `h₀` is the normalized value of the fixed crossing functional
on the real source tangent. -/
theorem canonicalCompletedNativeLogDerivativeMoment_zero_eq_normalized_symplectic_crossing
    (M : ℕ) :
    (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) =
      canonicalCompletedC3FullOperatorCentralCrossingFunctional M
          (canonicalCompletedC3FullWronskianOperatorRealSourceTangent M) /
        canonicalCompletedC3FullOperatorRealCollisionNormalization 0 := by
  calc
    (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) =
        deriv (canonicalCompletedC3FullOperatorFixedCenterRealBranch M) 0 :=
      (deriv_canonicalCompletedC3FullOperatorFixedCenterRealBranch_zero M).symm
    _ = deriv (canonicalCompletedC3FullOperatorRealCollisionQuotient M) 0 := by
      congr 1
      funext t
      exact (canonicalCompletedC3FullOperatorRealCollisionQuotient_eq_existing M t).symm
    _ = deriv (canonicalCompletedC3FullOperatorRealCollisionNumerator M) 0 /
          canonicalCompletedC3FullOperatorRealCollisionNormalization 0 :=
      deriv_canonicalCompletedC3FullOperatorRealCollisionQuotient_zero M
    _ = canonicalCompletedC3FullOperatorCentralCrossingFunctional M
          (canonicalCompletedC3FullWronskianOperatorRealSourceTangent M) /
          canonicalCompletedC3FullOperatorRealCollisionNormalization 0 := by
      rw [deriv_canonicalCompletedC3FullOperatorRealCollisionNumerator_zero]

/-- Fully block-visible spelling of the same statement.  It is a normalized
symplectic crossing, not a Gram or a norm identity. -/
theorem canonicalCompletedNativeLogDerivativeMoment_zero_eq_normalized_raw_add_archimedean_crossing
    (M : ℕ) :
    (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) =
      (inner ℂ
          (canonicalCompletedC3RawWronskianOperatorState M 0)
          (completedScalarBoundarySymplecticRotation
            (canonicalCompletedC3FullWronskianOperatorRawSourceTangent M)) +
        inner ℂ
          (canonicalCompletedC3ArchimedeanChartOperatorState 0)
          (canonicalCompletedC3ArchimedeanChartOperator
            (canonicalCompletedC3FullWronskianOperatorArchimedeanSourceTangent M))) /
        canonicalCompletedC3FullOperatorRealCollisionNormalization 0 := by
  rw [canonicalCompletedNativeLogDerivativeMoment_zero_eq_normalized_symplectic_crossing,
    canonicalCompletedC3FullOperatorCentralCrossingFunctional_tangent_eq_blocks]

/-! ## What Lean actually supplies -/

/-- Additivity in the tangent is inherited from the fixed continuous linear
functional. -/
theorem canonicalCompletedC3FullOperatorCentralCrossingFunctional_add
    (M : ℕ) (u v : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    canonicalCompletedC3FullOperatorCentralCrossingFunctional M (u + v) =
      canonicalCompletedC3FullOperatorCentralCrossingFunctional M u +
        canonicalCompletedC3FullOperatorCentralCrossingFunctional M v := by
  exact map_add _ _ _

/-- The fixed-response crossing is complex-linear in its source/tangent leg.
After restricting the actual curve to `ℝ`, the result is therefore a real
linear functional evaluated on one distinguished real tangent. -/
theorem canonicalCompletedC3FullOperatorCentralCrossingFunctional_smul
    (M : ℕ) (a : ℂ)
    (v : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    canonicalCompletedC3FullOperatorCentralCrossingFunctional M (a • v) =
      a • canonicalCompletedC3FullOperatorCentralCrossingFunctional M v := by
  exact map_smul _ _ _

/-- Exact kernel test for the one tangent which is canonically present in
this audit.  It does not import a positivity theorem for `h₀`: the real
source tangent is killed by the crossing functional exactly if `h₀` itself
vanishes. -/
theorem canonicalCompletedC3FullOperatorRealSourceTangent_mem_crossingKernel_iff
    (M : ℕ) :
    canonicalCompletedC3FullWronskianOperatorRealSourceTangent M ∈
        (canonicalCompletedC3FullOperatorCentralCrossingFunctional M).ker ↔
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) = 0 := by
  rw [LinearMap.mem_ker]
  rw [canonicalCompletedNativeLogDerivativeMoment_zero_eq_normalized_symplectic_crossing
    M]
  simp [canonicalCompletedC3FullOperatorRealCollisionNormalization_zero_ne_zero]

end

end CarrySelfAdjointOperator
