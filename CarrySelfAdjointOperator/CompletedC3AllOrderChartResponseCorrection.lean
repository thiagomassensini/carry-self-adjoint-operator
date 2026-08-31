import CarrySelfAdjointOperator.CompletedC3ChiralCrossedChartBridge
import CarrySelfAdjointOperator.CompletedNativeProductMomentCenter
import Mathlib.Tactic

/-!
# All-order replacement of the C3 chart by the xi completion factor

The raw completed C3 trace is the product of the C3 chart factor and the
centered native scalar.  The completed-native characteristic replaces that
chart factor by the xi completion factor while retaining the same native
scalar.  This module performs that replacement at the normalized-response
level and then extracts the identity at every Taylor order.

The resulting correction is exactly `xi response - chart response`; it is
not discarded, fitted, or assumed positive.
-/

open scoped ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section

/-- Half logarithmic response of the C3 chart factor in centered-height
coordinates. -/
def canonicalC3ChartFactorNormalizedResponse (z : ℂ) : ℂ :=
  completedGreenNormalizedResponse
    canonicalC3ChartFactorHeight canonicalC3ChartFactorHeightCompanion z

/-- Half logarithmic response of the tail-completed raw C3 height trace. -/
def canonicalCompletedC3RawHeightNormalizedResponse (z : ℂ) : ℂ :=
  completedGreenNormalizedResponse
    canonicalCompletedC3RawHeightValue
    canonicalCompletedC3RawHeightCompanion z

/-- The chart companion is literally minus the centered-height derivative
of the chart value. -/
theorem canonicalC3ChartFactorHeightCompanion_eq_neg_deriv (z : ℂ) :
    canonicalC3ChartFactorHeightCompanion z =
      -deriv canonicalC3ChartFactorHeight z := by
  have hcp : HasDerivAt (cpChartFactor 3)
      (deriv (cpChartFactor 3) (operatorHeightParameter z))
      (operatorHeightParameter z) :=
    (differentiable_cpChartFactor 3 (by norm_num)).differentiableAt.hasDerivAt
  have hcomp := hcp.comp z (hasDerivAt_operatorHeightParameter z)
  have hderiv :
      deriv canonicalC3ChartFactorHeight z =
        deriv (cpChartFactor 3) (operatorHeightParameter z) * Complex.I := by
    exact hcomp.deriv
  rw [hderiv]
  unfold canonicalC3ChartFactorHeightCompanion
  ring

/-- The centered chart factor is analytic at the Taylor center. -/
theorem canonicalC3ChartFactorHeight_analyticAt_zero :
    AnalyticAt ℂ canonicalC3ChartFactorHeight 0 := by
  have hparameter : AnalyticAt ℂ operatorHeightParameter 0 := by
    unfold operatorHeightParameter
    fun_prop
  exact
    ((differentiable_cpChartFactor 3 (by norm_num)).analyticAt
      (operatorHeightParameter 0)).comp hparameter

/-- The normalized chart response is analytic at the Taylor center. -/
theorem canonicalC3ChartFactorNormalizedResponse_analyticAt_zero :
    AnalyticAt ℂ canonicalC3ChartFactorNormalizedResponse 0 := by
  have hchart := canonicalC3ChartFactorHeight_analyticAt_zero
  have hchartNe : canonicalC3ChartFactorHeight 0 ≠ 0 :=
    canonicalC3ChartFactorHeight_ne_zero zero_mem_completedNativeHeightDomain
  have hcompanion :
      canonicalC3ChartFactorHeightCompanion =
        fun z : ℂ => -deriv canonicalC3ChartFactorHeight z := by
    funext z
    exact canonicalC3ChartFactorHeightCompanion_eq_neg_deriv z
  unfold canonicalC3ChartFactorNormalizedResponse
    completedGreenNormalizedResponse
  rw [hcompanion]
  exact hchart.deriv.neg.div (analyticAt_const.mul hchart)
    (mul_ne_zero (by norm_num) hchartNe)

/-- The normalized native-factor response is analytic at the Taylor center. -/
theorem nativeHeightScalarNormalizedResponse_analyticAt_zero :
    AnalyticAt ℂ nativeHeightScalarNormalizedResponse 0 := by
  unfold nativeHeightScalarNormalizedResponse completedGreenNormalizedResponse
    nativeHeightScalarBoundaryCompanion
  exact nativeHeightScalar_analyticAt_zero.deriv.neg.div
    (analyticAt_const.mul nativeHeightScalar_analyticAt_zero)
    (mul_ne_zero (by norm_num) nativeHeightScalar_zero_ne_zero)

/-- The normalized xi-factor response is analytic at the Taylor center. -/
theorem nativeXiCompletionNormalizedResponse_analyticAt_zero :
    AnalyticAt ℂ nativeXiCompletionNormalizedResponse 0 := by
  unfold nativeXiCompletionNormalizedResponse completedGreenNormalizedResponse
    nativeXiCompletionBoundaryCompanion
  exact nativeXiCompletionFactor_analyticAt_zero.deriv.neg.div
    (analyticAt_const.mul nativeXiCompletionFactor_analyticAt_zero)
    (mul_ne_zero (by norm_num)
      (nativeXiCompletionFactor_ne_zero
        zero_mem_completedNativeHeightDomain))

/-- The normalized TFVD log jet is the canonical companion of the same
centered native scalar.  The equality is obtained as an equality of germs on
the open strip, so no quotient is differentiated at a zero. -/
theorem
    canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout_eq_nativeCompanion
    {z : ℂ} (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout z =
      nativeHeightScalarBoundaryCompanion z := by
  have hstripNhd :
      {w : ℂ | operatorHeightParameter w ∈ genuineCriticalStrip} ∈ nhds z :=
    (hasDerivAt_operatorHeightParameter z).continuousAt.preimage_mem_nhds
      (isOpen_genuineCriticalStrip.mem_nhds hz)
  have heventual :
      canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout =ᶠ[nhds z]
        nativeHeightScalar := by
    filter_upwards [hstripNhd] with w hw
    exact
      canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar
        hw
  rw [canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout_eq_neg_deriv
    hz, heventual.deriv_eq]
  rfl

/-- Pointwise factor response for the raw C3 trace.  The raw trace carries
the same native scalar as the completed characteristic, but with the C3 chart
factor in place of the xi factor. -/
theorem canonicalCompletedC3RawHeightNormalizedResponse_eq_factorResponses
    {z : ℂ} (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hNative : nativeHeightScalar z ≠ 0) :
    canonicalCompletedC3RawHeightNormalizedResponse z =
      canonicalC3ChartFactorNormalizedResponse z +
        nativeHeightScalarNormalizedResponse z := by
  have hchart : canonicalC3ChartFactorHeight z ≠ 0 :=
    canonicalC3ChartFactorHeight_ne_zero hz
  unfold canonicalCompletedC3RawHeightNormalizedResponse
    canonicalC3ChartFactorNormalizedResponse
    nativeHeightScalarNormalizedResponse
    completedGreenNormalizedResponse
  rw [canonicalCompletedC3RawHeightValue_eq_chart_mul_normalized hz,
    canonicalCompletedC3RawHeightCompanion_eq_chartProductCompanion hz]
  unfold productBoundaryCompanion
  rw [
    canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar
      hz,
    canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout_eq_nativeCompanion
      hz]
  field_simp [hchart, hNative]

/-- Near the Taylor center, the raw normalized response is exactly the sum
of the chart response and the native-factor response. -/
theorem canonicalCompletedC3RawHeightNormalizedResponse_eventuallyEq_factors :
    canonicalCompletedC3RawHeightNormalizedResponse =ᶠ[nhds 0]
      canonicalC3ChartFactorNormalizedResponse +
        nativeHeightScalarNormalizedResponse := by
  have hdomain :
      {z : ℂ | operatorHeightParameter z ∈ genuineCriticalStrip} ∈ nhds 0 :=
    (hasDerivAt_operatorHeightParameter 0).continuousAt.preimage_mem_nhds
      (isOpen_genuineCriticalStrip.mem_nhds
        zero_mem_completedNativeHeightDomain)
  have hNative :=
    nativeHeightScalar_analyticAt_zero.continuousAt.eventually_ne
      nativeHeightScalar_zero_ne_zero
  filter_upwards [hdomain, hNative] with z hz hne
  exact
    canonicalCompletedC3RawHeightNormalizedResponse_eq_factorResponses hz hne

/-- Analytic response channel that records exactly the replacement of the C3
chart factor by the xi completion factor. -/
def canonicalCompletedC3ChartReplacementNormalizedResponse (z : ℂ) : ℂ :=
  nativeXiCompletionNormalizedResponse z -
    canonicalC3ChartFactorNormalizedResponse z

/-- The completed response is, as a germ at the center, the raw C3 response
plus the canonical xi-minus-chart replacement response. -/
theorem
    completedNativeGreenNormalizedResponse_eventuallyEq_raw_add_chartReplacement :
    completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion =ᶠ[nhds 0]
      canonicalCompletedC3RawHeightNormalizedResponse +
        canonicalCompletedC3ChartReplacementNormalizedResponse := by
  filter_upwards
    [completedNativeGreenNormalizedResponse_eventuallyEq_factorResponses,
      canonicalCompletedC3RawHeightNormalizedResponse_eventuallyEq_factors]
      with z hcompleted hraw
  change
    completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z =
      canonicalCompletedC3RawHeightNormalizedResponse z +
        (nativeXiCompletionNormalizedResponse z -
          canonicalC3ChartFactorNormalizedResponse z)
  simp only [Pi.add_apply] at hcompleted hraw
  rw [hcompleted, hraw]
  ring

/-- Taylor coefficient of the raw C3 normalized response. -/
def canonicalCompletedC3RawHeightResponseTaylorCoefficient
    (order : ℕ) : ℂ :=
  iteratedDeriv order canonicalCompletedC3RawHeightNormalizedResponse 0 /
    order.factorial

/-- Taylor coefficient of the normalized C3 chart response. -/
def canonicalC3ChartFactorResponseTaylorCoefficient (order : ℕ) : ℂ :=
  iteratedDeriv order canonicalC3ChartFactorNormalizedResponse 0 /
    order.factorial

/-- Every raw C3 response coefficient splits into its chart and native
factor coefficients. -/
theorem canonicalCompletedC3RawHeightResponseTaylorCoefficient_eq_factors
    (order : ℕ) :
    canonicalCompletedC3RawHeightResponseTaylorCoefficient order =
      canonicalC3ChartFactorResponseTaylorCoefficient order +
        nativeHeightScalarResponseTaylorCoefficient order := by
  unfold canonicalCompletedC3RawHeightResponseTaylorCoefficient
    canonicalC3ChartFactorResponseTaylorCoefficient
    nativeHeightScalarResponseTaylorCoefficient
  rw [Filter.EventuallyEq.iteratedDeriv_eq order
    canonicalCompletedC3RawHeightNormalizedResponse_eventuallyEq_factors]
  rw [iteratedDeriv_add
    canonicalC3ChartFactorNormalizedResponse_analyticAt_zero.contDiffAt
    nativeHeightScalarNormalizedResponse_analyticAt_zero.contDiffAt]
  ring

/-- All-order response correction caused by replacing the C3 chart factor
with the xi completion factor. -/
def canonicalCompletedC3ChartReplacementResponseTaylorCoefficient
    (order : ℕ) : ℂ :=
  nativeXiCompletionResponseTaylorCoefficient order -
    canonicalC3ChartFactorResponseTaylorCoefficient order

/-- The coefficient-level replacement is the actual Taylor coefficient of
the canonical xi-minus-chart response. -/
theorem canonicalCompletedC3ChartReplacementResponseTaylorCoefficient_eq_taylor
    (order : ℕ) :
    canonicalCompletedC3ChartReplacementResponseTaylorCoefficient order =
      iteratedDeriv order
          canonicalCompletedC3ChartReplacementNormalizedResponse 0 /
        order.factorial := by
  unfold canonicalCompletedC3ChartReplacementResponseTaylorCoefficient
    nativeXiCompletionResponseTaylorCoefficient
    canonicalC3ChartFactorResponseTaylorCoefficient
    canonicalCompletedC3ChartReplacementNormalizedResponse
  change
    iteratedDeriv order nativeXiCompletionNormalizedResponse 0 /
          order.factorial -
        iteratedDeriv order canonicalC3ChartFactorNormalizedResponse 0 /
          order.factorial =
      iteratedDeriv order
          (nativeXiCompletionNormalizedResponse -
            canonicalC3ChartFactorNormalizedResponse) 0 /
        order.factorial
  rw [iteratedDeriv_sub
    nativeXiCompletionNormalizedResponse_analyticAt_zero.contDiffAt
    canonicalC3ChartFactorNormalizedResponse_analyticAt_zero.contDiffAt]
  ring

/-- At every Taylor order, the completed response is the raw C3 response plus
the exact xi-minus-chart correction. -/
theorem completedNativeGreenResponseTaylorCoefficient_eq_raw_add_chartReplacement
    (order : ℕ) :
    completedNativeGreenResponseTaylorCoefficient order =
      canonicalCompletedC3RawHeightResponseTaylorCoefficient order +
        canonicalCompletedC3ChartReplacementResponseTaylorCoefficient order := by
  rw [completedNativeGreenResponseTaylorCoefficient_eq_factorCoefficients,
    canonicalCompletedC3RawHeightResponseTaylorCoefficient_eq_factors]
  unfold canonicalCompletedC3ChartReplacementResponseTaylorCoefficient
  ring

/-- Consequently every canonical logarithmic moment has the same exact
all-order decomposition. -/
theorem canonicalCompletedNativeLogDerivativeMoment_eq_raw_add_chartReplacement
    (n : ℕ) :
    (canonicalCompletedNativeLogDerivativeMoment n : ℂ) =
      canonicalCompletedC3RawHeightResponseTaylorCoefficient (2 * n + 1) +
        canonicalCompletedC3ChartReplacementResponseTaylorCoefficient
          (2 * n + 1) := by
  rw [← completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]
  exact
    completedNativeGreenResponseTaylorCoefficient_eq_raw_add_chartReplacement
      (2 * n + 1)

/-- Zeroth-order center audit of the same all-order identity. -/
theorem canonicalCompletedNativeLogDerivativeMoment_zero_eq_raw_add_chartReplacement :
    (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) =
      canonicalCompletedC3RawHeightResponseTaylorCoefficient 1 +
        canonicalCompletedC3ChartReplacementResponseTaylorCoefficient 1 := by
  simpa using
    canonicalCompletedNativeLogDerivativeMoment_eq_raw_add_chartReplacement 0

end

end CarrySelfAdjointOperator
