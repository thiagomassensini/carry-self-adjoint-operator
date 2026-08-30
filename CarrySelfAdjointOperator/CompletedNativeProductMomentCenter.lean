import CarrySelfAdjointOperator.CompletedNativeEvenCoordinateResolventBridge
import CarrySelfAdjointOperator.CompletedProductJet

open scoped BigOperators

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera
open Filter

noncomputable section

/-!
# Center decomposition of the completed native moment

The completed characteristic is a product of the archimedean completion
factor and the centered native scalar.  Its centered parity forces the first
jets of those factors to cancel.  At second order, however, the product rule
retains their mixed jet.  This file records that coupling directly in the
zeroth logarithmic moment used by the Hankel construction.
-/

/-- The completion factor is analytic at the centered height. -/
theorem nativeXiCompletionFactor_analyticAt_zero :
    AnalyticAt ℂ nativeXiCompletionFactor 0 := by
  have hOn : DifferentiableOn ℂ nativeXiCompletionFactor
      completedNativeHeightDomain := by
    intro z hz
    exact (nativeXiCompletionFactor_differentiableAt hz).differentiableWithinAt
  exact hOn.analyticAt
    (isOpen_completedNativeHeightDomain.mem_nhds
      zero_mem_completedNativeHeightDomain)

/-- The centered native scalar is analytic at the centered height. -/
theorem nativeHeightScalar_analyticAt_zero :
    AnalyticAt ℂ nativeHeightScalar 0 := by
  have hnative : operatorHeightParameter 0 ∈ nativeScalarDomain := by
    exact
      ⟨by norm_num [operatorHeightParameter],
        by norm_num [operatorHeightParameter]⟩
  have hparameter : AnalyticAt ℂ operatorHeightParameter 0 := by
    unfold operatorHeightParameter
    fun_prop
  change AnalyticAt ℂ (fun z => nativeScalar (operatorHeightParameter z)) 0
  exact
    (nativeScalar_differentiableOn.analyticAt
      (isOpen_nativeScalarDomain.mem_nhds hnative)).comp hparameter

/-- Centered evenness forces exact cancellation between the first jets of the
completion factor and the native scalar.  Neither factor is discarded. -/
theorem nativeCompletionFactor_nativeHeightScalar_firstDerivative_cancel :
    deriv nativeXiCompletionFactor 0 * nativeHeightScalar 0 +
        nativeXiCompletionFactor 0 * deriv nativeHeightScalar 0 = 0 := by
  have hstrip : operatorHeightParameter 0 ∈ genuineCriticalStrip :=
    zero_mem_completedNativeHeightDomain
  have hnative : operatorHeightParameter 0 ∈ nativeScalarDomain := by
    exact
      ⟨by norm_num [operatorHeightParameter],
        by norm_num [operatorHeightParameter]⟩
  have hmul :=
    ((nativeXiCompletionFactor_differentiableAt hstrip).hasDerivAt.mul
      (nativeHeightScalar_differentiableAt hnative).hasDerivAt).deriv
  have hzero : deriv completedNativeOperatorCharacteristic 0 = 0 :=
    deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
      completedNativeOperatorCharacteristic_eventually_even
  change deriv completedNativeOperatorCharacteristic 0 = _ at hmul
  rw [hzero] at hmul
  exact hmul.symm

/-- The second centered jet of the completed characteristic contains the
mixed factor jet with its exact Leibniz coefficient `2`. -/
theorem completedNativeOperatorCharacteristic_secondDerivative_product :
    iteratedDeriv 2 completedNativeOperatorCharacteristic 0 =
      iteratedDeriv 2 nativeXiCompletionFactor 0 * nativeHeightScalar 0 +
        2 * deriv nativeXiCompletionFactor 0 * deriv nativeHeightScalar 0 +
        nativeXiCompletionFactor 0 * iteratedDeriv 2 nativeHeightScalar 0 := by
  have hmul := iteratedDeriv_mul (n := 2)
    (nativeXiCompletionFactor_analyticAt_zero.contDiffAt :
      ContDiffAt ℂ 2 nativeXiCompletionFactor 0)
    (nativeHeightScalar_analyticAt_zero.contDiffAt :
      ContDiffAt ℂ 2 nativeHeightScalar 0)
  change iteratedDeriv 2
      (nativeXiCompletionFactor * nativeHeightScalar) 0 = _
  rw [hmul]
  simp [iteratedDeriv_succ, Finset.sum_range_succ]
  ring

/-- The zeroth completed-native logarithmic moment is the full second product
jet.  In particular, its mixed `A' G'` channel is part of the canonical moment
and cannot be omitted from a raw factorwise second-derivative calculation. -/
theorem canonicalCompletedNativeLogDerivativeMoment_zero_eq_productJet :
    (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) =
      -(iteratedDeriv 2 nativeXiCompletionFactor 0 * nativeHeightScalar 0 +
          2 * deriv nativeXiCompletionFactor 0 * deriv nativeHeightScalar 0 +
          nativeXiCompletionFactor 0 * iteratedDeriv 2 nativeHeightScalar 0) /
        (2 * nativeXiCompletionFactor 0 * nativeHeightScalar 0) := by
  have h := congrArg (fun x : ℝ => (x : ℂ))
    (canonicalCompletedNativeLogDerivativeMoment_eq 0)
  push_cast at h
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero] at h
  rw [← completedNativeEvenCharacteristicCoefficient_eq_real 0,
    ← completedNativeEvenCharacteristicCoefficient_eq_real 1] at h
  rw [completedNativeEvenCharacteristicCoefficient_zero] at h
  unfold completedNativeEvenCharacteristicCoefficient completedGreenTaylorJet at h
  norm_num at h
  rw [completedNativeOperatorCharacteristic_secondDerivative_product] at h
  simp only [completedNativeOperatorCharacteristic, nativeHeightScalar] at h
  rw [h]
  simp only [nativeHeightScalar]
  ring

/-- After using the exact first-jet cancellation, the same moment is the sum
of the two normalized logarithmic curvatures.  This is the factorwise form a
positive Green realization must implement; the mixed raw jet has not been
discarded, but absorbed by the two square corrections. -/
theorem canonicalCompletedNativeLogDerivativeMoment_zero_eq_factorLogCurvatures :
    (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) =
      -(1 / 2 : ℂ) *
        ((iteratedDeriv 2 nativeXiCompletionFactor 0 *
                nativeXiCompletionFactor 0 -
              deriv nativeXiCompletionFactor 0 ^ 2) /
            nativeXiCompletionFactor 0 ^ 2 +
          (iteratedDeriv 2 nativeHeightScalar 0 * nativeHeightScalar 0 -
              deriv nativeHeightScalar 0 ^ 2) /
            nativeHeightScalar 0 ^ 2) := by
  have hstrip : operatorHeightParameter 0 ∈ genuineCriticalStrip :=
    zero_mem_completedNativeHeightDomain
  have hA : nativeXiCompletionFactor 0 ≠ 0 :=
    nativeXiCompletionFactor_ne_zero hstrip
  have hG : nativeHeightScalar 0 ≠ 0 :=
    nativeHeightScalar_zero_ne_zero
  rw [canonicalCompletedNativeLogDerivativeMoment_zero_eq_productJet]
  have hcancel :=
    nativeCompletionFactor_nativeHeightScalar_firstDerivative_cancel
  have hsquare :
      deriv nativeXiCompletionFactor 0 ^ 2 * nativeHeightScalar 0 ^ 2 +
          2 * deriv nativeXiCompletionFactor 0 * nativeHeightScalar 0 *
            nativeXiCompletionFactor 0 * deriv nativeHeightScalar 0 +
          nativeXiCompletionFactor 0 ^ 2 * deriv nativeHeightScalar 0 ^ 2 = 0 := by
    calc
      _ = (deriv nativeXiCompletionFactor 0 * nativeHeightScalar 0 +
          nativeXiCompletionFactor 0 * deriv nativeHeightScalar 0) ^ 2 := by
            ring
      _ = 0 := by rw [hcancel]; norm_num
  field_simp [hA, hG]
  apply sub_eq_zero.mp
  calc
    _ = -(deriv nativeXiCompletionFactor 0 ^ 2 * nativeHeightScalar 0 ^ 2 +
          2 * deriv nativeXiCompletionFactor 0 * nativeHeightScalar 0 *
            nativeXiCompletionFactor 0 * deriv nativeHeightScalar 0 +
          nativeXiCompletionFactor 0 ^ 2 * deriv nativeHeightScalar 0 ^ 2) := by
            ring
    _ = 0 := by rw [hsquare]; ring

/-! ## All-order factor response -/

/-- Half logarithmic derivative of the archimedean completion factor. -/
def nativeXiCompletionNormalizedResponse (z : ℂ) : ℂ :=
  completedGreenNormalizedResponse
    nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion z

/-- Half logarithmic derivative of the centered native scalar. -/
def nativeHeightScalarNormalizedResponse (z : ℂ) : ℂ :=
  completedGreenNormalizedResponse
    nativeHeightScalar nativeHeightScalarBoundaryCompanion z

/-- Taylor coefficient of the normalized completion-factor response. -/
def nativeXiCompletionResponseTaylorCoefficient (order : ℕ) : ℂ :=
  iteratedDeriv order nativeXiCompletionNormalizedResponse 0 / order.factorial

/-- Taylor coefficient of the normalized native-scalar response. -/
def nativeHeightScalarResponseTaylorCoefficient (order : ℕ) : ℂ :=
  iteratedDeriv order nativeHeightScalarNormalizedResponse 0 / order.factorial

/-- Wherever both factors are nonzero, the normalized completed response is
the exact sum of their normalized logarithmic responses. -/
theorem completedNativeGreenNormalizedResponse_eq_factorResponses
    {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hA : nativeXiCompletionFactor z ≠ 0)
    (hG : nativeHeightScalar z ≠ 0) :
    completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z =
      nativeXiCompletionNormalizedResponse z +
        nativeHeightScalarNormalizedResponse z := by
  have hnative : operatorHeightParameter z ∈ nativeScalarDomain :=
    ⟨by linarith [hz.1], hz.2⟩
  have hmul :=
    ((nativeXiCompletionFactor_differentiableAt hz).hasDerivAt.mul
      (nativeHeightScalar_differentiableAt hnative).hasDerivAt).deriv
  change deriv completedNativeOperatorCharacteristic z = _ at hmul
  unfold nativeXiCompletionNormalizedResponse
    nativeHeightScalarNormalizedResponse completedGreenNormalizedResponse
    nativeXiCompletionBoundaryCompanion nativeHeightScalarBoundaryCompanion
  rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv, hmul]
  change
    -(deriv nativeXiCompletionFactor z * nativeHeightScalar z +
          nativeXiCompletionFactor z * deriv nativeHeightScalar z) /
        (2 * (nativeXiCompletionFactor z * nativeHeightScalar z)) =
      -deriv nativeXiCompletionFactor z / (2 * nativeXiCompletionFactor z) +
        -deriv nativeHeightScalar z / (2 * nativeHeightScalar z)
  field_simp [hA, hG]
  ring

/-- The factor-response identity holds as an equality of germs at the
centered height. -/
theorem completedNativeGreenNormalizedResponse_eventuallyEq_factorResponses :
    completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion =ᶠ[nhds 0]
      nativeXiCompletionNormalizedResponse +
        nativeHeightScalarNormalizedResponse := by
  have hdomain : completedNativeHeightDomain ∈ nhds (0 : ℂ) :=
    isOpen_completedNativeHeightDomain.mem_nhds
      zero_mem_completedNativeHeightDomain
  have hAne := nativeXiCompletionFactor_analyticAt_zero.continuousAt.eventually_ne
    (nativeXiCompletionFactor_ne_zero zero_mem_completedNativeHeightDomain)
  have hGne := nativeHeightScalar_analyticAt_zero.continuousAt.eventually_ne
    nativeHeightScalar_zero_ne_zero
  filter_upwards [hdomain, hAne, hGne] with z hz hA hG
  exact completedNativeGreenNormalizedResponse_eq_factorResponses hz hA hG

/-- Every Taylor coefficient of the completed response is the sum of the two
factor-response coefficients. -/
theorem completedNativeGreenResponseTaylorCoefficient_eq_factorCoefficients
    (order : ℕ) :
    completedNativeGreenResponseTaylorCoefficient order =
      nativeXiCompletionResponseTaylorCoefficient order +
        nativeHeightScalarResponseTaylorCoefficient order := by
  unfold completedNativeGreenResponseTaylorCoefficient
    nativeXiCompletionResponseTaylorCoefficient
    nativeHeightScalarResponseTaylorCoefficient
  rw [Filter.EventuallyEq.iteratedDeriv_eq order
    completedNativeGreenNormalizedResponse_eventuallyEq_factorResponses]
  have hXi : AnalyticAt ℂ nativeXiCompletionNormalizedResponse 0 := by
    unfold nativeXiCompletionNormalizedResponse completedGreenNormalizedResponse
      nativeXiCompletionBoundaryCompanion
    exact nativeXiCompletionFactor_analyticAt_zero.deriv.neg.div
      (analyticAt_const.mul nativeXiCompletionFactor_analyticAt_zero)
      (mul_ne_zero (by norm_num)
        (nativeXiCompletionFactor_ne_zero zero_mem_completedNativeHeightDomain))
  have hNative : AnalyticAt ℂ nativeHeightScalarNormalizedResponse 0 := by
    unfold nativeHeightScalarNormalizedResponse completedGreenNormalizedResponse
      nativeHeightScalarBoundaryCompanion
    exact nativeHeightScalar_analyticAt_zero.deriv.neg.div
      (analyticAt_const.mul nativeHeightScalar_analyticAt_zero)
      (mul_ne_zero (by norm_num) nativeHeightScalar_zero_ne_zero)
  rw [iteratedDeriv_add hXi.contDiffAt hNative.contDiffAt]
  ring

/-- All canonical completed-native moments split into the odd Taylor
coefficients of the two exact factor responses. -/
theorem canonicalCompletedNativeLogDerivativeMoment_eq_factorCoefficients
    (n : ℕ) :
    (canonicalCompletedNativeLogDerivativeMoment n : ℂ) =
      nativeXiCompletionResponseTaylorCoefficient (2 * n + 1) +
        nativeHeightScalarResponseTaylorCoefficient (2 * n + 1) := by
  rw [← completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]
  exact completedNativeGreenResponseTaylorCoefficient_eq_factorCoefficients
    (2 * n + 1)

/-- The first nonconstant response coefficient is the exact two-channel
decomposition of the zeroth completed-native moment. This is the center test
any product-enriched Hilbert jet must realize before an all-order Gram
identification can be attempted. -/
theorem canonicalCompletedNativeLogDerivativeMoment_zero_eq_factorResponseCoefficients :
    (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) =
      nativeXiCompletionResponseTaylorCoefficient 1 +
        nativeHeightScalarResponseTaylorCoefficient 1 := by
  simpa using canonicalCompletedNativeLogDerivativeMoment_eq_factorCoefficients 0

end

end CarrySelfAdjointOperator
