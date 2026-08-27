import CarrySelfAdjointOperator.CompletedNativeTfvdWronskianMoments
import CarrySelfAdjointOperator.CompletedNativeLogDerivativePoles

/-!
# Completed native even-coordinate resolvent bridge

The completed characteristic is locally reconstructed from its actual even
Taylor coefficients in the reduced coordinate `u = z^2`.  Differentiating
this identity identifies the global native logarithmic derivative with the
reduced logarithmic derivative, including the exact chain-rule factor.

Composing with the completed Jacobi resolvent readout gives a direct local
identity between the positive operator readout and the native logarithmic
derivative.  No zero, pole, prime, or spectral input enters the bridge.
-/

open Filter

namespace CarrySelfAdjointOperator

noncomputable section

/-- The global completed characteristic is locally the reconstructed even
characteristic in the reduced coordinate `u = z^2`. -/
theorem completedNativeOperatorCharacteristic_eventuallyEq_evenCharacteristic_sq :
    completedNativeOperatorCharacteristic =ᶠ[nhds 0]
      fun z => completedNativeEvenCharacteristic (z ^ 2) := by
  have hfull : ∀ᶠ z : ℂ in nhds 0,
      HasSum
        (fun n => z ^ n * completedNativeFullCharacteristicTaylorCoefficient n)
        (completedNativeOperatorCharacteristic z) := by
    simpa [completedNativeFullCharacteristicTaylorCoefficient,
      FormalMultilinearSeries.ofScalars_apply_eq] using
      (completedNativeOperatorCharacteristic_analyticAt
        zero_mem_completedNativeHeightDomain).hasFPowerSeriesAt.eventually_hasSum
  have heven : ∀ᶠ u : ℂ in nhds 0,
      HasSum
        (fun n => u ^ n * completedNativeEvenCharacteristicCoefficient n)
        (completedNativeEvenCharacteristic u) := by
    simpa [completedNativeEvenCharacteristicSeries,
      FormalMultilinearSeries.ofScalars_apply_eq] using
      completedNativeEvenCharacteristic_hasFPowerSeriesAt.eventually_hasSum
  have hsquare : Tendsto (fun z : ℂ => z ^ 2) (nhds 0) (nhds 0) := by
    have h : ContinuousAt (fun z : ℂ => z ^ 2) 0 := by fun_prop
    have ht := h.tendsto
    norm_num at ht
    exact ht
  filter_upwards [hfull, hsquare.eventually heven] with z hzFull hzEven
  have hEvenPart :
      HasSum
        (fun n => z ^ (2 * n) *
          completedNativeFullCharacteristicTaylorCoefficient (2 * n))
        (completedNativeEvenCharacteristic (z ^ 2)) := by
    refine HasSum.congr_fun hzEven (fun n => ?_)
    rw [completedNativeFullCharacteristicTaylorCoefficient_even, pow_mul]
  have hOddPart :
      HasSum
        (fun n => z ^ (2 * n + 1) *
          completedNativeFullCharacteristicTaylorCoefficient (2 * n + 1))
        0 := by
    refine HasSum.congr_fun
      (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0) (fun n => ?_)
    rw [completedNativeFullCharacteristicTaylorCoefficient_odd, mul_zero]
  have hall : HasSum
      (fun n => z ^ n * completedNativeFullCharacteristicTaylorCoefficient n)
      (completedNativeEvenCharacteristic (z ^ 2) + 0) :=
    HasSum.even_add_odd hEvenPart hOddPart
  exact hzFull.unique (by simpa only [add_zero] using hall)

/-- The derivative of the global completed characteristic is the derivative
of its reduced even germ with the exact chain-rule factor `2z`. -/
theorem completedNativeOperatorCharacteristic_deriv_eventuallyEq_evenCharacteristic_sq :
    (fun z => deriv completedNativeOperatorCharacteristic z) =ᶠ[nhds 0]
      fun z => 2 * z * deriv completedNativeEvenCharacteristic (z ^ 2) := by
  have heq :=
    completedNativeOperatorCharacteristic_eventuallyEq_evenCharacteristic_sq
  have heqSet :
      {z : ℂ | completedNativeOperatorCharacteristic z =
        completedNativeEvenCharacteristic (z ^ 2)} ∈ nhds 0 := heq
  obtain ⟨U, hUsub, hUopen, hzeroU⟩ := mem_nhds_iff.mp heqSet
  have hsquare : Tendsto (fun z : ℂ => z ^ 2) (nhds 0) (nhds 0) := by
    have h : ContinuousAt (fun z : ℂ => z ^ 2) 0 := by fun_prop
    have ht := h.tendsto
    norm_num at ht
    exact ht
  have hanalytic : ∀ᶠ z : ℂ in nhds 0,
      AnalyticAt ℂ completedNativeEvenCharacteristic (z ^ 2) :=
    hsquare.eventually
      completedNativeEvenCharacteristic_analyticAt.eventually_analyticAt
  filter_upwards [hUopen.mem_nhds hzeroU, hanalytic] with z hzU hzAnalytic
  have heqAt : completedNativeOperatorCharacteristic =ᶠ[nhds z]
      fun w => completedNativeEvenCharacteristic (w ^ 2) := by
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    exact hUsub hw
  have hsquareDeriv : HasDerivAt (fun w : ℂ => w ^ 2) (2 * z) z := by
    simpa using (hasDerivAt_pow 2 z)
  have hcomp := hzAnalytic.differentiableAt.hasDerivAt.comp z hsquareDeriv
  calc
    deriv completedNativeOperatorCharacteristic z =
        deriv (fun w => completedNativeEvenCharacteristic (w ^ 2)) z :=
      heqAt.deriv_eq
    _ = deriv completedNativeEvenCharacteristic (z ^ 2) * (2 * z) := by
      change deriv (completedNativeEvenCharacteristic ∘ fun w : ℂ => w ^ 2) z = _
      exact hcomp.deriv
    _ = 2 * z * deriv completedNativeEvenCharacteristic (z ^ 2) := by ring

/-- The native logarithmic derivative and the reduced logarithmic derivative
are the same local meromorphic germ under `u = z^2`. -/
theorem completedNativeOperatorLogDerivative_eventuallyEq_evenCoordinate :
    completedNativeOperatorLogDerivative =ᶠ[nhds 0]
      fun z => 2 * z * completedNativeLogDerivative (z ^ 2) := by
  filter_upwards
      [completedNativeOperatorCharacteristic_eventuallyEq_evenCharacteristic_sq,
        completedNativeOperatorCharacteristic_deriv_eventuallyEq_evenCharacteristic_sq]
    with z hz hderiv
  unfold completedNativeOperatorLogDerivative completedNativeLogDerivative
  rw [hz, hderiv]
  ring

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- In the height coordinate, the scalar readout of the completed positive
Jacobi resolvent is exactly the global native logarithmic derivative. -/
theorem CompletedNativeGreenWeylReducedHeightCertificate.completedJacobiResolventReadout_eventually_eq_operatorLogDerivative_evenCoordinate
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let jet := completedGreenJet
      (canonicalCompletedNativeGreenParityJet xiState)
    let readout := fun u : ℝ =>
      inner ℝ (∑' n : ℕ, u ^ n • greenJetEvenSectorJet jet n)
        (greenJetEvenSectorJet jet 0)
    ∀ᶠ t : ℝ in nhds 0,
      completedNativeOperatorLogDerivative (t : ℂ) =
        (2 : ℂ) * t * Complex.ofReal (readout (t ^ 2)) := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  dsimp only
  let jet := completedGreenJet
    (canonicalCompletedNativeGreenParityJet xiState)
  let readout := fun u : ℝ =>
    inner ℝ (∑' n : ℕ, u ^ n • greenJetEvenSectorJet jet n)
      (greenJetEvenSectorJet jet 0)
  have hreadout : ∀ᶠ u : ℝ in nhds 0,
      Complex.ofReal (readout u) = completedNativeLogDerivative (u : ℂ) := by
    simpa only [jet, readout] using
      certificate.completedJacobiResolventReadout_eventually_eq_nativeLogDerivative
  have hsquare : Tendsto (fun t : ℝ => t ^ 2) (nhds 0) (nhds 0) := by
    have h : ContinuousAt (fun t : ℝ => t ^ 2) 0 := by fun_prop
    have ht := h.tendsto
    norm_num at ht
    exact ht
  have hofReal : Tendsto (fun t : ℝ => (t : ℂ)) (nhds 0) (nhds 0) := by
    have h : ContinuousAt (fun t : ℝ => (t : ℂ)) 0 := by fun_prop
    have ht := h.tendsto
    norm_num at ht
    exact ht
  filter_upwards [hsquare.eventually hreadout,
    hofReal.eventually
      completedNativeOperatorLogDerivative_eventuallyEq_evenCoordinate]
      with t htReadout htLog
  rw [htLog]
  have hsq : (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) := by norm_num
  rw [hsq, ← htReadout]

end

end CarrySelfAdjointOperator
