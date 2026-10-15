import CarrySelfAdjointOperator.PrimeDepthNormalizedResponseVectorJet
import CarrySelfAdjointOperator.CanonicalCompletedC3GammaLedgerNumerator
import CarrySelfAdjointOperator.CompletedGreenForwardDifferenceLimit
import CarrySelfAdjointOperator.NativeSourceNormalizedKernelConnection

/-! A concrete two-point response from the existing completed structural
vectors. Head, exact tail, completion and chart correction keep their labels.
The diagonal uses the source derivative, not the zero fallback of division.
One fixed continuous linear readout recovers the canonical divided response.
This is a vector READOUT realization, not a positive Gram realization. -/
namespace CarrySelfAdjointOperator.DividedVectorResponse
open CPFormal.Analytic.Cp
open Filter
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

private abbrev completedNativeResponse : ℂ → ℂ :=
  completedGreenNormalizedResponse completedNativeOperatorCharacteristic
    completedNativeOperatorBoundaryCompanion

/-- The already normalized four geometric sectors, before scalar synthesis. -/
def sourceVector (z : ℂ) : CompletedPrimeDepthJetCarrier :=
  WithLp.toLp 2 (fun role => primeDepthNormalizedStructuralState role z)

theorem sourceVector_analyticAt_zero : AnalyticAt ℂ sourceVector 0 := by
  have hp := AnalyticAt.pi primeDepthNormalizedStructuralState_analyticAt
  exact (PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : CanonicalCompletedC3StructuralChannel =>
      CanonicalCompletedC3FullWronskianOperatorCarrier)).symm.toContinuousLinearMap.analyticAt _
        |>.comp hp

theorem sourceVector_readout (z : ℂ) :
    primeDepthNormalizedResponseVectorReadout (sourceVector z) =
      canonicalCompletedC3FullOperatorNormalizedResponse 1 z := by
  rw [primeDepthNormalizedResponseVectorReadout_apply]
  exact primeDepthNormalizedStructuralState_readout z

/-- Actual divided vector response. On a = z this is the source derivative. -/
def response (a z : ℂ) : CompletedPrimeDepthJetCarrier := dslope sourceVector a z

theorem response_off_diagonal (a z : ℂ) (h : z ≠ a) :
    response a z = (z-a)⁻¹ • (sourceVector z-sourceVector a) := by
  rw [response, dslope_of_ne _ h]
  rfl

theorem response_diagonal (a : ℂ) : response a a = deriv sourceVector a :=
  dslope_same _ _

/-- The vector equation precedes any scalar projection. -/
theorem response_source_equation (a z : ℂ) :
    (z-a) • response a z = sourceVector z-sourceVector a :=
  sub_smul_dslope _ _ _

theorem response_continuousAt_center : ContinuousAt (response 0) 0 :=
  continuousAt_dslope_same.mpr sourceVector_analyticAt_zero.differentiableAt

theorem response_readout (a z : ℂ) (ha : DifferentiableAt ℂ sourceVector a) :
    primeDepthNormalizedResponseVectorReadout (response a z) =
      dslope (canonicalCompletedC3FullOperatorNormalizedResponse 1) a z := by
  have h := primeDepthNormalizedResponseVectorReadout.dslope_comp sourceVector a z
    (fun _ => ha)
  have heq : primeDepthNormalizedResponseVectorReadout ∘ sourceVector =
      canonicalCompletedC3FullOperatorNormalizedResponse 1 :=
    funext sourceVector_readout
  rw [heq] at h
  exact h.symm

/-- An actual open source neighborhood, supplied by analyticity and the
existing normalized response identity; no moment-kernel premise occurs. -/
theorem response_readout_local :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ a ∈ U, ∀ z ∈ U,
        primeDepthNormalizedResponseVectorReadout (response a z) =
          dslope completedNativeResponse a z := by
  have hnear := sourceVector_analyticAt_zero.eventually_analyticAt.and
    (canonicalCompletedC3FullOperatorNormalizedResponse_eventuallyEq_completed 1)
  rcases mem_nhds_iff.mp hnear with ⟨U, hU, hopen, hzero⟩
  refine ⟨U, hopen, hzero, ?_⟩
  intro a ha z hz
  rw [response_readout a z (hU ha).1.differentiableAt]
  by_cases hza : z = a
  · subst z
    simp only [dslope_same]
    have heq : canonicalCompletedC3FullOperatorNormalizedResponse 1 =ᶠ[nhds a]
        completedNativeResponse := by
      filter_upwards [hopen.mem_nhds ha] with t ht
      exact (hU ht).2
    exact heq.deriv_eq
  · simp only [dslope_of_ne _ hza, slope]
    rw [(hU hz).2, (hU ha).2]

/-- The central scalar value is the actual zeroth native moment, rather than
an independently fitted norm. The vector is the derivative of the source. -/
theorem response_center_readout :
    primeDepthNormalizedResponseVectorReadout (response 0 0) =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rcases response_readout_local with ⟨U, _, hzero, hU⟩
  rw [hU 0 hzero 0 hzero, dslope_same]
  have h := completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical 0
  simpa [completedNativeGreenResponseTaylorCoefficient, iteratedDeriv_one,
    completedNativeResponse] using h

/-- The Cauchy leg is conjugated in the original source, before readout. -/
def polarizedResponse (z w : ℂ) : CompletedPrimeDepthJetCarrier := response (conj z) w

theorem polarizedResponse_readout_local :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ z w : ℂ, conj z ∈ U → w ∈ U →
        operatorHeightParameter z ∈ genuineCriticalStrip → w ≠ conj z →
        primeDepthNormalizedResponseVectorReadout (polarizedResponse z w) =
          (completedNativeResponse w-conj (completedNativeResponse z))/(w-conj z) := by
  rcases response_readout_local with ⟨U, hopen, hzero, hU⟩
  refine ⟨U, hopen, hzero, ?_⟩
  intro z w hz hw hs hne
  rw [polarizedResponse, hU (conj z) hz w hw, dslope_of_ne _ hne]
  simp only [slope, smul_eq_mul,
    completedNativeGreenNormalizedResponse_centeredReflection hs, div_eq_mul_inv]
  change (w-conj z)⁻¹*(completedNativeResponse w-conj (completedNativeResponse z)) =
    (completedNativeResponse w-conj (completedNativeResponse z))/(w-conj z)
  rw [div_eq_mul_inv, mul_comm]

private theorem readout_taylor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (L : E →L[ℂ] ℂ) {f : ℂ → E} (hf : AnalyticAt ℂ f 0) (r : ℕ) :
    L (completedGreenTaylorJet f r) = iteratedDeriv r (L ∘ f) 0/(r.factorial : ℂ) := by
  have hd := L.iteratedFDeriv_comp_left (hf.contDiffAt : ContDiffAt ℂ (r : ℕ) f 0)
    (i := r) le_rfl
  have he := congrArg (fun p => p (fun _ : Fin r => (1 : ℂ))) hd
  have he' : iteratedDeriv r (L ∘ f) 0 = L (iteratedDeriv r f 0) := he
  rw [completedGreenTaylorJet, map_smul, ← he']
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

/-- The ledger is extracted from the original source Taylor tower. Its
anti-diagonal structure is the one imposed by divided differences. -/
def coefficientVector (p q : ℕ) : CompletedPrimeDepthJetCarrier :=
  completedGreenTaylorJet sourceVector (p+q+1)

theorem coefficientVector_readout (p q : ℕ) :
    primeDepthNormalizedResponseVectorReadout (coefficientVector p q) =
      polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment p q := by
  rw [coefficientVector, readout_taylor primeDepthNormalizedResponseVectorReadout
    sourceVector_analyticAt_zero]
  have heq : primeDepthNormalizedResponseVectorReadout ∘ sourceVector =
      canonicalCompletedC3FullOperatorNormalizedResponse 1 :=
    funext sourceVector_readout
  rw [heq]
  change canonicalCompletedC3FullOperatorResponseTaylorCoefficient 1 (p+q+1) = _
  rw [canonicalCompletedC3FullOperatorResponseTaylorCoefficient_eq_completed]
  exact completedNativeGreenResponseTaylorCoefficient_succ_eq_polarized p q

/-- Finite synthesis retains both independent inputs and every ordered cross.
This is a vector-valued bilinear readout, not a Gram factorization. -/
theorem coefficientVector_finite_readout {N M : ℕ}
    (x : Fin N → ℂ) (y : Fin M → ℂ) (p : Fin N → ℕ) (q : Fin M → ℕ) :
    primeDepthNormalizedResponseVectorReadout
        (∑ i, ∑ j, (conj (x i)*y j) • coefficientVector (p i) (q j)) =
      ∑ i, ∑ j, conj (x i)*y j*
        polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment (p i) (q j) := by
  simp only [map_sum, map_smul, smul_eq_mul, coefficientVector_readout]

end
end CarrySelfAdjointOperator.DividedVectorResponse
