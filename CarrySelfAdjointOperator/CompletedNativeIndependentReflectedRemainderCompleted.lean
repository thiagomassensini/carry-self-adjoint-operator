import CarrySelfAdjointOperator.CompletedNativeIndependentReflectedNonGreenLedgerCrosswalk
import CarrySelfAdjointOperator.CompletedC3FullWronskianPolarization
import Mathlib.Tactic

/-!
# All-order completed-response identification of the real non-Green remainder

The real non-Green diagonal has already been identified functionally with the
fixed-center channel ledger at cutoff `M + 1`.  This file transports that
response equality through all real derivatives, and compares the result with
the independently reconstructed corrected chiral response.  The only Green
conclusion obtained here is cancellation of the *total* finite-atlas Green
jet sum.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section
set_option autoImplicit false

/-! ## All-order transport of the functional fixed-center crosswalk -/

/-- The response-level real diagonal crosswalk transports directly through
every iterated real derivative. -/
theorem iteratedDeriv_nonGreenRealDiagonal_eq_fixedCenterLedger
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (order : ℕ) :
    iteratedDeriv order
        (canonicalC3IndependentReflectedNonGreenRealDiagonalResponse
          M q hqpos.le hq1 S) 0 =
      iteratedDeriv order
        (fun t : ℝ =>
          canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator
            (M + 1) (t : ℂ)) 0 := by
  apply congrArg (fun f : ℝ → ℂ => iteratedDeriv order f 0)
  funext t
  exact canonicalC3IndependentReflectedNonGreenRealDiagonalResponse_eq_fixedCenterChannels
    M q hqpos hq1 S t

/-- The fixed-center ledger restricted to the real axis has the completed
response Taylor coefficient at every order.  The order-zero instance is
valid because the existing fixed-center germ theorem has already used the
proved central value of the completed response, rather than discarding its
constant reflected term formally. -/
theorem factorialNormalizedFixedCenterLedgerJet_eq_completedResponse
    (M order : ℕ) :
    factorialNormalizedRealJetCoefficient
        (fun t : ℝ =>
          canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator
            M (t : ℂ)) order =
      completedNativeGreenResponseTaylorCoefficient order := by
  have hledger : canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M =
      fun w : ℂ => canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M 0 w := by
    funext w
    exact canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator_eq_ledger M w
  have hpolar : (fun w : ℂ =>
      canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M 0 w) =ᶠ[nhds 0]
      completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion := by
    refine (canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_fixedCenter_eventuallyEq_response
      M).trans ?_
    filter_upwards [] with w
    unfold canonicalCompletedNativePolarizedResponseNumerator
    change
      completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w -
        (starRingEnd ℂ)
          (completedGreenNormalizedResponse
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion 0) =
      completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion w
    rw [completedNativeGreenNormalizedResponse_zero]
    simp
  have hnear : canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M =ᶠ[nhds 0]
      completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion := by
    exact (Filter.EventuallyEq.of_eq hledger).trans
      hpolar
  have hanalytic : AnalyticAt ℂ
      (canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M) 0 := by
    exact completedNativeGreenNormalizedResponse_analyticAt.congr hnear.symm
  unfold factorialNormalizedRealJetCoefficient
  rw [iteratedDeriv_comp_ofReal_eq_of_analyticAt hanalytic]
  unfold completedNativeGreenResponseTaylorCoefficient
  rw [Filter.EventuallyEq.iteratedDeriv_eq order hnear]

/-- Every canonical real non-Green remainder coefficient is the completed
response coefficient at the shifted literal derivative order `p + 1`. -/
theorem canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder_eq_completedResponse
    (M p : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder
      M p q hqpos.le hq1 S =
      completedNativeGreenResponseTaylorCoefficient (p + 1) := by
  unfold canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder
    canonicalC3IndependentReflectedNonGreenRealJetCoefficient
    factorialNormalizedRealJetCoefficient
  rw [iteratedDeriv_nonGreenRealDiagonal_eq_fixedCenterLedger M q hqpos hq1 S]
  exact factorialNormalizedFixedCenterLedgerJet_eq_completedResponse (M + 1) (p + 1)

/-! ## Parity of the canonical remainder index -/

/-- Even canonical indices use odd literal derivative order and therefore
recover the corresponding completed-native logarithmic moment. -/
theorem canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder_even_eq_moment
    (M n : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder
      M (2 * n) q hqpos.le hq1 S =
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  rw [canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder_eq_completedResponse
      M (2 * n) q hqpos hq1 S,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]

/-- Odd canonical indices use even literal derivative order and vanish.  The
words “even” and “odd” here classify the canonical index `p`, not the
derivative order `p + 1`. -/
theorem canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder_odd_eq_zero
    (M n : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder
      M (2 * n + 1) q hqpos.le hq1 S = 0 := by
  rw [canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder_eq_completedResponse
    M (2 * n + 1) q hqpos hq1 S]
  convert completedNativeGreenResponseTaylorCoefficient_even_eq_zero (n + 1) using 1
  congr 1

/-! ## Independent completed-response path for the six-analysis jet -/

/-- The canonical six-analysis coefficient is independently the completed
response coefficient.  This route passes through corrected chiral and the
full Wronskian response, not through the real non-Green remainder. -/
theorem canonicalC3BracketTfvdSixAnalysisJetCoefficient_eq_completedResponse
    (M p : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisJetCoefficient M p q hqpos.le hq1 S =
      completedNativeGreenResponseTaylorCoefficient (p + 1) := by
  rw [← canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_sixAnalysisJet
    M p q hqpos hq1 S,
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_response,
    canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient_eq_completed]

/-- The canonical six-analysis coefficient and the real non-Green remainder
are equal because they independently compute the same completed response
coefficient. -/
theorem canonicalC3BracketTfvdSixAnalysisJetCoefficient_eq_nonGreenRealRemainder
    (M p : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisJetCoefficient M p q hqpos.le hq1 S =
      canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder
        M p q hqpos.le hq1 S := by
  rw [canonicalC3BracketTfvdSixAnalysisJetCoefficient_eq_completedResponse
      M p q hqpos hq1 S,
    canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder_eq_completedResponse
      M p q hqpos hq1 S]

/-! ## Cancellation of the sewn total Green convolution -/

/-- The complete undressed Green convolution vanishes in every positive
literal order.  This is cancellation of the total sewn boundary only; it
does not make a claim about an individual camera pair. -/
theorem canonicalC3IndependentReflectedUndressedGreenConvolution_eq_zero
    (M p : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∑ j ∈ Finset.range (p + 1 + 1),
      canonicalC3IndependentReflectedResponsePrefactorJetCoefficient (p + 1 - j) *
        canonicalC3IndependentReflectedUndressedGreenJetCoefficient
          (M + 1) j q hqpos.le hq1 S 0 = 0 := by
  have hsplit :=
    canonicalC3BracketTfvdSixAnalysisJetCoefficient_eq_undressedGreen_convolution_add_realRemainder
      M p q hqpos hq1 S
  rw [canonicalC3BracketTfvdSixAnalysisJetCoefficient_eq_nonGreenRealRemainder
    M p q hqpos hq1 S] at hsplit
  apply add_left_cancel (a :=
    canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder M p q hqpos.le hq1 S)
  calc
    canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder M p q hqpos.le hq1 S +
        (∑ j ∈ Finset.range (p + 1 + 1),
          canonicalC3IndependentReflectedResponsePrefactorJetCoefficient (p + 1 - j) *
            canonicalC3IndependentReflectedUndressedGreenJetCoefficient
              (M + 1) j q hqpos.le hq1 S 0) =
        (∑ j ∈ Finset.range (p + 1 + 1),
          canonicalC3IndependentReflectedResponsePrefactorJetCoefficient (p + 1 - j) *
            canonicalC3IndependentReflectedUndressedGreenJetCoefficient
              (M + 1) j q hqpos.le hq1 S 0) +
          canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder
            M p q hqpos.le hq1 S := by
          ring
    _ = canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder
          M p q hqpos.le hq1 S := hsplit.symm
    _ = canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder M p q hqpos.le hq1 S +
          0 := (add_zero _).symm

/-- Camera-pairwise form of the same total convolution cancellation.  The
inner pairwise sum may cancel globally; no individual summand is asserted to
vanish. -/
theorem canonicalC3IndependentReflectedUndressedGreenCameraPairwiseConvolution_eq_zero
    (M p : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∑ j ∈ Finset.range (p + 1 + 1),
      canonicalC3IndependentReflectedResponsePrefactorJetCoefficient (p + 1 - j) *
        (∑ directCamera ∈ canonicalFiniteCameraAtlas (M + 1),
          ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas (M + 1),
            canonicalC3CameraResolvedIndependentReflectedUndressedGreenJetCoefficient
              (M + 1) j q hqpos.le hq1 S 0 directCamera reflectedCamera) = 0 := by
  calc
    (∑ j ∈ Finset.range (p + 1 + 1),
      canonicalC3IndependentReflectedResponsePrefactorJetCoefficient (p + 1 - j) *
        (∑ directCamera ∈ canonicalFiniteCameraAtlas (M + 1),
          ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas (M + 1),
            canonicalC3CameraResolvedIndependentReflectedUndressedGreenJetCoefficient
              (M + 1) j q hqpos.le hq1 S 0 directCamera reflectedCamera)) =
        ∑ j ∈ Finset.range (p + 1 + 1),
          canonicalC3IndependentReflectedResponsePrefactorJetCoefficient (p + 1 - j) *
            canonicalC3IndependentReflectedUndressedGreenJetCoefficient
              (M + 1) j q hqpos.le hq1 S 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [canonicalC3IndependentReflectedUndressedGreenJetCoefficient_eq_cameraPairwise_sum]
    _ = 0 := canonicalC3IndependentReflectedUndressedGreenConvolution_eq_zero
      M p q hqpos hq1 S

/-! ## Explicit first positive literal orders -/

/-- Literal order one of the total Green convolution. -/
theorem canonicalC3IndependentReflectedUndressedGreenConvolution_zero_index
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 1 *
        canonicalC3IndependentReflectedUndressedGreenJetCoefficient
          (M + 1) 0 q hqpos.le hq1 S 0 +
      canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 0 *
        canonicalC3IndependentReflectedUndressedGreenJetCoefficient
          (M + 1) 1 q hqpos.le hq1 S 0 = 0 := by
  simpa [Finset.sum_range_succ] using
    canonicalC3IndependentReflectedUndressedGreenConvolution_eq_zero M 0 q hqpos hq1 S

/-- Literal order two of the total Green convolution. -/
theorem canonicalC3IndependentReflectedUndressedGreenConvolution_one_index
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 2 *
        canonicalC3IndependentReflectedUndressedGreenJetCoefficient
          (M + 1) 0 q hqpos.le hq1 S 0 +
      canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 1 *
        canonicalC3IndependentReflectedUndressedGreenJetCoefficient
          (M + 1) 1 q hqpos.le hq1 S 0 +
      canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 0 *
        canonicalC3IndependentReflectedUndressedGreenJetCoefficient
          (M + 1) 2 q hqpos.le hq1 S 0 = 0 := by
  simpa [Finset.sum_range_succ] using
    canonicalC3IndependentReflectedUndressedGreenConvolution_eq_zero M 1 q hqpos hq1 S

/-- Literal order three of the total Green convolution. -/
theorem canonicalC3IndependentReflectedUndressedGreenConvolution_two_index
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 3 *
        canonicalC3IndependentReflectedUndressedGreenJetCoefficient
          (M + 1) 0 q hqpos.le hq1 S 0 +
      canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 2 *
        canonicalC3IndependentReflectedUndressedGreenJetCoefficient
          (M + 1) 1 q hqpos.le hq1 S 0 +
      canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 1 *
        canonicalC3IndependentReflectedUndressedGreenJetCoefficient
          (M + 1) 2 q hqpos.le hq1 S 0 +
      canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 0 *
        canonicalC3IndependentReflectedUndressedGreenJetCoefficient
          (M + 1) 3 q hqpos.le hq1 S 0 = 0 := by
  simpa [Finset.sum_range_succ] using
    canonicalC3IndependentReflectedUndressedGreenConvolution_eq_zero M 2 q hqpos hq1 S

/-! ## The central order-zero gate -/

/-- The new non-Green real diagonal vanishes at the center by the exact
fixed-center ledger crosswalk. -/
theorem canonicalC3IndependentReflectedNonGreenRealDiagonalResponse_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedNonGreenRealDiagonalResponse M q hqpos.le hq1 S 0 = 0 := by
  rw [canonicalC3IndependentReflectedNonGreenRealDiagonalResponse_eq_fixedCenterChannels
    M q hqpos hq1 S 0]
  simpa using canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator_zero (M + 1)

/-- The canonical six-analysis response itself has zero central value, by its
completed-response germ identification and the proved completed central
reflection cancellation. -/
theorem canonicalC3BracketTfvdSixAnalysisNormalizedResponse_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hqpos.le hq1 S 0 = 0 := by
  rw [(canonicalC3BracketTfvdSixAnalysisNormalizedResponse_eventuallyEq_completed
    M q hqpos hq1 S).self_of_nhds]
  exact completedNativeGreenNormalizedResponse_zero

/-- The prefactor central coefficient is nonzero.  This is a direct quotient
calculation using the existing nonvanishing of the xi completion and of the
already retained response denominator. -/
theorem canonicalC3IndependentReflectedResponsePrefactorJetCoefficient_zero_ne_zero :
    canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 0 ≠ 0 := by
  rw [canonicalC3IndependentReflectedResponsePrefactorJetCoefficient_zero]
  unfold canonicalC3IndependentReflectedResponsePrefactor mixedHermitianWeight
  apply div_ne_zero
  · exact mul_ne_zero
      (nativeXiCompletionFactor_ne_zero zero_mem_completedNativeHeightDomain)
      ((map_ne_zero (starRingEnd ℂ)).2
        (nativeXiCompletionFactor_ne_zero zero_mem_completedNativeHeightDomain))
  · exact canonicalC3BracketTfvdSixAnalysisResponseDenominator_zero_ne_zero

/-- The independent center-value calculation supplies the missing literal
order-zero convolution equation. -/
theorem canonicalC3IndependentReflectedUndressedGreenCentralProduct_eq_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 0 *
        canonicalC3IndependentReflectedUndressedGreenJetCoefficient
          (M + 1) 0 q hqpos.le hq1 S 0 = 0 := by
  have hsplit :=
    canonicalC3BracketTfvdSixAnalysisRealResponse_eq_prefactor_mul_undressedGreen_add_nonGreen
      M q hqpos hq1 S 0
  change canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hqpos.le hq1 S 0 =
      canonicalC3IndependentReflectedResponsePrefactor 0 *
          canonicalC3IndependentReflectedUndressedGreenCarrier
            (M + 1) q hqpos.le hq1 S 0 +
        canonicalC3IndependentReflectedNonGreenRealDiagonalResponse
          M q hqpos.le hq1 S 0 at hsplit
  rw [canonicalC3BracketTfvdSixAnalysisNormalizedResponse_zero M q hqpos hq1 S,
    canonicalC3IndependentReflectedNonGreenRealDiagonalResponse_zero M q hqpos hq1 S] at hsplit
  rw [canonicalC3IndependentReflectedResponsePrefactorJetCoefficient_zero,
    canonicalC3IndependentReflectedUndressedGreenJetCoefficient_zero]
  simpa [canonicalC3IndependentReflectedUndressedGreenCarrier] using hsplit.symm

/-- The literal zeroth total undressed Green jet vanishes at the shifted
cutoff.  This is the separately established central gate, not a consequence
of the positive-order convolution family. -/
theorem canonicalC3IndependentReflectedUndressedGreenJetCoefficient_zero_eq_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedUndressedGreenJetCoefficient
      (M + 1) 0 q hqpos.le hq1 S 0 = 0 := by
  exact (mul_eq_zero.mp
    (canonicalC3IndependentReflectedUndressedGreenCentralProduct_eq_zero
      M q hqpos hq1 S)).resolve_left
      canonicalC3IndependentReflectedResponsePrefactorJetCoefficient_zero_ne_zero

/-! ## Triangular consequence for total Green jets -/

/-- Once the separate central gate is available, the positive-order total
convolutions force every total undressed Green jet at cutoff `M + 1` to
vanish.  This theorem is intentionally about the sewn total boundary only. -/
theorem canonicalC3IndependentReflectedUndressedGreenJetCoefficient_eq_zero
    (M k : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedUndressedGreenJetCoefficient
      (M + 1) k q hqpos.le hq1 S 0 = 0 := by
  refine Nat.strong_induction_on k ?_
  intro k ih
  cases k with
  | zero =>
      exact canonicalC3IndependentReflectedUndressedGreenJetCoefficient_zero_eq_zero
        M q hqpos hq1 S
  | succ n =>
      have hconvolution :=
        canonicalC3IndependentReflectedUndressedGreenConvolution_eq_zero M n q hqpos hq1 S
      rw [Finset.sum_range_succ] at hconvolution
      have hprior :
          ∑ j ∈ Finset.range (n + 1),
            canonicalC3IndependentReflectedResponsePrefactorJetCoefficient (n + 1 - j) *
              canonicalC3IndependentReflectedUndressedGreenJetCoefficient
                (M + 1) j q hqpos.le hq1 S 0 = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [ih j (Finset.mem_range.mp hj), mul_zero]
      rw [hprior] at hconvolution
      simp only [zero_add, Nat.sub_self] at hconvolution
      exact (mul_eq_zero.mp hconvolution).resolve_left
        canonicalC3IndependentReflectedResponsePrefactorJetCoefficient_zero_ne_zero

/-- Consequently the camera-pairwise jet sum vanishes at every literal order.
This is global atlas cancellation and makes no claim about an individual
camera pair. -/
theorem canonicalC3IndependentReflectedUndressedGreenJetCoefficient_cameraPairwise_sum_eq_zero
    (M k : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (∑ directCamera ∈ canonicalFiniteCameraAtlas (M + 1),
      ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas (M + 1),
        canonicalC3CameraResolvedIndependentReflectedUndressedGreenJetCoefficient
          (M + 1) k q hqpos.le hq1 S 0 directCamera reflectedCamera) = 0 := by
  rw [← canonicalC3IndependentReflectedUndressedGreenJetCoefficient_eq_cameraPairwise_sum]
  exact canonicalC3IndependentReflectedUndressedGreenJetCoefficient_eq_zero
    M k q hqpos hq1 S

end

end CarrySelfAdjointOperator
