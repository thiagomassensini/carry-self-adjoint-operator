import CarrySelfAdjointOperator.CompletedNativeIndependentReflectedCanonicalSection
import CarrySelfAdjointOperator.CompletedNativeRawRealAllOrderBridge
import Mathlib.Tactic

/-!
# Real-axis convolution for the independent-reflected undressed carrier

The canonical six-analysis section uses conjugation in its reflected
coordinate, so its functional splitting cannot be differentiated termwise as
a complex identity.  This file restricts the already established functional
splitting to the real axis.  There conjugation fixes the input and the radial
Green dressing is identically one.  The result is an honest real Leibniz
convolution between the response prefactor and the holomorphic undressed
Green carrier, with the literal non-Green response retained as a real-axis
remainder.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section
set_option autoImplicit false

/-! ## Real restrictions -/

/-- The canonical six-analysis response restricted to the real axis. -/
def canonicalC3BracketTfvdSixAnalysisRealResponse
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) : ℂ :=
  canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hq0 hq1 S (t : ℂ)

@[simp] theorem canonicalC3BracketTfvdSixAnalysisRealResponse_apply
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) :
    canonicalC3BracketTfvdSixAnalysisRealResponse M q hq0 hq1 S t =
      canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hq0 hq1 S (t : ℂ) := rfl

/-- The normalized response prefactor restricted to the real axis. -/
def canonicalC3IndependentReflectedResponsePrefactorReal (t : ℝ) : ℂ :=
  canonicalC3IndependentReflectedResponsePrefactor (t : ℂ)

/-- The holomorphic undressed Green carrier restricted to the real axis. -/
def canonicalC3IndependentReflectedUndressedGreenCarrierReal
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) : ℂ :=
  canonicalC3IndependentReflectedUndressedGreenCarrier M q hq0 hq1 S (t : ℂ)

/-- The literal non-Green response on the real diagonal. -/
def canonicalC3IndependentReflectedNonGreenRealDiagonalResponse
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) : ℂ :=
  canonicalC3IndependentReflectedNonGreenResponse M q hq0 hq1 S (t : ℂ) (t : ℂ)

/-! ## The real diagonal -/

/-- Conjugation fixes the reflected coordinate of the canonical section on
the real axis. -/
theorem canonicalC3SixAnalysisJetSectionReflectedCoordinate_ofReal (t : ℝ) :
    canonicalC3SixAnalysisJetSectionReflectedCoordinate (t : ℂ) = (t : ℂ) := by
  simp [canonicalC3SixAnalysisJetSectionReflectedCoordinate]

/-- On the real axis the canonical section is the literal real diagonal of
the independent-reflected response. -/
theorem canonicalC3BracketTfvdSixAnalysisRealResponse_eq_independentReflected_realDiagonal
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) :
    canonicalC3BracketTfvdSixAnalysisRealResponse M q hqpos.le hq1 S t =
      canonicalC3IndependentReflectedNormalizedResponse M q hqpos.le hq1 S
        (t : ℂ) (t : ℂ) := by
  rw [canonicalC3BracketTfvdSixAnalysisRealResponse_apply,
    canonicalC3BracketTfvdSixAnalysisNormalizedResponse_eq_independentReflected_specialization
      M q hqpos hq1 S (t : ℂ)]
  simp [canonicalC3SixAnalysisJetSectionDirectCoordinate]

/-- The independent-reflected radial factor is identically one on the whole
real axis. -/
theorem canonicalC3IndependentReflectedRadialGreenFactor_ofReal (t : ℝ) :
    canonicalC3IndependentReflectedRadialGreenFactor (t : ℂ) = 1 := by
  rw [canonicalC3IndependentReflectedRadialGreenFactor_eq_br2RadialPhase]
  simp [br2RadialPhase, br2RadialExponent]

/-- On the real diagonal the compensation retains exactly the literal
non-Green response: the radial correction vanishes because its factor is
`rho(t) - 1`. -/
theorem canonicalC3IndependentReflectedUndressedCompensationResponse_realDiagonal_eq_nonGreen
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) :
    canonicalC3IndependentReflectedUndressedCompensationResponse M q hq0 hq1 S
        (t : ℂ) (t : ℂ) =
      canonicalC3IndependentReflectedNonGreenRealDiagonalResponse M q hq0 hq1 S t := by
  rw [canonicalC3IndependentReflectedUndressedCompensationResponse_eq_greenCorrection_add_nonGreen,
    canonicalC3IndependentReflectedRadialGreenFactor_ofReal]
  simp [canonicalC3IndependentReflectedNonGreenRealDiagonalResponse]

/-- The real six-analysis response splits into the nonconstant response
prefactor times the undressed Green carrier, plus the complete real-diagonal
non-Green response. -/
theorem canonicalC3BracketTfvdSixAnalysisRealResponse_eq_prefactor_mul_undressedGreen_add_nonGreen
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) :
    canonicalC3BracketTfvdSixAnalysisRealResponse M q hqpos.le hq1 S t =
      canonicalC3IndependentReflectedResponsePrefactorReal t *
          canonicalC3IndependentReflectedUndressedGreenCarrierReal
            (M + 1) q hqpos.le hq1 S t +
        canonicalC3IndependentReflectedNonGreenRealDiagonalResponse
          M q hqpos.le hq1 S t := by
  rw [canonicalC3BracketTfvdSixAnalysisRealResponse_apply,
    canonicalC3BracketTfvdSixAnalysisNormalizedResponse_eq_undressedGreen_add_compensation
      M q hqpos hq1 S (t : ℂ),
    canonicalC3SixAnalysisJetSectionReflectedCoordinate_ofReal,
    canonicalC3SixAnalysisJetSectionDirectCoordinate_apply,
    canonicalC3IndependentReflectedUndressedCompensationResponse_realDiagonal_eq_nonGreen]
  rfl

/-! ## Restricting holomorphic germs to the real axis -/

/-- An analytic complex germ yields a real-smooth restriction to the real
axis, at every prescribed finite order. -/
theorem analyticAt_comp_ofReal_contDiffAt
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    ContDiffAt ℝ n (fun t : ℝ => f (t : ℂ)) 0 := by
  have hfrestrict : ContDiffAt ℝ n f (0 : ℂ) :=
    (hf.contDiffAt : ContDiffAt ℂ n f 0).restrict_scalars ℝ
  have hline : ContDiffAt ℝ n (fun t : ℝ => (t : ℂ)) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt
  simpa [Function.comp_def] using
    ContDiffAt.comp (𝕜 := ℝ) (f := fun t : ℝ => (t : ℂ)) (g := f)
      (0 : ℝ) hfrestrict hline

/-- Every iterated real derivative of the restriction of an analytic complex
germ equals its complex iterated derivative at the center. -/
theorem iteratedDeriv_comp_ofReal_eq_of_analyticAt
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (order : ℕ) :
    iteratedDeriv order (fun t : ℝ => f (t : ℂ)) 0 =
      iteratedDeriv order f 0 := by
  have hline : Tendsto (fun t : ℝ => (t : ℂ)) (nhds 0) (nhds 0) := by
    change Tendsto Complex.ofReal (nhds 0) (nhds 0)
    exact Complex.continuous_ofReal.continuousAt
  have hlocal : ∀ᶠ t : ℝ in nhds 0, AnalyticAt ℂ f (t : ℂ) :=
    hline.eventually hf.eventually_analyticAt
  have hnear : ∀ n : ℕ,
      iteratedDeriv n (fun t : ℝ => f (t : ℂ)) =ᶠ[nhds 0]
        fun t : ℝ => iteratedDeriv n f (t : ℂ) := by
    intro n
    induction n with
    | zero => exact Eventually.of_forall (by intro t; rfl)
    | succ n ih =>
        have hderiv :
            deriv (iteratedDeriv n (fun t : ℝ => f (t : ℂ))) =ᶠ[nhds 0]
              fun t : ℝ => deriv (iteratedDeriv n f) (t : ℂ) := by
          filter_upwards [ih.deriv, hlocal] with t ht hft
          rw [ht]
          have houter : DifferentiableAt ℂ (iteratedDeriv n f) (t : ℂ) := by
            simpa only [iteratedDeriv_eq_iterate] using
              (hft.iterated_deriv n).differentiableAt
          exact deriv_comp_ofReal_eq houter
        simpa only [iteratedDeriv_succ] using hderiv
  exact (hnear order).eq_of_nhds

/-! ## Analytic inputs retained by the real interface -/

/-- The six-analysis response agrees, as a germ at the center, with the
completed normalized response. -/
theorem canonicalC3BracketTfvdSixAnalysisNormalizedResponse_eventuallyEq_completed
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hqpos.le hq1 S =ᶠ[nhds 0]
      completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion := by
  refine (Filter.EventuallyEq.of_eq
    (canonicalC3BracketTfvdSixAnalysisNormalizedResponse_eq_sixChannel
      M q hqpos hq1 S)).trans ?_
  exact (canonicalC3BracketTfvdSixChannelNormalizedResponse_eventuallyEq_response M).trans
    (canonicalC3BracketTfvdNormalizedResponse_eventuallyEq_completed M)

/-- The canonical six-analysis response is analytic at the Taylor center. -/
theorem canonicalC3BracketTfvdSixAnalysisNormalizedResponse_analyticAt_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    AnalyticAt ℂ
      (canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hqpos.le hq1 S) 0 := by
  exact completedNativeGreenNormalizedResponse_analyticAt.congr
    (canonicalC3BracketTfvdSixAnalysisNormalizedResponse_eventuallyEq_completed
      M q hqpos hq1 S).symm

/-- The fixed-direct-coordinate undressed Green carrier remains analytic at
the center.  This only repackages the already established undressed carrier
analyticity for the real-axis interface. -/
theorem canonicalC3IndependentReflectedUndressedGreenCarrier_analyticAt_zero
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    AnalyticAt ℂ
      (canonicalC3IndependentReflectedUndressedGreenCarrier M q hq0 hq1 S) 0 := by
  change AnalyticAt ℂ
    (fun v => canonicalC3IndependentReflectedUndressedGreenBoundary M q hq0 hq1 S 0 v) 0
  exact canonicalC3IndependentReflectedUndressedGreenBoundary_analyticAt_zero
    M q hq0 hq1 S 0

/-- The denominator used by the response prefactor is nonzero at the Taylor
center. -/
theorem canonicalC3BracketTfvdSixAnalysisResponseDenominator_zero_ne_zero :
    canonicalC3BracketTfvdSixAnalysisResponseDenominator 0 ≠ 0 := by
  unfold canonicalC3BracketTfvdSixAnalysisResponseDenominator mixedHermitianWeight
  apply mul_ne_zero
  · exact mul_ne_zero
      (canonicalC3ChartFactorHeight_ne_zero zero_mem_completedNativeHeightDomain)
      ((map_ne_zero (starRingEnd ℂ)).2
        (canonicalC3ChartFactorHeight_ne_zero zero_mem_completedNativeHeightDomain))
  · exact mul_ne_zero
      (mul_ne_zero (by norm_num) completedNativeOperatorCharacteristic_zero_ne_zero)
      ((map_ne_zero (starRingEnd ℂ)).2
        completedNativeOperatorCharacteristic_zero_ne_zero)

/-- The response prefactor is analytic at the Taylor center.  Its value and
higher derivatives are retained; it is not absorbed into the Green carrier. -/
theorem canonicalC3IndependentReflectedResponsePrefactor_analyticAt_zero :
    AnalyticAt ℂ canonicalC3IndependentReflectedResponsePrefactor 0 := by
  have hnum : AnalyticAt ℂ
      (fun u : ℂ => mixedHermitianWeight nativeXiCompletionFactor u 0) 0 := by
    unfold mixedHermitianWeight
    exact nativeXiCompletionFactor_analyticAt_zero.mul analyticAt_const
  have hden : AnalyticAt ℂ canonicalC3BracketTfvdSixAnalysisResponseDenominator 0 := by
    have hcharacteristic : AnalyticAt ℂ completedNativeOperatorCharacteristic 0 :=
      completedNativeOperatorCharacteristic_analyticAt zero_mem_completedNativeHeightDomain
    unfold canonicalC3BracketTfvdSixAnalysisResponseDenominator mixedHermitianWeight
    exact
      (canonicalC3ChartFactorHeight_analyticAt_zero.mul analyticAt_const).mul
        ((analyticAt_const.mul hcharacteristic).mul analyticAt_const)
  unfold canonicalC3IndependentReflectedResponsePrefactor
  exact hnum.div hden canonicalC3BracketTfvdSixAnalysisResponseDenominator_zero_ne_zero

/-! ## Factorial-normalized real coefficients -/

/-- Factorial-normalized real-axis derivative coefficient of a complex-valued
real function. -/
def factorialNormalizedRealJetCoefficient (f : ℝ → ℂ) (k : ℕ) : ℂ :=
  iteratedDeriv k f 0 / k.factorial

/-- The retained coefficient of the response prefactor.  This is a complex
jet of the prefactor itself, not a normalization of the Green carrier. -/
def canonicalC3IndependentReflectedResponsePrefactorJetCoefficient (k : ℕ) : ℂ :=
  iteratedDeriv k canonicalC3IndependentReflectedResponsePrefactor 0 / k.factorial

/-- The literal real-axis coefficient of the non-Green diagonal response. -/
def canonicalC3IndependentReflectedNonGreenRealJetCoefficient
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (k : ℕ) : ℂ :=
  factorialNormalizedRealJetCoefficient
    (canonicalC3IndependentReflectedNonGreenRealDiagonalResponse M q hq0 hq1 S) k

@[simp] theorem canonicalC3IndependentReflectedResponsePrefactorJetCoefficient_zero :
    canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 0 =
      canonicalC3IndependentReflectedResponsePrefactor 0 := by
  simp [canonicalC3IndependentReflectedResponsePrefactorJetCoefficient]

/-- The real-axis prefactor coefficients recover exactly the complex jets of
the analytic prefactor. -/
theorem factorialNormalizedRealJetCoefficient_prefactor_eq_complex
    (k : ℕ) :
    factorialNormalizedRealJetCoefficient
        canonicalC3IndependentReflectedResponsePrefactorReal k =
      canonicalC3IndependentReflectedResponsePrefactorJetCoefficient k := by
  unfold factorialNormalizedRealJetCoefficient
    canonicalC3IndependentReflectedResponsePrefactorReal
    canonicalC3IndependentReflectedResponsePrefactorJetCoefficient
  rw [iteratedDeriv_comp_ofReal_eq_of_analyticAt
    canonicalC3IndependentReflectedResponsePrefactor_analyticAt_zero]

/-- The real-axis undressed carrier coefficients recover the literal-order
complex undressed Green jet at direct coordinate zero. -/
theorem factorialNormalizedRealJetCoefficient_undressedGreenCarrier_eq_complex
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (k : ℕ) :
    factorialNormalizedRealJetCoefficient
        (canonicalC3IndependentReflectedUndressedGreenCarrierReal M q hq0 hq1 S) k =
      canonicalC3IndependentReflectedUndressedGreenJetCoefficient M k q hq0 hq1 S 0 := by
  unfold factorialNormalizedRealJetCoefficient
    canonicalC3IndependentReflectedUndressedGreenCarrierReal
    canonicalC3IndependentReflectedUndressedGreenJetCoefficient
  rw [iteratedDeriv_comp_ofReal_eq_of_analyticAt
    (canonicalC3IndependentReflectedUndressedGreenCarrier_analyticAt_zero M q hq0 hq1 S)]
  rfl

/-- The canonical `p + 1` jet can be read through the real restriction of
the total six-analysis response. -/
theorem canonicalC3BracketTfvdSixAnalysisJetCoefficient_eq_realDerivative
    (M p : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisJetCoefficient M p q hqpos.le hq1 S =
      factorialNormalizedRealJetCoefficient
        (canonicalC3BracketTfvdSixAnalysisRealResponse M q hqpos.le hq1 S) (p + 1) := by
  unfold canonicalC3BracketTfvdSixAnalysisJetCoefficient
    factorialNormalizedRealJetCoefficient
    canonicalC3BracketTfvdSixAnalysisRealResponse
  rw [iteratedDeriv_comp_ofReal_eq_of_analyticAt
    (canonicalC3BracketTfvdSixAnalysisNormalizedResponse_analyticAt_zero
      M q hqpos hq1 S)]

/-- The real restriction of the total response is smooth to every requested
finite order, because the complex response germ is analytic. -/
theorem canonicalC3BracketTfvdSixAnalysisRealResponse_contDiffAt
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (n : ℕ) :
    ContDiffAt ℝ n
      (canonicalC3BracketTfvdSixAnalysisRealResponse M q hqpos.le hq1 S) 0 := by
  change ContDiffAt ℝ n
    (fun t : ℝ => canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hqpos.le hq1 S
      (t : ℂ)) 0
  exact analyticAt_comp_ofReal_contDiffAt
    (canonicalC3BracketTfvdSixAnalysisNormalizedResponse_analyticAt_zero
      M q hqpos hq1 S) n

/-- The real restriction of the prefactor is smooth to every requested
finite order. -/
theorem canonicalC3IndependentReflectedResponsePrefactorReal_contDiffAt
    (n : ℕ) :
    ContDiffAt ℝ n canonicalC3IndependentReflectedResponsePrefactorReal 0 := by
  change ContDiffAt ℝ n
    (fun t : ℝ => canonicalC3IndependentReflectedResponsePrefactor (t : ℂ)) 0
  exact analyticAt_comp_ofReal_contDiffAt
    canonicalC3IndependentReflectedResponsePrefactor_analyticAt_zero n

/-- The real restriction of the undressed carrier is smooth to every
requested finite order. -/
theorem canonicalC3IndependentReflectedUndressedGreenCarrierReal_contDiffAt
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (n : ℕ) :
    ContDiffAt ℝ n
      (canonicalC3IndependentReflectedUndressedGreenCarrierReal M q hq0 hq1 S) 0 := by
  change ContDiffAt ℝ n
    (fun t : ℝ => canonicalC3IndependentReflectedUndressedGreenCarrier M q hq0 hq1 S
      (t : ℂ)) 0
  exact analyticAt_comp_ofReal_contDiffAt
    (canonicalC3IndependentReflectedUndressedGreenCarrier_analyticAt_zero
      M q hq0 hq1 S) n

/-! ## Real Leibniz convolution -/

/-- Factorial normalization turns the real Leibniz rule into convolution.
This elementary lemma is deliberately stated only on the real interface. -/
theorem factorialNormalizedRealJetCoefficient_mul_eq_convolution_forward
    {f g : ℝ → ℂ} {n : ℕ}
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0) :
    factorialNormalizedRealJetCoefficient (fun t => f t * g t) n =
      ∑ i ∈ Finset.range (n + 1),
        factorialNormalizedRealJetCoefficient f i *
          factorialNormalizedRealJetCoefficient g (n - i) := by
  classical
  have hsum :
      ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℂ) * iteratedDeriv i f 0 * iteratedDeriv (n - i) g 0 =
        (n.factorial : ℂ) *
          ∑ i ∈ Finset.range (n + 1),
            factorialNormalizedRealJetCoefficient f i *
              factorialNormalizedRealJetCoefficient g (n - i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold factorialNormalizedRealJetCoefficient
    have hle : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hfactorial :
        (n.choose i : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) =
          (n.factorial : ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hle
    field_simp [show (i.factorial : ℂ) ≠ 0 by exact_mod_cast i.factorial_ne_zero,
      show ((n - i).factorial : ℂ) ≠ 0 by
        exact_mod_cast (n - i).factorial_ne_zero]
    rw [← hfactorial]
    ring
  unfold factorialNormalizedRealJetCoefficient at hsum ⊢
  change iteratedDeriv n (f * g) 0 / (n.factorial : ℂ) = _
  rw [iteratedDeriv_mul hf hg, hsum]
  field_simp [show (n.factorial : ℂ) ≠ 0 by exact_mod_cast n.factorial_ne_zero]

/-- The same convolution in the orientation used by the response formula:
the prefactor has order `n - j` and the Green carrier has order `j`. -/
theorem factorialNormalizedRealJetCoefficient_mul_eq_convolution
    {f g : ℝ → ℂ} {n : ℕ}
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0) :
    factorialNormalizedRealJetCoefficient (fun t => f t * g t) n =
      ∑ j ∈ Finset.range (n + 1),
        factorialNormalizedRealJetCoefficient f (n - j) *
          factorialNormalizedRealJetCoefficient g j := by
  rw [factorialNormalizedRealJetCoefficient_mul_eq_convolution_forward hf hg]
  rw [← Finset.sum_range_reflect
    (fun j => factorialNormalizedRealJetCoefficient f (n - j) *
      factorialNormalizedRealJetCoefficient g j) (n + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hsub : n + 1 - 1 - j = n - j := by omega
  rw [hsub, Nat.sub_sub_self hjle]

/-- The literal non-Green real diagonal is smooth to every prescribed finite
order.  This is obtained from the exact real splitting; no complex
analyticity of the conjugate physical section is asserted. -/
theorem canonicalC3IndependentReflectedNonGreenRealDiagonalResponse_contDiffAt
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (n : ℕ) :
    ContDiffAt ℝ n
      (canonicalC3IndependentReflectedNonGreenRealDiagonalResponse M q hqpos.le hq1 S) 0 := by
  let response : ℝ → ℂ :=
    canonicalC3BracketTfvdSixAnalysisRealResponse M q hqpos.le hq1 S
  let prefactor : ℝ → ℂ := canonicalC3IndependentReflectedResponsePrefactorReal
  let carrier : ℝ → ℂ :=
    canonicalC3IndependentReflectedUndressedGreenCarrierReal (M + 1) q hqpos.le hq1 S
  let nonGreen : ℝ → ℂ :=
    canonicalC3IndependentReflectedNonGreenRealDiagonalResponse M q hqpos.le hq1 S
  have hsplit : nonGreen = fun t => response t - prefactor t * carrier t := by
    funext t
    dsimp only [response, prefactor, carrier, nonGreen]
    calc
      canonicalC3IndependentReflectedNonGreenRealDiagonalResponse M q hqpos.le hq1 S t =
          canonicalC3IndependentReflectedResponsePrefactorReal t *
              canonicalC3IndependentReflectedUndressedGreenCarrierReal
                (M + 1) q hqpos.le hq1 S t +
            canonicalC3IndependentReflectedNonGreenRealDiagonalResponse M q hqpos.le hq1 S t -
              canonicalC3IndependentReflectedResponsePrefactorReal t *
                canonicalC3IndependentReflectedUndressedGreenCarrierReal
                  (M + 1) q hqpos.le hq1 S t := by ring
      _ = response t - prefactor t * carrier t := by
        rw [← canonicalC3BracketTfvdSixAnalysisRealResponse_eq_prefactor_mul_undressedGreen_add_nonGreen
          M q hqpos hq1 S t]
  change ContDiffAt ℝ n nonGreen 0
  rw [hsplit]
  exact
    (canonicalC3BracketTfvdSixAnalysisRealResponse_contDiffAt M q hqpos hq1 S n).sub
      ((canonicalC3IndependentReflectedResponsePrefactorReal_contDiffAt n).mul
        (canonicalC3IndependentReflectedUndressedGreenCarrierReal_contDiffAt
          (M + 1) q hqpos.le hq1 S n))

/-- The canonical index `p` carries the real-diagonal non-Green derivative
of literal order `p + 1`.  This name makes the shift explicit instead of
hiding it in notation. -/
def canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder
    (M p : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) : ℂ :=
  canonicalC3IndependentReflectedNonGreenRealJetCoefficient M q hq0 hq1 S (p + 1)

/-- The canonical six-analysis jet is an all-order real-axis convolution of
the nonconstant response prefactor with literal-order undressed Green jets,
plus the retained real non-Green remainder.  No complex derivative is taken
of the conjugate physical section or of the radial dressing. -/
theorem canonicalC3BracketTfvdSixAnalysisJetCoefficient_eq_undressedGreen_convolution_add_realRemainder
    (M p : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisJetCoefficient M p q hqpos.le hq1 S =
      (∑ j ∈ Finset.range (p + 1 + 1),
        canonicalC3IndependentReflectedResponsePrefactorJetCoefficient (p + 1 - j) *
          canonicalC3IndependentReflectedUndressedGreenJetCoefficient
            (M + 1) j q hqpos.le hq1 S 0) +
        canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder
          M p q hqpos.le hq1 S := by
  let response : ℝ → ℂ :=
    canonicalC3BracketTfvdSixAnalysisRealResponse M q hqpos.le hq1 S
  let prefactor : ℝ → ℂ := canonicalC3IndependentReflectedResponsePrefactorReal
  let carrier : ℝ → ℂ :=
    canonicalC3IndependentReflectedUndressedGreenCarrierReal (M + 1) q hqpos.le hq1 S
  let nonGreen : ℝ → ℂ :=
    canonicalC3IndependentReflectedNonGreenRealDiagonalResponse M q hqpos.le hq1 S
  have hsplit : response = fun t => prefactor t * carrier t + nonGreen t := by
    funext t
    dsimp only [response, prefactor, carrier, nonGreen]
    exact canonicalC3BracketTfvdSixAnalysisRealResponse_eq_prefactor_mul_undressedGreen_add_nonGreen
      M q hqpos hq1 S t
  have hproduct : ContDiffAt ℝ (p + 1) (fun t => prefactor t * carrier t) 0 := by
    dsimp only [prefactor, carrier]
    exact (canonicalC3IndependentReflectedResponsePrefactorReal_contDiffAt (p + 1)).mul
      (canonicalC3IndependentReflectedUndressedGreenCarrierReal_contDiffAt
        (M + 1) q hqpos.le hq1 S (p + 1))
  have hnonGreen : ContDiffAt ℝ (p + 1) nonGreen 0 := by
    dsimp only [nonGreen]
    exact canonicalC3IndependentReflectedNonGreenRealDiagonalResponse_contDiffAt
      M q hqpos hq1 S (p + 1)
  have hadd :
      factorialNormalizedRealJetCoefficient
          (fun t => prefactor t * carrier t + nonGreen t) (p + 1) =
        factorialNormalizedRealJetCoefficient
            (fun t => prefactor t * carrier t) (p + 1) +
          factorialNormalizedRealJetCoefficient nonGreen (p + 1) := by
    unfold factorialNormalizedRealJetCoefficient
    change iteratedDeriv (p + 1) ((fun t => prefactor t * carrier t) + nonGreen) 0 /
        ((p + 1).factorial : ℂ) = _
    rw [iteratedDeriv_add hproduct hnonGreen]
    ring
  rw [canonicalC3BracketTfvdSixAnalysisJetCoefficient_eq_realDerivative
    M p q hqpos hq1 S]
  change factorialNormalizedRealJetCoefficient response (p + 1) = _
  rw [hsplit, hadd,
    factorialNormalizedRealJetCoefficient_mul_eq_convolution
      (canonicalC3IndependentReflectedResponsePrefactorReal_contDiffAt (p + 1))
      (canonicalC3IndependentReflectedUndressedGreenCarrierReal_contDiffAt
        (M + 1) q hqpos.le hq1 S (p + 1))]
  simp_rw [factorialNormalizedRealJetCoefficient_prefactor_eq_complex,
    factorialNormalizedRealJetCoefficient_undressedGreenCarrier_eq_complex]
  rfl

/-- Substituting the established fixed-atlas pairwise jet sum yields the
camera-pairwise triangular expansion of the canonical jet. -/
theorem canonicalC3BracketTfvdSixAnalysisJetCoefficient_eq_cameraPairwise_undressedGreen_convolution_add_realRemainder
    (M p : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisJetCoefficient M p q hqpos.le hq1 S =
      (∑ j ∈ Finset.range (p + 1 + 1),
        canonicalC3IndependentReflectedResponsePrefactorJetCoefficient (p + 1 - j) *
          (∑ directCamera ∈ canonicalFiniteCameraAtlas (M + 1),
            ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas (M + 1),
              canonicalC3CameraResolvedIndependentReflectedUndressedGreenJetCoefficient
                (M + 1) j q hqpos.le hq1 S 0 directCamera reflectedCamera)) +
        canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder
          M p q hqpos.le hq1 S := by
  rw [canonicalC3BracketTfvdSixAnalysisJetCoefficient_eq_undressedGreen_convolution_add_realRemainder
    M p q hqpos hq1 S]
  apply congrArg (fun z : ℂ => z +
    canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder M p q hqpos.le hq1 S)
  apply Finset.sum_congr rfl
  intro j _
  rw [canonicalC3IndependentReflectedUndressedGreenJetCoefficient_eq_cameraPairwise_sum]

/-- The corrected chiral coefficient inherits the same real-axis triangular
decomposition only as a downstream corollary of the six-analysis identity. -/
theorem canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_cameraPairwise_undressedGreen_convolution_add_realRemainder
    (M p : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p =
      (∑ j ∈ Finset.range (p + 1 + 1),
        canonicalC3IndependentReflectedResponsePrefactorJetCoefficient (p + 1 - j) *
          (∑ directCamera ∈ canonicalFiniteCameraAtlas (M + 1),
            ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas (M + 1),
              canonicalC3CameraResolvedIndependentReflectedUndressedGreenJetCoefficient
                (M + 1) j q hqpos.le hq1 S 0 directCamera reflectedCamera)) +
        canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder
          M p q hqpos.le hq1 S := by
  rw [canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_sixAnalysisJet
    M p q hqpos hq1 S]
  exact canonicalC3BracketTfvdSixAnalysisJetCoefficient_eq_cameraPairwise_undressedGreen_convolution_add_realRemainder
    M p q hqpos hq1 S

/-! ## Low-order shape checks -/

/-- At canonical index zero, the literal derivative order is one. -/
theorem canonicalC3BracketTfvdSixAnalysisJetCoefficient_zero_eq_undressedGreen_convolution_add_realRemainder
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisJetCoefficient M 0 q hqpos.le hq1 S =
      canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 1 *
          canonicalC3IndependentReflectedUndressedGreenJetCoefficient
            (M + 1) 0 q hqpos.le hq1 S 0 +
        canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 0 *
          canonicalC3IndependentReflectedUndressedGreenJetCoefficient
            (M + 1) 1 q hqpos.le hq1 S 0 +
        canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder
          M 0 q hqpos.le hq1 S := by
  simpa [Finset.sum_range_succ] using
    canonicalC3BracketTfvdSixAnalysisJetCoefficient_eq_undressedGreen_convolution_add_realRemainder
      M 0 q hqpos hq1 S

/-- At canonical index one, the literal derivative order is two. -/
theorem canonicalC3BracketTfvdSixAnalysisJetCoefficient_one_eq_undressedGreen_convolution_add_realRemainder
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisJetCoefficient M 1 q hqpos.le hq1 S =
      canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 2 *
          canonicalC3IndependentReflectedUndressedGreenJetCoefficient
            (M + 1) 0 q hqpos.le hq1 S 0 +
        canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 1 *
          canonicalC3IndependentReflectedUndressedGreenJetCoefficient
            (M + 1) 1 q hqpos.le hq1 S 0 +
        canonicalC3IndependentReflectedResponsePrefactorJetCoefficient 0 *
          canonicalC3IndependentReflectedUndressedGreenJetCoefficient
            (M + 1) 2 q hqpos.le hq1 S 0 +
        canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder
          M 1 q hqpos.le hq1 S := by
  simpa [Finset.sum_range_succ] using
    canonicalC3BracketTfvdSixAnalysisJetCoefficient_eq_undressedGreen_convolution_add_realRemainder
      M 1 q hqpos hq1 S

/-- At canonical index two, the literal derivative order is three. -/
theorem canonicalC3BracketTfvdSixAnalysisJetCoefficient_two_eq_undressedGreen_convolution_add_realRemainder
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisJetCoefficient M 2 q hqpos.le hq1 S =
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
            (M + 1) 3 q hqpos.le hq1 S 0 +
        canonicalC3IndependentReflectedNonGreenRealCanonicalJetRemainder
          M 2 q hqpos.le hq1 S := by
  simpa [Finset.sum_range_succ] using
    canonicalC3BracketTfvdSixAnalysisJetCoefficient_eq_undressedGreen_convolution_add_realRemainder
      M 2 q hqpos hq1 S

end

end CarrySelfAdjointOperator
