import CarrySelfAdjointOperator.CompletedNativeIndependentReflectedUndressedGreenAnalytic

/-!
# Canonical six-analysis section of the independent-reflected response

The old one-variable six-analysis response is recovered only after the
independent reflected coordinate is specialized.  This file records that
specialization before taking any derivative.  In particular, the reflected
coordinate of that section is conjugation, so the decomposition obtained here
is functional rather than a termwise complex-jet identity.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary

noncomputable section
set_option autoImplicit false

/-- The direct coordinate of the one-variable canonical section. -/
def canonicalC3SixAnalysisJetSectionDirectCoordinate (x : ℂ) : ℂ := x

/-- The reflected coordinate of the one-variable canonical section. -/
def canonicalC3SixAnalysisJetSectionReflectedCoordinate (x : ℂ) : ℂ :=
  (starRingEnd ℂ) x

@[simp] theorem canonicalC3SixAnalysisJetSectionDirectCoordinate_apply (x : ℂ) :
    canonicalC3SixAnalysisJetSectionDirectCoordinate x = x := rfl

@[simp] theorem canonicalC3SixAnalysisJetSectionReflectedCoordinate_apply (x : ℂ) :
    canonicalC3SixAnalysisJetSectionReflectedCoordinate x = (starRingEnd ℂ) x := rfl

/-- The reflected coordinate of the canonical section is not a complex
derivative direction at the center. -/
theorem canonicalC3SixAnalysisJetSectionReflectedCoordinate_not_differentiableAt_zero :
    ¬ DifferentiableAt ℂ canonicalC3SixAnalysisJetSectionReflectedCoordinate 0 := by
  change ¬ DifferentiableAt ℂ (fun x : ℂ => (starRingEnd ℂ) x) 0
  exact complexConjugation_not_differentiableAt_zero

/-- The six roles on the canonical section have the same parameter assignment
as the historical response: `z` uses `x`, `w` is central, and `reflectedZ`
uses `conj x`. -/
theorem canonicalC3SixAnalysisJetSection_roleParameter
    (x : ℂ) (role : CanonicalC3SixSourceParameterRole) :
    canonicalC3IndependentReflectedRoleParameter
        (canonicalC3SixAnalysisJetSectionDirectCoordinate x)
        (canonicalC3SixAnalysisJetSectionReflectedCoordinate x) role =
      match role with
      | .z => operatorHeightParameter x
      | .w => operatorHeightParameter 0
      | .reflectedZ => reflectedParameter (operatorHeightParameter x) := by
  cases role <;>
    simp only [canonicalC3IndependentReflectedRoleParameter,
      canonicalC3SixAnalysisJetSectionDirectCoordinate_apply,
      canonicalC3SixAnalysisJetSectionReflectedCoordinate_apply]
  exact (reflectedParameter_operatorHeightParameter_eq_operatorHeightParameter_conj x).symm

/-- The canonical six-analysis response is exactly the physical section of
the two-coordinate independent-reflected response. -/
theorem canonicalC3BracketTfvdSixAnalysisNormalizedResponse_eq_independentReflected_specialization
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (x : ℂ) :
    canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hqpos.le hq1 S x =
      canonicalC3IndependentReflectedNormalizedResponse M q hqpos.le hq1 S
        (canonicalC3SixAnalysisJetSectionDirectCoordinate x)
        (canonicalC3SixAnalysisJetSectionReflectedCoordinate x) := by
  simpa only [canonicalC3SixAnalysisJetSectionDirectCoordinate_apply,
    canonicalC3SixAnalysisJetSectionReflectedCoordinate_apply] using
    (canonicalC3IndependentReflectedNormalizedResponse_physicalSection
      M q hqpos hq1 S x).symm

/-- The normalized response-level prefactor that embeds the undressed Green
carrier into the completed response. -/
def canonicalC3IndependentReflectedResponsePrefactor (u : ℂ) : ℂ :=
  mixedHermitianWeight nativeXiCompletionFactor u 0 /
    canonicalC3BracketTfvdSixAnalysisResponseDenominator u

/-- The canonical undressed Green carrier, with its direct coordinate fixed
at the center. -/
def canonicalC3IndependentReflectedUndressedGreenCarrier
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (v : ℂ) : ℂ :=
  canonicalC3IndependentReflectedUndressedGreenBoundary M q hq0 hq1 S 0 v

/-- A pairwise undressed Green kernel is independent of its direct coordinate. -/
theorem canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel_independent_u
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u₁ u₂ v : ℂ)
    (directCamera reflectedCamera : ℕ) :
    canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
      M q hq0 hq1 S u₁ v directCamera reflectedCamera =
    canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
      M q hq0 hq1 S u₂ v directCamera reflectedCamera := by
  unfold canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
  rw [cameraResolvedIndependentReflectedUndressedDirectGreenPort_independent
      M q hq0 hq1 S u₁ v u₂ v directCamera,
    cameraResolvedIndependentReflectedUndressedReflectedGreenPort_independent_u
      M q hq0 hq1 S u₁ u₂ v reflectedCamera]

/-- The total undressed Green carrier is independent of its direct coordinate. -/
theorem canonicalC3IndependentReflectedUndressedGreenBoundary_independent_u
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u₁ u₂ v : ℂ) :
    canonicalC3IndependentReflectedUndressedGreenBoundary M q hq0 hq1 S u₁ v =
      canonicalC3IndependentReflectedUndressedGreenBoundary M q hq0 hq1 S u₂ v := by
  rw [canonicalC3IndependentReflectedUndressedGreenBoundary_eq_cameraPairwise,
    canonicalC3IndependentReflectedUndressedGreenBoundary_eq_cameraPairwise]
  apply Finset.sum_congr rfl
  intro directCamera _
  apply Finset.sum_congr rfl
  intro reflectedCamera _
  exact canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel_independent_u
    M q hq0 hq1 S u₁ u₂ v directCamera reflectedCamera

/-- The two-coordinate undressed boundary is the one-coordinate carrier. -/
theorem canonicalC3IndependentReflectedUndressedGreenBoundary_eq_carrier
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    canonicalC3IndependentReflectedUndressedGreenBoundary M q hq0 hq1 S u v =
      canonicalC3IndependentReflectedUndressedGreenCarrier M q hq0 hq1 S v := by
  unfold canonicalC3IndependentReflectedUndressedGreenCarrier
  exact canonicalC3IndependentReflectedUndressedGreenBoundary_independent_u
    M q hq0 hq1 S u 0 v

/-- The undressed Green summand at the same normalized-response level as the
full completed response. -/
def canonicalC3IndependentReflectedUndressedGreenResponse
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) : ℂ :=
  (mixedHermitianWeight nativeXiCompletionFactor u 0 *
    canonicalC3IndependentReflectedUndressedGreenBoundary (M + 1) q hq0 hq1 S u v) /
    canonicalC3BracketTfvdSixAnalysisResponseDenominator u

/-- At response level, the undressed contribution is the prefactor times the
one-coordinate undressed carrier. -/
theorem canonicalC3IndependentReflectedUndressedGreenResponse_eq_prefactor_mul_carrier
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    canonicalC3IndependentReflectedUndressedGreenResponse M q hq0 hq1 S u v =
      canonicalC3IndependentReflectedResponsePrefactor u *
        canonicalC3IndependentReflectedUndressedGreenCarrier (M + 1) q hq0 hq1 S v := by
  unfold canonicalC3IndependentReflectedUndressedGreenResponse
    canonicalC3IndependentReflectedResponsePrefactor
  rw [canonicalC3IndependentReflectedUndressedGreenBoundary_eq_carrier]
  ring

/-- The residual response after retaining the undressed Green summand.  Its
first term is the exact corrected-minus-undressed Green contribution; its
second term retains the complete non-Green response. -/
def canonicalC3IndependentReflectedUndressedCompensationResponse
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) : ℂ :=
  (mixedHermitianWeight nativeXiCompletionFactor u 0 *
    (canonicalC3IndependentReflectedCorrectedGreenBoundary (M + 1) q hq0 hq1 S u v -
      canonicalC3IndependentReflectedUndressedGreenBoundary (M + 1) q hq0 hq1 S u v)) /
    canonicalC3BracketTfvdSixAnalysisResponseDenominator u +
      canonicalC3IndependentReflectedNonGreenResponse M q hq0 hq1 S u v

/-- The Green part retained in the compensation is precisely the established
correction term, while the non-Green response remains separate. -/
theorem canonicalC3IndependentReflectedUndressedCompensationResponse_eq_greenCorrection_add_nonGreen
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    canonicalC3IndependentReflectedUndressedCompensationResponse M q hq0 hq1 S u v =
      (mixedHermitianWeight nativeXiCompletionFactor u 0 *
        ((canonicalC3IndependentReflectedRadialGreenFactor v - 1) *
          inner ℂ
            (canonicalC3IndependentReflectedUndressedDirectGreenPort
              (M + 1) q hq0 hq1 S u v).2
            (canonicalC3IndependentReflectedUndressedReflectedGreenPort
              (M + 1) q hq0 hq1 S u v).1)) /
        canonicalC3BracketTfvdSixAnalysisResponseDenominator u +
          canonicalC3IndependentReflectedNonGreenResponse M q hq0 hq1 S u v := by
  unfold canonicalC3IndependentReflectedUndressedCompensationResponse
  rw [canonicalC3IndependentReflectedCorrectedGreenBoundary_eq_undressed_add_radial]
  ring

/-- The full independent-reflected response is the response-level undressed
Green term plus the explicitly retained compensation. -/
theorem canonicalC3IndependentReflectedNormalizedResponse_eq_undressedGreen_add_compensation
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    canonicalC3IndependentReflectedNormalizedResponse M q hq0 hq1 S u v =
      canonicalC3IndependentReflectedUndressedGreenResponse M q hq0 hq1 S u v +
        canonicalC3IndependentReflectedUndressedCompensationResponse M q hq0 hq1 S u v := by
  rw [canonicalC3IndependentReflectedNormalizedResponse_eq_green_add_nonGreen]
  unfold canonicalC3IndependentReflectedNormalizedCorrectedGreenResponse
    canonicalC3IndependentReflectedUndressedGreenResponse
    canonicalC3IndependentReflectedUndressedCompensationResponse
  ring

/-- Functional crosswalk for the canonical one-variable response.  The
undressed carrier is evaluated along conjugation and is multiplied by the
literal response prefactor; no complex derivative is taken here. -/
theorem canonicalC3BracketTfvdSixAnalysisNormalizedResponse_eq_undressedGreen_add_compensation
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (x : ℂ) :
    canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hqpos.le hq1 S x =
      canonicalC3IndependentReflectedResponsePrefactor x *
        canonicalC3IndependentReflectedUndressedGreenCarrier (M + 1) q hqpos.le hq1 S
          (canonicalC3SixAnalysisJetSectionReflectedCoordinate x) +
        canonicalC3IndependentReflectedUndressedCompensationResponse M q hqpos.le hq1 S
          (canonicalC3SixAnalysisJetSectionDirectCoordinate x)
          (canonicalC3SixAnalysisJetSectionReflectedCoordinate x) := by
  calc
    canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hqpos.le hq1 S x =
        canonicalC3IndependentReflectedNormalizedResponse M q hqpos.le hq1 S
          (canonicalC3SixAnalysisJetSectionDirectCoordinate x)
          (canonicalC3SixAnalysisJetSectionReflectedCoordinate x) :=
      canonicalC3BracketTfvdSixAnalysisNormalizedResponse_eq_independentReflected_specialization
        M q hqpos hq1 S x
    _ = canonicalC3IndependentReflectedUndressedGreenResponse M q hqpos.le hq1 S
          (canonicalC3SixAnalysisJetSectionDirectCoordinate x)
          (canonicalC3SixAnalysisJetSectionReflectedCoordinate x) +
        canonicalC3IndependentReflectedUndressedCompensationResponse M q hqpos.le hq1 S
          (canonicalC3SixAnalysisJetSectionDirectCoordinate x)
          (canonicalC3SixAnalysisJetSectionReflectedCoordinate x) :=
      canonicalC3IndependentReflectedNormalizedResponse_eq_undressedGreen_add_compensation
        M q hqpos.le hq1 S _ _
    _ = canonicalC3IndependentReflectedResponsePrefactor x *
          canonicalC3IndependentReflectedUndressedGreenCarrier (M + 1) q hqpos.le hq1 S
            (canonicalC3SixAnalysisJetSectionReflectedCoordinate x) +
        canonicalC3IndependentReflectedUndressedCompensationResponse M q hqpos.le hq1 S
          (canonicalC3SixAnalysisJetSectionDirectCoordinate x)
          (canonicalC3SixAnalysisJetSectionReflectedCoordinate x) := by
      rw [canonicalC3IndependentReflectedUndressedGreenResponse_eq_prefactor_mul_carrier]
      rfl

/-- The Schwarz companion is an exact repackaging of the conjugated
undressed carrier.  This equality does not identify it with a summand of the
canonical response. -/
def canonicalC3IndependentReflectedUndressedGreenSchwarzCompanion
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (x : ℂ) : ℂ :=
  (starRingEnd ℂ)
    (canonicalC3IndependentReflectedUndressedGreenCarrier M q hq0 hq1 S
      ((starRingEnd ℂ) x))

/-- The original conjugated carrier is the conjugate of its Schwarz
companion, exactly and without a response identification. -/
theorem canonicalC3IndependentReflectedUndressedGreenCarrier_conj_eq_star_companion
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (x : ℂ) :
    canonicalC3IndependentReflectedUndressedGreenCarrier M q hq0 hq1 S
        ((starRingEnd ℂ) x) =
      (starRingEnd ℂ)
        (canonicalC3IndependentReflectedUndressedGreenSchwarzCompanion
          M q hq0 hq1 S x) := by
  change canonicalC3IndependentReflectedUndressedGreenCarrier M q hq0 hq1 S
      ((starRingEnd ℂ) x) =
    star (star (canonicalC3IndependentReflectedUndressedGreenCarrier M q hq0 hq1 S
      ((starRingEnd ℂ) x)))
  simp

/-- The old index convention is literal: index `p` selects derivative order
`p + 1`, whereas the undressed carrier coefficients use their literal order. -/
theorem canonicalC3BracketTfvdSixAnalysisJetCoefficient_eq_order_p_add_one
    (M p : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisJetCoefficient M p q hq0 hq1 S =
      iteratedDeriv (p + 1)
        (canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hq0 hq1 S) 0 /
          (p + 1).factorial := rfl

end

end CarrySelfAdjointOperator
