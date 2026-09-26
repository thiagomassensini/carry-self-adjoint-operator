import CarrySelfAdjointOperator.CompletedNativeIndependentReflectedRemainderCompleted
import Mathlib.Tactic

/-!
# Local vanishing of the sewn undressed Green carrier

The all-order vanishing theorem in the preceding file concerns the sewn total
undressed Green boundary.  Here it is converted, using the canonical analytic
power series at the origin, into a local functional statement.  No assertion
is made about an individual camera-pair kernel.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section
set_option autoImplicit false

/-! ## The canonical analytic series -/

/-- The scalar coefficient of the canonical analytic series for the fixed
direct-coordinate carrier is definitionally its literal-order undressed Green
jet. -/
theorem canonicalC3IndependentReflectedUndressedGreenCarrier_powerSeriesCoefficient_eq_jet
    (M k : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    iteratedDeriv k
        (canonicalC3IndependentReflectedUndressedGreenCarrier M q hq0 hq1 S) 0 /
        (k.factorial : ℂ) =
      canonicalC3IndependentReflectedUndressedGreenJetCoefficient M k q hq0 hq1 S 0 := by
  rfl

/-- At the shifted cutoff, every coefficient of the carrier's canonical
analytic series vanishes.  This includes literal order zero through the
separately established central gate. -/
theorem canonicalC3IndependentReflectedUndressedGreenCarrier_powerSeriesCoefficient_eq_zero
    (M k : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    iteratedDeriv k
        (canonicalC3IndependentReflectedUndressedGreenCarrier
          (M + 1) q hqpos.le hq1 S) 0 /
        (k.factorial : ℂ) = 0 := by
  rw [canonicalC3IndependentReflectedUndressedGreenCarrier_powerSeriesCoefficient_eq_jet]
  exact canonicalC3IndependentReflectedUndressedGreenJetCoefficient_eq_zero
    M k q hqpos hq1 S

/-- The formal series supplied by `AnalyticAt.hasFPowerSeriesAt` for the
sewn carrier is the zero series. -/
theorem canonicalC3IndependentReflectedUndressedGreenCarrier_powerSeries_eq_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    FormalMultilinearSeries.ofScalars ℂ
        (fun k =>
          iteratedDeriv k
              (canonicalC3IndependentReflectedUndressedGreenCarrier
                (M + 1) q hqpos.le hq1 S) 0 /
            (k.factorial : ℂ)) = 0 := by
  rw [FormalMultilinearSeries.ofScalars_series_eq_zero]
  funext k
  exact canonicalC3IndependentReflectedUndressedGreenCarrier_powerSeriesCoefficient_eq_zero
    M k q hqpos hq1 S

/-! ## Germ-level consequences -/

/-- The sewn total undressed Green carrier vanishes as an analytic germ at the
center.  This is a local conclusion only; it makes no claim away from `0`. -/
theorem canonicalC3IndependentReflectedUndressedGreenCarrier_eventuallyEq_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3IndependentReflectedUndressedGreenCarrier
      (M + 1) q hqpos.le hq1 S =ᶠ[nhds 0] 0 := by
  have hseries :=
    (canonicalC3IndependentReflectedUndressedGreenCarrier_analyticAt_zero
      (M + 1) q hqpos.le hq1 S).hasFPowerSeriesAt
  rw [canonicalC3IndependentReflectedUndressedGreenCarrier_powerSeries_eq_zero
    M q hqpos hq1 S] at hseries
  exact hseries.eventually_eq_zero

/-- This theorem proves only the vanishing of the finite sewn camera-pair
sum.  It does not imply the vanishing of any individual pair kernel. -/
theorem canonicalC3IndependentReflectedUndressedGreenCameraPairwiseSum_eventuallyEq_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (fun v : ℂ =>
      ∑ directCamera ∈ canonicalFiniteCameraAtlas (M + 1),
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas (M + 1),
          canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
            (M + 1) q hqpos.le hq1 S 0 v directCamera reflectedCamera) =ᶠ[nhds 0] 0 := by
  filter_upwards [canonicalC3IndependentReflectedUndressedGreenCarrier_eventuallyEq_zero
    M q hqpos hq1 S] with v hv
  rw [← canonicalC3IndependentReflectedUndressedGreenBoundary_eq_cameraPairwise]
  simpa [canonicalC3IndependentReflectedUndressedGreenCarrier] using hv

/-- For each fixed direct coordinate, the normalized response has the
compensation as its germ in the reflected variable. -/
theorem canonicalC3IndependentReflectedNormalizedResponse_eventuallyEq_compensation
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) :
    (fun v => canonicalC3IndependentReflectedNormalizedResponse
      M q hqpos.le hq1 S u v) =ᶠ[nhds 0]
      (fun v => canonicalC3IndependentReflectedUndressedCompensationResponse
        M q hqpos.le hq1 S u v) := by
  filter_upwards [canonicalC3IndependentReflectedUndressedGreenCarrier_eventuallyEq_zero
    M q hqpos hq1 S] with v hv
  rw [canonicalC3IndependentReflectedNormalizedResponse_eq_undressedGreen_add_compensation,
    canonicalC3IndependentReflectedUndressedGreenResponse_eq_prefactor_mul_carrier, hv]
  simp

/-- The real canonical response agrees locally with the real non-Green
diagonal response.  This is a corollary of the complex germ statement, not a
termwise complex differentiation of the conjugate section. -/
theorem canonicalC3BracketTfvdSixAnalysisRealResponse_eventuallyEq_nonGreen
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisRealResponse M q hqpos.le hq1 S =ᶠ[nhds 0]
      canonicalC3IndependentReflectedNonGreenRealDiagonalResponse
        M q hqpos.le hq1 S := by
  have hcarrierReal :
      canonicalC3IndependentReflectedUndressedGreenCarrierReal
        (M + 1) q hqpos.le hq1 S =ᶠ[nhds 0] 0 := by
    have htend : Tendsto (fun t : ℝ => (t : ℂ)) (nhds 0) (nhds 0) := by
      change ContinuousAt Complex.ofReal 0
      exact Complex.continuous_ofReal.continuousAt
    change (fun t : ℝ =>
      canonicalC3IndependentReflectedUndressedGreenCarrier
        (M + 1) q hqpos.le hq1 S (t : ℂ)) =ᶠ[nhds 0] 0
    exact (canonicalC3IndependentReflectedUndressedGreenCarrier_eventuallyEq_zero
      M q hqpos hq1 S).comp_tendsto htend
  filter_upwards [hcarrierReal] with t ht
  rw [canonicalC3BracketTfvdSixAnalysisRealResponse_eq_prefactor_mul_undressedGreen_add_nonGreen
      M q hqpos hq1 S t,
    ht]
  simp

/-- Combining the local real response equality with the global real-diagonal
ledger crosswalk gives the fixed-center ledger as the local response germ. -/
theorem canonicalC3BracketTfvdSixAnalysisRealResponse_eventuallyEq_fixedCenterLedger
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisRealResponse M q hqpos.le hq1 S =ᶠ[nhds 0]
      (fun t : ℝ => canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator
        (M + 1) (t : ℂ)) := by
  refine (canonicalC3BracketTfvdSixAnalysisRealResponse_eventuallyEq_nonGreen
    M q hqpos hq1 S).trans ?_
  filter_upwards [] with t
  exact canonicalC3IndependentReflectedNonGreenRealDiagonalResponse_eq_fixedCenterChannels
    M q hqpos hq1 S t

end

end CarrySelfAdjointOperator
