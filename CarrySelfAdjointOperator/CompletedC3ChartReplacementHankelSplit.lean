import CarrySelfAdjointOperator.CompletedC3AllOrderChartResponseCorrection
import CarrySelfAdjointOperator.CanonicalCompletedNativeStieltjesOperator
import Mathlib.Tactic

/-!
# Hankel split induced by the all-order chart replacement

The completed-native moments split exactly into a raw C3 response channel and
the response correction produced by replacing the C3 chart factor with the
xi completion factor.  This module transports that pointwise identity to both
canonical Hankel towers.

No positivity premise is used in the matrix identities.  Separate closing
lemmas record the two valid ways in which one positive-definite channel and
one positive-semidefinite channel imply completed Stieltjes positivity.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- Real odd Taylor coefficients of the raw C3 normalized response. -/
def canonicalCompletedC3RawHeightLogDerivativeMoment (n : ℕ) : ℝ :=
  (canonicalCompletedC3RawHeightResponseTaylorCoefficient (2 * n + 1)).re

/-- Real odd Taylor coefficients of the xi-minus-chart replacement response. -/
def canonicalCompletedC3ChartReplacementLogDerivativeMoment (n : ℕ) : ℝ :=
  (canonicalCompletedC3ChartReplacementResponseTaylorCoefficient
    (2 * n + 1)).re

/-- Pointwise real moment split inherited from the complex all-order response
identity. -/
theorem canonicalCompletedNativeLogDerivativeMoment_eq_raw_add_chartReplacement_real
    (n : ℕ) :
    canonicalCompletedNativeLogDerivativeMoment n =
      canonicalCompletedC3RawHeightLogDerivativeMoment n +
        canonicalCompletedC3ChartReplacementLogDerivativeMoment n := by
  have h := congrArg Complex.re
    (canonicalCompletedNativeLogDerivativeMoment_eq_raw_add_chartReplacement n)
  simpa [canonicalCompletedC3RawHeightLogDerivativeMoment,
    canonicalCompletedC3ChartReplacementLogDerivativeMoment] using h

/-- Every completed Hankel Gram section is the entrywise sum of the raw C3
and xi-minus-chart sections. -/
theorem canonicalCompletedNativeHankelGram_eq_raw_add_chartReplacement
    (N : ℕ) :
    hankelGram canonicalCompletedNativeLogDerivativeMoment N =
      hankelGram canonicalCompletedC3RawHeightLogDerivativeMoment N +
        hankelGram
          canonicalCompletedC3ChartReplacementLogDerivativeMoment N := by
  ext i j
  simp only [hankelGram_apply, Matrix.add_apply]
  exact
    canonicalCompletedNativeLogDerivativeMoment_eq_raw_add_chartReplacement_real
      ((i : ℕ) + (j : ℕ))

/-- The shifted completed Hankel section has the identical two-channel split. -/
theorem canonicalCompletedNativeShiftedHankel_eq_raw_add_chartReplacement
    (N : ℕ) :
    shiftedHankel canonicalCompletedNativeLogDerivativeMoment N =
      shiftedHankel canonicalCompletedC3RawHeightLogDerivativeMoment N +
        shiftedHankel
          canonicalCompletedC3ChartReplacementLogDerivativeMoment N := by
  ext i j
  simp only [shiftedHankel_apply, Matrix.add_apply]
  exact
    canonicalCompletedNativeLogDerivativeMoment_eq_raw_add_chartReplacement_real
      ((i : ℕ) + (j : ℕ) + 1)

/-- Raw C3 positive definiteness together with positive semidefiniteness of
the xi-minus-chart correction closes the completed Stieltjes gate. -/
theorem canonicalCompletedNativeStieltjesPositivity_of_raw_posDef_of_chartReplacement_posSemidef
    (hraw : ∀ N : ℕ,
      (hankelGram canonicalCompletedC3RawHeightLogDerivativeMoment N).PosDef ∧
        (shiftedHankel
          canonicalCompletedC3RawHeightLogDerivativeMoment N).PosDef)
    (hcorrection : ∀ N : ℕ,
      (hankelGram
          canonicalCompletedC3ChartReplacementLogDerivativeMoment N).PosSemidef ∧
        (shiftedHankel
          canonicalCompletedC3ChartReplacementLogDerivativeMoment N).PosSemidef) :
    CanonicalCompletedNativeStieltjesPositivity := by
  intro N
  rw [canonicalCompletedNativeHankelGram_eq_raw_add_chartReplacement,
    canonicalCompletedNativeShiftedHankel_eq_raw_add_chartReplacement]
  exact
    ⟨(hraw N).1.add_posSemidef (hcorrection N).1,
      (hraw N).2.add_posSemidef (hcorrection N).2⟩

/-- Dually, raw C3 positive semidefiniteness and positive definiteness of the
xi-minus-chart correction also close the completed Stieltjes gate. -/
theorem canonicalCompletedNativeStieltjesPositivity_of_raw_posSemidef_of_chartReplacement_posDef
    (hraw : ∀ N : ℕ,
      (hankelGram
          canonicalCompletedC3RawHeightLogDerivativeMoment N).PosSemidef ∧
        (shiftedHankel
          canonicalCompletedC3RawHeightLogDerivativeMoment N).PosSemidef)
    (hcorrection : ∀ N : ℕ,
      (hankelGram
          canonicalCompletedC3ChartReplacementLogDerivativeMoment N).PosDef ∧
        (shiftedHankel
          canonicalCompletedC3ChartReplacementLogDerivativeMoment N).PosDef) :
    CanonicalCompletedNativeStieltjesPositivity := by
  intro N
  rw [canonicalCompletedNativeHankelGram_eq_raw_add_chartReplacement,
    canonicalCompletedNativeShiftedHankel_eq_raw_add_chartReplacement]
  exact
    ⟨Matrix.PosDef.posSemidef_add (hraw N).1 (hcorrection N).1,
      Matrix.PosDef.posSemidef_add (hraw N).2 (hcorrection N).2⟩

end

end CarrySelfAdjointOperator
