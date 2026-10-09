import CarrySelfAdjointOperator.CompletedNativeChiralReturnMixedSourceJets
import CarrySelfAdjointOperator.PrimeDepthGeometricMomentRecurrence

/-!
# Reverse source-first boundary coefficient audit

The odd Green tower uses raw derivatives of -F'/F; the source-first response
uses -F'/(2F). This module exposes their exact all-order normalization.
No positive Gram, moment sign, new carrier, or completion truncation is used.
These are coefficient readouts AFTER the already-complete TFVD synthesis.
The even/odd formulas identify the limiting face, not finite-step crosses.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- The normalization factor is fixed by the existing companion -F'. -/
theorem completedNativeOperatorLogDerivative_eq_twice_greenResponse :
    completedNativeOperatorLogDerivative = fun z => (2 : ℂ) *
      completedGreenNormalizedResponse completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z := by
  funext z
  rw [completedGreenNormalizedResponse, completedNativeOperatorBoundaryCompanion_eq_neg_deriv]
  unfold completedNativeOperatorLogDerivative
  ring

/-- Raw source coefficients agree with the independent prime-depth response.
The canonical recursive moment sequence is not used in this proof. -/
theorem nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment (j : ℕ) :
    nativeSourceOddBoundaryCoefficient j = 2 * primeDepthGeometricMoment j := by
  unfold nativeSourceOddBoundaryCoefficient primeDepthGeometricMoment
  rw [primeDepthCompletedNativeResponseTaylorCoefficient_eq_completed]
  unfold completedNativeGreenResponseTaylorCoefficient
  rw [completedNativeOperatorLogDerivative_eq_twice_greenResponse,
    iteratedDeriv_const_mul_field]
  norm_num [Complex.mul_re, Complex.div_natCast_re]
  ring

/-- The complete tower's signed ordered boundary coefficient, including its
outer factor 2, is FOUR times the normalized geometric response coefficient. -/
theorem nativeSourceOddBoundaryCoefficient_weighted_eq_primeDepth (j a : ℕ) :
    2 * (-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j * (-1 : ℝ)^a =
      4 * (-1 : ℝ)^(j+a) * primeDepthGeometricMoment j := by
  rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment, pow_add]
  ring

/-- Even boundary block: signs are inherited from the alternating Green
identity; the response index is i+j, with no shift. -/
theorem nativeSourceEvenBoundaryCoefficient_eq_polarizedPrimeDepth (i j : ℕ) :
    2 * (-1 : ℝ)^(i+j) * nativeSourceOddBoundaryCoefficient (i+j) =
      4 * (-1 : ℝ)^(i+j) *
        (polarizedGreenMomentCoefficient primeDepthGeometricMoment (2*i) (2*j)).re := by
  rw [polarizedGreenMomentCoefficient_even_even,
    nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment]
  simp only [Complex.ofReal_re]
  ring

/-- Odd boundary block: the response index is i+j+1, with the SAME alternating
coordinate signs as the even block. -/
theorem nativeSourceOddBoundaryCoefficient_eq_polarizedPrimeDepth (i j : ℕ) :
    2 * (-1 : ℝ)^(i+j) * nativeSourceOddBoundaryCoefficient (i+j+1) =
      4 * (-1 : ℝ)^(i+j) *
        (polarizedGreenMomentCoefficient primeDepthGeometricMoment (2*i+1) (2*j+1)).re := by
  rw [polarizedGreenMomentCoefficient_odd_odd,
    nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment]
  simp only [Complex.ofReal_re]
  ring
/-- All ordered crosses in every finite Green tower remain identical after
source-first coefficient identification. No remainder term is removed: this
lemma rewrites the prefix only, after its vector synthesis. -/
theorem nativeSourceOddGreenTower_eq_primeDepth (r : ℕ) (b : ℕ → ℂ) :
    2 * (∑ j ∈ Finset.range r, (-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j *
      (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a * (conj (b a)*b (2*j-a)).re)) =
    4 * (∑ j ∈ Finset.range r, (-1 : ℝ)^j * primeDepthGeometricMoment j *
      (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a * (conj (b a)*b (2*j-a)).re)) := by
  simp_rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring
end
end CarrySelfAdjointOperator
