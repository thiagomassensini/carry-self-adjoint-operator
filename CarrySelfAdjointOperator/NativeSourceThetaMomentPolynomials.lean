import CarrySelfAdjointOperator.CompletedNativeAllOrderMomentUpperBound
import Mathlib.Analysis.Polynomial.Basic

/-! A source-derived polynomial transform against the ORIGINAL positive Xi
cosine kernel. The polynomials use only characteristic coefficients. No
positive moment measure, zeros or target Gram defines this transform. -/
namespace CarrySelfAdjointOperator
open scoped BigOperators
open MeasureTheory Set Polynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem integrableOn_polynomial_mul_nativeXiKernel (P : ℝ[X]) :
    IntegrableOn (fun u : ℝ => P.eval u * completedNativeXiCosineKernel u) (Ioi 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [Polynomial.eval_add, add_mul]
    apply Integrable.add <;> assumption
  | monomial n a =>
    simpa only [IntegrableOn, Polynomial.eval_monomial, mul_assoc] using
      (integrableOn_pow_mul_completedNativeXiCosineKernel n).const_mul a

/-- Integration against the existing source kernel, with no changed measure. -/
def nativeXiPolynomialIntegral : ℝ[X] →ₗ[ℝ] ℝ where
  toFun P := ∫ u in Ioi (0 : ℝ), P.eval u * completedNativeXiCosineKernel u
  map_add' P Q := by
    simp only [Polynomial.eval_add, add_mul]
    exact integral_add (integrableOn_polynomial_mul_nativeXiKernel P)
      (integrableOn_polynomial_mul_nativeXiKernel Q)
  map_smul' a P := by
    simp only [Polynomial.eval_smul, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact integral_const_mul a _

theorem nativeXiPolynomialIntegral_monomial_even (n : ℕ) (a : ℝ) :
    nativeXiPolynomialIntegral (Polynomial.monomial (2*n) a) =
      a * completedNativeXiCosineMoment n := by
  change (∫ u in Ioi (0 : ℝ), (Polynomial.monomial (2*n) a).eval u *
    completedNativeXiCosineKernel u) = _
  simp only [Polynomial.eval_monomial, mul_assoc]
  rw [integral_const_mul]
  rfl

/-- The source derivative numerator at order n, before division by c0. -/
def nativeThetaMomentTopCoefficient (n : ℕ) : ℝ :=
  (-1 : ℝ)^n * ((n+1 : ℕ) : ℝ) / ((2*n+2).factorial : ℝ)

/-- Recursive polynomials determined by the completed characteristic itself.
The recursion is the source product equation, not a positivity fit. -/
def nativeThetaMomentPolynomial : ℕ → ℝ[X] :=
  Nat.lt_wfRel.wf.fix fun n previous =>
    (completedNativeRealEvenCharacteristicCoefficient 0)⁻¹ •
      (Polynomial.monomial (2*n+2) (nativeThetaMomentTopCoefficient n) -
        ∑ k : Fin n, completedNativeRealEvenCharacteristicCoefficient (n-k) •
          previous k k.isLt)

theorem nativeThetaMomentPolynomial_eq (n : ℕ) :
    nativeThetaMomentPolynomial n =
      (completedNativeRealEvenCharacteristicCoefficient 0)⁻¹ •
        (Polynomial.monomial (2*n+2) (nativeThetaMomentTopCoefficient n) -
          ∑ k ∈ Finset.range n, completedNativeRealEvenCharacteristicCoefficient (n-k) •
            nativeThetaMomentPolynomial k) := by
  rw [nativeThetaMomentPolynomial, WellFounded.fix_eq]
  congr 2
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dif_pos (Finset.mem_range.mp hk)]

theorem nativeXiPolynomialIntegral_top (n : ℕ) :
    nativeXiPolynomialIntegral
      (Polynomial.monomial (2*n+2) (nativeThetaMomentTopCoefficient n)) =
      -((n+1 : ℕ) : ℝ)*completedNativeRealEvenCharacteristicCoefficient (n+1) := by
  rw [show 2*n+2 = 2*(n+1) by omega, nativeXiPolynomialIntegral_monomial_even,
    completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder]
  unfold nativeThetaMomentTopCoefficient
  rw [pow_succ]
  ring

/-- Every logarithmic moment is an integral of a source-derived polynomial
against the original positive kernel, without a sign assertion on the polynomial. -/
theorem nativeThetaMomentPolynomial_integral (n : ℕ) :
    nativeXiPolynomialIntegral (nativeThetaMomentPolynomial n) =
      canonicalCompletedNativeLogDerivativeMoment n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [nativeThetaMomentPolynomial_eq, map_smul, map_sub, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [nativeXiPolynomialIntegral_top]
    have hs : (∑ k ∈ Finset.range n, completedNativeRealEvenCharacteristicCoefficient (n-k) *
        nativeXiPolynomialIntegral (nativeThetaMomentPolynomial k)) =
        ∑ k ∈ Finset.range n, canonicalCompletedNativeLogDerivativeMoment k *
          completedNativeRealEvenCharacteristicCoefficient (n-k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ih k (Finset.mem_range.mp hk), mul_comm]
    rw [hs, canonicalCompletedNativeLogDerivativeMoment_eq]
    ring

theorem nativeThetaMomentPolynomial_coeff_above (n d : ℕ) (hd : 2*n+2 < d) :
    (nativeThetaMomentPolynomial n).coeff d = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [nativeThetaMomentPolynomial_eq]
    simp only [Polynomial.coeff_smul, Polynomial.coeff_sub, Polynomial.finsetSum_coeff,
      Polynomial.coeff_monomial, smul_eq_mul]
    rw [if_neg (by omega : 2*n+2 ≠ d)]
    have hs : (∑ k ∈ Finset.range n, completedNativeRealEvenCharacteristicCoefficient (n-k) *
        (nativeThetaMomentPolynomial k).coeff d) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [ih k (Finset.mem_range.mp hk) (by have := Finset.mem_range.mp hk; omega), mul_zero]
    rw [hs]
    ring

theorem nativeThetaMomentPolynomial_coeff_top (n : ℕ) :
    (nativeThetaMomentPolynomial n).coeff (2*n+2) =
      (completedNativeRealEvenCharacteristicCoefficient 0)⁻¹ * nativeThetaMomentTopCoefficient n := by
  rw [nativeThetaMomentPolynomial_eq]
  simp only [Polynomial.coeff_smul, Polynomial.coeff_sub, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, if_true, smul_eq_mul]
  have hs : (∑ k ∈ Finset.range n, completedNativeRealEvenCharacteristicCoefficient (n-k) *
      (nativeThetaMomentPolynomial k).coeff (2*n+2)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [nativeThetaMomentPolynomial_coeff_above k _ (by have := Finset.mem_range.mp hk; omega),
      mul_zero]
  rw [hs, sub_zero]

end
end CarrySelfAdjointOperator
