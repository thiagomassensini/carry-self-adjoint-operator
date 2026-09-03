import CarrySelfAdjointOperator.CompletedNativeChiralPickFactorization
import Mathlib.Tactic

/-!
# The signed chiral energy difference as a genuine quadratic norm

On the diagonal, the signed difference of the two chiral energies factors
exactly as

`‖P₊‖² − ‖P₋‖² = (1 − |q|²)·‖P₊‖²`,

where `q = completedNativeHermiteBiehlerChiralQuotient` is the Cayley transform
of `a = −F'/F` (`completedNativeNormalizedNegativeChiralTraceKernel_eq_quotient_mul_positive`
gives `P₋ = q·P₊`).  This file records the consequence:

When `q` is a *contraction* (`‖q‖ ≤ 1` — the Cayley/Schur form of the Herglotz
gate), the signed difference is a **genuine quadratic norm**: the Gram diagonal
of the explicit state `√(1 − |q|²) • P₊`.  Nothing assumes beforehand that the
difference is positive — the only input is contractivity of the quotient, from
which the positivity of the difference follows.
-/

open scoped ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

/-- **The signed chiral difference is a genuine Gram diagonal under
contraction.**  With `‖q‖ ≤ 1`, the difference of the positive and negative
chiral Gram channels equals `⟪w, w⟫` for the explicit defect state
`w = √(1 − ‖q‖²) • P₊`.  No prior positivity of the difference is assumed. -/
theorem completedNativeChiralTraceDifference_eq_defectGram_of_quotient_contraction
    {z : ℂ}
    (hzPositive : completedNativePositiveHermiteBiehlerCoordinate z ≠ 0)
    (hq : ‖completedNativeHermiteBiehlerChiralQuotient z‖ ≤ 1) :
    completedNativeNormalizedPositiveChiralTraceKernel z z -
        completedNativeNormalizedNegativeChiralTraceKernel z z =
      inner ℂ
        ((↑(Real.sqrt (1 -
              ‖completedNativeHermiteBiehlerChiralQuotient z‖ ^ 2)) : ℂ) •
          completedNativeNormalizedPositiveChiralTraceState z)
        ((↑(Real.sqrt (1 -
              ‖completedNativeHermiteBiehlerChiralQuotient z‖ ^ 2)) : ℂ) •
          completedNativeNormalizedPositiveChiralTraceState z) := by
  have hdef : (0 : ℝ) ≤ 1 - ‖completedNativeHermiteBiehlerChiralQuotient z‖ ^ 2 := by
    nlinarith [hq, norm_nonneg (completedNativeHermiteBiehlerChiralQuotient z)]
  rw [completedNativeNormalizedChiralDifference_eq_positive_mul_quotientDefect
      hzPositive hzPositive,
    completedNativeNormalizedPositiveChiralTraceKernel,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, Real.mul_self_sqrt hdef,
    mul_comm (conj (completedNativeHermiteBiehlerChiralQuotient z))
      (completedNativeHermiteBiehlerChiralQuotient z),
    Complex.mul_conj']
  push_cast
  ring

/-- **Positivity of the signed chiral difference follows from contraction.**
Since the difference is a Gram diagonal, its real part is nonnegative — the
Herglotz gate obtained from `‖q‖ ≤ 1`, not assumed. -/
theorem completedNativeChiralTraceDifference_re_nonneg_of_quotient_contraction
    {z : ℂ}
    (hzPositive : completedNativePositiveHermiteBiehlerCoordinate z ≠ 0)
    (hq : ‖completedNativeHermiteBiehlerChiralQuotient z‖ ≤ 1) :
    0 ≤ (completedNativeNormalizedPositiveChiralTraceKernel z z -
          completedNativeNormalizedNegativeChiralTraceKernel z z).re := by
  rw [completedNativeChiralTraceDifference_eq_defectGram_of_quotient_contraction
    hzPositive hq]
  have h := @inner_self_nonneg ℂ _ _ _ _
    ((↑(Real.sqrt (1 -
          ‖completedNativeHermiteBiehlerChiralQuotient z‖ ^ 2)) : ℂ) •
      completedNativeNormalizedPositiveChiralTraceState z)
  simpa using h

end

end CarrySelfAdjointOperator
