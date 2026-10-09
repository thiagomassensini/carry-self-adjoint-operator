import CarrySelfAdjointOperator.CompletedC3AdjacentClockGreenTransport

/-!
# Exact symmetric and imbalance coefficients of the adjacent material return

This decomposes the existing channel, retaining both complex source products.
A positive real imbalance coefficient does not sign its complex amplitude.
-/
namespace CarrySelfAdjointOperator
open CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false

/-- The two exact coefficients in the existing adjacent return. -/
theorem adjacentMaterialLogGap_decomposition (n : ℕ) (A B : ℂ) :
    positiveLogGap n * A - positiveLogGap (n + 1) * B =
      ((positiveLogGap n + positiveLogGap (n + 1)) / 2) * (A - B) +
      ((positiveLogGap n - positiveLogGap (n + 1)) / 2) * (A + B) := by ring

/-- Positive imbalance is a literal second logarithmic difference. -/
theorem adjacentMaterialLogGap_difference_eq (n : ℕ) :
    positiveLogGap n - positiveLogGap (n + 1) =
      (Real.log (1 + 1 / (((n + 1 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ))) : ℂ) := by
  have ha : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hb : (0 : ℝ) < (n + 2 : ℕ) := by positivity
  have hd : (0 : ℝ) < (n + 3 : ℕ) := by positivity
  have hratio : (1 : ℝ) + 1 / (((n + 1 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ)) =
      ((n + 2 : ℕ) : ℝ) ^ 2 / (((n + 1 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ)) := by
    field_simp
    push_cast
    ring
  rw [hratio, Real.log_div (pow_ne_zero 2 hb.ne') (mul_ne_zero ha.ne' hd.ne'),
    Real.log_pow, Real.log_mul ha.ne' hd.ne']
  simp only [positiveLogGap, Nat.add_assoc]
  push_cast
  ring

/-- A sign for the coefficient only; no source-energy inequality is inferred. -/
theorem adjacentMaterialLogGap_difference_re_pos (n : ℕ) :
    0 < (positiveLogGap n - positiveLogGap (n + 1)).re := by
  rw [adjacentMaterialLogGap_difference_eq, Complex.ofReal_re]
  apply Real.log_pos
  have h : (0 : ℝ) < 1 / (((n + 1 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ)) := by positivity
  linarith

/-- Apply the decomposition to the source products actually retained per leg.
Independent parameters z,w and both outer samples are preserved. -/
theorem canonicalC3AdjacentClockReturn_eq_symmetric_add_imbalance
    (z w : ℂ) (n : ℕ) :
    (canonicalC3AdjacentClockChannels z w n).2 =
      ((positiveLogGap n + positiveLogGap (n + 1)) / 2) *
        (positiveDirichletGradient w (n + 1) * positiveDirichletValue z n -
          positiveDirichletGradient w n * positiveDirichletValue z (n + 2)) +
      ((positiveLogGap n - positiveLogGap (n + 1)) / 2) *
        (positiveDirichletGradient w (n + 1) * positiveDirichletValue z n +
          positiveDirichletGradient w n * positiveDirichletValue z (n + 2)) := by
  simpa only [canonicalC3AdjacentClockChannels, mul_assoc] using
    adjacentMaterialLogGap_decomposition n
      (positiveDirichletGradient w (n + 1) * positiveDirichletValue z n)
      (positiveDirichletGradient w n * positiveDirichletValue z (n + 2))

end
end CarrySelfAdjointOperator
