import CarrySelfAdjointOperator.NativeSourceSchurThetaMasses
import CarrySelfAdjointOperator.NativeCompletedSourceFourthThetaScale
import Mathlib.Tactic

/-!
# Signed original-source cross-curvature gate

The primitives are the existing division-free native source Schur remainders.
Only the *cross-curvature budget* is an assumption; positivity of future
remainders and native boundary positivity are consequences.

The factorial-moment control below proves that the budget is stronger than
generic Stieltjes moment positivity and does not follow from the formal
source recurrence alone.  It is NOT a counterexample to the C2 source.
-/

namespace CarrySelfAdjointOperator.SourceSchurCurvature
open CarrySelfAdjointOperator Polynomial
noncomputable section
set_option autoImplicit false

def evenR (n : ℕ) : ℝ := nativeSourceSchurRemainder 0 n
def oddR (n : ℕ) : ℝ := nativeSourceSchurRemainder 1 n

private theorem next_pos_of_half_cross (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (h : |a*c-b^2| < b^2/2) :
    0 < c := by
  have hlt := (abs_lt.mp h).1
  have hb2 : 0 < b^2 := sq_pos_of_pos hb
  have hprod : 0 < a*c := by nlinarith
  exact (mul_pos_iff_of_pos_left ha).mp hprod

private theorem next_pos_of_bounded_relative_cross (a b c ρ : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hρ : ρ < 1)
    (h : |a*c-b^2| < ρ*b^2) :
    0 < c := by
  have hlo := (abs_lt.mp h).1
  have hb2 : 0 < b^2 := sq_pos_of_pos hb
  have hbrest : 0 < (1-ρ)*b^2 :=
    mul_pos (sub_pos.mpr hρ) hb2
  have hprod : 0 < a*c := by nlinarith
  exact (mul_pos_iff_of_pos_left ha).mp hprod

/-- Any strict relative curvature budget below one propagates positivity.
The 1/2 threshold is numerical reconnaissance, not needed in the theorem. -/
theorem cross_curvature_propagates_sign_of_bounded_budget
    (e o : ℕ → ℝ) (ρ : ℝ)
    (he0 : 0 < e 0) (ho0 : 0 < o 0) (hρ : ρ < 1)
    (hodd : ∀ n, |e n * e (n+1) - (o n)^2| < ρ*(o n)^2)
    (heven : ∀ n, |o n * o (n+1) - (e (n+1))^2| <
       ρ*(e (n+1))^2) :
    ∀ n, 0 < e n ∧ 0 < o n := by
  intro n
  induction n with
  | zero => exact ⟨he0, ho0⟩
  | succ n ih =>
    obtain ⟨he, ho⟩ := ih
    have he' : 0 < e (n+1) :=
      next_pos_of_bounded_relative_cross (e n) (o n) (e (n+1))
        ρ he ho hρ (hodd n)
    have ho' : 0 < o (n+1) :=
      next_pos_of_bounded_relative_cross (o n) (e (n+1)) (o (n+1))
        ρ ho he' hρ (heven n)
    exact ⟨he', ho'⟩

theorem cross_curvature_propagates_sign (e o : ℕ → ℝ)
    (he0 : 0 < e 0) (ho0 : 0 < o 0)
    (hodd : ∀ n, |e n * e (n+1) - (o n)^2| < (o n)^2/2)
    (heven : ∀ n, |o n * o (n+1) - (e (n+1))^2| < (e (n+1))^2/2) :
    ∀ n, 0 < e n ∧ 0 < o n := by
  intro n
  induction n with
  | zero => exact ⟨he0, ho0⟩
  | succ n ih =>
    obtain ⟨he, ho⟩ := ih
    have he' : 0 < e (n+1) :=
      next_pos_of_half_cross (e n) (o n) (e (n+1)) he ho (hodd n)
    have ho' : 0 < o (n+1) :=
      next_pos_of_half_cross (o n) (e (n+1)) (o (n+1))
        ho he' (heven n)
    exact ⟨he', ho'⟩

/-- Original-source boundary positivity for any fixed budget ρ < 1.
The hypotheses are the unresolved source-sign problem. -/
theorem source_signs_of_bounded_relative_curvature (ρ : ℝ) (hρ : ρ < 1)
    (he0 : 0 < evenR 0) (ho0 : 0 < oddR 0)
    (hodd : ∀ n,
      |evenR n * evenR (n+1) - (oddR n)^2| < ρ*(oddR n)^2)
    (heven : ∀ n,
      |oddR n * oddR (n+1) - (evenR (n+1))^2| <
        ρ*(evenR (n+1))^2) :
    ∀ n, 0 < evenR n ∧ 0 < oddR n :=
  cross_curvature_propagates_sign_of_bounded_budget evenR oddR ρ
    he0 ho0 hρ hodd heven

theorem evenR_zero_pos : 0 < evenR 0 := by
  have hc : 0 < completedNativeRealEvenCharacteristicCoefficient 0 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/3)
      completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  have hm : 0 < canonicalCompletedNativeLogDerivativeMoment 0 := by
    have h := nativeSourceMixedLeadingCoefficients_pos.1
    rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
      primeDepthGeometricMoment_eq_canonical] at h
    linarith
  change 0 < nativeSourceSchurRemainder 0 0
  rw [nativeSourceSchurRemainder_eq]
  simpa [sourceMomentSchur, dotProduct] using mul_pos hc hm

theorem oddR_zero_pos : 0 < oddR 0 :=
  nativeSourceSchurRemainder_first_odd_pos

/-- Exact decomposition: the absolute bound contains both a lower and an
upper source-balance obligation.  Only the lower one is needed for sign. -/
theorem abs_cross_curvature_iff_two_sided (a b c ρ : ℝ) :
    |a*c-b^2| < ρ*b^2 ↔
      (1-ρ)*b^2 < a*c ∧ a*c < (1+ρ)*b^2 := by
  rw [abs_lt]
  constructor
  · intro h
    constructor <;> nlinarith [h.1, h.2]
  · intro h
    constructor <;> nlinarith [h.1, h.2]

private theorem next_pos_of_one_sided (a b c ρ : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hρ : ρ < 1)
    (hlower : (1-ρ)*b^2 < a*c) :
    0 < c := by
  have hb2 : 0 < b^2 := sq_pos_of_pos hb
  have hprod : 0 < a*c := lt_trans
    (mul_pos (sub_pos.mpr hρ) hb2) hlower
  exact (mul_pos_iff_of_pos_left ha).mp hprod

/-- One-sided source conditions suffice for positivity in all orders.
This is strictly weaker than the two-sided balanced-curvature condition. -/
theorem native_boundary_pos_of_one_sided_cross_curvature (ρ : ℝ)
    (hρ : ρ < 1)
    (hodd : ∀ n,
      (1-ρ)*(oddR n)^2 < evenR n*evenR (n+1))
    (heven : ∀ n,
      (1-ρ)*(evenR (n+1))^2 < oddR n*oddR (n+1)) :
    ∀ n : ℕ, 1 ≤ n → ∀ x : Fin (2*n) → ℂ, x ≠ 0 →
      0 < nativeSourceFiniteBoundaryEnergy (2*n) x := by
  have hp : ∀ n : ℕ, 0 < evenR n ∧ 0 < oddR n := by
    intro n
    induction n with
    | zero => exact ⟨evenR_zero_pos, oddR_zero_pos⟩
    | succ n ih =>
      obtain ⟨he, ho⟩ := ih
      have he' : 0 < evenR (n+1) :=
        next_pos_of_one_sided (evenR n) (oddR n) (evenR (n+1))
          ρ he ho hρ (hodd n)
      have ho' : 0 < oddR (n+1) :=
        next_pos_of_one_sided (oddR n) (evenR (n+1)) (oddR (n+1))
          ρ ho he' hρ (heven n)
      exact ⟨he', ho'⟩
  apply nativeSourceBoundary_all_pos_iff_sourceSchur.mpr
  intro n
  simpa only [evenR, oddR] using hp n

theorem native_boundary_pos_of_bounded_cross_curvature (ρ : ℝ)
    (hρ : ρ < 1)
    (hodd : ∀ n,
      |evenR n * evenR (n+1) - (oddR n)^2| < ρ*(oddR n)^2)
    (heven : ∀ n,
      |oddR n * oddR (n+1) - (evenR (n+1))^2| <
        ρ*(evenR (n+1))^2) :
    ∀ n : ℕ, 1 ≤ n → ∀ x : Fin (2*n) → ℂ, x ≠ 0 →
      0 < nativeSourceFiniteBoundaryEnergy (2*n) x := by
  apply nativeSourceBoundary_all_pos_iff_sourceSchur.mpr
  exact source_signs_of_bounded_relative_curvature ρ hρ
    evenR_zero_pos oddR_zero_pos hodd heven

theorem native_boundary_pos_of_half_cross_curvature
    (hodd : ∀ n,
      |evenR n * evenR (n+1) - (oddR n)^2| < (oddR n)^2/2)
    (heven : ∀ n,
      |oddR n * oddR (n+1) - (evenR (n+1))^2| <
        (evenR (n+1))^2/2) :
    ∀ n : ℕ, 1 ≤ n → ∀ x : Fin (2*n) → ℂ, x ≠ 0 →
      0 < nativeSourceFiniteBoundaryEnergy (2*n) x := by
  have hp := cross_curvature_propagates_sign evenR oddR
    evenR_zero_pos oddR_zero_pos hodd heven
  apply nativeSourceBoundary_all_pos_iff_sourceSchur.mpr
  intro n
  simpa only [evenR, oddR] using hp n

theorem native_radial_return_contractive_of_half_cross_curvature
    (hodd : ∀ n,
      |evenR n * evenR (n+1) - (oddR n)^2| < (oddR n)^2/2)
    (heven : ∀ n,
      |oddR n * oddR (n+1) - (evenR (n+1))^2| <
        (evenR (n+1))^2/2) :
    ∀ N : ℕ, ∀ᶠ k : ℕ in Filter.atTop,
      ‖ChiralReturn.radialReturnTransfer k N‖ ≤ 1 := by
  apply radialReturnTransfer_all_orders_of_sourceSchur
  exact cross_curvature_propagates_sign evenR oddR
    evenR_zero_pos oddR_zero_pos hodd heven

/-- The exact source polynomial mass difference is not assumed positive. -/
def signedThetaMass (s n : ℕ) : ℝ :=
  nativeThetaPositiveMass (nativeSchurThetaPolynomial s n) -
    nativeThetaNegativeMass (nativeSchurThetaPolynomial s n)

theorem evenR_eq_signedThetaMass (n : ℕ) :
    evenR n = signedThetaMass 0 n := by
  exact nativeSourceSchurRemainder_eq_thetaMasses 0 n

theorem oddR_eq_signedThetaMass (n : ℕ) :
    oddR n = signedThetaMass 1 n := by
  exact nativeSourceSchurRemainder_eq_thetaMasses 1 n

/-- A counterexample from a strictly positive compact Stieltjes measure:
the moments of Lebesgue measure on [0,1] are 1/(n+1). -/
def uniformMoment (n : ℕ) : ℝ := 1 / ((n+1 : ℕ) : ℝ)

theorem uniform_even_zero : sourceMomentSchur uniformMoment 0 0 = 1 := by
  norm_num [sourceMomentSchur, uniformMoment, dotProduct]

theorem uniform_odd_zero : sourceMomentSchur uniformMoment 1 0 = 1/2 := by
  norm_num [sourceMomentSchur, uniformMoment, dotProduct]

theorem uniform_even_one : sourceMomentSchur uniformMoment 0 1 = 1/12 := by
  rw [SourcePositiveReduction.sourceMomentSchur_singleton]
  norm_num [uniformMoment]

theorem compact_uniform_control_breaks_half_gate :
    ¬ (|sourceMomentSchur uniformMoment 0 0 *
          sourceMomentSchur uniformMoment 0 1 -
          (sourceMomentSchur uniformMoment 1 0)^2| <
          (sourceMomentSchur uniformMoment 1 0)^2/2) := by
  rw [uniform_even_zero, uniform_even_one, uniform_odd_zero]
  norm_num

/-!
## Universal top-symbol balance of the original signed theta Schur polynomials

By `nativeSchurThetaPolynomial_coeff_top` the even/odd leading
coefficients are respectively +(2n+1)/(4n+2)! and -(2n+2)/(4n+4)!.
The adjacent top-symbol product ratios reduce to the explicit functions
below. Both approach 1 from below at rate O(1/n).
This is a statement about leading symbols, NOT about integrals or
positivity of the completed source Schur remainders.
-/

private theorem factorial_step_two (k : ℕ) :
    ((k+2).factorial : ℝ) =
      ((k+2 : ℕ) : ℝ) * ((k+1 : ℕ) : ℝ) * (k.factorial : ℝ) := by
  rw [show k+2=(k+1)+1 by omega, Nat.factorial_succ,
      Nat.cast_mul, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring

def evenLead (n : ℕ) : ℝ :=
  (nativeSchurThetaPolynomial 0 n).coeff (4*n+2)

def oddLead (n : ℕ) : ℝ :=
  (nativeSchurThetaPolynomial 1 n).coeff (4*n+4)

theorem evenLead_eq (n : ℕ) :
    evenLead n = ((2*n+1 : ℕ) : ℝ) / ((4*n+2).factorial : ℝ) := by
  rw [evenLead, show 4*n+2=2*(2*n+0)+2 by omega,
    nativeSchurThetaPolynomial_coeff_top]
  norm_num

theorem oddLead_eq (n : ℕ) :
    oddLead n = - ((2*n+2 : ℕ) : ℝ) / ((4*n+4).factorial : ℝ) := by
  rw [oddLead, show 4*n+4=2*(2*n+1)+2 by omega,
    nativeSchurThetaPolynomial_coeff_top]
  norm_num
  ring

theorem factorial_even_odd_steps (n : ℕ) :
    ((4*n+4).factorial : ℝ) =
       ((4*n+4 : ℕ) : ℝ) * ((4*n+3 : ℕ) : ℝ) *
         ((4*n+2).factorial : ℝ) := by
  convert factorial_step_two (4*n+2) using 1

theorem factorial_odd_even_steps (n : ℕ) :
    ((4*n+6).factorial : ℝ) =
       ((4*n+6 : ℕ) : ℝ) * ((4*n+5 : ℕ) : ℝ) *
         ((4*n+4).factorial : ℝ) := by
  convert factorial_step_two (4*n+4) using 1

theorem actual_top_odd_product_ratio (n : ℕ) :
    evenLead n * evenLead (n+1) *
       (2 * ((n+1:ℕ):ℝ) * ((4*n+5:ℕ):ℝ)) =
       (oddLead n)^2 * (((2*n+1:ℕ):ℝ) * ((4*n+3:ℕ):ℝ)) := by
  rw [evenLead_eq, evenLead_eq, oddLead_eq]
  have h34 := factorial_even_odd_steps n
  have h56 := factorial_odd_even_steps n
  have hF : ((4*n+2).factorial:ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (4*n+2))
  have h3 : (0:ℝ) < ((4*n+3:ℕ):ℝ) := by positivity
  have h4 : (0:ℝ) < ((4*n+4:ℕ):ℝ) := by positivity
  have h5 : (0:ℝ) < ((4*n+5:ℕ):ℝ) := by positivity
  have h6 : (0:ℝ) < ((4*n+6:ℕ):ℝ) := by positivity
  rw [show 4*(n+1)+2=4*n+6 by omega,
      show 2*(n+1)+1=2*n+3 by omega,
      h56, h34]
  field_simp
  push_cast
  ring

theorem actual_top_even_product_ratio (n : ℕ) :
    oddLead n * oddLead (n+1) *
      (((2*(n+1)+1:ℕ):ℝ)*((4*(n+1)+3:ℕ):ℝ)) =
      (evenLead (n+1))^2 *
        (2*((n+1:ℕ):ℝ)*((4*(n+1)+1:ℕ):ℝ)) := by
  rw [oddLead_eq, oddLead_eq, evenLead_eq]
  have hF := factorial_odd_even_steps n
  have hG : ((4*n+8).factorial:ℝ) =
      ((4*n+8:ℕ):ℝ)*((4*n+7:ℕ):ℝ)*((4*n+6).factorial:ℝ) := by
    simpa [Nat.mul_add, Nat.add_assoc] using factorial_even_odd_steps (n+1)
  have h0 : ((4*n+4).factorial:ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (4*n+4)
  rw [show 4*(n+1)+4=4*n+8 by omega,
      show 4*(n+1)+2=4*n+6 by omega,
      show 2*(n+1)+2=2*n+4 by omega,
      show 2*(n+1)+1=2*n+3 by omega,
      hG, hF]
  field_simp
  push_cast
  ring


/-! The negative odd leading symbol cannot itself dominate the signed
integral.  The complete lower-degree part must provide the compensation. -/
def oddLowerPolynomial (n : ℕ) : ℝ[X] :=
  nativeSchurThetaPolynomial 1 n -
    Polynomial.monomial (4*n+4) (oddLead n)

theorem oddLowerPolynomial_top_coefficient_zero (n : ℕ) :
    (oddLowerPolynomial n).coeff (4*n+4) = 0 := by
  simp [oddLowerPolynomial, oddLead]

theorem oddLead_negative (n : ℕ) : oddLead n < 0 := by
  rw [oddLead_eq]
  have hn : (0:ℝ) < ((2*n+2:ℕ):ℝ) := by positivity
  have hf : (0:ℝ) < ((4*n+4).factorial:ℝ) := by positivity
  simpa only [neg_div] using (neg_neg_of_pos (div_pos hn hf))

theorem oddR_eq_leadingMass_add_lowerIntegral (n : ℕ) :
    oddR n =
      oddLead n * completedNativeXiCosineMoment (2*n+2) +
      nativeXiPolynomialIntegral (oddLowerPolynomial n) := by
  have hsplit : nativeSchurThetaPolynomial 1 n =
      Polynomial.monomial (4*n+4) (oddLead n) +
        oddLowerPolynomial n := by
    simp [oddLowerPolynomial]
  change nativeSourceSchurRemainder 1 n = _
  rw [← nativeSchurThetaPolynomial_integral 1 n, hsplit, map_add,
    show 4*n+4 = 2*(2*n+2) by omega,
    nativeXiPolynomialIntegral_monomial_even]

/-- Positive odd source energy requires lower-degree terms to dominate
the strictly negative leading contribution (not merely to be small). -/
theorem oddR_positive_requires_lower_compensation (n : ℕ)
    (hpos : 0 < oddR n) :
    -oddLead n * completedNativeXiCosineMoment (2*n+2) <
      nativeXiPolynomialIntegral (oddLowerPolynomial n) := by
  rw [oddR_eq_leadingMass_add_lowerIntegral] at hpos
  linarith

def oddCenteredLeadingRatio (n : ℕ) : ℝ :=
  ((2*n+1 : ℕ) : ℝ) * ((4*n+3 : ℕ) : ℝ) /
    (2*((n+1 : ℕ) : ℝ)*((4*n+5 : ℕ) : ℝ))

def evenCenteredLeadingRatio (n : ℕ) : ℝ :=
  (2*(n:ℝ)*((4*n+1 : ℕ) : ℝ)) /
    (((2*n+1 : ℕ) : ℝ) * ((4*n+3 : ℕ) : ℝ))

theorem oddLeadingRatio_gap (n : ℕ) :
    1-oddCenteredLeadingRatio n =
      ((8*n+7 : ℕ) : ℝ) /
        (2*((n+1 : ℕ) : ℝ)*((4*n+5 : ℕ) : ℝ)) := by
  unfold oddCenteredLeadingRatio
  push_cast
  have h1 : (0:ℝ) < (n:ℝ)+1 := by positivity
  have h2 : (0:ℝ) < 4*(n:ℝ)+5 := by positivity
  field_simp
  ring

theorem evenLeadingRatio_gap (n : ℕ) :
    1-evenCenteredLeadingRatio n =
      ((8*n+3 : ℕ) : ℝ) /
        (((2*n+1 : ℕ) : ℝ)*((4*n+3 : ℕ) : ℝ)) := by
  unfold evenCenteredLeadingRatio
  push_cast
  have h1 : (0:ℝ) < 2*(n:ℝ)+1 := by positivity
  have h2 : (0:ℝ) < 4*(n:ℝ)+3 := by positivity
  field_simp
  ring

theorem oddLeadingRatio_strictly_below_one (n : ℕ) :
    0 < oddCenteredLeadingRatio n ∧ oddCenteredLeadingRatio n < 1 := by
  constructor
  · unfold oddCenteredLeadingRatio
    positivity
  · have hd := oddLeadingRatio_gap n
    have hp : 0 < ((8*n+7 : ℕ) : ℝ) /
      (2*((n+1 : ℕ) : ℝ)*((4*n+5 : ℕ) : ℝ)) := by positivity
    linarith

theorem evenLeadingRatio_strictly_below_one (n : ℕ) (hn : 0 < n) :
    0 < evenCenteredLeadingRatio n ∧ evenCenteredLeadingRatio n < 1 := by
  constructor
  · unfold evenCenteredLeadingRatio
    have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    positivity
  · have hd := evenLeadingRatio_gap n
    have hp : 0 < ((8*n+3 : ℕ) : ℝ) /
      (((2*n+1 : ℕ) : ℝ)*((4*n+3 : ℕ) : ℝ)) := by positivity
    linarith

theorem oddLeadingRatio_gap_le_one_over_n (n : ℕ) :
    1-oddCenteredLeadingRatio n ≤ 1/(((n+1:ℕ):ℝ)) := by
  rw [oddLeadingRatio_gap]
  push_cast
  have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hd : (0:ℝ) < 4*(n:ℝ)+5 := by positivity
  apply (div_le_div_iff₀ (by positivity) hn).mpr
  nlinarith

theorem evenLeadingRatio_gap_le_one_over_n (n : ℕ) (hn : 0 < n) :
    1-evenCenteredLeadingRatio n ≤ 1/(n:ℝ) := by
  rw [evenLeadingRatio_gap]
  push_cast
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have h1 : (0:ℝ) < 2*(n:ℝ)+1 := by positivity
  have h2 : (0:ℝ) < 4*(n:ℝ)+3 := by positivity
  apply (div_le_div_iff₀ (mul_pos h1 h2) hn').mpr
  nlinarith

theorem evenLeadingRatio_gap_le_two_over_n (n : ℕ) :
    1-evenCenteredLeadingRatio n ≤ 2/(((n+1:ℕ):ℝ)) := by
  rw [evenLeadingRatio_gap]
  push_cast
  have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
  have h1 : (0:ℝ) < 2*(n:ℝ)+1 := by positivity
  have h2 : (0:ℝ) < 4*(n:ℝ)+3 := by positivity
  apply (div_le_div_iff₀ (mul_pos h1 h2) hn).mpr
  nlinarith [sq_nonneg (n:ℝ)]

theorem oddLeadingRatio_tendsto_one :
    Filter.Tendsto oddCenteredLeadingRatio Filter.atTop (nhds 1) := by
  have hLo (n : ℕ) : 0 ≤ 1-oddCenteredLeadingRatio n := by
    rw [oddLeadingRatio_gap]
    positivity
  have hZero : Filter.Tendsto (fun n : ℕ => 1-oddCenteredLeadingRatio n)
      Filter.atTop (nhds (0:ℝ)) :=
    squeeze_zero hLo oddLeadingRatio_gap_le_one_over_n
      (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  convert ((tendsto_const_nhds (x := (1:ℝ))).sub hZero) using 1
  · ext n; ring
  · norm_num

theorem evenLeadingRatio_tendsto_one :
    Filter.Tendsto evenCenteredLeadingRatio Filter.atTop (nhds 1) := by
  have hLo (n : ℕ) : 0 ≤ 1-evenCenteredLeadingRatio n := by
    rw [evenLeadingRatio_gap]
    positivity
  have hZero : Filter.Tendsto (fun n : ℕ => 1-evenCenteredLeadingRatio n)
      Filter.atTop (nhds (0:ℝ)) :=
    squeeze_zero hLo evenLeadingRatio_gap_le_two_over_n
      (by simpa [div_eq_mul_inv] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2:ℝ))
  convert ((tendsto_const_nhds (x := (1:ℝ))).sub hZero) using 1
  · ext n; ring
  · norm_num

/-- Independent positive-measure control: the moments of exp(-x) dx.
Their complete Stieltjes positivity is a classical fact; we use here
only the first two Schur eliminations. -/
def factorialMoment (n : ℕ) : ℝ := n.factorial

theorem factorial_even_zero : sourceMomentSchur factorialMoment 0 0 = 1 := by
  norm_num [sourceMomentSchur, factorialMoment, dotProduct]

theorem factorial_odd_zero : sourceMomentSchur factorialMoment 1 0 = 1 := by
  norm_num [sourceMomentSchur, factorialMoment, dotProduct]

theorem factorial_even_one : sourceMomentSchur factorialMoment 0 1 = 1 := by
  rw [SourcePositiveReduction.sourceMomentSchur_singleton]
  norm_num [factorialMoment]

theorem factorial_odd_one : sourceMomentSchur factorialMoment 1 1 = 2 := by
  rw [SourcePositiveReduction.sourceMomentSchur_singleton]
  norm_num [factorialMoment]

/-- The proposed half-curvature gate is stronger than positivity.
At the second centered triple the normalized cross-curvature equals one. -/
theorem factorial_control_breaks_half_gate :
    ¬ (|sourceMomentSchur factorialMoment 1 0 *
          sourceMomentSchur factorialMoment 1 1 -
          (sourceMomentSchur factorialMoment 0 1)^2| <
          (sourceMomentSchur factorialMoment 0 1)^2/2) := by
  rw [factorial_odd_zero, factorial_odd_one, factorial_even_one]
  norm_num

#print axioms native_boundary_pos_of_one_sided_cross_curvature
#print axioms native_boundary_pos_of_bounded_cross_curvature
#print axioms native_boundary_pos_of_half_cross_curvature
#print axioms native_radial_return_contractive_of_half_cross_curvature
#print axioms oddR_eq_leadingMass_add_lowerIntegral
#print axioms oddR_positive_requires_lower_compensation
#print axioms actual_top_odd_product_ratio
#print axioms actual_top_even_product_ratio
#print axioms oddLeadingRatio_tendsto_one
#print axioms evenLeadingRatio_tendsto_one
#print axioms oddLeadingRatio_gap
#print axioms evenLeadingRatio_gap
#print axioms compact_uniform_control_breaks_half_gate
#print axioms factorial_control_breaks_half_gate

end
end CarrySelfAdjointOperator.SourceSchurCurvature
