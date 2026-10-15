import CarrySelfAdjointOperator.NativeThetaAdaptivePrefix

/-! An a priori modal rule and its scalar error budget.  The coefficient mass
is a bound on the already synthesized polynomial, not a changed source metric.
The geometric integral estimate linking the actual error to this budget is
proved in the research note, not claimed formal here.  The principal positive
lower bound remains a separate open obligation. -/
namespace CarrySelfAdjointOperator
open scoped BigOperators
open Polynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

def nativeThetaCoefficientMass (P : ℝ[X]) : ℝ := ∑ k ∈ P.support, |P.coeff k|

theorem nativeThetaCoefficientMass_nonneg (P : ℝ[X]) : 0 ≤ nativeThetaCoefficientMass P :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem nativeThetaCoefficientMass_pos_of_coeff {P : ℝ[X]} {k : ℕ} (hk : P.coeff k ≠ 0) :
    0 < nativeThetaCoefficientMass P := by
  unfold nativeThetaCoefficientMass
  exact (abs_pos.mpr hk).trans_le (Finset.single_le_sum (fun j _ => abs_nonneg (P.coeff j))
    (Polynomial.mem_support_iff.mpr hk))

/-- An estimate on the fully synthesized polynomial, with every coefficient
and ordered cross retained. -/
theorem nativeThetaPolynomial_eval_bound (P : ℝ[X]) {u : ℝ} (hu : 0 ≤ u)
    {d : ℕ} (hd : P.natDegree ≤ d) :
    |P.eval u| ≤ nativeThetaCoefficientMass P*Real.exp ((d : ℝ)*u) := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  calc
    |∑ k ∈ P.support, P.coeff k*u^k| ≤ ∑ k ∈ P.support, |P.coeff k*u^k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ P.support, |P.coeff k| *Real.exp ((d : ℝ)*u) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_of_nonneg (pow_nonneg hu k)]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hkdegree : k ≤ d := (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)).trans hd
      calc
        u^k ≤ (Real.exp u)^k := pow_le_pow_left₀ hu (by linarith [Real.add_one_le_exp u]) k
        _ = Real.exp ((k : ℝ)*u) := (Real.exp_nat_mul u k).symm
        _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkdegree) hu)
    _ = nativeThetaCoefficientMass P*Real.exp ((d : ℝ)*u) := by
      rw [nativeThetaCoefficientMass, Finset.sum_mul]

theorem nativeSchurThetaCoefficientMass_pos (s n : ℕ) :
    0 < nativeThetaCoefficientMass (nativeSchurThetaPolynomial s n) := by
  apply nativeThetaCoefficientMass_pos_of_coeff (k := 2*(2*n+s)+2)
  rw [nativeSchurThetaPolynomial_coeff_top]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)) (by positivity)) (by positivity)

def nativeThetaAdaptiveTarget (n : ℕ) (P : ℝ[X]) : ℝ :=
  nativeThetaCoefficientMass P*Real.exp (-((n : ℝ)+3)^2)

def nativeThetaAdaptiveBudget (n : ℕ) (P : ℝ[X]) : ℝ :=
  nativeThetaCoefficientMass P*(64*Real.pi*((n : ℝ)+3)^2*
    Real.exp (-Real.pi*((n : ℝ)+3)^2))

theorem nativeSchurThetaAdaptiveTarget_pos (s n : ℕ) :
    0 < nativeThetaAdaptiveTarget n (nativeSchurThetaPolynomial s n) :=
  mul_pos (nativeSchurThetaCoefficientMass_pos s n) (Real.exp_pos _)

/-- Purely scalar and uniform in n.  It does not assert that the signed
principal integral exceeds the target. -/
theorem nativeThetaAdaptiveBudget_le_half_target (n : ℕ) (P : ℝ[X]) :
    nativeThetaAdaptiveBudget n P ≤ nativeThetaAdaptiveTarget n P/2 := by
  let t : ℝ := ((n : ℝ)+3)^2
  have ht : 9 ≤ t := by dsimp [t]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have ht0 : 0 ≤ t := by linarith
  have hpow : (6561 : ℝ) ≤ t^4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9) ht 4
    norm_num at h
    exact h
  have hmul := mul_le_mul_of_nonneg_right hpow ht0
  have hpoly : 512*t ≤ (2*t)^5/120 := by nlinarith
  have hexp : (2*t)^5/120 ≤ Real.exp (2*t) := by
    have h := Real.pow_div_factorial_le_exp (2*t) (by positivity : 0 ≤ 2*t) 5
    norm_num at h
    exact h
  have hpi : 128*Real.pi*t ≤ 512*t := by nlinarith [Real.pi_lt_four]
  have he : 128*Real.pi*t ≤ Real.exp ((Real.pi-1)*t) := by
    exact (hpi.trans hpoly |>.trans hexp).trans
      (Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three]))
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-Real.pi*t)).le
  have heq : Real.exp ((Real.pi-1)*t)*Real.exp (-Real.pi*t) = Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hm
  have hhalf : 64*Real.pi*t*Real.exp (-Real.pi*t) ≤ Real.exp (-t)/2 := by nlinarith
  have h := mul_le_mul_of_nonneg_left hhalf (nativeThetaCoefficientMass_nonneg P)
  simpa only [nativeThetaAdaptiveBudget, nativeThetaAdaptiveTarget, t, mul_div_assoc] using h

end
end CarrySelfAdjointOperator
