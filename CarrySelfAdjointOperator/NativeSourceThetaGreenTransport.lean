import CarrySelfAdjointOperator.NativeSourceSchurThetaMasses
import CarrySelfAdjointOperator.CompletedNativeXiThetaMoments

/-! The source differential identity K = A'' - A/4 gives an actual Green
flux for every polynomial. Its boundary terms are retained explicitly.
For the source Schur polynomials both central traces vanish, at every order.
The transported density is not asserted positive. -/
namespace CarrySelfAdjointOperator
open scoped BigOperators
open Polynomial MeasureTheory Set Filter XiThetaCosine
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

def nativeThetaGreenPolynomial (P : ℝ[X]) : ℝ[X] :=
  P.derivative.derivative - (1/4 : ℝ) • P

def nativeThetaGreenFlux (P : ℝ[X]) (u : ℝ) : ℝ :=
  P.eval u * thetaTailFirst u - P.derivative.eval u * thetaTail u

theorem nativeThetaGreenPolynomial_smul (a : ℝ) (P : ℝ[X]) :
    nativeThetaGreenPolynomial (a • P) = a • nativeThetaGreenPolynomial P := by
  simp only [nativeThetaGreenPolynomial, Polynomial.derivative_smul, smul_sub,
    smul_smul]
  rw [mul_comm (1/4 : ℝ) a]

theorem nativeThetaGreenPolynomial_sum {ι : Type*} (S : Finset ι) (P : ι → ℝ[X]) :
    nativeThetaGreenPolynomial (∑ i ∈ S, P i) =
      ∑ i ∈ S, nativeThetaGreenPolynomial (P i) := by
  simp only [nativeThetaGreenPolynomial, Polynomial.derivative_sum,
    Finset.smul_sum, Finset.sum_sub_distrib]

theorem nativeThetaGreenFlux_hasDerivAt (P : ℝ[X]) (u : ℝ) :
    HasDerivAt (nativeThetaGreenFlux P)
      (P.eval u * completedNativeXiCosineKernel u -
        (nativeThetaGreenPolynomial P).eval u * thetaTail u) u := by
  have h := ((P.hasDerivAt u).mul (hasDerivAt_thetaTailFirst u)).sub
    ((P.derivative.hasDerivAt u).mul (hasDerivAt_thetaTail u))
  apply h.congr_deriv
  rw [← thetaTailSecond_sub_quarter u]
  simp only [nativeThetaGreenPolynomial, Polynomial.eval_sub, Polynomial.eval_smul,
    smul_eq_mul]
  ring

theorem integrableOn_polynomial_mul_thetaTail (P : ℝ[X]) :
    IntegrableOn (fun u : ℝ => P.eval u * thetaTail u) (Ioi 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [Polynomial.eval_add, add_mul]
    apply Integrable.add <;> assumption
  | monomial n a =>
    simpa only [IntegrableOn, Polynomial.eval_monomial, mul_assoc] using
      (integrableOn_pow_mul_thetaTail n).const_mul a

private theorem pow_mul_tendsto_zero_of_native_decay
    (f : ℝ → ℝ) (n : ℕ)
    (hdecay : ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : ℝ}, 0 ≤ u →
      ‖f u‖ ≤ C * Real.exp (-(3/2 : ℝ)*u)) :
    Tendsto (fun u : ℝ => u^n*f u) atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ := hdecay
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall (fun u => norm_nonneg (u^n*f u))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    calc
      ‖u^n*f u‖ = u^n*‖f u‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu n)]
      _ ≤ u^n*(C*Real.exp (-(3/2 : ℝ)*u)) :=
        mul_le_mul_of_nonneg_left (hbound hu) (pow_nonneg hu n)
      _ = C*(u^n*Real.exp (-(3/2 : ℝ)*u)) := by ring
  · have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (n : ℝ) (3/2 : ℝ) (by norm_num)
    have hn : Tendsto (fun u : ℝ => u^n*Real.exp (-(3/2 : ℝ)*u))
        atTop (nhds 0) := by simpa only [Real.rpow_natCast] using h
    simpa only [mul_zero] using hn.const_mul C

theorem polynomial_mul_thetaTail_tendsto_zero (P : ℝ[X]) :
    Tendsto (fun u : ℝ => P.eval u * thetaTail u) atTop (nhds 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [Polynomial.eval_add, add_mul, add_zero] using hP.add hQ
  | monomial n a =>
    simpa only [Polynomial.eval_monomial, mul_assoc, mul_zero] using
      (pow_mul_tendsto_zero_of_native_decay thetaTail n exists_thetaTail_exp_decay).const_mul a

theorem polynomial_mul_thetaTailFirst_tendsto_zero (P : ℝ[X]) :
    Tendsto (fun u : ℝ => P.eval u * thetaTailFirst u) atTop (nhds 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [Polynomial.eval_add, add_mul, add_zero] using hP.add hQ
  | monomial n a =>
    simpa only [Polynomial.eval_monomial, mul_assoc, mul_zero] using
      (pow_mul_tendsto_zero_of_native_decay thetaTailFirst n
        exists_thetaTailFirst_exp_decay).const_mul a

theorem nativeThetaGreenFlux_tendsto_zero (P : ℝ[X]) :
    Tendsto (nativeThetaGreenFlux P) atTop (nhds 0) := by
  unfold nativeThetaGreenFlux
  simpa only [sub_zero] using
    (polynomial_mul_thetaTailFirst_tendsto_zero P).sub
      (polynomial_mul_thetaTail_tendsto_zero P.derivative)

/-- Exact integration by parts, INCLUDING both central traces. -/
theorem nativeXiPolynomialIntegral_eq_thetaGreen_integral (P : ℝ[X]) :
    nativeXiPolynomialIntegral P =
      (∫ u in Ioi (0 : ℝ), (nativeThetaGreenPolynomial P).eval u * thetaTail u) +
        P.eval 0 / 2 + P.derivative.eval 0 * thetaTail 0 := by
  have hf := integrableOn_polynomial_mul_nativeXiKernel P
  have hg := integrableOn_polynomial_mul_thetaTail (nativeThetaGreenPolynomial P)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := (0 : ℝ)) (m := (0 : ℝ))
    (fun u _ => nativeThetaGreenFlux_hasDerivAt P u) (hf.sub hg)
    (nativeThetaGreenFlux_tendsto_zero P)
  rw [integral_sub hf hg] at h
  change nativeXiPolynomialIntegral P - _ = _ at h
  simp only [nativeThetaGreenFlux, thetaTailFirst_zero] at h
  linarith

theorem nativeThetaMomentPolynomial_coeff_below_two (n d : ℕ) (hd : d < 2) :
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
      rw [ih k (Finset.mem_range.mp hk), mul_zero]
    rw [hs]
    ring

theorem nativeThetaQuadraticPolynomial_coeff_below_two
    (s N d : ℕ) (x : Fin N → ℝ) (hd : d < 2) :
    (nativeThetaQuadraticPolynomial s N x).coeff d = 0 := by
  simp only [nativeThetaQuadraticPolynomial, Polynomial.coeff_smul,
    Polynomial.finsetSum_coeff, smul_eq_mul,
    nativeThetaMomentPolynomial_coeff_below_two _ d hd, mul_zero, Finset.sum_const_zero]

theorem nativeThetaQuadraticPolynomial_center_traces (s N : ℕ) (x : Fin N → ℝ) :
    (nativeThetaQuadraticPolynomial s N x).eval 0 = 0 ∧
      (nativeThetaQuadraticPolynomial s N x).derivative.eval 0 = 0 := by
  simp only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
    Nat.cast_zero, zero_add, mul_one]
  exact ⟨nativeThetaQuadraticPolynomial_coeff_below_two s N 0 x (by omega),
    nativeThetaQuadraticPolynomial_coeff_below_two s N 1 x (by omega)⟩

/-- The full source quadratic form, with every ordered cross, has the same
exact Green transfer for arbitrary dimension and arbitrary input. -/
theorem nativeSourceMomentQuadratic_eq_thetaGreen_integral
    (s N : ℕ) (x : Fin N → ℝ) :
    sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment s N x =
      ∫ u in Ioi (0 : ℝ),
        (nativeThetaGreenPolynomial (nativeThetaQuadraticPolynomial s N x)).eval u *
          thetaTail u := by
  rw [← nativeThetaQuadraticPolynomial_integral s N x,
    nativeXiPolynomialIntegral_eq_thetaGreen_integral]
  obtain ⟨h0,h1⟩ := nativeThetaQuadraticPolynomial_center_traces s N x
  simp [h0,h1]

theorem nativeSchurThetaPolynomial_coeff_below_two (s n d : ℕ) (hd : d < 2) :
    (nativeSchurThetaPolynomial s n).coeff d = 0 := by
  simp only [nativeSchurThetaPolynomial, nativeThetaQuadraticPolynomial,
    Polynomial.coeff_smul, Polynomial.finsetSum_coeff, smul_eq_mul,
    nativeThetaMomentPolynomial_coeff_below_two _ d hd, mul_zero, Finset.sum_const_zero]

theorem nativeSchurThetaPolynomial_center_traces (s n : ℕ) :
    (nativeSchurThetaPolynomial s n).eval 0 = 0 ∧
      (nativeSchurThetaPolynomial s n).derivative.eval 0 = 0 := by
  simp only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative, Nat.cast_zero, zero_add,
    mul_one]
  exact ⟨nativeSchurThetaPolynomial_coeff_below_two s n 0 (by omega),
    nativeSchurThetaPolynomial_coeff_below_two s n 1 (by omega)⟩

theorem nativeSchurThetaGreenFlux_zero (s n : ℕ) :
    nativeThetaGreenFlux (nativeSchurThetaPolynomial s n) 0 = 0 := by
  obtain ⟨h0,h1⟩ := nativeSchurThetaPolynomial_center_traces s n
  simp [nativeThetaGreenFlux, h0, h1]

/-- The same source remainder, after its actual Green flux integrates out. -/
theorem nativeSourceSchurRemainder_eq_thetaGreen_integral (s n : ℕ) :
    nativeSourceSchurRemainder s n =
      ∫ u in Ioi (0 : ℝ),
        (nativeThetaGreenPolynomial (nativeSchurThetaPolynomial s n)).eval u * thetaTail u := by
  rw [← nativeSchurThetaPolynomial_integral s n,
    nativeXiPolynomialIntegral_eq_thetaGreen_integral]
  obtain ⟨h0,h1⟩ := nativeSchurThetaPolynomial_center_traces s n
  simp [h0,h1]

/-- The Green transfer flips the universal top sign, but does not make both
sectors pointwise positive. -/
theorem nativeSchurThetaGreenPolynomial_coeff_top (s n : ℕ) :
    (nativeThetaGreenPolynomial (nativeSchurThetaPolynomial s n)).coeff (2*(2*n+s)+2) =
      -(1/4 : ℝ) *
        ((-1 : ℝ)^s * ((2*n+s+1 : ℕ) : ℝ) / ((2*(2*n+s)+2).factorial : ℝ)) := by
  simp only [nativeThetaGreenPolynomial, Polynomial.coeff_sub, Polynomial.coeff_smul,
    Polynomial.coeff_derivative, smul_eq_mul]
  have habove : (nativeSchurThetaPolynomial s n).coeff (2*(2*n+s)+2+1+1) = 0 := by
    rw [nativeSchurThetaPolynomial, Polynomial.coeff_smul,
      nativeThetaQuadraticPolynomial_coeff_above _ _ _ _ (by omega)]
    simp
  rw [habove, nativeSchurThetaPolynomial_coeff_top]
  ring

theorem nativeSchurThetaGreenPolynomial_even_coeff_top_neg (n : ℕ) :
    (nativeThetaGreenPolynomial (nativeSchurThetaPolynomial 0 n)).coeff (2*(2*n)+2) < 0 := by
  have h := nativeSchurThetaGreenPolynomial_coeff_top 0 n
  simp only [add_zero, pow_zero, one_mul] at h
  rw [h]
  exact mul_neg_of_neg_of_pos (by norm_num) (div_pos (by positivity) (by positivity))

theorem nativeSchurThetaGreenPolynomial_coeff_above (s n d : ℕ)
    (hd : 2*(2*n+s)+2 < d) :
    (nativeThetaGreenPolynomial (nativeSchurThetaPolynomial s n)).coeff d = 0 := by
  have habove (e : ℕ) (he : 2*(2*n+s)+2 < e) :
      (nativeSchurThetaPolynomial s n).coeff e = 0 := by
    rw [nativeSchurThetaPolynomial, Polynomial.coeff_smul,
      nativeThetaQuadraticPolynomial_coeff_above _ _ _ e he]
    simp
  simp only [nativeThetaGreenPolynomial, Polynomial.coeff_sub, Polynomial.coeff_smul,
    Polynomial.coeff_derivative, smul_eq_mul]
  rw [habove d hd, habove (d+1+1) (by omega)]
  ring

theorem nativeSchurThetaGreenPolynomial_even_natDegree (n : ℕ) :
    (nativeThetaGreenPolynomial (nativeSchurThetaPolynomial 0 n)).natDegree = 2*(2*n)+2 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro d hd
    exact nativeSchurThetaGreenPolynomial_coeff_above 0 n d (by simpa only [add_zero] using hd)
  · exact (nativeSchurThetaGreenPolynomial_even_coeff_top_neg n).ne

theorem nativeSchurThetaGreenPolynomial_even_tendsto_atBot (n : ℕ) :
    Tendsto (fun u : ℝ =>
      (nativeThetaGreenPolynomial (nativeSchurThetaPolynomial 0 n)).eval u) atTop atBot := by
  apply Polynomial.tendsto_atBot_of_leadingCoeff_nonpos
  · rw [← Polynomial.natDegree_pos_iff_degree_pos, nativeSchurThetaGreenPolynomial_even_natDegree]
    omega
  · rw [← Polynomial.coeff_natDegree, nativeSchurThetaGreenPolynomial_even_natDegree]
    exact (nativeSchurThetaGreenPolynomial_even_coeff_top_neg n).le

theorem nativeSchurThetaPolynomial_first_even :
    nativeSchurThetaPolynomial 0 0 = Polynomial.monomial 2 (1/2 : ℝ) := by
  apply Polynomial.funext
  intro u
  rw [nativeSchurThetaPolynomial_zero, nativeThetaMomentPolynomial_eq 0]
  norm_num [nativeThetaMomentTopCoefficient, Polynomial.eval_smul, Polynomial.eval_monomial]
  field_simp [completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero]

/-- The most direct two-integration-by-parts density already has a negative
point in the first even case. This is a route-specific obstruction only. -/
theorem nativeSchurThetaGreenPolynomial_first_even_negative :
    (nativeThetaGreenPolynomial (nativeSchurThetaPolynomial 0 0)).eval 3 = -(1/8 : ℝ) := by
  rw [nativeSchurThetaPolynomial_first_even]
  norm_num [nativeThetaGreenPolynomial, Polynomial.derivative_monomial,
    Polynomial.eval_sub, Polynomial.eval_smul, Polynomial.eval_monomial]

theorem nativeSchurThetaGreenPolynomial_first_even_not_norm_sq
    {H : Type*} [SeminormedAddCommGroup H] (f : ℝ → H) :
    ¬(∀ u : ℝ, 0 ≤ u →
      (nativeThetaGreenPolynomial (nativeSchurThetaPolynomial 0 0)).eval u = ‖f u‖^2) := by
  intro he
  have h := he 3 (by norm_num)
  rw [nativeSchurThetaGreenPolynomial_first_even_negative] at h
  nlinarith [sq_nonneg ‖f 3‖]

/-- The first odd sign has an exact nonlocal theta core, a square term,
and a nonnegative fourth theta-tail moment. This reuses the fixed source,
not the desired sign of the remainder. -/
theorem nativeSourceSchurRemainder_first_odd_eq_theta_balance :
    nativeSourceSchurRemainder 1 0 =
      (2*completedNativeThetaTailMoment 0^2-completedNativeThetaTailMoment 2) /
        (2*completedNativeRealEvenCharacteristicCoefficient 0) +
      completedNativeThetaTailMoment 2^2 /
        (64*completedNativeRealEvenCharacteristicCoefficient 0) +
      completedNativeThetaTailMoment 4 / 48 := by
  rw [nativeSourceSchurRemainder_eq]
  simp only [sourceMomentSchur, dotProduct, Fin.sum_univ_zero, sub_zero, mul_zero]
  rw [canonicalCompletedNativeLogDerivativeMoment_eq 1]
  norm_num [Finset.sum_range_succ]
  rw [canonicalCompletedNativeLogDerivativeMoment_eq 0]
  norm_num [Finset.sum_range_succ]
  rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder 1,
    completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder 2]
  norm_num
  rw [completedNativeXiCosineMoment_one_eq_thetaTailMoments,
    completedNativeXiCosineMoment_two_eq_thetaTailMoments]
  have hc0 : completedNativeRealEvenCharacteristicCoefficient 0 =
      1/2-(1/4 : ℝ)*completedNativeThetaTailMoment 0 := by
    rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder 0]
    norm_num
    exact completedNativeXiCosineMoment_zero_eq_thetaTailMoments
  field_simp [completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero]
  have hmul := congrArg (fun t : ℝ => t*completedNativeThetaTailMoment 2) hc0
  have hmul2 := congrArg (fun t : ℝ =>
    t*completedNativeThetaTailMoment 2*completedNativeRealEvenCharacteristicCoefficient 0) hc0
  have hmul3 := congrArg (fun t : ℝ =>
    t*completedNativeThetaTailMoment 2*completedNativeRealEvenCharacteristicCoefficient 0^2) hc0
  nlinarith [hmul, hmul2, hmul3]

/-- This is the source inequality used by the existing kurtosis proof:
its proof uses the specific theta bounds, not Hankel positivity. -/
theorem nativeThetaFirstOddCore_pos :
    0 < 2*completedNativeThetaTailMoment 0^2-completedNativeThetaTailMoment 2 := by
  have hzero := completedNativeThetaTailMoment_zero_gt
  have htwo := completedNativeThetaTailMoment_two_lt
  nlinarith [sq_nonneg (completedNativeThetaTailMoment 0-(113/10000 : ℝ))]

theorem nativeSourceSchurRemainder_first_odd_theta_core_lower :
    (2*completedNativeThetaTailMoment 0^2-completedNativeThetaTailMoment 2) /
      (2*completedNativeRealEvenCharacteristicCoefficient 0) ≤
        nativeSourceSchurRemainder 1 0 := by
  rw [nativeSourceSchurRemainder_first_odd_eq_theta_balance]
  have h0 : 0 < completedNativeRealEvenCharacteristicCoefficient 0 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/3)
      completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  have htwo : 0 ≤ completedNativeThetaTailMoment 2^2 /
      (64*completedNativeRealEvenCharacteristicCoefficient 0) := by positivity
  have hfour := completedNativeThetaTailMoment_nonneg 4
  linarith

end
end CarrySelfAdjointOperator
