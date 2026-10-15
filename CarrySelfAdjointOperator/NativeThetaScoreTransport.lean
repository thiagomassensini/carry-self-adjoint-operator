import CarrySelfAdjointOperator.NativeXiThetaDifferentiation
import CarrySelfAdjointOperator.NativeSchurEulerBalance

/-! Exact score transport for the complete source.  All analytic hypotheses
are discharged for the infinite theta kernel.  The resulting balance is an
all-order identity, not an all-order positivity assertion. -/
namespace CarrySelfAdjointOperator
open Set Filter MeasureTheory Polynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Logarithmic slope of the unchanged completed source weight. -/
def nativeThetaScore (u : ℝ) : ℝ :=
  -u*completedNativeXiCosineKernelFirst u / completedNativeXiCosineKernel u

theorem completedNativeXiCosineKernelFirst_continuous :
    Continuous completedNativeXiCosineKernelFirst := by
  have h4 : Continuous (XiThetaScore.atomSum 4 (9/2)) :=
    continuous_iff_continuousAt.mpr (fun u =>
      (XiThetaScore.atomSum_hasDerivAt 4 (by norm_num : (0 : ℝ) ≤ 9/2) u).continuousAt)
  have h6 : Continuous (XiThetaScore.atomSum 6 (13/2)) :=
    continuous_iff_continuousAt.mpr (fun u =>
      (XiThetaScore.atomSum_hasDerivAt 6 (by norm_num : (0 : ℝ) ≤ 13/2) u).continuousAt)
  have h2 : Continuous (XiThetaScore.atomSum 2 (5/2)) :=
    continuous_iff_continuousAt.mpr (fun u =>
      (XiThetaScore.atomSum_hasDerivAt 2 (by norm_num : (0 : ℝ) ≤ 5/2) u).continuousAt)
  exact ((h4.const_mul (9/2)).sub (h6.const_mul (2*Real.pi))).const_mul (8*Real.pi^2) |>.sub
    (((h2.const_mul (5/2)).sub (h4.const_mul (2*Real.pi))).const_mul (12*Real.pi))

private theorem integrableOn_pow_mul_kernelFirst (power : ℕ) :
    IntegrableOn (fun u : ℝ => u^power*completedNativeXiCosineKernelFirst u) (Ioi 0) := by
  obtain ⟨C,hC,hbound⟩ := completedNativeXiCosineKernelFirst_decay
  have hbaseR := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (power : ℝ)) (b := (3/2 : ℝ))
    (by have := Nat.cast_nonneg (α := ℝ) power; linarith) (by norm_num) (by norm_num)
  have hbase : IntegrableOn (fun u : ℝ => C*(u^power*Real.exp (-(3/2 : ℝ)*u))) (Ioi 0) := by
    simpa only [IntegrableOn, Real.rpow_natCast, Real.rpow_one] using hbaseR.const_mul C
  apply hbase.mono'
  · exact (continuous_id.pow power).aestronglyMeasurable.mul
      completedNativeXiCosineKernelFirst_continuous.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    calc
      ‖u^power*completedNativeXiCosineKernelFirst u‖ = u^power*‖completedNativeXiCosineKernelFirst u‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu.le power)]
      _ ≤ u^power*(C*Real.exp (-(3/2 : ℝ)*u)) :=
        mul_le_mul_of_nonneg_left (hbound hu.le) (pow_nonneg hu.le power)
      _ = _ := by ring

theorem integrableOn_polynomial_mul_kernelFirst (P : ℝ[X]) :
    IntegrableOn (fun u : ℝ => P.eval u*completedNativeXiCosineKernelFirst u) (Ioi 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [Polynomial.eval_add, add_mul]
    apply Integrable.add <;> assumption
  | monomial n a => simpa only [IntegrableOn, Polynomial.eval_monomial, mul_assoc] using
      (integrableOn_pow_mul_kernelFirst n).const_mul a

theorem nativeThetaScore_density (P : ℝ[X]) {u : ℝ} (hu : 0 ≤ u) :
    nativeThetaScore u*P.eval u*completedNativeXiCosineKernel u =
      -(X*P).eval u*completedNativeXiCosineKernelFirst u := by
  unfold nativeThetaScore
  have h := (completedNativeXiCosineKernel_pos hu).ne'
  simp only [Polynomial.eval_mul, Polynomial.eval_X]
  field_simp

theorem integrableOn_nativeThetaScore_density (P : ℝ[X]) :
    IntegrableOn (fun u : ℝ => nativeThetaScore u*P.eval u*completedNativeXiCosineKernel u) (Ioi 0) := by
  apply (integrableOn_polynomial_mul_kernelFirst (X*P)).neg.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simpa only [Pi.neg_apply, neg_mul] using (nativeThetaScore_density P hu.le).symm

def nativeThetaScoreIntegral (P : ℝ[X]) : ℝ :=
  ∫ u in Ioi (0 : ℝ), nativeThetaScore u*P.eval u*completedNativeXiCosineKernel u

theorem polynomial_mul_nativeXiKernel_tendsto_zero (P : ℝ[X]) :
    Tendsto (fun u : ℝ => P.eval u*completedNativeXiCosineKernel u) atTop (nhds 0) := by
  obtain ⟨C,hC,hbound⟩ := XiThetaCosine.exists_completedNativeXiCosineKernel_exp_decay
  have hp (n : ℕ) : Tendsto (fun u : ℝ => u^n*completedNativeXiCosineKernel u) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero'
    · exact Eventually.of_forall (fun u => norm_nonneg _)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
      calc
        ‖u^n*completedNativeXiCosineKernel u‖ = u^n*‖completedNativeXiCosineKernel u‖ := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu n)]
        _ ≤ u^n*(C*Real.exp (-(3/2 : ℝ)*u)) :=
          mul_le_mul_of_nonneg_left (hbound hu) (pow_nonneg hu n)
        _ = C*(u^n*Real.exp (-(3/2 : ℝ)*u)) := by ring
    · simpa only [Real.rpow_natCast, mul_zero] using
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) (3/2 : ℝ) (by norm_num)).const_mul C
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Polynomial.eval_add, add_mul, add_zero] using hP.add hQ
  | monomial n a => simpa only [Polynomial.eval_monomial, mul_assoc, mul_zero] using (hp n).const_mul a

/-- Both flux boundaries vanish: at zero because of X, at infinity by the
actual source decay.  No boundary or modal residual is discarded. -/
theorem nativeXiPolynomialIntegral_euler_score (P : ℝ[X]) :
    nativeXiPolynomialIntegral (X*P.derivative) =
      -nativeXiPolynomialIntegral P + nativeThetaScoreIntegral P := by
  have hf := integrableOn_polynomial_mul_nativeXiKernel (P+X*P.derivative)
  have hg := integrableOn_nativeThetaScore_density P
  have hder (u : ℝ) (hu : u ∈ Ici (0 : ℝ)) :
      HasDerivAt (fun u : ℝ => (X*P).eval u*completedNativeXiCosineKernel u)
        ((P+X*P.derivative).eval u*completedNativeXiCosineKernel u -
          nativeThetaScore u*P.eval u*completedNativeXiCosineKernel u) u := by
    have h := ((X*P).hasDerivAt u).mul (completedNativeXiCosineKernel_hasDerivAt u)
    apply h.congr_deriv
    rw [nativeThetaScore_density P hu]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_X, one_mul,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := (0 : ℝ)) (m := (0 : ℝ)) hder (hf.sub hg)
    (polynomial_mul_nativeXiKernel_tendsto_zero (X*P))
  rw [integral_sub hf hg] at h
  change nativeXiPolynomialIntegral (P+X*P.derivative) - nativeThetaScoreIntegral P = _ at h
  simp only [map_add, Polynomial.eval_mul, Polynomial.eval_X, zero_mul, sub_zero] at h
  linarith

/-- Actual odd-sector transport at every order; invertibility of the old
prefix is the only matrix hypothesis, with no assumed sign of the new pivot. -/
theorem nativeSchurScore_odd_balance (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n)) :
    ((4*n+5 : ℕ) : ℝ)*nativeSourceSchurRemainder 1 n =
      2*completedNativeRealEvenCharacteristicCoefficient 0*(nativeSchurCriticalReadout 1 n)^2 +
        nativeThetaScoreIntegral (nativeSchurThetaPolynomial 1 n) := by
  have h := nativeSchurEuler_odd_balance n hA
  unfold nativeSchurEulerPolynomial at h
  rw [nativeXiPolynomialIntegral_euler_score, nativeSchurThetaPolynomial_integral] at h
  push_cast at h ⊢
  linarith

theorem nativeSchurScore_even_balance (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 n)) :
    ((4*n+3 : ℕ) : ℝ)*nativeSourceSchurRemainder 0 n =
      nativeThetaScoreIntegral (nativeSchurThetaPolynomial 0 n) := by
  have h := nativeSchurEuler_even_balance n hA
  unfold nativeSchurEulerPolynomial at h
  rw [nativeXiPolynomialIntegral_euler_score, nativeSchurThetaPolynomial_integral] at h
  push_cast at h ⊢
  linarith

end
end CarrySelfAdjointOperator
