import CarrySelfAdjointOperator.NativeSourceThetaMomentPolynomials
import CarrySelfAdjointOperator.NativeSourceAllOrderSchur

/-! The original source Schur remainders as actual theta integrals. The
odd-sector polynomial has a negative leading coefficient at EVERY order.
This excludes a pointwise-square reading of this density, not other source
representations and not positivity of the integral itself. -/
namespace CarrySelfAdjointOperator
open scoped BigOperators Matrix
open Polynomial Filter
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

def nativeThetaQuadraticPolynomial (s N : ℕ) (x : Fin N → ℝ) : ℝ[X] :=
  ∑ i : Fin N, ∑ j : Fin N, (x i*x j) • nativeThetaMomentPolynomial (i.val+j.val+s)

theorem nativeThetaQuadraticPolynomial_integral (s N : ℕ) (x : Fin N → ℝ) :
    nativeXiPolynomialIntegral (nativeThetaQuadraticPolynomial s N x) =
      sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment s N x := by
  simp only [nativeThetaQuadraticPolynomial, map_sum, map_smul, smul_eq_mul,
    nativeThetaMomentPolynomial_integral, sourceMomentQuadratic, sourceMomentMatrix,
    dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def nativeSchurCriticalCoefficients (s n : ℕ) : Fin (n+1) → ℝ :=
  Fin.snoc (-((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)⁻¹ *ᵥ
    sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment s n)) 1

def nativeSchurThetaPolynomial (s n : ℕ) : ℝ[X] :=
  completedNativeRealEvenCharacteristicCoefficient 0 •
    nativeThetaQuadraticPolynomial s (n+1) (nativeSchurCriticalCoefficients s n)

/-- The critical-direction identity also holds for the total nonsingular
inverse: at a singular prefix this inverse is zero. No positivity is needed
for this one identity; the full sewing still requires an invertible prefix. -/
theorem sourceMomentSchur_critical_direction_total (m : ℕ → ℝ) (s n : ℕ) :
    sourceMomentQuadratic m s (n+1)
      (Fin.snoc (-((sourceMomentMatrix m s n)⁻¹ *ᵥ sourceMomentCoupling m s n)) 1) =
      sourceMomentSchur m s n := by
  let A := sourceMomentMatrix m s n
  let b := sourceMomentCoupling m s n
  let v := A⁻¹ *ᵥ b
  change sourceMomentQuadratic m s (n+1) (Fin.snoc (-v) 1) = m (2*n+s)-b ⬝ᵥ v
  rw [sourceMomentQuadratic_snoc]
  rcases Matrix.nonsing_inv_cancel_or_zero A with hI | hZ
  · have hv : A *ᵥ v = b := by
      dsimp [v]
      rw [Matrix.mulVec_mulVec, hI.2, Matrix.one_mulVec]
    have hq : sourceMomentQuadratic m s n (-v) = b ⬝ᵥ v := by
      change (-v) ⬝ᵥ (A *ᵥ (-v)) = b ⬝ᵥ v
      simp only [Matrix.mulVec_neg, hv, neg_dotProduct, dotProduct_neg, neg_neg]
      exact dotProduct_comm _ _
    change sourceMomentQuadratic m s n (-v)+2*1*(b ⬝ᵥ (-v))+m (2*n+s)*1^2 = _
    rw [hq, dotProduct_neg]
    ring
  · have hv : v = 0 := by simp [v, hZ]
    change sourceMomentQuadratic m s n (-v)+2*1*(b ⬝ᵥ (-v))+m (2*n+s)*1^2 = _
    rw [hv]
    simp [sourceMomentQuadratic]

theorem nativeSchurThetaPolynomial_zero (s : ℕ) :
    nativeSchurThetaPolynomial s 0 =
      completedNativeRealEvenCharacteristicCoefficient 0 • nativeThetaMomentPolynomial s := by
  simp [nativeSchurThetaPolynomial, nativeThetaQuadraticPolynomial,
    nativeSchurCriticalCoefficients]

/-- Concrete first odd density, before integration: its negative quartic
tail is already present in the source's first strict kurtosis inequality. -/
theorem nativeSchurThetaPolynomial_first_odd_eval (u : ℝ) :
    (nativeSchurThetaPolynomial 1 0).eval u =
      completedNativeXiCosineMoment 1 /
        (4*completedNativeRealEvenCharacteristicCoefficient 0)*u^2 - u^4/12 := by
  rw [nativeSchurThetaPolynomial_zero, nativeThetaMomentPolynomial_eq 1]
  simp only [Polynomial.eval_smul, Polynomial.eval_sub, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, smul_eq_mul]
  norm_num [nativeThetaMomentTopCoefficient, Finset.sum_range_succ]
  rw [nativeThetaMomentPolynomial_eq 0]
  norm_num [nativeThetaMomentTopCoefficient, Polynomial.eval_smul, Polynomial.eval_monomial]
  rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder 1]
  norm_num
  field_simp [completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero]
  ring

/-- Actual native R, with its original c0 normalization and every coupling. -/
theorem nativeSchurThetaPolynomial_integral (s n : ℕ) :
    nativeXiPolynomialIntegral (nativeSchurThetaPolynomial s n) =
      nativeSourceSchurRemainder s n := by
  rw [nativeSchurThetaPolynomial, map_smul, nativeThetaQuadraticPolynomial_integral]
  simp only [smul_eq_mul, nativeSchurCriticalCoefficients]
  rw [sourceMomentSchur_critical_direction_total _ s n]
  exact (nativeSourceSchurRemainder_eq s n).symm

theorem nativeThetaQuadraticPolynomial_coeff_above (s n : ℕ) (x : Fin (n+1) → ℝ)
    (d : ℕ) (hd : 2*(2*n+s)+2 < d) :
    (nativeThetaQuadraticPolynomial s (n+1) x).coeff d = 0 := by
  simp only [nativeThetaQuadraticPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_smul, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hi := i.isLt
  have hj := j.isLt
  rw [nativeThetaMomentPolynomial_coeff_above _ d (by omega), mul_zero]

theorem nativeThetaQuadraticPolynomial_coeff_top (s n : ℕ) (x : Fin (n+1) → ℝ) :
    (nativeThetaQuadraticPolynomial s (n+1) x).coeff (2*(2*n+s)+2) =
      (x (Fin.last n))^2 * (completedNativeRealEvenCharacteristicCoefficient 0)⁻¹ *
        nativeThetaMomentTopCoefficient (2*n+s) := by
  classical
  simp only [nativeThetaQuadraticPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_smul, smul_eq_mul]
  rw [Finset.sum_eq_single (Fin.last n)]
  · rw [Finset.sum_eq_single (Fin.last n)]
    · simp only [Fin.val_last]
      rw [show n+n+s = 2*n+s by omega, nativeThetaMomentPolynomial_coeff_top]
      ring
    · intro j _ hj
      have hjn : j.val < n := by
        have hjv : j.val ≠ n := by
          intro he
          apply hj
          exact Fin.ext he
        have := j.isLt
        omega
      rw [nativeThetaMomentPolynomial_coeff_above _ _ (by omega), mul_zero]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · intro i _ hi
    have hin : i.val < n := by
      have hiv : i.val ≠ n := by
        intro he
        apply hi
        exact Fin.ext he
      have := i.isLt
      omega
    apply Finset.sum_eq_zero
    intro j _
    have hj := j.isLt
    rw [nativeThetaMomentPolynomial_coeff_above _ _ (by omega), mul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The highest coefficient is universal: old couplings cannot change it. -/
theorem nativeSchurThetaPolynomial_coeff_top (s n : ℕ) :
    (nativeSchurThetaPolynomial s n).coeff (2*(2*n+s)+2) =
      (-1 : ℝ)^s * ((2*n+s+1 : ℕ) : ℝ) / ((2*(2*n+s)+2).factorial : ℝ) := by
  rw [nativeSchurThetaPolynomial, Polynomial.coeff_smul,
    nativeThetaQuadraticPolynomial_coeff_top]
  simp only [nativeSchurCriticalCoefficients, Fin.snoc_last, one_pow, one_mul, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero,
    one_mul]
  unfold nativeThetaMomentTopCoefficient
  have he : (-1 : ℝ)^(2*n+s) = (-1 : ℝ)^s := by
    rw [pow_add, pow_mul]
    norm_num
  rw [he]

theorem nativeSchurThetaPolynomial_odd_coeff_top_neg (n : ℕ) :
    (nativeSchurThetaPolynomial 1 n).coeff (2*(2*n+1)+2) < 0 := by
  rw [nativeSchurThetaPolynomial_coeff_top]
  simp only [pow_one, neg_one_mul]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (by positivity)

theorem nativeSchurThetaPolynomial_odd_natDegree (n : ℕ) :
    (nativeSchurThetaPolynomial 1 n).natDegree = 2*(2*n+1)+2 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro d hd
    rw [nativeSchurThetaPolynomial, Polynomial.coeff_smul,
      nativeThetaQuadraticPolynomial_coeff_above _ _ _ d hd]
    simp
  · exact (nativeSchurThetaPolynomial_odd_coeff_top_neg n).ne

theorem nativeSchurThetaPolynomial_odd_leadingCoeff_neg (n : ℕ) :
    (nativeSchurThetaPolynomial 1 n).leadingCoeff < 0 := by
  rw [← Polynomial.coeff_natDegree, nativeSchurThetaPolynomial_odd_natDegree]
  exact nativeSchurThetaPolynomial_odd_coeff_top_neg n

theorem nativeSchurThetaPolynomial_odd_tendsto_atBot (n : ℕ) :
    Tendsto (fun u : ℝ => (nativeSchurThetaPolynomial 1 n).eval u) atTop atBot := by
  apply Polynomial.tendsto_atBot_of_leadingCoeff_nonpos
  · rw [← Polynomial.natDegree_pos_iff_degree_pos, nativeSchurThetaPolynomial_odd_natDegree]
    omega
  · exact (nativeSchurThetaPolynomial_odd_leadingCoeff_neg n).le

/-- The original positive theta weight does not remove the negative tail. -/
theorem nativeSchurThetaPolynomial_odd_density_eventually_neg (n : ℕ) :
    ∀ᶠ u : ℝ in atTop,
      (nativeSchurThetaPolynomial 1 n).eval u * completedNativeXiCosineKernel u < 0 := by
  filter_upwards [(nativeSchurThetaPolynomial_odd_tendsto_atBot n).eventually
    (eventually_lt_atBot (0 : ℝ)), eventually_ge_atTop (0 : ℝ)] with u hu hu0
  exact mul_neg_of_neg_of_pos hu (completedNativeXiCosineKernel_pos hu0)

/-- This particular polynomial density cannot itself be a pointwise norm
square. No impossibility of other integral representations is inferred. -/
theorem nativeSchurThetaPolynomial_odd_not_pointwise_norm_sq
    (n : ℕ) {H : Type*} [SeminormedAddCommGroup H] (f : ℝ → H) :
    ¬(∀ u : ℝ, 0 ≤ u → (nativeSchurThetaPolynomial 1 n).eval u = ‖f u‖^2) := by
  intro he
  obtain ⟨u, hu, hu0⟩ := ((nativeSchurThetaPolynomial_odd_tendsto_atBot n).eventually
    (eventually_lt_atBot (0 : ℝ)) |>.and (eventually_ge_atTop (0 : ℝ))).exists
  rw [he u hu0] at hu
  exact (not_lt_of_ge (sq_nonneg _)) hu

end
end CarrySelfAdjointOperator
