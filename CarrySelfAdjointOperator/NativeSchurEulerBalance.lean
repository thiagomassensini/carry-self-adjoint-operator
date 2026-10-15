import CarrySelfAdjointOperator.NativeThetaEulerRecurrence
import CarrySelfAdjointOperator.NativeSchurConvolutionCancellation

/-! All-order critical-source Euler balance. An explicit positive square
survives in the odd sector. The remaining Euler density is signed and is
retained; no all-order mass domination is asserted. -/
namespace CarrySelfAdjointOperator
open Polynomial Matrix
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

local notation "m" => canonicalCompletedNativeLogDerivativeMoment
local notation "c₀" => completedNativeRealEvenCharacteristicCoefficient 0

private theorem source_quadratic_sum (q : ℕ → ℝ) (s n : ℕ) (v : Fin n → ℝ) :
    sourceMomentQuadratic q s n v = ∑ i, ∑ j, v i*v j*q (i.val+j.val+s) := by
  simp only [sourceMomentQuadratic, sourceMomentMatrix, dotProduct, Matrix.mulVec,
    Pi.star_apply, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem critical_weighted_row_zero (q : ℕ → ℝ) (s n : ℕ)
    (v : Fin (n+1) → ℝ)
    (ho : ∀ a < n, ∑ j : Fin (n+1), v j*q (a+j.val+s) = 0) :
    ∑ i : Fin (n+1), ∑ j : Fin (n+1),
      ((i.val : ℝ)-(n : ℝ))*v i*v j*q (i.val+j.val+s) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  calc
    _ = ((i.val : ℝ)-(n : ℝ))*v i * ∑ j, v j*q (i.val+j.val+s) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by
      by_cases hi : i.val < n
      · rw [ho i.val hi,mul_zero]
      · have he : i.val=n := by have := i.isLt; omega
        rw [he,sub_self,zero_mul,zero_mul]

theorem sourceMomentCritical_weighted_degree (q : ℕ → ℝ) (s n : ℕ)
    (v : Fin (n+1) → ℝ)
    (ho : ∀ a < n, ∑ j : Fin (n+1), v j*q (a+j.val+s) = 0) :
    ∑ i : Fin (n+1), ∑ j : Fin (n+1),
      ((2*(i.val+j.val+s)+2 : ℕ) : ℝ)*v i*v j*q (i.val+j.val+s) =
        ((4*n+2*s+2 : ℕ) : ℝ)*sourceMomentQuadratic q s (n+1) v := by
  have hr := critical_weighted_row_zero q s n v ho
  have hc : (∑ i : Fin (n+1), ∑ j : Fin (n+1),
      ((j.val : ℝ)-(n : ℝ))*v i*v j*q (i.val+j.val+s)) = 0 := by
    rw [Finset.sum_comm]
    convert hr using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.add_comm j.val i.val]
    ring
  calc
    _ = ((4*n+2*s+2 : ℕ) : ℝ)*sourceMomentQuadratic q s (n+1) v +
        2*(∑ i : Fin (n+1), ∑ j : Fin (n+1),
          ((i.val : ℝ)-(n : ℝ))*v i*v j*q (i.val+j.val+s)) +
        2*(∑ i : Fin (n+1), ∑ j : Fin (n+1),
          ((j.val : ℝ)-(n : ℝ))*v i*v j*q (i.val+j.val+s)) := by
      rw [source_quadratic_sum]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    _ = _ := by rw [hr,hc]; ring

theorem nativeThetaQuadratic_euler_integral (s N : ℕ) (v : Fin N → ℝ) :
    nativeXiPolynomialIntegral (X*(nativeThetaQuadraticPolynomial s N v).derivative) =
      (∑ i : Fin N, ∑ j : Fin N,
        ((2*(i.val+j.val+s)+2 : ℕ) : ℝ)*v i*v j*m (i.val+j.val+s)) -
      2*(∑ i : Fin N, ∑ j : Fin N,
        v i*v j*sourceMomentConvolution m (i.val+j.val+s)) := by
  have he : X*(nativeThetaQuadraticPolynomial s N v).derivative =
      ∑ i : Fin N, ∑ j : Fin N, (v i*v j) • nativeThetaEulerPolynomial (i.val+j.val+s) := by
    simp only [nativeThetaQuadraticPolynomial, Polynomial.derivative_sum,
      Polynomial.derivative_smul, Finset.mul_sum, mul_smul_comm, nativeThetaEulerPolynomial]
  rw [he]
  simp only [map_sum,map_smul,smul_eq_mul,nativeThetaEulerPolynomial_integral,
    sourceMomentConvolution]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The invertible old prefix supplies orthogonality. No sign of the old
prefix, the new pivot or the full target matrix is assumed. -/
theorem nativeSchurCriticalCoefficients_orthogonal (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n)) :
    ∀ a < n, ∑ j : Fin (n+1),
      nativeSchurCriticalCoefficients s n j*m (a+j.val+s) = 0 := by
  let A := sourceMomentMatrix m s n
  let b := sourceMomentCoupling m s n
  let w := A⁻¹ *ᵥ b
  letI := hA.invertible
  have hw : A *ᵥ w = b := by
    dsimp [w,A]
    rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]
  intro a ha
  have hr := congrFun hw (⟨a,ha⟩ : Fin n)
  change (∑ j : Fin n, m (a+j.val+s)*w j) = m (a+n+s) at hr
  simp only [nativeSchurCriticalCoefficients, Fin.sum_univ_castSucc,
    Fin.snoc_castSucc,Fin.snoc_last,Fin.val_castSucc,Fin.val_last,one_mul]
  change (∑ j : Fin n, -w j*m (a+j.val+s))+m (a+n+s) = 0
  rw [← hr]
  simp only [neg_mul, Finset.sum_neg_distrib]
  have he : (∑ j : Fin n, w j*m (a+j.val+s)) = ∑ j : Fin n, m (a+j.val+s)*w j := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  ring

def nativeSchurEulerPolynomial (s n : ℕ) : ℝ[X] :=
  X*(nativeSchurThetaPolynomial s n).derivative

def nativeSchurCriticalReadout (s n : ℕ) : ℝ :=
  ∑ i : Fin (n+1), nativeSchurCriticalCoefficients s n i*m i.val

/-- Uniform identity for every odd critical direction: a source-derived
positive square plus the COMPLETE signed Euler density. -/
theorem nativeSchurEuler_odd_balance (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m 1 n)) :
    ((4*n+4 : ℕ) : ℝ)*nativeSourceSchurRemainder 1 n =
      nativeXiPolynomialIntegral (nativeSchurEulerPolynomial 1 n) +
        2*c₀*(nativeSchurCriticalReadout 1 n)^2 := by
  have ho := nativeSchurCriticalCoefficients_orthogonal 1 n hA
  have he := nativeThetaQuadratic_euler_integral 1 (n+1) (nativeSchurCriticalCoefficients 1 n)
  rw [sourceMomentCritical_weighted_degree m 1 n _ ho,
    sourceMomentConvolution_critical_odd m n _ ho] at he
  have hcrit := sourceMomentSchur_critical_direction_total m 1 n
  change sourceMomentQuadratic m 1 (n+1) (nativeSchurCriticalCoefficients 1 n) = _ at hcrit
  rw [hcrit] at he
  have hpol : nativeSchurEulerPolynomial 1 n =
      c₀ • (X*(nativeThetaQuadraticPolynomial 1 (n+1) (nativeSchurCriticalCoefficients 1 n)).derivative) := by
    simp only [nativeSchurEulerPolynomial,nativeSchurThetaPolynomial,
      Polynomial.derivative_smul,mul_smul_comm]
  rw [hpol,map_smul]
  simp only [smul_eq_mul,nativeSchurCriticalReadout,nativeSourceSchurRemainder_eq]
  norm_num only at he
  linear_combination -c₀*he

theorem nativeSchurEuler_even_balance (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m 0 n)) :
    ((4*n+2 : ℕ) : ℝ)*nativeSourceSchurRemainder 0 n =
      nativeXiPolynomialIntegral (nativeSchurEulerPolynomial 0 n) := by
  have ho := nativeSchurCriticalCoefficients_orthogonal 0 n hA
  have he := nativeThetaQuadratic_euler_integral 0 (n+1) (nativeSchurCriticalCoefficients 0 n)
  rw [sourceMomentCritical_weighted_degree m 0 n _ ho] at he
  simp only [Nat.add_zero] at he
  rw [sourceMomentConvolution_critical_even m n _ (by simpa using ho)] at he
  have hcrit := sourceMomentSchur_critical_direction_total m 0 n
  change sourceMomentQuadratic m 0 (n+1) (nativeSchurCriticalCoefficients 0 n) = _ at hcrit
  rw [hcrit] at he
  have hpol : nativeSchurEulerPolynomial 0 n =
      c₀ • (X*(nativeThetaQuadraticPolynomial 0 (n+1) (nativeSchurCriticalCoefficients 0 n)).derivative) := by
    simp only [nativeSchurEulerPolynomial,nativeSchurThetaPolynomial,
      Polynomial.derivative_smul,mul_smul_comm]
  rw [hpol,map_smul]
  simp only [smul_eq_mul,nativeSourceSchurRemainder_eq]
  norm_num only at he
  linear_combination -c₀*he

/-- A source estimate, valid at arbitrary depth, with the negative part of
the Euler density retained. Its sufficiency does not establish its premise. -/
theorem nativeSchurEuler_odd_lower_bound (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m 1 n)) :
    2*c₀*(nativeSchurCriticalReadout 1 n)^2 -
        nativeThetaNegativeMass (nativeSchurEulerPolynomial 1 n) ≤
      ((4*n+4 : ℕ) : ℝ)*nativeSourceSchurRemainder 1 n := by
  rw [nativeSchurEuler_odd_balance n hA,nativeXiPolynomialIntegral_eq_masses]
  linarith [nativeThetaPositiveMass_nonneg (nativeSchurEulerPolynomial 1 n)]

theorem nativeSchurEuler_odd_square_nonneg (n : ℕ) :
    0 ≤ 2*c₀*(nativeSchurCriticalReadout 1 n)^2 := by
  have hc : 0 < c₀ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/3)
    completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  exact mul_nonneg (mul_nonneg (by norm_num) hc.le) (sq_nonneg _)

theorem nativeSchurEuler_odd_mass_balance (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m 1 n)) :
    ((4*n+4 : ℕ) : ℝ)*nativeSourceSchurRemainder 1 n =
      2*c₀*(nativeSchurCriticalReadout 1 n)^2 +
        nativeThetaPositiveMass (nativeSchurEulerPolynomial 1 n) -
        nativeThetaNegativeMass (nativeSchurEulerPolynomial 1 n) := by
  rw [nativeSchurEuler_odd_balance n hA,nativeXiPolynomialIntegral_eq_masses]
  ring

/-- Exact remaining sign obligation. No assertion of this domination is
smuggled into the source recurrence or the positive square. -/
theorem nativeSchurEuler_odd_pos_iff_mass_balance (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m 1 n)) :
    0 < nativeSourceSchurRemainder 1 n ↔
      nativeThetaNegativeMass (nativeSchurEulerPolynomial 1 n) <
        2*c₀*(nativeSchurCriticalReadout 1 n)^2 +
          nativeThetaPositiveMass (nativeSchurEulerPolynomial 1 n) := by
  have hp : (0 : ℝ) < ((4*n+4 : ℕ) : ℝ) := by positivity
  rw [← mul_pos_iff_of_pos_left hp,nativeSchurEuler_odd_mass_balance n hA,sub_pos]

end
end CarrySelfAdjointOperator
