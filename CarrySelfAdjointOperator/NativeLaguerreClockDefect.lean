import CarrySelfAdjointOperator.NativeCauchyLaguerreExactGram

/-! Exact finite Jacobi row defect. The material clock is `log(j+1)`.
The formula below does not construct a bounded geometric log operator. -/
namespace CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000

/-- Algebraic formula for the real-index derivative; the analytic derivative
and the maximal multiplication domain are separate obligations. -/
def featureDerivativeFormula (r j : ℕ) : ℝ :=
  feature r j * ((r : ℝ)/((j : ℝ)+1/2) - (r+1 : ℕ)/((j : ℝ)+3/2))

def fullJacobiRow (r j : ℕ) : ℝ :=
  (r : ℝ) * feature (r-1) j - (2*(r : ℝ)+1)*feature r j +
    (r+1 : ℕ)*feature (r+1) j

theorem fullJacobiRow_eq_derivativeFormula (r j : ℕ) :
    fullJacobiRow r j = featureDerivativeFormula r j := by
  cases r with
  | zero =>
    unfold fullJacobiRow featureDerivativeFormula feature rho
    simp only [Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, pow_zero, pow_one,
      zero_div, zero_sub, zero_add]
    field_simp
    ring
  | succ r =>
    unfold fullJacobiRow featureDerivativeFormula feature rho
    simp only [Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one, pow_succ]
    field_simp
    ring

/-- The actual tridiagonal row restricted to orders `0..R`, applied to a
feature column. The upper neighbor is retained precisely when `r<R`. -/
def cutoffJacobiRow (R r j : ℕ) : ℝ :=
  (r : ℝ)*feature (r-1) j - (2*(r : ℝ)+1)*feature r j +
    if r<R then (r+1 : ℕ)*feature (r+1) j else 0

theorem finite_clock_defect_entry (R j : ℕ) (r : Fin (R+1)) :
    cutoffJacobiRow R r j - Real.log ((j : ℝ)+1)*feature r j =
      featureDerivativeFormula r j - Real.log ((j : ℝ)+1)*feature r j -
        if (r : ℕ)=R then (R+1 : ℕ)*feature (R+1) j else 0 := by
  rw [← fullJacobiRow_eq_derivativeFormula]
  by_cases hr : (r : ℕ)=R
  · simp [cutoffJacobiRow, fullJacobiRow, hr]
    ring
  · have hlt : (r : ℕ)<R := by omega
    simp [cutoffJacobiRow, fullJacobiRow, hr, hlt]

theorem finite_clock_defect_seed :
    cutoffJacobiRow 0 0 0 - Real.log (1 : ℝ)*feature 0 0 = -2/3 := by
  norm_num [cutoffJacobiRow, feature, rho]

def materialClockMatrix (M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.diagonal (fun j => (Real.log ((j : ℝ)+1) : ℂ))

theorem material_clock_commutator_entry (M : ℕ) (i j : Fin M) :
    (cauchyMatrix M * materialClockMatrix M - materialClockMatrix M * cauchyMatrix M) i j =
      (cauchyEntry i j : ℂ) *
        ((Real.log ((j : ℝ)+1) : ℂ) - (Real.log ((i : ℝ)+1) : ℂ)) := by
  simp [Matrix.mul_apply, materialClockMatrix, cauchyMatrix, Matrix.diagonal_apply]
  ring

theorem material_clock_does_not_commute :
    cauchyMatrix 2 * materialClockMatrix 2 ≠ materialClockMatrix 2 * cauchyMatrix 2 := by
  intro h
  have he := material_clock_commutator_entry 2 (0 : Fin 2) (1 : Fin 2)
  rw [h, sub_self] at he
  have hp : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hn : (Real.log (2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [Matrix.zero_apply, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one,
    zero_add, Real.log_one, Complex.ofReal_zero, sub_zero] at he
  have hc : (cauchyEntry 0 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show cauchyEntry 0 1 ≠ 0 by unfold cauchyEntry; positivity)
  rw [show (1 : ℝ)+1=2 by norm_num] at he
  exact (mul_ne_zero hc hn) he.symm

end
end CarrySelfAdjointOperator.NativeLaguerre
