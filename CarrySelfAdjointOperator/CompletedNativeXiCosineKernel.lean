import CarrySelfAdjointOperator.NativeScalarZetaIdentification
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# The Jacobi--theta cosine kernel of the completed native characteristic

The completed native characteristic is the classical Riemann Xi function on
the centered real-height axis.  This file fixes the normalization of its
standard Jacobi--theta cosine kernel.

For an integer mode `n` and `u : ℝ`, the summand is written in the factored
form

`2 π n² exp (5u/2) (2 π n² exp (2u) - 3) exp (-π n² exp (2u))`.

Summing over all integers automatically supplies the factor two coming from
the nonzero modes `n` and `-n`; the zero mode vanishes.  Thus this is the
kernel whose half-line cosine transform has the normalization

`ξ(1/2 + i t) = ∫₀∞ Φ(u) cos(tu) du`.

This module proves absolute summability of the theta series and strict
positivity of the resulting kernel on `u ≥ 0`.  The transform identity and
the strict moment inequality are developed downstream.
-/

namespace CarrySelfAdjointOperator

open HurwitzZeta MeasureTheory Set

noncomputable section

/-- The `n`th integer mode of the standard Riemann Xi cosine kernel.  The
factorization makes its positivity on the positive half-line transparent. -/
def completedNativeXiCosineKernelTerm (n : ℤ) (u : ℝ) : ℝ :=
  2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) *
      (2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u) - 3) *
    Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))

/-- Expanded form of one Xi-kernel mode. -/
theorem completedNativeXiCosineKernelTerm_eq (n : ℤ) (u : ℝ) :
    completedNativeXiCosineKernelTerm n u =
      (4 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
          6 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
        Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)) := by
  unfold completedNativeXiCosineKernelTerm
  have hexp : Real.exp (9 * u / 2) =
      Real.exp (5 * u / 2) * Real.exp (2 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  rw [hexp]
  ring_nf

/-- The integer theta series defining the Xi cosine kernel is absolutely
summable at every real `u`. -/
theorem summable_completedNativeXiCosineKernelTerm (u : ℝ) :
    Summable (fun n : ℤ ↦ completedNativeXiCosineKernelTerm n u) := by
  have hT : 0 < Real.exp (2 * u) := Real.exp_pos _
  have hfour :=
    summable_pow_mul_jacobiTheta₂_term_bound 0 hT 4
  have htwo :=
    summable_pow_mul_jacobiTheta₂_term_bound 0 hT 2
  have hfour' : Summable (fun n : ℤ ↦
      (n : ℝ) ^ 4 *
        Real.exp (-Real.pi * (Real.exp (2 * u) * (n : ℝ) ^ 2))) := by
    simpa only [zero_mul, mul_zero, sub_zero, Int.cast_abs, sq_abs,
      show ∀ x : ℝ, |x| ^ 4 = x ^ 4 by
        intro x
        calc
          |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring_nf
          _ = (x ^ 2) ^ 2 := by rw [sq_abs]
          _ = x ^ 4 := by ring_nf] using hfour
  have htwo' : Summable (fun n : ℤ ↦
      (n : ℝ) ^ 2 *
        Real.exp (-Real.pi * (Real.exp (2 * u) * (n : ℝ) ^ 2))) := by
    simpa only [zero_mul, mul_zero, sub_zero, Int.cast_abs, sq_abs] using htwo
  rw [show (fun n : ℤ ↦ completedNativeXiCosineKernelTerm n u) =
      fun n : ℤ ↦
        (4 * Real.pi ^ 2 * Real.exp (9 * u / 2)) *
            ((n : ℝ) ^ 4 *
              Real.exp (-Real.pi * (Real.exp (2 * u) * (n : ℝ) ^ 2))) -
          (6 * Real.pi * Real.exp (5 * u / 2)) *
            ((n : ℝ) ^ 2 *
              Real.exp (-Real.pi * (Real.exp (2 * u) * (n : ℝ) ^ 2))) by
    funext n
    rw [completedNativeXiCosineKernelTerm_eq]
    ring_nf]
  exact (hfour'.mul_left _).sub (htwo'.mul_left _)

/-- The standard half-line cosine kernel for the completed native
characteristic.  Summing over `ℤ` includes both nonzero theta modes. -/
def completedNativeXiCosineKernel (u : ℝ) : ℝ :=
  ∑' n : ℤ, completedNativeXiCosineKernelTerm n u

@[simp] theorem completedNativeXiCosineKernelTerm_zero (u : ℝ) :
    completedNativeXiCosineKernelTerm 0 u = 0 := by
  simp [completedNativeXiCosineKernelTerm]

/-- The integer modes occur in equal positive/negative pairs. -/
@[simp] theorem completedNativeXiCosineKernelTerm_neg (n : ℤ) (u : ℝ) :
    completedNativeXiCosineKernelTerm (-n) u =
      completedNativeXiCosineKernelTerm n u := by
  simp [completedNativeXiCosineKernelTerm]

/-- Natural-index version of the kernel.  This records explicitly that the
integer theta sum supplies twice the positive-mode series. -/
theorem completedNativeXiCosineKernel_eq_two_mul_tsum (u : ℝ) :
    completedNativeXiCosineKernel u =
      2 * ∑' n : ℕ,
        completedNativeXiCosineKernelTerm (n + 1 : ℤ) u := by
  unfold completedNativeXiCosineKernel
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat]
  · rw [completedNativeXiCosineKernelTerm_zero, zero_add, nsmul_eq_mul]
    have hp := tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ ↦ completedNativeXiCosineKernelTerm (n : ℤ) u)
    rw [hp]
    simp only [Nat.cast_add, Nat.cast_one]
    norm_num
  · intro n
    exact completedNativeXiCosineKernelTerm_neg n u
  · exact summable_completedNativeXiCosineKernelTerm u

/-- Every nonzero theta mode is strictly positive on the closed positive
half-line. -/
theorem completedNativeXiCosineKernelTerm_pos
    {n : ℤ} (hn : n ≠ 0) {u : ℝ} (hu : 0 ≤ u) :
    0 < completedNativeXiCosineKernelTerm n u := by
  have hncast : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hnsq : 1 ≤ (n : ℝ) ^ 2 := by
    rw [one_le_sq_iff_one_le_abs, ← Int.cast_abs, ← Int.cast_one,
      Int.cast_le]
    exact Int.one_le_abs hn
  have hexp : 1 ≤ Real.exp (2 * u) :=
    Real.one_le_exp (by linarith)
  have hprod : 1 ≤ (n : ℝ) ^ 2 * Real.exp (2 * u) := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ (n : ℝ) ^ 2 * Real.exp (2 * u) :=
        mul_le_mul hnsq hexp zero_le_one (sq_nonneg (n : ℝ))
  have hbracket :
      0 < 2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u) - 3 := by
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hscale : 0 < 2 * Real.pi := by positivity
    have := mul_le_mul_of_nonneg_left hprod hscale.le
    nlinarith
  unfold completedNativeXiCosineKernelTerm
  positivity

/-- Every theta mode is nonnegative on the closed positive half-line. -/
theorem completedNativeXiCosineKernelTerm_nonneg
    (n : ℤ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ completedNativeXiCosineKernelTerm n u := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact (completedNativeXiCosineKernelTerm_pos hn hu).le

/-- The Jacobi--theta Xi cosine kernel is strictly positive on `u ≥ 0`. -/
theorem completedNativeXiCosineKernel_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < completedNativeXiCosineKernel u := by
  unfold completedNativeXiCosineKernel
  exact (summable_completedNativeXiCosineKernelTerm u).tsum_pos
    (fun n ↦ completedNativeXiCosineKernelTerm_nonneg n hu)
    1 (completedNativeXiCosineKernelTerm_pos (by norm_num) hu)

/-- The even moments of the concrete Xi cosine kernel. -/
def completedNativeXiCosineMoment (order : ℕ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), u ^ (2 * order) * completedNativeXiCosineKernel u

end

end CarrySelfAdjointOperator
