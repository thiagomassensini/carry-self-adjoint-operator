import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Radial Vandermonde coordinates and their first high jets

The nodes are arbitrary distinct real numbers. Positivity is only needed by
the later analytic sampling adapter, not by this finite algebra. The nodal
polynomial supplies the moment recurrence, while the exact inverse formula
shows that every coordinate above the interpolation range has its expected
power of the radial variable.
-/

namespace CarrySelfAdjointOperator

open scoped BigOperators Matrix
open Polynomial

noncomputable section
set_option autoImplicit false

/-- Rows are powers and columns are nodes, as in the radial sampling chart. -/
def radialVandermondeMatrix {N : ℕ} (a : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ := (Matrix.vandermonde a)ᵀ

/-- The inverse maps boundary jets to the sampled source coefficients. -/
def radialVandermondeInverse {N : ℕ} (a : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ := (radialVandermondeMatrix a)⁻¹

/-- The monic polynomial that vanishes at every radial node. -/
def radialVandermondeNodalPolynomial {N : ℕ} (a : Fin N → ℝ) : Polynomial ℝ :=
  ∏ i : Fin N, (X - C (a i))

/-- Distinct nodes make the radial Vandermonde matrix invertible. -/
theorem radialVandermondeMatrix_det_ne_zero {N : ℕ} (a : Fin N → ℝ)
    (ha : Function.Injective a) : (radialVandermondeMatrix a).det ≠ 0 := by
  rw [radialVandermondeMatrix, Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr ha

theorem radialVandermondeMatrix_det_isUnit {N : ℕ} (a : Fin N → ℝ)
    (ha : Function.Injective a) : IsUnit (radialVandermondeMatrix a).det :=
  isUnit_iff_ne_zero.mpr (radialVandermondeMatrix_det_ne_zero a ha)

theorem radialVandermondeMatrix_isUnit {N : ℕ} (a : Fin N → ℝ)
    (ha : Function.Injective a) : IsUnit (radialVandermondeMatrix a) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (radialVandermondeMatrix_det_isUnit a ha)

theorem radialVandermondeMatrix_mul_inverse {N : ℕ} (a : Fin N → ℝ)
    (ha : Function.Injective a) :
    radialVandermondeMatrix a * radialVandermondeInverse a = 1 :=
  Matrix.mul_nonsing_inv _ (radialVandermondeMatrix_det_isUnit a ha)

/-- The inverse matrix extracts each coefficient of a polynomial of degree below N. -/
theorem radialVandermonde_inverse_moment {N : ℕ} (a : Fin N → ℝ)
    (ha : Function.Injective a) (r j : Fin N) :
    (∑ i : Fin N, a i ^ (r : ℕ) * radialVandermondeInverse a i j) =
      if r = j then 1 else 0 := by
  have h := radialVandermondeMatrix_mul_inverse a ha
  have hij := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M r j) h
  simpa [radialVandermondeMatrix, radialVandermondeInverse,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.vandermonde_apply,
    Matrix.one_apply] using hij

theorem radialVandermondeNodalPolynomial_coeff_pred {N : ℕ} (a : Fin N → ℝ)
    (hN : 0 < N) :
    (radialVandermondeNodalPolynomial a).coeff (N - 1) = -∑ i : Fin N, a i := by
  simpa [radialVandermondeNodalPolynomial] using
    (Polynomial.prod_X_sub_C_coeff_card_pred
      (Finset.univ : Finset (Fin N)) a (by simp [hN]))

theorem radialVandermondeNodalPolynomial_eval {N : ℕ} (a : Fin N → ℝ)
    (i : Fin N) : (radialVandermondeNodalPolynomial a).eval (a i) = 0 := by
  unfold radialVandermondeNodalPolynomial
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem radialVandermondeNodalPolynomial_monic {N : ℕ} (a : Fin N → ℝ) :
    (radialVandermondeNodalPolynomial a).Monic := by
  unfold radialVandermondeNodalPolynomial
  exact Polynomial.monic_prod_of_monic Finset.univ _
    (by intro i hi; exact Polynomial.monic_X_sub_C _)

theorem radialVandermondeNodalPolynomial_natDegree {N : ℕ} (a : Fin N → ℝ) :
    (radialVandermondeNodalPolynomial a).natDegree = N := by
  unfold radialVandermondeNodalPolynomial
  rw [Polynomial.natDegree_prod_of_monic]
  · simp
  · intro i hi
    exact Polynomial.monic_X_sub_C _

theorem radialVandermondeNodalPolynomial_coeff_top {N : ℕ} (a : Fin N → ℝ) :
    (radialVandermondeNodalPolynomial a).coeff N = 1 := by
  have hdeg := radialVandermondeNodalPolynomial_natDegree a
  simpa only [hdeg] using (radialVandermondeNodalPolynomial_monic a).coeff_natDegree

/-- The nodal polynomial gives the full power recurrence for any source weights. -/
theorem radialVandermondeMoment_recurrence {N : ℕ} (a d : Fin N → ℝ)
    (r : ℕ) :
    (∑ i : Fin N, d i * a i ^ (N + r)) =
      -∑ k ∈ Finset.range N, (radialVandermondeNodalPolynomial a).coeff k *
        (∑ i : Fin N, d i * a i ^ (r + k)) := by
  classical
  let p := radialVandermondeNodalPolynomial a
  have hpdeg : p.natDegree = N := radialVandermondeNodalPolynomial_natDegree a
  have hptop : p.coeff N = 1 := radialVandermondeNodalPolynomial_coeff_top a
  have hnode (i : Fin N) : a i ^ N =
      -∑ k ∈ Finset.range N, p.coeff k * a i ^ k := by
    have hz : p.eval (a i) = 0 := radialVandermondeNodalPolynomial_eval a i
    rw [Polynomial.eval_eq_sum_range' (p := p) (n := N + 1) (by omega) (a i)] at hz
    rw [Finset.sum_range_succ] at hz
    rw [hptop, one_mul] at hz
    linarith [hz]
  have hterm (i : Fin N) :
      d i * a i ^ (N + r) =
        -∑ k ∈ Finset.range N, p.coeff k * (d i * a i ^ (r + k)) := by
    rw [pow_add, hnode]
    rw [neg_mul, mul_neg, Finset.sum_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [pow_add]
    ring
  calc
    _ = ∑ i : Fin N, (-∑ k ∈ Finset.range N,
        p.coeff k * (d i * a i ^ (r + k))) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hterm i
    _ = -∑ k ∈ Finset.range N, p.coeff k *
        (∑ i : Fin N, d i * a i ^ (r + k)) := by
          rw [Finset.sum_neg_distrib, Finset.sum_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          rw [← Finset.mul_sum]

/-- For high coordinates the inverse formula is an exact polynomial, not a
Laurent expression. -/
def radialVandermondeHighCoordinate {N : ℕ} (a : Fin N → ℝ)
    (x : Fin N → ℂ) (t : ℝ) (m : ℕ) : ℂ :=
  ∑ j : Fin N,
    (((∑ i : Fin N, a i ^ m * radialVandermondeInverse a i j) *
      t ^ (m - (j : ℕ)) : ℝ) : ℂ) * x j

/-- The regularized coordinate agrees with the unchanged jet prefix. -/
def radialVandermondeBoundaryCoordinate {N : ℕ} (a : Fin N → ℝ)
    (x : Fin N → ℂ) (t : ℝ) (m : ℕ) : ℂ :=
  if hm : m < N then x ⟨m, hm⟩ else radialVandermondeHighCoordinate a x t m

theorem radialVandermondeHighCoordinate_factor {N : ℕ} (a : Fin N → ℝ)
    (x : Fin N → ℂ) (t : ℝ) (m : ℕ) (hm : N ≤ m) :
    radialVandermondeHighCoordinate a x t m =
      ((t : ℂ) ^ (m - N + 1)) *
        ∑ j : Fin N,
          (((∑ i : Fin N, a i ^ m * radialVandermondeInverse a i j) *
            t ^ (N - 1 - (j : ℕ)) : ℝ) : ℂ) * x j := by
  unfold radialVandermondeHighCoordinate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hpow : m - (j : ℕ) = (m - N + 1) + (N - 1 - (j : ℕ)) := by omega
  rw [hpow, pow_add]
  push_cast
  ring

/-- The first high moment of the inverse Vandermonde chart is the first
elementary symmetric function of the nodes. -/
theorem radialVandermonde_lastHighMoment {N : ℕ} (a : Fin N → ℝ)
    (ha : Function.Injective a) (hN : 0 < N) :
    (∑ i : Fin N, a i ^ N * radialVandermondeInverse a i ⟨N - 1, by omega⟩) =
      ∑ i : Fin N, a i := by
  classical
  let last : Fin N := ⟨N - 1, by omega⟩
  have hrec := radialVandermondeMoment_recurrence a
    (fun i => radialVandermondeInverse a i last) 0
  have hlow (k : ℕ) (hk : k < N) :
      (∑ i : Fin N, radialVandermondeInverse a i last * a i ^ k) =
        if k = N - 1 then 1 else 0 := by
    have h := radialVandermonde_inverse_moment a ha ⟨k,hk⟩ last
    simpa [last, mul_comm] using h
  have hsum : (∑ k ∈ Finset.range N,
      (radialVandermondeNodalPolynomial a).coeff k *
        (∑ i : Fin N, radialVandermondeInverse a i last * a i ^ k)) =
      (radialVandermondeNodalPolynomial a).coeff (N - 1) := by
    calc
      _ = ∑ k ∈ Finset.range N,
          (radialVandermondeNodalPolynomial a).coeff k *
            (if k = N - 1 then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [hlow k (Finset.mem_range.mp hk)]
      _ = (radialVandermondeNodalPolynomial a).coeff (N - 1) := by
            rw [Finset.sum_eq_single (N - 1)]
            · simp
            · intro k hk hkn
              simp [hkn]
            · intro hnot
              exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  simp only [Nat.add_zero, Nat.zero_add] at hrec
  rw [hsum] at hrec
  rw [radialVandermondeNodalPolynomial_coeff_pred a hN] at hrec
  have hcomm : (∑ i : Fin N, radialVandermondeInverse a i last * a i ^ N) =
      (∑ i : Fin N, a i ^ N * radialVandermondeInverse a i last) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hcomm] at hrec
  simpa [last] using hrec

/-- The coefficient of `t` in the first reconstructed high coordinate. -/
theorem radialVandermondeHighCoordinate_firstJet {N : ℕ} (a : Fin N → ℝ)
    (x : Fin N → ℂ) (t : ℝ) (ha : Function.Injective a) (hN : 0 < N) :
    radialVandermondeHighCoordinate a x t N =
      (t : ℂ) * (∑ i : Fin N, a i) * x ⟨N - 1, by omega⟩ +
        (t : ℂ) ^ 2 *
          ∑ j ∈ (Finset.univ.erase (⟨N - 1, by omega⟩ : Fin N)),
            (((∑ i : Fin N, a i ^ N * radialVandermondeInverse a i j) *
              t ^ (N - (j : ℕ) - 2) : ℝ) : ℂ) * x j := by
  classical
  unfold radialVandermondeHighCoordinate
  let last : Fin N := ⟨N - 1, by omega⟩
  have hlast : (∑ i : Fin N, a i ^ N * radialVandermondeInverse a i last) =
      ∑ i : Fin N, a i := radialVandermonde_lastHighMoment a ha hN
  have hterm (j : Fin N) (hj : j ≠ last) :
      (((∑ i : Fin N, a i ^ N * radialVandermondeInverse a i j) *
        t ^ (N - (j : ℕ)) : ℝ) : ℂ) * x j =
        (t : ℂ)^2 *
          (((∑ i : Fin N, a i ^ N * radialVandermondeInverse a i j) *
            t ^ (N - (j : ℕ) - 2) : ℝ) : ℂ) * x j := by
    have hjlt : (j : ℕ) < N - 1 := by
      have := j.isLt
      have hjval : (j : ℕ) ≠ N - 1 := by
        intro h
        apply hj
        apply Fin.ext
        simpa [last] using h
      omega
    have hexp : N - (j : ℕ) = 2 + (N - (j : ℕ) - 2) := by omega
    have hpow : t ^ (N - (j : ℕ)) = t ^ 2 * t ^ (N - (j : ℕ) - 2) := by
      calc
        t ^ (N - (j : ℕ)) = t ^ ((N - (j : ℕ) - 2) + 2) := by
          congr 1
          omega
        _ = t ^ (N - (j : ℕ) - 2) * t ^ 2 := by rw [pow_add]
        _ = t ^ 2 * t ^ (N - (j : ℕ) - 2) := by ring
    rw [hpow]
    push_cast
    ring
  let f : Fin N → ℂ := fun j =>
    (((∑ i : Fin N, a i ^ N * radialVandermondeInverse a i j) *
      t ^ (N - (j : ℕ)) : ℝ) : ℂ) * x j
  let g : Fin N → ℂ := fun j =>
    (((∑ i : Fin N, a i ^ N * radialVandermondeInverse a i j) *
      t ^ (N - (j : ℕ) - 2) : ℝ) : ℂ) * x j
  change (∑ j : Fin N, f j) = _
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ last)]
  have hfirst : f last = (t : ℂ) * (∑ i : Fin N, a i) * x last := by
    have hn : N - (last : ℕ) = 1 := by change N - (N - 1) = 1; omega
    simp only [f, hlast, hn]
    push_cast
    ring
  rw [hfirst]
  have hrest : (∑ j ∈ Finset.univ.erase last, f j) =
      (t : ℂ)^2 * ∑ j ∈ Finset.univ.erase last, g j := by
    calc
      _ = ∑ j ∈ Finset.univ.erase last, (t : ℂ)^2 * g j := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          f j = (((∑ i : Fin N, a i ^ N * radialVandermondeInverse a i j) *
              t ^ (N - (j : ℕ)) : ℝ) : ℂ) * x j := rfl
          _ = ((t : ℂ)^2 *
              (((∑ i : Fin N, a i ^ N * radialVandermondeInverse a i j) *
                t ^ (N - (j : ℕ) - 2) : ℝ) : ℂ)) * x j := hterm j (Finset.ne_of_mem_erase hj)
          _ = (t : ℂ)^2 * g j := by dsimp [g]; ring
      _ = (t : ℂ)^2 * ∑ j ∈ Finset.univ.erase last, g j := by
        rw [Finset.mul_sum]
  rw [hrest]


end
end CarrySelfAdjointOperator
