import CarrySelfAdjointOperator.CompletedNativePoleAtomHankelPerturbation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# Finite convolution transport of the C2 pole atom

The normalized pole factor is `1 + 4u`, whose coefficient sequence is the
one-step update `a_n ↦ a_n + 4 a_{n-1}`. Convolution by the completed
coefficient sequence sends the geometric atom `(-4)^j` back to the
pre-factor coefficients. Contracting against a transported critical source
direction therefore evaluates its polynomial at `-4`.

These are algebraic identities only. The transport equation is explicit as a
hypothesis, and no sign of a source kernel, Schur remainder, or pivot is used.
-/

namespace CarrySelfAdjointOperator

open scoped Matrix
noncomputable section
set_option autoImplicit false

/-- Coefficients after multiplication by the normalized pole factor `1+4u`. -/
def nativePoleFactorProductCoefficient (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  a n + if n = 0 then 0 else 4 * a (n - 1)

/-- Lower triangular coefficient-convolution matrix. -/
def nativePoleConvolutionMatrix (c : ℕ → ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if j.val ≤ i.val then c (i.val - j.val) else 0

/-- The finite coefficient convolution of `c` with the geometric pole atom. -/
def nativePoleGeometricConvolution (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), c (n - j) * (-4 : ℝ) ^ j

private theorem nativePoleGeometricConvolution_succ (c : ℕ → ℝ) (n : ℕ) :
    nativePoleGeometricConvolution c (n + 1) =
      c (n + 1) - 4 * nativePoleGeometricConvolution c n := by
  unfold nativePoleGeometricConvolution
  rw [Finset.sum_range_succ']
  simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, pow_zero, mul_one]
  rw [show (∑ j ∈ Finset.range (n + 1),
        c (n - j) * (-4 : ℝ) ^ (j + 1)) =
      -4 * ∑ j ∈ Finset.range (n + 1),
        c (n - j) * (-4 : ℝ) ^ j by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [pow_succ]
          ring_nf]
  ring_nf

/-- Multiplication by `1+4u` followed by convolution with
`1/(1+4u)=Σ (-4)^j u^j` recovers every pre-factor coefficient. -/
theorem nativePoleFactorProduct_geometricConvolution (a : ℕ → ℝ) (n : ℕ) :
    nativePoleGeometricConvolution (nativePoleFactorProductCoefficient a) n = a n := by
  induction n with
  | zero => simp [nativePoleGeometricConvolution, nativePoleFactorProductCoefficient]
  | succ n ih =>
      rw [nativePoleGeometricConvolution_succ,
        nativePoleFactorProductCoefficient]
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      rw [ih]
      rw [show n + 1 - 1 = n by omega]
      ring_nf

private theorem nativePoleConvolutionMatrix_mulVec_atom_apply
    (c : ℕ → ℝ) {N : ℕ} (i : Fin N) :
    (nativePoleConvolutionMatrix c N *ᵥ poleAtomVector N) i =
      nativePoleGeometricConvolution c i.val := by
  simp only [Matrix.mulVec, dotProduct, nativePoleConvolutionMatrix,
    poleAtomVector]
  rw [Finset.sum_fin_eq_sum_range]
  have hi : i.val < N := i.isLt
  have hcancel :
      (∑ j ∈ Finset.range N,
        (if h : j < N then
          (if j ≤ i.val then c (i.val - j) else 0) * (-4 : ℝ) ^ j else 0)) =
      ∑ j ∈ Finset.range N,
        (if j ≤ i.val then c (i.val - j) * (-4 : ℝ) ^ j else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    simp [hjN]
  have hsum :
      (∑ j ∈ Finset.range N,
        (if j ≤ i.val then c (i.val - j) * (-4 : ℝ) ^ j else 0)) =
      ∑ j ∈ Finset.range (i.val + 1),
        (if j ≤ i.val then c (i.val - j) * (-4 : ℝ) ^ j else 0) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hjnot
    have hjgt : i.val < j := by
      have : ¬ j < i.val + 1 := by
        intro hlt
        apply hjnot
        exact Finset.mem_range.mpr hlt
      omega
    simp [not_le_of_gt hjgt]
  rw [hcancel, hsum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ i.val := by
    have hj' := Finset.mem_range.mp hj
    omega
  simp [hjle]

/-- Finite matrix form of the pole-factor cancellation. -/
theorem nativePoleFactorConvolutionMatrix_mul_atom (a : ℕ → ℝ) (N : ℕ) :
    nativePoleConvolutionMatrix (nativePoleFactorProductCoefficient a) N *ᵥ
        poleAtomVector N = fun i => a i.val := by
  funext i
  rw [nativePoleConvolutionMatrix_mulVec_atom_apply,
    nativePoleFactorProduct_geometricConvolution]

/-- A transported critical source direction evaluates the pre-factor
coefficient vector by evaluating its polynomial at the pole atom `-4`. -/
theorem nativePoleCriticalPairing_eq_polynomialEvaluation
    {N : ℕ} (a : ℕ → ℝ) (c₀ : ℝ) (x y : Fin N → ℝ)
    (htransport :
      (nativePoleConvolutionMatrix (nativePoleFactorProductCoefficient a) N).transpose
          *ᵥ y = c₀ • x) :
    dotProduct (fun i : Fin N => a i.val) y =
      c₀ * ∑ i : Fin N, x i * (-4 : ℝ) ^ (i : ℕ) := by
  rw [← nativePoleFactorConvolutionMatrix_mul_atom a N]
  calc
    dotProduct
        (nativePoleConvolutionMatrix (nativePoleFactorProductCoefficient a) N *ᵥ
          poleAtomVector N) y =
        dotProduct (poleAtomVector N)
          ((nativePoleConvolutionMatrix (nativePoleFactorProductCoefficient a) N).transpose
            *ᵥ y) := by
          calc
            _ = dotProduct y
                (nativePoleConvolutionMatrix (nativePoleFactorProductCoefficient a) N *ᵥ
                  poleAtomVector N) := dotProduct_comm _ _
            _ = dotProduct (poleAtomVector N)
                ((nativePoleConvolutionMatrix (nativePoleFactorProductCoefficient a) N).transpose
                  *ᵥ y) :=
                (Matrix.dotProduct_transpose_mulVec
                  (nativePoleConvolutionMatrix (nativePoleFactorProductCoefficient a) N)
                  (poleAtomVector N) y).symm
    _ = c₀ * ∑ i : Fin N, x i * (-4 : ℝ) ^ (i : ℕ) := by
      rw [htransport]
      simp [dotProduct, poleAtomVector, Finset.mul_sum]
      ring_nf

/-- The even-sector pole correction contracts to the negative square of the
critical polynomial evaluation. This is not a sign claim for the full kernel. -/
theorem nativePoleCritical_evenCorrection_eq
    {N : ℕ} (a : ℕ → ℝ) (c₀ : ℝ) (x y : Fin N → ℝ)
    (htransport :
      (nativePoleConvolutionMatrix (nativePoleFactorProductCoefficient a) N).transpose
          *ᵥ y = c₀ • x) :
    -4 * (dotProduct (fun i : Fin N => a i.val) y) ^ 2 =
      -4 * c₀ ^ 2 * (∑ i : Fin N, x i * (-4 : ℝ) ^ (i : ℕ)) ^ 2 := by
  rw [nativePoleCriticalPairing_eq_polynomialEvaluation a c₀ x y htransport]
  ring_nf

/-- The odd-sector pole correction contracts to the positive square of the
critical polynomial evaluation. This is not a sign claim for the full kernel. -/
theorem nativePoleCritical_oddCorrection_eq
    {N : ℕ} (a : ℕ → ℝ) (c₀ : ℝ) (x y : Fin N → ℝ)
    (htransport :
      (nativePoleConvolutionMatrix (nativePoleFactorProductCoefficient a) N).transpose
          *ᵥ y = c₀ • x) :
    16 * (dotProduct (fun i : Fin N => a i.val) y) ^ 2 =
      16 * c₀ ^ 2 * (∑ i : Fin N, x i * (-4 : ℝ) ^ (i : ℕ)) ^ 2 := by
  rw [nativePoleCriticalPairing_eq_polynomialEvaluation a c₀ x y htransport]
  ring_nf

end

end CarrySelfAdjointOperator
