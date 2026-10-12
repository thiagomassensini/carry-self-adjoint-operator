import CarrySelfAdjointOperator.NativePhysicalMixedProbes
import Mathlib.LinearAlgebra.Vandermonde

namespace CarrySelfAdjointOperator.PhysicalSewing
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open NativeLaguerre
noncomputable section
set_option autoImplicit false

theorem rho_injective : Function.Injective rho := by
  intro i j hij
  have hi : (2*(i : ℝ)+3) ≠ 0 := by positivity
  have hj : (2*(j : ℝ)+3) ≠ 0 := by positivity
  unfold rho at hij
  field_simp at hij
  have he : (i : ℝ) = (j : ℝ) := by nlinarith
  exact_mod_cast he

def laguerreFirstMomentMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun r j => (feature r.val j.val : ℂ)

def laguerreFirstMoments (N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) :=
  (laguerreFirstMomentMatrix N).mulVecLin

theorem laguerreFirstMomentMatrix_vandermonde (N : ℕ) :
    laguerreFirstMomentMatrix N =
      (Matrix.vandermonde (fun j : Fin N => (rho j.val : ℂ)))ᵀ *
        Matrix.diagonal (fun j : Fin N => (feature 0 j.val : ℂ)) := by
  ext r j
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.vandermonde_apply,
    laguerreFirstMomentMatrix, feature, pow_zero]
  push_cast
  ring

theorem laguerreFirstMomentMatrix_det_ne_zero (N : ℕ) :
    (laguerreFirstMomentMatrix N).det ≠ 0 := by
  rw [laguerreFirstMomentMatrix_vandermonde, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  apply mul_ne_zero
  · apply Matrix.det_vandermonde_ne_zero_iff.mpr
    intro i j h
    exact Fin.ext (rho_injective (Complex.ofReal_injective h))
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _
    have hf : 0 < feature 0 j.val := by unfold feature; positivity
    exact_mod_cast hf.ne'

/-- Arbitrary finite dimension, including the empty dimension. -/
theorem laguerreFirstMoments_injective (N : ℕ) : Function.Injective (laguerreFirstMoments N) := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr
    (laguerreFirstMomentMatrix_det_ne_zero N))

theorem laguerreFirstMoments_decode (N : ℕ) (v : Fin N → ℂ) :
    (laguerreFirstMomentMatrix N)⁻¹ *ᵥ laguerreFirstMoments N v = v := by
  change (laguerreFirstMomentMatrix N)⁻¹ *ᵥ ((laguerreFirstMomentMatrix N) *ᵥ v) = v
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (laguerreFirstMomentMatrix_det_ne_zero N)), Matrix.one_mulVec]

theorem twoPortLaguerreFirstMoments_injective (N : ℕ) :
    Function.Injective (fun p : (Fin N → ℂ) × (Fin N → ℂ) =>
      (laguerreFirstMoments N p.1, laguerreFirstMoments N p.2)) := by
  intro p s h
  exact Prod.ext (laguerreFirstMoments_injective N (congrArg Prod.fst h))
    (laguerreFirstMoments_injective N (congrArg Prod.snd h))

theorem laguerreFirstMoments_secondPortDefect (N : ℕ) (theta v wG : Fin N → ℂ) :
    laguerreFirstMoments N wG = laguerreFirstMoments N (fun j => theta j*v j) ↔
      secondPortDefect N theta v wG = 0 := by
  rw [(laguerreFirstMoments_injective N).eq_iff]
  exact sub_eq_zero.symm

/-- Algebraic synthetic example; theta is not an evaluation of F. -/
theorem shortHead_synthetic_canary :
    laguerreReadout 0 (![3,-5] : Fin 2 → ℂ) = 0 ∧
    laguerreReadout 0 (fun j : Fin 2 => (![Complex.I/8,Complex.I/4] : Fin 2 → ℂ) j *
      (![3,-5] : Fin 2 → ℂ) j) = -Complex.I/4 := by
  constructor <;> norm_num [laguerreReadout, feature, rho, Fin.sum_univ_two]
  ring

theorem shortHead_cannot_determine_synthetic_secondPort :
    ¬ ∃ T : ℂ → ℂ, ∀ v : Fin 2 → ℂ,
      laguerreReadout 0 (fun j => (![Complex.I/8,Complex.I/4] : Fin 2 → ℂ) j * v j) =
        T (laguerreReadout 0 v) := by
  rintro ⟨T, hT⟩
  have hz := hT 0
  have hc := hT (![3,-5])
  simp only [Pi.zero_apply, mul_zero, laguerreReadout, Finset.sum_const_zero] at hz
  rw [shortHead_synthetic_canary.1, shortHead_synthetic_canary.2, ← hz] at hc
  have hi : Complex.I ≠ 0 := Complex.I_ne_zero
  apply hi
  linear_combination -4*hc

/-- Each mixed probe retains its own exact Laguerre tail. -/
theorem mixedPhysicalProbes_headTail (N k R : ℕ) (theta d : Fin N → ℂ) (a : Fin N) :
    mixedPhysicalProbes N k theta d a = mixedProbeScale k *
      ((∑ r : Fin (R+1), (feature r.val a.val : ℂ) * laguerreReadout r.val d) +
       matrixPairing (tailDiagonal R N * cauchyMatrix N * tailDiagonal R N) (Pi.single a 1) d) := by
  have he : mixedPhysicalProbes N k theta d a = mixedProbeScale k *
      matrixPairing (cauchyMatrix N) (Pi.single a 1) d := by
    rw [mixedPhysicalProbes_formula]
    simp [matrixPairing, dotProduct, Pi.single_apply]
  rw [he, matrixPairing_head_tail]
  congr 2
  apply Finset.sum_congr rfl
  intro r _
  simp [laguerreReadout, Pi.single_apply]

theorem mixedPhysicalProbes_tail_as_originalGram (N k R : ℕ) (theta d : Fin N → ℂ) (a : Fin N) :
    mixedPhysicalProbes N k theta d a = mixedProbeScale k *
      ((∑ r : Fin (R+1), (feature r.val a.val : ℂ) * laguerreReadout r.val d) +
       matrixPairing (cauchyMatrix N) (tailDiagonal R N *ᵥ Pi.single a 1) (tailDiagonal R N *ᵥ d)) := by
  rw [mixedPhysicalProbes_headTail]
  congr 2
  unfold matrixPairing
  simp only [← Matrix.mulVec_mulVec]
  have hd : (tailDiagonal R N)ᴴ = tailDiagonal R N := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [tailDiagonal, Matrix.conjTranspose_apply, RCLike.star_def]
    · simp [tailDiagonal, Matrix.conjTranspose_apply, hij, Ne.symm hij]
  have he : star (Pi.single a (1 : ℂ)) ᵥ* tailDiagonal R N =
      star (tailDiagonal R N *ᵥ Pi.single a 1) := by
    rw [Matrix.star_mulVec, hd]
  rw [Matrix.dotProduct_mulVec, he]

end
end CarrySelfAdjointOperator.PhysicalSewing
