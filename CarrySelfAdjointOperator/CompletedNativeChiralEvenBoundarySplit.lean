import CarrySelfAdjointOperator.CompletedNativeChiralEvenBoundaryEnergy
import Mathlib.Logic.Equiv.Fin.Basic

/-! The parity phases come from the existing alternating Green tower.
No Hilbert structure, weight choice, operator or finite-step truncation is added. -/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def nativeSourceEvenBoundaryIndex (n : ℕ) (i : Fin n) : Fin (2*n) := ⟨2*(i : ℕ),by omega⟩
def nativeSourceOddBoundaryIndex (n : ℕ) (i : Fin n) : Fin (2*n) := ⟨2*(i : ℕ)+1,by omega⟩

private theorem sum_fin_even_odd (n : ℕ) (f : Fin (2*n) → ℝ) :
    (∑ a, f a) = (∑ i : Fin n, f (nativeSourceEvenBoundaryIndex n i)) + ∑ i : Fin n, f (nativeSourceOddBoundaryIndex n i) := by
  let e : Fin n × Fin 2 ≃ Fin (2*n) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))
  rw [← e.sum_comp f, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Finset.sum_add_distrib]
  apply congrArg₂ (fun a b : ℝ => a+b)
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Fin.ext
    simp [e,finProdFinEquiv,nativeSourceEvenBoundaryIndex]
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Fin.ext
    simp [e,finProdFinEquiv,nativeSourceOddBoundaryIndex]
    omega

/-- The phase is forced by the even alternating boundary coefficients. -/
def nativeSourceEvenBoundaryPhase (n : ℕ) (x : Fin (2*n) → ℂ) (i : Fin n) : ℂ :=
  (((-1 : ℝ)^(i : ℕ) : ℝ) : ℂ) * x (nativeSourceEvenBoundaryIndex n i)

/-- The odd block has the same inherited phase, with its one-step index shift. -/
def nativeSourceOddBoundaryPhase (n : ℕ) (x : Fin (2*n) → ℂ) (i : Fin n) : ℂ :=
  (((-1 : ℝ)^(i : ℕ) : ℝ) : ℂ) * x (nativeSourceOddBoundaryIndex n i)

private theorem real_cross_scale (a b : ℝ) (u v : ℂ) :
    (conj ((a : ℂ)*u)*((b : ℂ)*v)).re = a*b*(conj u*v).re := by
  simp only [Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,sub_zero]
  ring

/-- The raw even-dimensional limiting face contains exactly both response
blocks. This identity concerns the limiting face ONLY. -/
theorem nativeSourceFiniteBoundaryEnergy_even_split (n : ℕ) (x : Fin (2*n) → ℂ) :
    nativeSourceFiniteBoundaryEnergy (2*n) x = 4 *
      ((∑ i : Fin n, ∑ j : Fin n, primeDepthGeometricMoment ((i : ℕ)+(j : ℕ)) *
        (conj (nativeSourceEvenBoundaryPhase n x i)*nativeSourceEvenBoundaryPhase n x j).re) +
       (∑ i : Fin n, ∑ j : Fin n, primeDepthGeometricMoment ((i : ℕ)+(j : ℕ)+1) *
        (conj (nativeSourceOddBoundaryPhase n x i)*nativeSourceOddBoundaryPhase n x j).re)) := by
  let K : Fin (2*n) → Fin (2*n) → ℝ := fun a b =>
    if Even ((a : ℕ)+(b : ℕ)) then
      2 * (-1 : ℝ)^(((a : ℕ)+(b : ℕ))/2+(a : ℕ)) *
        nativeSourceOddBoundaryCoefficient (((a : ℕ)+(b : ℕ))/2) *
          (conj (x a)*x b).re else 0
  have hee (i j : Fin n) : K (nativeSourceEvenBoundaryIndex n i) (nativeSourceEvenBoundaryIndex n j) =
      4*primeDepthGeometricMoment ((i : ℕ)+(j : ℕ)) *
        (conj (nativeSourceEvenBoundaryPhase n x i)*nativeSourceEvenBoundaryPhase n x j).re := by
    have he : Even (2*(i : ℕ)+2*(j : ℕ)) := ⟨(i : ℕ)+(j : ℕ),by omega⟩
    have hd : (2*(i : ℕ)+2*(j : ℕ))/2 = (i : ℕ)+(j : ℕ) := by omega
    have hp : (-1 : ℝ)^(2*(i : ℕ)) = 1 := Even.neg_one_pow ⟨(i : ℕ),by omega⟩
    dsimp only [K,nativeSourceEvenBoundaryIndex]
    rw [if_pos he,hd,pow_add,hp,mul_one,
      nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment]
    unfold nativeSourceEvenBoundaryPhase
    rw [real_cross_scale,pow_add]
    dsimp only [nativeSourceEvenBoundaryIndex,nativeSourceOddBoundaryIndex]
    ring
  have hoo (i j : Fin n) : K (nativeSourceOddBoundaryIndex n i) (nativeSourceOddBoundaryIndex n j) =
      4*primeDepthGeometricMoment ((i : ℕ)+(j : ℕ)+1) *
        (conj (nativeSourceOddBoundaryPhase n x i)*nativeSourceOddBoundaryPhase n x j).re := by
    have he : Even ((2*(i : ℕ)+1)+(2*(j : ℕ)+1)) := ⟨(i : ℕ)+(j : ℕ)+1,by omega⟩
    have hd : ((2*(i : ℕ)+1)+(2*(j : ℕ)+1))/2 = (i : ℕ)+(j : ℕ)+1 := by omega
    have ht : ((i : ℕ)+(j : ℕ)+1)+(2*(i : ℕ)+1) = (i : ℕ)+(j : ℕ)+(2*(i : ℕ)+2) := by omega
    have hp : (-1 : ℝ)^(2*(i : ℕ)+2) = 1 := Even.neg_one_pow ⟨(i : ℕ)+1,by omega⟩
    dsimp only [K,nativeSourceOddBoundaryIndex]
    rw [if_pos he,hd,ht,pow_add,hp,mul_one,
      nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment]
    unfold nativeSourceOddBoundaryPhase
    rw [real_cross_scale,pow_add]
    dsimp only [nativeSourceEvenBoundaryIndex,nativeSourceOddBoundaryIndex]
    ring
  have heo (i j : Fin n) : K (nativeSourceEvenBoundaryIndex n i) (nativeSourceOddBoundaryIndex n j) = 0 := by
    apply if_neg
    rintro ⟨a,ha⟩
    dsimp only [nativeSourceEvenBoundaryIndex,nativeSourceOddBoundaryIndex] at ha
    omega
  have hoe (i j : Fin n) : K (nativeSourceOddBoundaryIndex n i) (nativeSourceEvenBoundaryIndex n j) = 0 := by
    apply if_neg
    rintro ⟨a,ha⟩
    dsimp only [nativeSourceEvenBoundaryIndex,nativeSourceOddBoundaryIndex] at ha
    omega
  rw [nativeSourceFiniteBoundaryEnergy_eq_coefficient_sum]
  change (∑ a, ∑ b, K a b) = _
  rw [sum_fin_even_odd n]
  simp_rw [sum_fin_even_odd n,hee,hoo,heo,hoe]
  simp only [Finset.sum_const_zero,add_zero,zero_add]
  simp only [mul_assoc,Finset.mul_sum,mul_add]
end
end CarrySelfAdjointOperator
