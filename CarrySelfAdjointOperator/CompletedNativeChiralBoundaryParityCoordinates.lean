import CarrySelfAdjointOperator.CompletedNativeChiralEvenBoundarySplit

/-! Only the inverse signed even/odd reindexing; no new carrier or metric. -/
namespace CarrySelfAdjointOperator
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false

/-- The inverse of the inherited parity phases on the original coordinates. -/
def nativeSourceBoundaryFromParity (n : ℕ) (y z : Fin n → ℂ)
    (a : Fin (2*n)) : ℂ :=
  let i : Fin n := ⟨(a : ℕ)/2,by omega⟩
  (((-1 : ℝ)^(i : ℕ) : ℝ) : ℂ) * (if (a : ℕ)%2=0 then y i else z i)

private theorem phase_square (i : ℕ) :
    (((-1 : ℝ)^i : ℝ) : ℂ) * (((-1 : ℝ)^i : ℝ) : ℂ) = 1 := by
  norm_cast
  rw [← pow_add]
  exact Even.neg_one_pow ⟨i,by omega⟩

@[simp] theorem nativeSourceEvenBoundaryPhase_fromParity (n : ℕ) (y z : Fin n → ℂ) :
    nativeSourceEvenBoundaryPhase n (nativeSourceBoundaryFromParity n y z) = y := by
  funext i
  unfold nativeSourceEvenBoundaryPhase nativeSourceBoundaryFromParity
  dsimp only [nativeSourceEvenBoundaryIndex]
  have hd : 2*(i : ℕ)/2 = (i : ℕ) := by omega
  have hm : 2*(i : ℕ)%2 = 0 := by omega
  simp only [hd,hm,if_true]
  rw [← mul_assoc,phase_square,one_mul]

@[simp] theorem nativeSourceOddBoundaryPhase_fromParity (n : ℕ) (y z : Fin n → ℂ) :
    nativeSourceOddBoundaryPhase n (nativeSourceBoundaryFromParity n y z) = z := by
  funext i
  unfold nativeSourceOddBoundaryPhase nativeSourceBoundaryFromParity
  dsimp only [nativeSourceOddBoundaryIndex]
  have hd : (2*(i : ℕ)+1)/2 = (i : ℕ) := by omega
  have hm : (2*(i : ℕ)+1)%2 = 1 := by omega
  simp only [hd,hm,one_ne_zero,if_false]
  rw [← mul_assoc,phase_square,one_mul]

@[simp] theorem nativeSourceBoundaryFromParity_phases (n : ℕ) (x : Fin (2*n) → ℂ) :
    nativeSourceBoundaryFromParity n
      (nativeSourceEvenBoundaryPhase n x) (nativeSourceOddBoundaryPhase n x) = x := by
  funext a
  unfold nativeSourceBoundaryFromParity
  dsimp only
  split_ifs with ha
  · unfold nativeSourceEvenBoundaryPhase
    dsimp only [nativeSourceEvenBoundaryIndex]
    have hi : (⟨2*((a : ℕ)/2),by omega⟩ : Fin (2*n)) = a := by
      apply Fin.ext
      dsimp only
      omega
    rw [hi,← mul_assoc,phase_square,one_mul]
  · unfold nativeSourceOddBoundaryPhase
    dsimp only [nativeSourceOddBoundaryIndex]
    have hi : (⟨2*((a : ℕ)/2)+1,by omega⟩ : Fin (2*n)) = a := by
      apply Fin.ext
      dsimp only
      omega
    rw [hi,← mul_assoc,phase_square,one_mul]

/-- Nonzero source data cannot disappear in both parity blocks. -/
theorem nativeSourceBoundaryPhase_nonzero (n : ℕ) (x : Fin (2*n) → ℂ) (hx : x ≠ 0) :
    nativeSourceEvenBoundaryPhase n x ≠ 0 ∨ nativeSourceOddBoundaryPhase n x ≠ 0 := by
  by_contra h
  push Not at h
  have hi := nativeSourceBoundaryFromParity_phases n x
  rw [h.1,h.2] at hi
  apply hx
  rw [← hi]
  funext a
  simp [nativeSourceBoundaryFromParity]
end
end CarrySelfAdjointOperator
