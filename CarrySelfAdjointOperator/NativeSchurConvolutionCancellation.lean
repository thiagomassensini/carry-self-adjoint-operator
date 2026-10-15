import CarrySelfAdjointOperator.NativeSourceAllOrderSchur

/-! Exact cancellation of the logarithmic source convolution in monic
Schur critical directions. Orthogonality is to the OLD prefix only. -/
namespace CarrySelfAdjointOperator
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def sourceMomentConvolution (q : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, q k*q (n-1-k)

def sourceMomentConvolutionLeg (q : ℕ → ℝ) (s i j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range i, q k*q (i-1-k+j+s)

private theorem convolution_split_one (q : ℕ → ℝ) (i j : ℕ) :
    sourceMomentConvolution q (i+j+1) =
      (∑ k ∈ Finset.range i, q k*q (i+j-k)) +
      (∑ k ∈ Finset.range j, q k*q (i+j-k)) + q i*q j := by
  unfold sourceMomentConvolution
  rw [show i+j+1=i+(j+1) by omega, Finset.sum_range_add]
  simp only [show i+(j+1)-1=i+j by omega, Nat.add_sub_add_left]
  have hr : (∑ k ∈ Finset.range (j+1), q (i+k)*q (j-k)) =
      ∑ k ∈ Finset.range (j+1), q k*q (i+j-k) := by
    rw [← Finset.sum_range_reflect (fun k => q (i+k)*q (j-k)) (j+1)]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [show j+1-1-k=j-k by omega, show j-(j-k)=k by omega,
      show i+(j-k)=i+j-k by omega]
    ring
  rw [hr, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel_right]
  ring

theorem sourceMomentConvolution_split_one (q : ℕ → ℝ) (i j : ℕ) :
    sourceMomentConvolution q (i+j+1) =
      sourceMomentConvolutionLeg q 1 i j + sourceMomentConvolutionLeg q 1 j i + q i*q j := by
  rw [convolution_split_one]
  unfold sourceMomentConvolutionLeg
  have hi : (∑ k ∈ Finset.range i, q k*q (i+j-k)) =
      ∑ k ∈ Finset.range i, q k*q (i-1-k+j+1) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [show i+j-k=i-1-k+j+1 by have := Finset.mem_range.mp hk; omega]
  have hj : (∑ k ∈ Finset.range j, q k*q (i+j-k)) =
      ∑ k ∈ Finset.range j, q k*q (j-1-k+i+1) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [show i+j-k=j-1-k+i+1 by have := Finset.mem_range.mp hk; omega]
  rw [hi,hj]

theorem sourceMomentConvolution_split_zero (q : ℕ → ℝ) (i j : ℕ) :
    sourceMomentConvolution q (i+j) =
      sourceMomentConvolutionLeg q 0 i j + sourceMomentConvolutionLeg q 0 j i := by
  cases i with
  | zero => simp [sourceMomentConvolution, sourceMomentConvolutionLeg]
  | succ i =>
    rw [show i+1+j=i+j+1 by omega, convolution_split_one]
    unfold sourceMomentConvolutionLeg
    rw [Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.zero_add, Nat.add_zero]
    have hj : (∑ k ∈ Finset.range j, q k*q (i+j-k)) =
        ∑ k ∈ Finset.range j, q k*q (j-1-k+(i+1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [show i+j-k=j-1-k+(i+1) by have := Finset.mem_range.mp hk; omega]
    have hi : (∑ k ∈ Finset.range i, q k*q (i+j-k)) =
        ∑ k ∈ Finset.range i, q k*q (i-k+j) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [show i+j-k=i-k+j by have := Finset.mem_range.mp hk; omega]
    rw [hi,hj]
    ring

private theorem critical_convolution_leg_zero (q : ℕ → ℝ) (s n : ℕ)
    (v : Fin (n+1) → ℝ)
    (ho : ∀ a < n, ∑ j : Fin (n+1), v j*q (a+j.val+s) = 0) :
    ∑ i : Fin (n+1), ∑ j : Fin (n+1),
      v i*v j*sourceMomentConvolutionLeg q s i.val j.val = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : (∑ j : Fin (n+1), v j*sourceMomentConvolutionLeg q s i.val j.val) = 0 := by
    simp only [sourceMomentConvolutionLeg, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hir := i.isLt
    calc
      _ = q k * ∑ j : Fin (n+1), v j*q (i.val-1-k+j.val+s) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [ho (i.val-1-k) (by omega), mul_zero]
  calc
    _ = v i * ∑ j : Fin (n+1), v j*sourceMomentConvolutionLeg q s i.val j.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [hi,mul_zero]

private theorem critical_convolution_other_leg_zero (q : ℕ → ℝ) (s n : ℕ)
    (v : Fin (n+1) → ℝ)
    (ho : ∀ a < n, ∑ j : Fin (n+1), v j*q (a+j.val+s) = 0) :
    ∑ i : Fin (n+1), ∑ j : Fin (n+1),
      v i*v j*sourceMomentConvolutionLeg q s j.val i.val = 0 := by
  rw [Finset.sum_comm]
  convert critical_convolution_leg_zero q s n v ho using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sourceMomentConvolution_critical_even (q : ℕ → ℝ) (n : ℕ)
    (v : Fin (n+1) → ℝ)
    (ho : ∀ a < n, ∑ j : Fin (n+1), v j*q (a+j.val) = 0) :
    ∑ i : Fin (n+1), ∑ j : Fin (n+1), v i*v j*sourceMomentConvolution q (i.val+j.val) = 0 := by
  simp_rw [sourceMomentConvolution_split_zero]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [critical_convolution_leg_zero q 0 n v (by simpa using ho),
    critical_convolution_other_leg_zero q 0 n v (by simpa using ho), zero_add]

theorem sourceMomentConvolution_critical_odd (q : ℕ → ℝ) (n : ℕ)
    (v : Fin (n+1) → ℝ)
    (ho : ∀ a < n, ∑ j : Fin (n+1), v j*q (a+j.val+1) = 0) :
    ∑ i : Fin (n+1), ∑ j : Fin (n+1), v i*v j*sourceMomentConvolution q (i.val+j.val+1) =
      (∑ i : Fin (n+1), v i*q i.val)^2 := by
  simp_rw [sourceMomentConvolution_split_one]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [critical_convolution_leg_zero q 1 n v ho,
    critical_convolution_other_leg_zero q 1 n v ho]
  simp only [zero_add]
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end CarrySelfAdjointOperator
