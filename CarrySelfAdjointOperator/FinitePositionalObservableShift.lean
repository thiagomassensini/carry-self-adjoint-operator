import CarrySelfAdjointOperator.PositionalDepthRefinement
import CarrySelfAdjointOperator.FiniteNativeDepthCameraCommutator

/-! Sampling positional charts along depth. The matrix shift samples the next
chart in the interior; its missing final sample is retained explicitly.
A fixed-number trajectory stabilizes, unlike a growing center/leg fiber. -/
namespace CarrySelfAdjointOperator
open CarryGeometry
open scoped Matrix
noncomputable section

def finitePositionalObservable (F : ℕ × ℕ → ℝ) (b n N : ℕ) : Fin N → ℝ :=
  fun k => F (positionalDepthCoordinates b k.val n)

/-- The existing truncated shift on any sampled trajectory, including its boundary. -/
theorem finiteDepthShift_sample_apply (f : ℕ → ℝ) (N : ℕ) (i : Fin N) :
    (finiteDepthShift N).mulVec (fun j => f j.val) i =
      if i.val + 1 < N then f (i.val + 1) else 0 := by
  classical
  unfold Matrix.mulVec dotProduct
  by_cases h : i.val + 1 < N
  · rw [if_pos h]
    let j : Fin N := ⟨i.val + 1, h⟩
    rw [Finset.sum_eq_single j]
    · simp [finiteDepthShift, j]
    · intro k _ hkj
      have hk : i.val + 1 ≠ k.val := by
        intro heq
        apply hkj
        exact Fin.ext heq.symm
      simp [finiteDepthShift, hk]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro j _
    have hj : i.val + 1 ≠ j.val := by omega
    simp [finiteDepthShift, hj]

/-- Boundary correction in a nonempty prefix. -/
theorem finiteDepthShift_sample_add_boundary (f : ℕ → ℝ) (N : ℕ)
    (i : Fin (N + 1)) :
    (finiteDepthShift (N + 1)).mulVec (fun j => f j.val) i +
        (if i.val = N then f (N + 1) else 0) = f (i.val + 1) := by
  rw [finiteDepthShift_sample_apply]
  by_cases h : i.val = N
  · simp [h]
  · have hi : i.val + 1 < N + 1 := by omega
    simp [h, hi]

theorem finitePositionalObservable_shift (F : ℕ × ℕ → ℝ) (b n N : ℕ)
    (i : Fin N) (hi : i.val + 1 < N) :
    (finiteDepthShift N).mulVec (finitePositionalObservable F b n N) i =
      F (positionalDepthRefinement b i.val n) := by
  unfold finitePositionalObservable
  rw [finiteDepthShift_sample_apply (fun k => F (positionalDepthCoordinates b k n)), if_pos hi,
    positionalDepthCoordinates_succ_eq_refinement]

/-- The existing weighted difference, with the omitted next observation restored. -/
theorem finitePositionalObservable_difference_add_boundary
    (F : ℕ × ℕ → ℝ) (b n N : ℕ) (q : ℝ) (i : Fin (N + 1)) :
    (finiteDepthDifference q (N + 1)).mulVec
        (finitePositionalObservable F b n (N + 1)) i +
      q⁻¹ * (if i.val = N then F (positionalDepthCoordinates b (N + 1) n) else 0) =
    q⁻¹ * F (positionalDepthRefinement b i.val n) -
      F (positionalDepthCoordinates b i.val n) := by
  have h := finiteDepthShift_sample_add_boundary
    (fun k => F (positionalDepthCoordinates b k n)) N i
  unfold finitePositionalObservable
  simp only [finiteDepthDifference, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← positionalDepthCoordinates_succ_eq_refinement]
  linear_combination q⁻¹ * h

theorem positionalDepthCoordinates_eq_terminal (b k n : ℕ)
    (h : n < placeValue b k) : positionalDepthCoordinates b k n = (0, n) := by
  simp [positionalDepthCoordinates, quotientAtDepth, residueAtDepth,
    Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]

/-- Explicit stabilization threshold; this concerns a fixed number only. -/
theorem positionalObservable_stable (F : ℕ × ℕ → ℝ) (b n k : ℕ)
    (hb : 1 < b) (hk : n ≤ k) :
    F (positionalDepthCoordinates b k n) = F (0, n) := by
  rw [positionalDepthCoordinates_eq_terminal b k n
    (lt_of_le_of_lt hk (Nat.lt_pow_self hb))]

/-- After stabilization, an unweighted chart observable has no ordinary variation. -/
theorem positionalObservable_difference_stable (F : ℕ × ℕ → ℝ) (b n k : ℕ)
    (hb : 1 < b) (hk : n ≤ k) (q : ℝ) :
    q⁻¹ * F (positionalDepthCoordinates b (k + 1) n) -
        F (positionalDepthCoordinates b k n) = (q⁻¹ - 1) * F (0, n) := by
  rw [positionalObservable_stable F b n (k + 1) hb (by omega),
    positionalObservable_stable F b n k hb hk]
  ring

/-- Allowing an observable of coordinates alone does not create arbitrary depth data. -/
theorem no_positionalObservable_eq_depth (b n : ℕ) (hb : 1 < b) :
    ¬ ∃ F : ℕ × ℕ → ℝ, ∀ k, F (positionalDepthCoordinates b k n) = (k : ℝ) := by
  rintro ⟨F, hF⟩
  have h0 := positionalObservable_stable F b n n hb (le_refl _)
  have h1 := positionalObservable_stable F b n (n + 1) hb (by omega)
  rw [hF] at h0 h1
  push_cast at h1
  linarith

end
end CarrySelfAdjointOperator
