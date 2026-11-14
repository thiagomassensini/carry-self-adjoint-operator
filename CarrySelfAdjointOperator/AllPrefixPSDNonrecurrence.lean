import CarrySelfAdjointOperator.LogarithmicMomentHankel
import CarrySelfAdjointOperator.CompletedNativeHardyAlgebra
import Mathlib.Tactic

/-!
# Positive definite Hankel prefixes from PSD and nonrecurrence

This file is sequence-generic. Positivity of every finite prefix and absence
of finite moment relations suffice; no Gram or measure representation is an
assumption.
-/

namespace CarrySelfAdjointOperator

noncomputable section
open scoped Matrix

/-- A Hankel prefix starting at an arbitrary moment shift. -/
def momentHankelPrefix (moments : ℕ → ℝ) (shift N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j ↦ moments (shift + (i : ℕ) + (j : ℕ))

theorem momentHankelPrefix_isSymm (moments : ℕ → ℝ) (shift N : ℕ) :
    (momentHankelPrefix moments shift N).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp [momentHankelPrefix, Nat.add_left_comm, Nat.add_comm]

private theorem momentHankel_quadratic_add_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.IsSymm)
    (x y : ι → ℝ) (t : ℝ) :
    (x + t • y) ⬝ᵥ (M *ᵥ (x + t • y)) =
      x ⬝ᵥ (M *ᵥ x) + 2*t*(x ⬝ᵥ (M *ᵥ y)) + t^2*(y ⬝ᵥ (M *ᵥ y)) := by
  have ht : Mᵀ = M := hM.eq
  have hvec : Matrix.vecMul y M = M *ᵥ y := by
    calc
      Matrix.vecMul y M = Mᵀ *ᵥ y := by
        simpa only [Matrix.transpose_transpose] using (Matrix.vecMul_transpose Mᵀ y)
      _ = M *ᵥ y := by rw [ht]
  have hcross : y ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ (M *ᵥ y) := by
    rw [Matrix.dotProduct_mulVec, hvec, dotProduct_comm]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hcross]
  ring

private def momentProbeIndices (n j : ℕ) : Fin n ⊕ Unit → Fin (n+j+1) :=
  Sum.elim (fun i => ⟨i.val, by omega⟩) (fun _ => ⟨j, by omega⟩)

private def momentProbeVector {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    Fin n ⊕ Unit → ℝ :=
  Sum.elim x (fun _ => t)

private def momentProbeBase {n : ℕ} (x : Fin n → ℝ) : Fin n ⊕ Unit → ℝ :=
  momentProbeVector x 0

private def momentProbeUnit {n : ℕ} : Fin n ⊕ Unit → ℝ :=
  Sum.elim (fun _ => 0) (fun _ => 1)

private theorem momentProbe_base_energy
    {moments : ℕ → ℝ} {shift n j : ℕ} (x : Fin n → ℝ) :
    momentProbeBase x ⬝ᵥ
      ((momentHankelPrefix moments shift (n+j+1)).submatrix
        (momentProbeIndices n j) (momentProbeIndices n j) *ᵥ momentProbeBase x) =
      x ⬝ᵥ (momentHankelPrefix moments shift n *ᵥ x) := by
  classical
  simp [momentProbeBase, momentProbeVector, momentProbeIndices,
    momentHankelPrefix, Matrix.submatrix, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type]

private theorem momentProbe_cross
    {moments : ℕ → ℝ} {shift n j : ℕ} (x : Fin n → ℝ) :
    momentProbeBase x ⬝ᵥ
      ((momentHankelPrefix moments shift (n+j+1)).submatrix
        (momentProbeIndices n j) (momentProbeIndices n j) *ᵥ momentProbeUnit) =
      ∑ i : Fin n, x i * moments (shift + (i : ℕ) + j) := by
  classical
  simp [momentProbeBase, momentProbeVector, momentProbeUnit,
    momentProbeIndices, momentHankelPrefix, Matrix.submatrix,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

private theorem momentProbe_unit_energy
    {moments : ℕ → ℝ} {shift n j : ℕ} :
    momentProbeUnit (n := n) ⬝ᵥ
      ((momentHankelPrefix moments shift (n+j+1)).submatrix
        (momentProbeIndices n j) (momentProbeIndices n j) *ᵥ momentProbeUnit) =
      moments (shift + j + j) := by
  classical
  simp [momentProbeUnit, momentProbeIndices,
    momentHankelPrefix, Matrix.submatrix, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type]

/-- If all Hankel prefixes are positive semidefinite, a zero-energy finite
vector pairs to zero with every monomial in the shifted moment sequence. -/
private theorem momentHankel_zeroEnergy_relation
    {moments : ℕ → ℝ} {shift n : ℕ}
    (hpsd : ∀ N, (momentHankelPrefix moments shift N).PosSemidef)
    (x : Fin n → ℝ)
    (henergy : x ⬝ᵥ (momentHankelPrefix moments shift n *ᵥ x) = 0) :
    ∀ j : ℕ, ∑ i : Fin n, x i * moments (shift + (i : ℕ) + j) = 0 := by
  intro j
  let K := (momentHankelPrefix moments shift (n+j+1)).submatrix
    (momentProbeIndices n j) (momentProbeIndices n j)
  have hK : K.PosSemidef := (hpsd (n+j+1)).submatrix (momentProbeIndices n j)
  have hKsym : K.IsSymm := Matrix.isHermitian_iff_isSymm.mp hK.isHermitian
  let b := ∑ i : Fin n, x i * moments (shift + (i : ℕ) + j)
  let c := moments (shift + j + j)
  have hbase : momentProbeBase x ⬝ᵥ (K *ᵥ momentProbeBase x) = 0 := by
    rw [momentProbe_base_energy]
    exact henergy
  have hcross : momentProbeBase x ⬝ᵥ (K *ᵥ momentProbeUnit) = b := by
    simp [K, b, momentProbe_cross]
  have hunit : momentProbeUnit (n := n) ⬝ᵥ
      (K *ᵥ momentProbeUnit) = c := by
    simp [K, c, momentProbe_unit_energy]
  have hc : 0 ≤ c := by
    have hnonneg := hK.dotProduct_mulVec_nonneg (momentProbeUnit (n := n))
    simpa [c, K, Pi.star_apply, star_trivial, momentProbe_unit_energy] using hnonneg
  by_contra hb
  have hbne : b ≠ 0 := hb
  have hc1 : c + 1 ≠ 0 := by linarith
  have hq := hK.dotProduct_mulVec_nonneg
    (momentProbeBase x + (-b/(c+1)) • momentProbeUnit (n := n))
  have hq' : 0 ≤ (momentProbeBase x + (-b/(c+1)) • momentProbeUnit (n := n)) ⬝ᵥ
      (K *ᵥ (momentProbeBase x + (-b/(c+1)) • momentProbeUnit (n := n))) := by
    simpa [Pi.star_apply, star_trivial] using hq
  rw [momentHankel_quadratic_add_smul K hKsym _ _ _] at hq'
  rw [hbase, hcross, hunit] at hq'
  have hbpos : 0 < b^2 := sq_pos_of_ne_zero hbne
  have hc1pos : 0 < (c+1)^2 := sq_pos_of_ne_zero hc1
  field_simp [hc1] at hq'
  nlinarith [sq_nonneg b, sq_nonneg c]

/-- For a real sequence, PSD of every shifted Hankel prefix and no finite
moment relation at that shift imply positive definiteness of every prefix. -/
theorem momentHankelPrefix_posDef_of_all_posSemidef_of_noFiniteMomentRelationAt
    (moments : ℕ → ℝ) (shift : ℕ)
    (hpsd : ∀ N, (momentHankelPrefix moments shift N).PosSemidef)
    (hno : NoFiniteMomentRelationAt moments shift) :
    ∀ N, (momentHankelPrefix moments shift N).PosDef := by
  intro n
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_iff_isSymm.mpr (momentHankelPrefix_isSymm moments shift n))
  intro x hx
  by_contra hnot
  have henergy : x ⬝ᵥ (momentHankelPrefix moments shift n *ᵥ x) = 0 := by
    have hnonneg := (hpsd n).dotProduct_mulVec_nonneg x
    have hnonneg' : 0 ≤ x ⬝ᵥ (momentHankelPrefix moments shift n *ᵥ x) := by
      simpa [Pi.star_apply, star_trivial] using hnonneg
    have hnot' : ¬ 0 < x ⬝ᵥ (momentHankelPrefix moments shift n *ᵥ x) := hnot
    linarith
  have hrel := momentHankel_zeroEnergy_relation hpsd x henergy
  let a : ℕ → ℝ := fun k => if hk : k < n then x ⟨k, hk⟩ else 0
  have ha : ∀ k, k ∉ Finset.range n → a k = 0 := by
    intro k hk
    simp [a, Finset.mem_range] at hk ⊢
    omega
  have hfinite : ∀ j : ℕ,
      ∑ k ∈ Finset.range n, a k * moments (shift + k + j) = 0 := by
    intro j
    have hrange := Fin.sum_univ_eq_sum_range
      (fun k : ℕ => if hk : k < n then x ⟨k, hk⟩ * moments (shift + k + j) else 0) n
    have hrelj := hrel j
    have hsum : (∑ i : Fin n, x i * moments (shift + (i : ℕ) + j)) =
        ∑ k ∈ Finset.range n,
          if hk : k < n then x ⟨k, hk⟩ * moments (shift + k + j) else 0 := by
      simpa using hrange
    rw [hsum] at hrelj
    simpa [a, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.sum_const_zero,
      Finset.mem_range] using hrelj
  have hallzero := hno (Finset.range n) a ha hfinite
  apply hx
  funext i
  have hi := hallzero i.val
  simpa [a] using hi

end

end CarrySelfAdjointOperator
