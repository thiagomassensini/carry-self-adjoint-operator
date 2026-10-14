import CarrySelfAdjointOperator.CompletedNativeChiralReturnArbitraryOrder
import CarrySelfAdjointOperator.CompletedNativeLogCoefficientMajorant
import CarrySelfAdjointOperator.CompletedNativeChiralEvenBoundaryStieltjesGate

/-! Exact extension identities at arbitrary order. No new pivot sign is assumed
as an axiom or proved by the coefficient majorant. -/
namespace CarrySelfAdjointOperator
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

def sourceMomentMatrix (m : ℕ → ℝ) (s n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => m (i.val+j.val+s)

def sourceMomentCoupling (m : ℕ → ℝ) (s n : ℕ) : Fin n → ℝ :=
  fun i => m (i.val+n+s)

def sourceMomentQuadratic (m : ℕ → ℝ) (s n : ℕ) (x : Fin n → ℝ) : ℝ :=
  star x ⬝ᵥ (sourceMomentMatrix m s n *ᵥ x)

def sourceMomentSchur (m : ℕ → ℝ) (s n : ℕ) : ℝ :=
  m (2*n+s) - sourceMomentCoupling m s n ⬝ᵥ
    ((sourceMomentMatrix m s n)⁻¹ *ᵥ sourceMomentCoupling m s n)

theorem sourceMomentMatrix_isHermitian (m : ℕ → ℝ) (s n : ℕ) :
    (sourceMomentMatrix m s n).IsHermitian := by
  ext i j
  simp [sourceMomentMatrix, add_comm]

theorem sourceMomentQuadratic_snoc (m : ℕ → ℝ) (s n : ℕ)
    (x : Fin n → ℝ) (t : ℝ) :
    sourceMomentQuadratic m s (n+1) (Fin.snoc x t) =
      sourceMomentQuadratic m s n x +
      2*t*(sourceMomentCoupling m s n ⬝ᵥ x) + m (2*n+s)*t^2 := by
  classical
  simp only [sourceMomentQuadratic, sourceMomentMatrix, Matrix.mulVec, dotProduct,
    Pi.star_apply, star_trivial, Fin.sum_univ_castSucc, Fin.val_castSucc,
    Fin.val_last, Fin.snoc_castSucc, Fin.snoc_last, mul_add, Finset.sum_add_distrib]
  have he : (∑ i : Fin n, x i * (m (i.val+n+s)*t)) =
      t*(sourceMomentCoupling m s n ⬝ᵥ x) := by
    simp only [sourceMomentCoupling, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hf : (∑ j : Fin n, m (n+j.val+s)*x j) = sourceMomentCoupling m s n ⬝ᵥ x := by
    simp [sourceMomentCoupling, dotProduct, add_comm]
  rw [he, hf]
  simp only [dotProduct, Nat.add_comm]
  ring_nf

/-- The complete square uses every old-new coupling. Invertibility comes
only from positivity of the old prefix, not of the new one. -/
theorem sourceMomentSchur_sewing (m : ℕ → ℝ) (s n : ℕ)
    (hA : (sourceMomentMatrix m s n).PosDef) (x : Fin n → ℝ) (t : ℝ) :
    sourceMomentQuadratic m s (n+1) (Fin.snoc x t) =
      sourceMomentQuadratic m s n
        (x + t • ((sourceMomentMatrix m s n)⁻¹ *ᵥ sourceMomentCoupling m s n)) +
      sourceMomentSchur m s n*t^2 := by
  let A := sourceMomentMatrix m s n
  let b := sourceMomentCoupling m s n
  let v := A⁻¹ *ᵥ b
  letI := hA.isUnit.invertible
  have hv : A *ᵥ v = b := by
    dsimp [v, A]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have ht : Aᵀ = A := by
    ext i j
    simp [A, sourceMomentMatrix, add_comm]
  have hxv : v ⬝ᵥ (A *ᵥ x) = b ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, ← ht, Matrix.vecMul_transpose, hv]
  have hq : sourceMomentQuadratic m s n (x+t • v) =
      sourceMomentQuadratic m s n x + 2*t*(b ⬝ᵥ x) + (b ⬝ᵥ v)*t^2 := by
    change (x+t • v) ⬝ᵥ (A *ᵥ (x+t • v)) =
      x ⬝ᵥ (A *ᵥ x) + 2*t*(b ⬝ᵥ x) + (b ⬝ᵥ v)*t^2
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hv]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hxv]
    rw [dotProduct_comm x b, dotProduct_comm v b]
    ring
  rw [sourceMomentQuadratic_snoc]
  change _ = sourceMomentQuadratic m s n (x+t • v) +
    (m (2*n+s)-b ⬝ᵥ v)*t^2
  rw [hq]
  ring

/-- A concrete nonzero test vector reads the exact next pivot. -/
theorem sourceMomentSchur_critical_direction (m : ℕ → ℝ) (s n : ℕ)
    (hA : (sourceMomentMatrix m s n).PosDef) :
    sourceMomentQuadratic m s (n+1)
      (Fin.snoc (-((sourceMomentMatrix m s n)⁻¹ *ᵥ sourceMomentCoupling m s n)) 1) =
      sourceMomentSchur m s n := by
  rw [sourceMomentSchur_sewing m s n hA]
  simp [sourceMomentQuadratic]

theorem sourceMomentMatrix_succ_posDef_iff (m : ℕ → ℝ) (s n : ℕ)
    (hA : (sourceMomentMatrix m s n).PosDef) :
    (sourceMomentMatrix m s (n+1)).PosDef ↔ 0 < sourceMomentSchur m s n := by
  constructor
  · intro hp
    have hx : (Fin.snoc (-((sourceMomentMatrix m s n)⁻¹ *ᵥ sourceMomentCoupling m s n)) (1 : ℝ) : Fin (n+1) → ℝ) ≠ 0 := by
      intro hx
      have hh := congrFun hx (Fin.last n)
      simp at hh
    have hh := hp.dotProduct_mulVec_pos hx
    change 0 < sourceMomentQuadratic m s (n+1) _ at hh
    rwa [sourceMomentSchur_critical_direction m s n hA] at hh
  · intro hs
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (sourceMomentMatrix_isHermitian m s (n+1))
    intro z hz
    change 0 < sourceMomentQuadratic m s (n+1) z
    have he : Fin.snoc (Fin.init z) (z (Fin.last n)) = z := Fin.snoc_init_self z
    rw [← he, sourceMomentSchur_sewing m s n hA]
    by_cases ht : z (Fin.last n) = 0
    · have hi : Fin.init z ≠ 0 := by
        intro hi
        apply hz
        rw [← he, hi, ht]
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      simpa [ht, sourceMomentQuadratic] using hA.dotProduct_mulVec_pos hi
    · exact add_pos_of_nonneg_of_pos
        (hA.posSemidef.dotProduct_mulVec_nonneg _)
        (mul_pos hs (sq_pos_of_ne_zero ht))

/-- Quantifiers genuinely range over ALL orders. This is a criterion, not
a proof of its right hand side for the native source. -/
theorem sourceMomentMatrix_all_posDef_iff_schur (m : ℕ → ℝ) (s : ℕ) :
    (∀ n, (sourceMomentMatrix m s n).PosDef) ↔ ∀ n, 0 < sourceMomentSchur m s n := by
  constructor
  · intro hp n
    exact (sourceMomentMatrix_succ_posDef_iff m s n (hp n)).mp (hp (n+1))
  · intro hs n
    induction n with
    | zero =>
      apply Matrix.PosDef.of_dotProduct_mulVec_pos (sourceMomentMatrix_isHermitian m s 0)
      intro x hx
      exact (hx (Subsingleton.elim _ _)).elim
    | succ n ih => exact (sourceMomentMatrix_succ_posDef_iff m s n ih).mpr (hs n)

/-- Native recurrence remainder after eliminating an old prefix. This removes
division by c0, while retaining the old matrix inverse. It changes no feature. -/
def nativeSourceSchurRemainder (s n : ℕ) : ℝ :=
  -((2*n+s+1 : ℕ) : ℝ)*completedNativeRealEvenCharacteristicCoefficient (2*n+s+1) -
    (∑ k ∈ Finset.range (2*n+s), canonicalCompletedNativeLogDerivativeMoment k *
      completedNativeRealEvenCharacteristicCoefficient (2*n+s-k)) -
    completedNativeRealEvenCharacteristicCoefficient 0 *
      (sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment s n ⬝ᵥ
        ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)⁻¹ *ᵥ
          sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment s n))

theorem nativeSourceSchurRemainder_eq (s n : ℕ) :
    nativeSourceSchurRemainder s n = completedNativeRealEvenCharacteristicCoefficient 0 *
      sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment s n := by
  have h0 := completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero
  unfold nativeSourceSchurRemainder sourceMomentSchur
  rw [canonicalCompletedNativeLogDerivativeMoment_eq]
  field_simp

theorem nativeSourceBoundary_all_pos_iff_sourceSchur :
    (∀ n : ℕ, 1 ≤ n → ∀ x : Fin (2*n) → ℂ, x ≠ 0 →
      0 < nativeSourceFiniteBoundaryEnergy (2*n) x) ↔
      ∀ n, 0 < nativeSourceSchurRemainder 0 n ∧ 0 < nativeSourceSchurRemainder 1 n := by
  have h0 : 0 < completedNativeRealEvenCharacteristicCoefficient 0 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/3)
      completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  rw [nativeSourceEvenBoundary_positive_iff_stieltjes]
  change (∀ n, (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 n).PosDef ∧
    (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n).PosDef) ↔ _
  simp_rw [nativeSourceSchurRemainder_eq, mul_pos_iff_of_pos_left h0]
  rw [forall_and, forall_and, sourceMomentMatrix_all_posDef_iff_schur,
    sourceMomentMatrix_all_posDef_iff_schur]

/-- Explicit source remainders suffice for the original return at every fixed
order. Proving their sign remains the source problem. -/
theorem radialReturnTransfer_all_orders_of_sourceSchur
    (hR : ∀ n, 0 < nativeSourceSchurRemainder 0 n ∧ 0 < nativeSourceSchurRemainder 1 n) :
    ∀ N : ℕ, ∀ᶠ k : ℕ in Filter.atTop,
      ‖ChiralReturn.radialReturnTransfer k N‖ ≤ 1 := by
  apply ChiralReturn.radialReturnTransfer_all_orders_of_strict_boundary_positivity
  have hp := nativeSourceBoundary_all_pos_iff_sourceSchur.mpr hR
  intro n x hx
  by_cases hn : n = 0
  · subst n
    simp only [Nat.mul_zero] at x hx ⊢
    exact (hx (Subsingleton.elim _ _)).elim
  · exact hp n (by omega) x hx

end
end CarrySelfAdjointOperator
