import CarrySelfAdjointOperator.NativeSourceAllOrderSchur

/-! A countermodel to inference from finite native prefixes and the sharp
absolute majorant ONLY. This altered sequence is NOT the native source and
does NOT preserve its full recurrence or theta representation. -/
namespace CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def sourceLogMomentMajorant (n : ℕ) : ℝ :=
  (22/175 : ℝ)^(n+1)-(1/25 : ℝ)^(n+1)

theorem sourceLogMomentMajorant_pos (n : ℕ) : 0 < sourceLogMomentMajorant n := by
  unfold sourceLogMomentMajorant
  exact sub_pos.mpr (pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega))

/-- An explicit altered sequence: it agrees with all source moments needed
for both size-L prefixes, yet its next unshifted diagonal is negative. -/
def prefixOnlyNegativeExtension (L n : ℕ) : ℝ :=
  if n < 2*L then canonicalCompletedNativeLogDerivativeMoment n
  else if n = 2*L then -sourceLogMomentMajorant n/2 else 0

theorem prefixOnlyNegativeExtension_eq (L n : ℕ) (hn : n < 2*L) :
    prefixOnlyNegativeExtension L n = canonicalCompletedNativeLogDerivativeMoment n := by
  simp [prefixOnlyNegativeExtension, hn]

theorem prefixOnlyNegativeExtension_sharp_bound (L n : ℕ) :
    |prefixOnlyNegativeExtension L n| ≤ sourceLogMomentMajorant n := by
  unfold prefixOnlyNegativeExtension
  split_ifs with hlt heq
  · exact canonicalCompletedNativeLogDerivativeMoment_sharp_decay n
  · rw [abs_div, abs_neg, abs_of_pos (sourceLogMomentMajorant_pos n)]
    norm_num
    linarith [sourceLogMomentMajorant_pos n]
  · simpa using (sourceLogMomentMajorant_pos n).le

theorem prefixOnlyNegativeExtension_both_prefixes (L : ℕ) :
    hankelGram (prefixOnlyNegativeExtension L) L =
      hankelGram canonicalCompletedNativeLogDerivativeMoment L ∧
    shiftedHankel (prefixOnlyNegativeExtension L) L =
      shiftedHankel canonicalCompletedNativeLogDerivativeMoment L := by
  constructor <;> ext i j
  · exact prefixOnlyNegativeExtension_eq L _ (by omega)
  · exact prefixOnlyNegativeExtension_eq L _ (by omega)

/-- Even all old-new crosses of the next unshifted extension are retained.
Only its new diagonal and the later sequence are altered. -/
theorem prefixOnlyNegativeExtension_next_coupling (L : ℕ) :
    sourceMomentCoupling (prefixOnlyNegativeExtension L) 0 L =
      sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment 0 L := by
  funext i
  exact prefixOnlyNegativeExtension_eq L _ (by omega)

/-- Every source recurrence already inspected in the preserved prefix is
also unchanged. The recurrence at and beyond the altered index is not kept. -/
theorem prefixOnlyNegativeExtension_finite_source_recurrence
    (L n : ℕ) (hn : n < 2*L) :
    completedNativeRealEvenCharacteristicCoefficient 0 * prefixOnlyNegativeExtension L n +
      (∑ k ∈ Finset.range n, prefixOnlyNegativeExtension L k *
        completedNativeRealEvenCharacteristicCoefficient (n-k)) =
      -((n+1 : ℕ) : ℝ)*completedNativeRealEvenCharacteristicCoefficient (n+1) := by
  rw [prefixOnlyNegativeExtension_eq L n hn]
  have he : (∑ k ∈ Finset.range n, prefixOnlyNegativeExtension L k *
      completedNativeRealEvenCharacteristicCoefficient (n-k)) =
      ∑ k ∈ Finset.range n, canonicalCompletedNativeLogDerivativeMoment k *
        completedNativeRealEvenCharacteristicCoefficient (n-k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [prefixOnlyNegativeExtension_eq L k (lt_trans (Finset.mem_range.mp hk) hn)]
  rw [he]
  exact canonicalCompletedNativeLogDerivativeMoment_real_recurrence n

theorem prefixOnlyNegativeExtension_next_not_posSemidef (L : ℕ) :
    ¬(hankelGram (prefixOnlyNegativeExtension L) (L+1)).PosSemidef := by
  intro hp
  have hh := hp.diag_nonneg (i := Fin.last L)
  have he : hankelGram (prefixOnlyNegativeExtension L) (L+1)
      (Fin.last L) (Fin.last L) = -sourceLogMomentMajorant (2*L)/2 := by
    simp [hankelGram, prefixOnlyNegativeExtension, two_mul]
  rw [he] at hh
  linarith [sourceLogMomentMajorant_pos (2*L)]

/-- For every finite cutoff, the prefix and sharp all-order decay data admit
a negative next extension. No counterexample to the actual source is asserted. -/
theorem finite_native_prefix_and_decay_do_not_force_next_sign (L : ℕ) :
    ∃ m : ℕ → ℝ,
      (∀ n, n < 2*L → m n = canonicalCompletedNativeLogDerivativeMoment n) ∧
      (∀ n, |m n| ≤ sourceLogMomentMajorant n) ∧
      hankelGram m L = hankelGram canonicalCompletedNativeLogDerivativeMoment L ∧
      shiftedHankel m L = shiftedHankel canonicalCompletedNativeLogDerivativeMoment L ∧
      ¬(hankelGram m (L+1)).PosSemidef := by
  exact ⟨prefixOnlyNegativeExtension L, prefixOnlyNegativeExtension_eq L,
    prefixOnlyNegativeExtension_sharp_bound L,
    (prefixOnlyNegativeExtension_both_prefixes L).1,
    (prefixOnlyNegativeExtension_both_prefixes L).2,
    prefixOnlyNegativeExtension_next_not_posSemidef L⟩

end
end CarrySelfAdjointOperator
