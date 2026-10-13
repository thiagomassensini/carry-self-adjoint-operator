import CarrySelfAdjointOperator.NativeLaguerreLpModes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecificLimits.Normed

namespace CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators InnerProductSpace ComplexConjugate lp ENNReal
open Filter Topology
noncomputable section
set_option autoImplicit false

theorem feature_product_summable (i j : ℕ) :
    Summable (fun r : ℕ => feature r i * feature r j) := by
  have hpos : 0 ≤ rho i * rho j := mul_nonneg (rho_pos i).le (rho_pos j).le
  have hlt : rho i * rho j < 1 := by
    calc
      rho i * rho j < rho i * 1 := mul_lt_mul_of_pos_left (rho_lt_one j) (rho_pos i)
      _ < 1 := by simpa using rho_lt_one i
  have h := (summable_geometric_of_lt_one hpos hlt).mul_left (feature 0 i * feature 0 j)
  apply h.congr
  intro r
  simp only [feature, pow_zero, mul_pow]
  ring

/-- The old finite head/tail identity determines the literal infinite column Gram. -/
theorem feature_product_hasSum (i j : ℕ) :
    HasSum (fun r : ℕ => feature r i * feature r j) (cauchyEntry i j) := by
  have h := feature_product_summable i j
  have ht := h.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have he : (∑' r : ℕ, feature r i * feature r j) = cauchyEntry i j :=
    tendsto_nhds_unique ht (head_entry_tendsto_cauchy i j)
  exact he ▸ h.hasSum

/-- No weights are introduced: these are exactly the certified physical features. -/
def laguerreColumn (j : ℕ) : ℓ²(ℕ, ℂ) :=
  ⟨fun r => (feature r j : ℂ), by
    apply memℓp_gen
    apply (feature_product_summable j j).congr
    intro r
    have hf : 0 ≤ feature r j := by
      have hr := pow_nonneg (rho_pos j).le r
      unfold feature
      positivity
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hf, pow_two]⟩

@[simp] theorem laguerreColumn_apply (j r : ℕ) :
    laguerreColumn j r = (feature r j : ℂ) := rfl

theorem inner_laguerreColumn (i j : ℕ) :
    inner ℂ (laguerreColumn i) (laguerreColumn j) = (cauchyEntry i j : ℂ) := by
  rw [lp.inner_eq_tsum]
  simp only [laguerreColumn_apply, RCLike.inner_apply, Complex.conj_ofReal,
    ← Complex.ofReal_mul]
  simpa only [mul_comm] using
    (Complex.hasSum_ofReal.mpr (feature_product_hasSum i j)).tsum_eq

theorem laguerreColumn_physicalGram (i j : ℕ) :
    inner ℂ (laguerreColumn i) (laguerreColumn j) =
      inner ℂ (completedNativeChiralCauchyFeature i) (completedNativeChiralCauchyFeature j) := by
  rw [inner_laguerreColumn, inner_completedNativeChiralCauchyFeature]
  simp [cauchyEntry, Nat.cast_add]

def physicalCauchySynthesis : (ℕ →₀ ℂ) →ₗ[ℂ] CanonicalCompletedNativeChiralCauchyCarrier :=
  Finsupp.linearCombination ℂ completedNativeChiralCauchyFeature

def laguerreColumnSynthesis : (ℕ →₀ ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ) :=
  Finsupp.linearCombination ℂ laguerreColumn

/-- Arbitrary independent finite supports, with all ordered crossings preserved. -/
theorem laguerreColumnSynthesis_inner (c d : ℕ →₀ ℂ) :
    inner ℂ (laguerreColumnSynthesis c) (laguerreColumnSynthesis d) =
      inner ℂ (physicalCauchySynthesis c) (physicalCauchySynthesis d) := by
  simp only [laguerreColumnSynthesis, physicalCauchySynthesis,
    Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, laguerreColumn_physicalGram]

theorem laguerreColumnSynthesis_norm (c : ℕ →₀ ℂ) :
    ‖laguerreColumnSynthesis c‖ = ‖physicalCauchySynthesis c‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) (laguerreColumnSynthesis c),
    norm_sq_eq_re_inner (𝕜 := ℂ) (physicalCauchySynthesis c),
    laguerreColumnSynthesis_inner]

end
end CarrySelfAdjointOperator.NativeLaguerre
