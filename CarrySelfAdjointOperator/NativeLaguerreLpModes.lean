import CarrySelfAdjointOperator.NativeLaguerreLogMoments
import CarrySelfAdjointOperator.NativeCauchyLaguerreExactGram

/-! Measurable Laguerre modes in the original complex L² carrier.
Only the explicitly certified orders below are asserted orthonormal. -/
namespace CarrySelfAdjointOperator.NativeLaguerre
open MeasureTheory Set
open scoped BigOperators InnerProductSpace unitInterval
noncomputable section
set_option autoImplicit false

private theorem integrable_interval_log_power (n : ℕ) :
    Integrable (fun u : unitInterval => (-Real.log (u : ℝ))^n) := by
  have h := integrable_logarithmic_moment n (a := 0) (by norm_num)
  simpa only [Real.rpow_zero, one_mul, Function.comp_def] using
    unitInterval.measurePreserving_coe.integrable_comp_of_integrable h

/-- Square integrability includes every natural logarithmic degree. -/
theorem memLp_interval_log_power (n : ℕ) :
    MemLp (fun u : unitInterval => (-Real.log (u : ℝ))^n) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    (((Real.measurable_log.comp measurable_subtype_coe).neg.pow_const n).aestronglyMeasurable)).mpr
  simpa [← pow_mul] using integrable_interval_log_power (n*2)

/-- An actual L² class, with no endpoint continuity assumption. -/
def logarithmicMonomialLp (n : ℕ) : CanonicalCompletedNativeChiralCauchyCarrier :=
  (memLp_interval_log_power n).ofReal.toLp
    (fun u : unitInterval => (((-Real.log (u : ℝ))^n : ℝ) : ℂ))

theorem logarithmicMonomialLp_ae (n : ℕ) :
    (logarithmicMonomialLp n : unitInterval → ℂ) =ᵐ[volume]
      (fun u => (((-Real.log (u : ℝ))^n : ℝ) : ℂ)) :=
  MemLp.coeFn_toLp _

/-- Exact moments in the Hilbert space, for all pairs of natural degrees. -/
theorem inner_logarithmicMonomialLp (i j : ℕ) :
    inner ℂ (logarithmicMonomialLp i) (logarithmicMonomialLp j) =
      ((i+j).factorial : ℂ) := by
  rw [L2.inner_def]
  have he : (fun u : unitInterval =>
      inner ℂ (logarithmicMonomialLp i u) (logarithmicMonomialLp j u)) =ᵐ[volume]
      (fun u => (((-Real.log (u : ℝ))^(i+j) : ℝ) : ℂ)) := by
    filter_upwards [logarithmicMonomialLp_ae i, logarithmicMonomialLp_ae j] with u hi hj
    simp [hi, hj, RCLike.inner_apply, ← pow_add, mul_comm]
  rw [integral_congr_ae he]
  have hsub := integral_subtype_comap (μ := (volume : Measure ℝ)) (s := Icc (0 : ℝ) 1)
    measurableSet_Icc (fun u : ℝ => (((-Real.log u)^(i+j) : ℝ) : ℂ))
  rw [show (∫ u : unitInterval, (((-Real.log (u : ℝ))^(i+j) : ℝ) : ℂ)) =
      ∫ u in Icc (0 : ℝ) 1, (((-Real.log u)^(i+j) : ℝ) : ℂ) by
        simpa [unitInterval.volume_def] using hsub]
  rw [integral_complex_ofReal]
  have hm := integral_logarithmic_moment (i+j) (a := 0) (by norm_num)
  simpa using congrArg (fun x : ℝ => (x : ℂ)) hm

/-- L_r(-log u), as a finite combination of genuine measurable L² classes. -/
def laguerreMode (r : ℕ) : CanonicalCompletedNativeChiralCauchyCarrier :=
  ∑ a ∈ Finset.range (r+1),
    ((((-1 : ℝ)^a * (r.choose a : ℝ) / (a.factorial : ℝ)) : ℝ) : ℂ) •
      logarithmicMonomialLp a

/-- Every order is represented by the original Laguerre polynomial a.e. -/
theorem laguerreMode_ae (r : ℕ) :
    (laguerreMode r : unitInterval → ℂ) =ᵐ[volume]
      (fun u => ∑ a ∈ Finset.range (r+1),
        ((((-1 : ℝ)^a * (r.choose a : ℝ) / (a.factorial : ℝ)) : ℝ) : ℂ) *
          (((-Real.log (u : ℝ))^a : ℝ) : ℂ)) := by
  let c : ℕ → ℂ := fun a => ((((-1 : ℝ)^a * (r.choose a : ℝ) / (a.factorial : ℝ)) : ℝ) : ℂ)
  change (∑ a ∈ Finset.range (r+1), c a • logarithmicMonomialLp a :
    CanonicalCompletedNativeChiralCauchyCarrier) =ᵐ[volume]
    (fun u => ∑ a ∈ Finset.range (r+1), c a * (((-Real.log (u : ℝ))^a : ℝ) : ℂ))
  filter_upwards [Lp.coeFn_finsetSum (Finset.range (r+1))
    (fun a => c a • logarithmicMonomialLp a),
    (ae_all_iff).mpr (fun a => Lp.coeFn_smul (c a) (logarithmicMonomialLp a)),
    (ae_all_iff).mpr logarithmicMonomialLp_ae] with u hsum hsmul hlog
  rw [hsum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [hsmul a]
  simp only [Pi.smul_apply, smul_eq_mul, hlog a]

/-- Kernel-checked orthonormality of the first three functional modes. -/
theorem laguerreMode_first_three_orthonormal :
    Orthonormal ℂ (fun r : Fin 3 => laguerreMode r.val) := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [laguerreMode, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      inner_logarithmicMonomialLp] <;> norm_num [map_ofNat]

/-- Functional Mellin moments on the same interval measure. -/
theorem integral_interval_logarithmic_moment (n : ℕ) {a : ℝ} (ha : -1 < a) :
    (∫ u : unitInterval, (u : ℝ)^a * (-Real.log (u : ℝ))^n) =
      (n.factorial : ℝ) / (a+1)^(n+1) := by
  have hsub := integral_subtype_comap (μ := (volume : Measure ℝ))
    (s := Icc (0 : ℝ) 1) measurableSet_Icc
    (fun u : ℝ => u^a * (-Real.log u)^n)
  calc
    _ = ∫ u in Icc (0 : ℝ) 1, u^a * (-Real.log u)^n := by
      simpa only [unitInterval.volume_def] using hsub
    _ = _ := integral_logarithmic_moment n ha

/-- Every logarithmic degree has its exact overlap with the original half density. -/
theorem inner_logarithmicMonomialLp_feature (n j : ℕ) :
    inner ℂ (logarithmicMonomialLp n) (completedNativeChiralCauchyFeature j) =
      (((n.factorial : ℝ) / ((j : ℝ)+3/2)^(n+1) : ℝ) : ℂ) := by
  rw [L2.inner_def]
  have he : (fun u : unitInterval => inner ℂ (logarithmicMonomialLp n u)
      (completedNativeChiralCauchyFeature j u)) =ᵐ[volume]
      (fun u => (((u : ℝ)^((j : ℝ)+1/2) * (-Real.log (u : ℝ))^n : ℝ) : ℂ)) := by
    filter_upwards [logarithmicMonomialLp_ae n,
      ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)
        (completedNativeChiralCauchyContinuousFeature j)] with u hn hj
    change inner ℂ (logarithmicMonomialLp n u)
      (ContinuousMap.toLp 2 volume ℂ (completedNativeChiralCauchyContinuousFeature j) u) = _
    rw [hn, hj]
    simp only [completedNativeChiralCauchyContinuousFeature, ContinuousMap.coe_mk,
      RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    rw [Real.rpow_add_of_nonneg u.property.1 (by positivity) (by norm_num),
      Real.rpow_natCast, ← Real.sqrt_eq_rpow]
    ring
  rw [integral_congr_ae he, integral_complex_ofReal,
    integral_interval_logarithmic_moment n (show -1 < (j : ℝ)+1/2 by have := Nat.cast_nonneg (α := ℝ) j; linarith)]
  congr 2
  ring

/-- Every functional mode recovers the already certified physical feature column. -/
theorem laguerreMode_feature (r j : ℕ) :
    inner ℂ (laguerreMode r) (completedNativeChiralCauchyFeature j) =
      (feature r j : ℂ) := by
  rw [feature_polynomial_moment]
  simp only [laguerreMode, sum_inner, inner_smul_left, inner_logarithmicMonomialLp_feature,
    Complex.conj_ofReal]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hf : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  rw [← Complex.ofReal_mul]
  congr 1
  simp only [inv_pow, div_eq_mul_inv]
  calc
    _ = ((-1 : ℝ)^a * (r.choose a : ℝ)) *
        ((a.factorial : ℝ)⁻¹ * (a.factorial : ℝ)) *
        (((j : ℝ)+3/2)^(a+1))⁻¹ := by ring
    _ = _ := by rw [inv_mul_cancel₀ hf]; ring

/-- The physical amplitude is retained exactly once. -/
theorem laguerreMode_radial_state (r : ℕ) (k j : ℕ) :
    inner ℂ (laguerreMode r) (completedNativeRadialChiralCauchyState k j) =
      (Real.sqrt ((k : ℝ)+1) : ℂ) * (feature r j : ℂ) := by
  rw [completedNativeRadialChiralCauchyState, inner_smul_right,
    laguerreMode_feature]


end
end CarrySelfAdjointOperator.NativeLaguerre
