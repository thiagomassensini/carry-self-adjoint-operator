import CarrySelfAdjointOperator.NativeLaguerreLpModes
import Mathlib.Analysis.InnerProductSpace.Positive
import CarrySelfAdjointOperator.NativeLaguerreAdvanceMatrix

/-! Bounded multiplication on the original physical complex L² space. -/
namespace CarrySelfAdjointOperator.NativeLaguerre
open MeasureTheory
open scoped InnerProductSpace unitInterval ComplexOrder ComplexConjugate
noncomputable section
set_option autoImplicit false

private theorem multiplier_memLp (m : C(unitInterval, ℂ))
    (f : CanonicalCompletedNativeChiralCauchyCarrier) :
    MemLp (fun u => m u * f u) 2 volume := by
  refine (Lp.memLp f).of_le_mul (c := ‖m‖) (m.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall (fun u => ?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (m.norm_coe_le_norm u) (norm_nonneg _)

private def multiplierLinear (m : C(unitInterval, ℂ)) :
    CanonicalCompletedNativeChiralCauchyCarrier →ₗ[ℂ]
      CanonicalCompletedNativeChiralCauchyCarrier where
  toFun f := (multiplier_memLp m f).toLp (fun u => m u * f u)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (multiplier_memLp m (f+g)),
      Lp.coeFn_add f g, Lp.coeFn_add
        ((multiplier_memLp m f).toLp (fun u => m u*f u))
        ((multiplier_memLp m g).toLp (fun u => m u*g u)),
      MemLp.coeFn_toLp (multiplier_memLp m f),
      MemLp.coeFn_toLp (multiplier_memLp m g)] with u hfg ha hb hf hg
    simp only [hfg, ha, Pi.add_apply, hb, hf, hg, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (multiplier_memLp m (c • f)),
      Lp.coeFn_smul c f, Lp.coeFn_smul c
        ((multiplier_memLp m f).toLp (fun u => m u*f u)),
      MemLp.coeFn_toLp (multiplier_memLp m f)] with u hcf hc hcm hf
    simp only [hcf, hc, hcm, hf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private theorem multiplierLinear_bound (m : C(unitInterval, ℂ))
    (f : CanonicalCompletedNativeChiralCauchyCarrier) :
    ‖multiplierLinear m f‖ ≤ ‖m‖ * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [MemLp.coeFn_toLp (multiplier_memLp m f)] with u hu
  change ‖(multiplier_memLp m f).toLp (fun u => m u*f u) u‖ ≤ _
  rw [hu, norm_mul]
  exact mul_le_mul_of_nonneg_right (m.norm_coe_le_norm u) (norm_nonneg _)

/-- Multiplication by a continuous bounded coefficient, on the whole original H. -/
def intervalMultiplier (m : C(unitInterval, ℂ)) :
    CanonicalCompletedNativeChiralCauchyCarrier →L[ℂ]
      CanonicalCompletedNativeChiralCauchyCarrier :=
  (multiplierLinear m).mkContinuous ‖m‖ (multiplierLinear_bound m)

theorem intervalMultiplier_ae (m : C(unitInterval, ℂ))
    (f : CanonicalCompletedNativeChiralCauchyCarrier) :
    (intervalMultiplier m f : unitInterval → ℂ) =ᵐ[volume] (fun u => m u*f u) :=
  (multiplier_memLp m f).coeFn_toLp

theorem intervalMultiplier_norm_le (m : C(unitInterval, ℂ)) :
    ‖intervalMultiplier m‖ ≤ ‖m‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/-- The physical radial multiplier u. -/
def physicalRadialCoefficient : C(unitInterval, ℂ) where
  toFun u := ((u : ℝ) : ℂ)
  continuous_toFun := by fun_prop

def physicalRadialAdvance := intervalMultiplier physicalRadialCoefficient

/-- The original half-density column advances by one address, before pairing. -/
theorem physicalRadialAdvance_feature (j : ℕ) :
    physicalRadialAdvance (completedNativeChiralCauchyFeature j) =
      completedNativeChiralCauchyFeature (j+1) := by
  apply Lp.ext
  filter_upwards [intervalMultiplier_ae physicalRadialCoefficient
      (completedNativeChiralCauchyFeature j),
    ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)
      (completedNativeChiralCauchyContinuousFeature j),
    ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)
      (completedNativeChiralCauchyContinuousFeature (j+1))] with u hA hj hnext
  change intervalMultiplier physicalRadialCoefficient (completedNativeChiralCauchyFeature j) u = _
  rw [hA]
  simp only [completedNativeChiralCauchyFeature]
  rw [hj, hnext]
  simp [physicalRadialCoefficient, completedNativeChiralCauchyContinuousFeature, pow_succ]
  ring

theorem physicalRadialAdvance_state (k j : ℕ) :
    physicalRadialAdvance (completedNativeRadialChiralCauchyState k j) =
      completedNativeRadialChiralCauchyState k (j+1) := by
  simp only [completedNativeRadialChiralCauchyState, map_smul, physicalRadialAdvance_feature]

theorem intervalMultiplier_toLp (m f : C(unitInterval, ℂ)) :
    intervalMultiplier m (ContinuousMap.toLp 2 volume ℂ f) =
      ContinuousMap.toLp 2 volume ℂ (m*f) := by
  apply Lp.ext
  filter_upwards [intervalMultiplier_ae m (ContinuousMap.toLp 2 volume ℂ f),
    ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ) f,
    ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ) (m*f)] with u hA hf hmf
  rw [hA, hf, hmf]
  rfl

theorem intervalMultiplier_mul (m n : C(unitInterval, ℂ)) :
    intervalMultiplier (m*n) = intervalMultiplier m * intervalMultiplier n := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [intervalMultiplier_ae (m*n) f,
    intervalMultiplier_ae m (intervalMultiplier n f), intervalMultiplier_ae n f]
    with u hmn hm hn
  change intervalMultiplier (m*n) f u = intervalMultiplier m (intervalMultiplier n f) u
  rw [hmn, hm, hn]
  simp only [ContinuousMap.mul_apply, mul_assoc]

theorem intervalMultiplier_one : intervalMultiplier 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [intervalMultiplier_ae 1 f] with u hu
  change intervalMultiplier 1 f u = f u
  simpa only [ContinuousMap.one_apply, one_mul] using hu

theorem intervalMultiplier_sub (m n : C(unitInterval, ℂ)) :
    intervalMultiplier (m-n) = intervalMultiplier m - intervalMultiplier n := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [intervalMultiplier_ae (m-n) f, intervalMultiplier_ae m f,
    intervalMultiplier_ae n f, Lp.coeFn_sub (intervalMultiplier m f) (intervalMultiplier n f)]
    with u hmn hm hn hs
  change intervalMultiplier (m-n) f u = (intervalMultiplier m f - intervalMultiplier n f) u
  rw [hmn, hs]
  simp only [Pi.sub_apply, hm, hn, ContinuousMap.sub_apply, sub_mul]

theorem intervalMultiplier_isSelfAdjoint (m : C(unitInterval, ℂ))
    (hm : ∀ u, conj (m u) = m u) : IsSelfAdjoint (intervalMultiplier m) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [intervalMultiplier_ae m f, intervalMultiplier_ae m g] with u hf hg
  change inner ℂ (intervalMultiplier m f u) (g u) =
    inner ℂ (f u) (intervalMultiplier m g u)
  simp only [hf, hg, RCLike.inner_apply, map_mul, hm]
  ring

theorem intervalMultiplier_isPositive (m : C(unitInterval, ℂ))
    (hm : ∀ u, m u = ((m u).re : ℂ)) (hp : ∀ u, 0 ≤ (m u).re) :
    (intervalMultiplier m).IsPositive := by
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (intervalMultiplier_isSelfAdjoint m (fun u => by rw [hm u]; simp)), ?_⟩
  intro f
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, L2.inner_def,
    ← integral_re (L2.integrable_inner (intervalMultiplier m f) f)]
  apply integral_nonneg_of_ae
  filter_upwards [intervalMultiplier_ae m f] with u hu
  change 0 ≤ (inner ℂ (intervalMultiplier m f u) (f u)).re
  rw [hu, hm u]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  nlinarith [hp u, sq_nonneg (f u).re, sq_nonneg (f u).im,
    mul_nonneg (hp u) (sq_nonneg (f u).re), mul_nonneg (hp u) (sq_nonneg (f u).im)]

theorem physicalRadialAdvance_isSelfAdjoint : IsSelfAdjoint physicalRadialAdvance := by
  apply intervalMultiplier_isSelfAdjoint
  intro u
  simp [physicalRadialCoefficient]

theorem physicalRadialAdvance_norm_le_one : ‖physicalRadialAdvance‖ ≤ 1 := by
  apply (intervalMultiplier_norm_le _).trans
  apply (ContinuousMap.norm_le physicalRadialCoefficient (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro u
  simpa [physicalRadialCoefficient, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg u.property.1] using u.property.2

/-- Positivity belongs to the radial multiplication operator on H. -/
theorem physicalRadialAdvance_isPositive : physicalRadialAdvance.IsPositive := by
  apply intervalMultiplier_isPositive
  · intro u; simp [physicalRadialCoefficient]
  · intro u; simpa [physicalRadialCoefficient] using u.property.1

/-- The complementary multiplier is positive too: 0 ≤ M_u ≤ I. -/
theorem physicalRadialAdvance_complement_isPositive :
    (1-physicalRadialAdvance).IsPositive := by
  rw [physicalRadialAdvance, ← intervalMultiplier_one, ← intervalMultiplier_sub]
  apply intervalMultiplier_isPositive
  · intro u; simp [physicalRadialCoefficient]
  · intro u; simpa [physicalRadialCoefficient] using sub_nonneg.mpr u.property.2


/-- All physical radial moments, before a Laguerre basis is asserted complete. -/
theorem inner_logarithmicMonomialLp_advance (i j : ℕ) :
    inner ℂ (logarithmicMonomialLp i) (physicalRadialAdvance (logarithmicMonomialLp j)) =
      (((i+j).factorial : ℝ) / (2 : ℝ)^(i+j+1) : ℝ) := by
  rw [L2.inner_def]
  have he : (fun u : unitInterval => inner ℂ (logarithmicMonomialLp i u)
      (physicalRadialAdvance (logarithmicMonomialLp j) u)) =ᵐ[volume]
      (fun u => (((u : ℝ) * (-Real.log (u : ℝ))^(i+j) : ℝ) : ℂ)) := by
    filter_upwards [logarithmicMonomialLp_ae i, logarithmicMonomialLp_ae j,
      intervalMultiplier_ae physicalRadialCoefficient (logarithmicMonomialLp j)] with u hi hj hA
    change inner ℂ (logarithmicMonomialLp i u)
      (intervalMultiplier physicalRadialCoefficient (logarithmicMonomialLp j) u) = _
    rw [hi, hA, hj]
    simp [physicalRadialCoefficient, RCLike.inner_apply, Complex.ofReal_mul,
      ← pow_add, mul_comm, mul_left_comm]
  rw [integral_congr_ae he, integral_complex_ofReal]
  have hm := integral_interval_logarithmic_moment (i+j) (a := 1) (by norm_num)
  norm_num only [Real.rpow_one, show (1 : ℝ)+1=2 by norm_num] at hm
  exact congrArg (fun x : ℝ => (x : ℂ)) hm

/-- Exact functional matrix for arbitrary orders, as a finite Gamma moment sum.
The binomial closed form for arbitrary r,s is a separate remaining gate. -/
theorem physicalRadialAdvance_matrix_moment_sum (r s : ℕ) :
    inner ℂ (laguerreMode r) (physicalRadialAdvance (laguerreMode s)) =
      ∑ a ∈ Finset.range (r+1), ∑ b ∈ Finset.range (s+1),
        ((((-1 : ℝ)^a * (r.choose a : ℝ) / (a.factorial : ℝ)) : ℝ) : ℂ) *
        ((((-1 : ℝ)^b * (s.choose b : ℝ) / (b.factorial : ℝ)) : ℝ) : ℂ) *
        ((((a+b).factorial : ℝ) / (2 : ℝ)^(a+b+1) : ℝ) : ℂ) := by
  simp only [laguerreMode, map_sum, map_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    inner_logarithmicMonomialLp_advance, mul_assoc, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Actual physical matrix entries for the first three Laguerre modes. -/
theorem physicalRadialAdvance_first_three_matrix (r s : Fin 3) :
    inner ℂ (laguerreMode r.val) (physicalRadialAdvance (laguerreMode s.val)) =
      (advanceEntry r.val s.val : ℂ) := by
  fin_cases r <;> fin_cases s <;>
    simp only [laguerreMode, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, inner_logarithmicMonomialLp_advance] <;>
    norm_num [advanceEntry, map_ofNat, Nat.choose]


end
end CarrySelfAdjointOperator.NativeLaguerre
