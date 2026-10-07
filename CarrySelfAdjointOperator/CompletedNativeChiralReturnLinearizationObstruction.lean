import CarrySelfAdjointOperator.CompletedNativeChiralReturnSourceTrace
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# A finite obstruction to closing storage by first-order sample control

The diagnostic uses the unchanged radial Cauchy vectors and their complete
finite syntheses. It does not replace the native quotient. Its slope is a
free analytic test parameter, not a coefficient selected from moments.
Even individually contractive samples, tending uniformly to the centered
value, can have a negative integrated balance in a cancellation direction.
The actual completed source tangent is exposed independently at the end.
-/
namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- First-order diagnostic on the ORIGINAL radial grid; not the native source. -/
def affineRadialMultiplierProbe (a : ℝ) (k n : ℕ) : ℂ :=
  -1 + (a : ℂ) * ((n + 1 : ℕ) : ℂ) / (((k : ℝ) + 1 : ℝ) : ℂ)

/-- All coefficients are synthesized before observing the diagnostic energy. -/
def affineRadialReturnedProbe (a : ℝ) (k : ℕ) {N : ℕ} (c : Fin N → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  ∑ i, c i • (affineRadialMultiplierProbe a k i •
    completedNativeRadialChiralCauchyState k i)

/-- Exact two-vector cancellation, retaining both ordered cross terms. -/
theorem affineRadialProbe_opposite_energy (a : ℝ) (k : ℕ) :
    ‖∑ i : Fin 2, (![1, -1] : Fin 2 → ℂ) i •
        completedNativeRadialChiralCauchyState k i‖ ^ 2 -
      ‖affineRadialReturnedProbe a k ![1, -1]‖ ^ 2 =
        -(a ^ 2 / (6 * ((k : ℝ) + 1))) := by
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hc : ((((k : ℝ) + 1 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hk
  have h : inner ℂ
      (∑ i : Fin 2, (![1, -1] : Fin 2 → ℂ) i • completedNativeRadialChiralCauchyState k i)
      (∑ i : Fin 2, (![1, -1] : Fin 2 → ℂ) i • completedNativeRadialChiralCauchyState k i) -
      inner ℂ (affineRadialReturnedProbe a k ![1, -1])
        (affineRadialReturnedProbe a k ![1, -1]) =
        ((-(a ^ 2 / (6 * ((k : ℝ) + 1))) : ℝ) : ℂ) := by
    simp only [affineRadialReturnedProbe, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_smul, neg_smul, ← sub_eq_add_neg]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      inner_completedNativeRadialChiralCauchyState, affineRadialMultiplierProbe,
      map_add, map_neg, map_one, map_mul, map_div₀, Complex.conj_ofReal,
      map_natCast]
    push_cast
    norm_num
    field_simp [hc]
    ring
  have hr := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.ofReal_re] at hr
  simpa only [← RCLike.re_to_complex, ← norm_sq_eq_re_inner (𝕜 := ℂ)] using hr

/-- The negative witness persists at EVERY cutoff; it is not a rounding effect. -/
theorem affineRadialProbe_opposite_energy_neg {a : ℝ} (ha : a ≠ 0) (k : ℕ) :
    ‖∑ i : Fin 2, (![1, -1] : Fin 2 → ℂ) i •
        completedNativeRadialChiralCauchyState k i‖ ^ 2 -
      ‖affineRadialReturnedProbe a k ![1, -1]‖ ^ 2 < 0 := by
  rw [affineRadialProbe_opposite_energy]
  exact neg_neg_of_pos (div_pos (sq_pos_of_ne_zero ha) (by positivity))

/-- Each sample can be contractive on the very same negative-balance witness. -/
theorem affineRadialProbe_sample_norm_le_one {a : ℝ} (ha : 0 ≤ a)
    (k : ℕ) (hk : 2 * a ≤ (k : ℝ) + 1) (i : Fin 2) :
    ‖affineRadialMultiplierProbe a k i‖ ≤ 1 := by
  have hi : ((i : ℕ) + 1 : ℝ) ≤ 2 := by exact_mod_cast (show (i : ℕ) + 1 ≤ 2 by omega)
  have hp : 0 < (k : ℝ) + 1 := by positivity
  have hl : 0 ≤ a * ((i : ℕ) + 1 : ℝ) / ((k : ℝ) + 1) := by positivity
  have hu : a * ((i : ℕ) + 1 : ℝ) / ((k : ℝ) + 1) ≤ 2 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hi ha]
  have hcast : affineRadialMultiplierProbe a k i =
      ((-1 + a * ((i : ℕ) + 1 : ℝ) / ((k : ℝ) + 1) : ℝ) : ℂ) := by
    simp [affineRadialMultiplierProbe]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- The probe approaches the SAME centered value at each fixed sample. -/
theorem affineRadialProbe_tendsto_center (a : ℝ) (n : ℕ) :
    Tendsto (fun k => affineRadialMultiplierProbe a k n) atTop (nhds (-1)) := by
  have ht := (canonicalGreenJetStep_tendsto_zero.const_mul
    ((a : ℂ) * ((n + 1 : ℕ) : ℂ))).const_add (-1)
  convert ht using 1
  · ext k
    simp only [affineRadialMultiplierProbe, canonicalGreenJetStep, div_eq_mul_inv]
    push_cast
    ring
  · simp

/-- Arbitrarily small UNIFORM sample error and samplewise contraction do
not repair the negative full synthesis. This refutes the approximation
strategy only; the native completed source is not the affine probe. -/
theorem affineRadialProbe_uniform_control_not_energy_dominance {a : ℝ}
    (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      (∀ i : Fin 2, ‖affineRadialMultiplierProbe a k i + 1‖ < ε) ∧
      (∀ i : Fin 2, ‖affineRadialMultiplierProbe a k i‖ ≤ 1) ∧
      ‖∑ i : Fin 2, (![1, -1] : Fin 2 → ℂ) i •
          completedNativeRadialChiralCauchyState k i‖ ^ 2 -
        ‖affineRadialReturnedProbe a k ![1, -1]‖ ^ 2 < 0 := by
  have hclose : ∀ᶠ k : ℕ in atTop,
      ∀ i : Fin 2, ‖affineRadialMultiplierProbe a k i + 1‖ < ε := by
    have hi (i : Fin 2) : ∀ᶠ k : ℕ in atTop,
        ‖affineRadialMultiplierProbe a k i + 1‖ < ε := by
      have ht : Tendsto (fun k => ‖affineRadialMultiplierProbe a k i + 1‖)
          atTop (nhds 0) := by
        simpa using ((affineRadialProbe_tendsto_center a i).add_const 1).norm
      exact ht.eventually (eventually_lt_nhds hε)
    simpa only [Finset.mem_univ, forall_true_left] using
      (Finset.univ : Finset (Fin 2)).eventually_all.2 (fun i _ => hi i)
  have hk : ∀ᶠ k : ℕ in atTop, 2 * a ≤ (k : ℝ) + 1 := by
    have ht : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually (eventually_ge_atTop (2 * a))] with k hk
    linarith
  filter_upwards [hclose, hk] with k hclose hk
  exact ⟨hclose, fun i => affineRadialProbe_sample_norm_le_one ha.le k hk i,
    affineRadialProbe_opposite_energy_neg ha.ne' k⟩

/-- Source-first centered value, using the complete characteristic, not moments. -/
theorem nativeChiralQuotient_center_eq_neg_one :
    completedNativeHermiteBiehlerChiralQuotient 0 = -1 := by
  unfold completedNativeHermiteBiehlerChiralQuotient
  rw [completedNativePositiveHermiteBiehlerCoordinate_zero,
    completedNativeNegativeHermiteBiehlerCoordinate_zero]
  field_simp [Complex.I_ne_zero, completedNativeOperatorCharacteristic_zero_ne_zero]

/-- Centered source reflection forces a reciprocal chiral germ. This exact
constraint is retained by the complete characteristic and lost by an affine
truncation; it does not imply contractivity. -/
theorem nativeChiralQuotient_reflection_reciprocal :
    ∀ᶠ z : ℂ in nhds 0,
      completedNativeHermiteBiehlerChiralQuotient (-z) *
        completedNativeHermiteBiehlerChiralQuotient z = 1 := by
  have hP0 : completedNativePositiveHermiteBiehlerCoordinate 0 ≠ 0 := by
    rw [completedNativePositiveHermiteBiehlerCoordinate_zero]
    exact mul_ne_zero Complex.I_ne_zero completedNativeOperatorCharacteristic_zero_ne_zero
  have hN0 : completedNativeNegativeHermiteBiehlerCoordinate 0 ≠ 0 := by
    rw [completedNativeNegativeHermiteBiehlerCoordinate_zero]
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
      completedNativeOperatorCharacteristic_zero_ne_zero
  have hp := hasDerivAt_completedNativePositiveHermiteBiehlerCoordinate_zero.continuousAt.eventually_ne hP0
  have hn := hasDerivAt_completedNativeNegativeHermiteBiehlerCoordinate_zero.continuousAt.eventually_ne hN0
  have hd := completedNativeOperatorCharacteristic_eventually_even.deriv
  filter_upwards [completedNativeOperatorCharacteristic_eventually_even, hd, hp, hn]
    with z hz hdz hp hn
  rw [deriv_comp_neg] at hdz
  have hdneg : deriv completedNativeOperatorCharacteristic (-z) =
      -deriv completedNativeOperatorCharacteristic z := by linear_combination -hdz
  have hpn : completedNativePositiveHermiteBiehlerCoordinate (-z) =
      -completedNativeNegativeHermiteBiehlerCoordinate z := by
    unfold completedNativePositiveHermiteBiehlerCoordinate completedNativeNegativeHermiteBiehlerCoordinate
    rw [hz, hdneg]
    ring
  have hnn : completedNativeNegativeHermiteBiehlerCoordinate (-z) =
      -completedNativePositiveHermiteBiehlerCoordinate z := by
    unfold completedNativePositiveHermiteBiehlerCoordinate completedNativeNegativeHermiteBiehlerCoordinate
    rw [hz, hdneg]
    ring
  unfold completedNativeHermiteBiehlerChiralQuotient
  rw [hpn, hnn]
  field_simp

/-- The affine test loses the source reciprocal round trip at second order. -/
theorem affineRadialProbe_reflection_product (a : ℝ) (k n : ℕ) :
    affineRadialMultiplierProbe (-a) k n * affineRadialMultiplierProbe a k n =
      1 - ((a : ℂ) * ((n + 1 : ℕ) : ℂ) /
        (((k : ℝ) + 1 : ℝ) : ℂ)) ^ 2 := by
  simp only [affineRadialMultiplierProbe, Complex.ofReal_neg]
  ring

/-- The raw transverse source curvature; no canonical moment is an input. -/
def nativeRadialSourceCurvature : ℂ :=
  -2 * iteratedDeriv 2 completedNativeOperatorCharacteristic 0 /
    completedNativeOperatorCharacteristic 0

/-- The actual source has this tangent along each fixed radial sample.
This is convergence of samples; it supplies no uniform quadratic sign. -/
theorem nativeRadialSource_tangent (n : ℕ) :
    Tendsto (fun k => Complex.I *
      ((completedNativeHermiteBiehlerChiralQuotient
          (canonicalCompletedC3RadialTiltPoint k n) + 1) /
        canonicalCompletedC3RadialTiltPoint k n))
      atTop (nhds nativeRadialSourceCurvature) := by
  have hp : Tendsto (fun k => canonicalCompletedC3RadialTiltPoint k n)
      atTop (nhdsWithin 0 ({0} : Set ℂ)ᶜ) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨canonicalCompletedC3RadialTiltPoint_tendsto_zero n,
        Filter.Eventually.of_forall fun k => by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
            (fun h : canonicalCompletedC3RadialTiltPoint k n = 0 =>
              canonicalCompletedC3RadialTiltPoint_im_ne_zero k n
                (by rw [h]; rfl))⟩
  have hs := hasDerivAt_completedNativeHermiteBiehlerChiralQuotient_zero_raw.tendsto_slope.comp hp
  have ht := (tendsto_const_nhds (x := Complex.I)).mul hs
  convert ht using 1
  · ext k
    simp only [Function.comp_def, slope_def_field, sub_zero, nativeChiralQuotient_center_eq_neg_one, sub_neg_eq_add]
  · unfold nativeRadialSourceCurvature
    ring_nf
    rw [Complex.I_sq]
    ring

/-- Every finite native sample family shares the genuine source tangent.
The quantifier concerns samples, NOT quadratic forms over all coefficients. -/
theorem nativeRadialSource_tangent_uniform (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ i : Fin N,
      ‖Complex.I *
        ((completedNativeHermiteBiehlerChiralQuotient
            (canonicalCompletedC3RadialTiltPoint k i) + 1) /
          canonicalCompletedC3RadialTiltPoint k i) - nativeRadialSourceCurvature‖ < ε := by
  have hi (i : Fin N) : ∀ᶠ k : ℕ in atTop,
      ‖Complex.I *
        ((completedNativeHermiteBiehlerChiralQuotient
            (canonicalCompletedC3RadialTiltPoint k i) + 1) /
          canonicalCompletedC3RadialTiltPoint k i) - nativeRadialSourceCurvature‖ < ε := by
    have ht := ((nativeRadialSource_tangent i).sub_const nativeRadialSourceCurvature).norm
    have ht0 : Tendsto (fun k => ‖Complex.I *
        ((completedNativeHermiteBiehlerChiralQuotient
            (canonicalCompletedC3RadialTiltPoint k i) + 1) /
          canonicalCompletedC3RadialTiltPoint k i) - nativeRadialSourceCurvature‖)
        atTop (nhds 0) := by simpa using ht
    exact ht0.eventually (eventually_lt_nhds hε)
  simpa only [Finset.mem_univ, forall_true_left] using
    (Finset.univ : Finset (Fin N)).eventually_all.2 (fun i _ => hi i)

end
end CarrySelfAdjointOperator.ChiralReturn
