import CarrySelfAdjointOperator.NativeIntervalMultiplier
import CarrySelfAdjointOperator.NativeCompletedFiniteGreenResidual

/-! Green resolvent on the original two-leg physical Hilbert space.
No full Laguerre transform or signed positivity is assumed. -/
namespace CarrySelfAdjointOperator.NativeLaguerre
open MeasureTheory
open scoped unitInterval InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false

theorem intervalMultiplier_smul (c : ℂ) (m : C(unitInterval, ℂ)) :
    intervalMultiplier (c • m) = c • intervalMultiplier m := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [intervalMultiplier_ae (c • m) f, intervalMultiplier_ae m f,
    Lp.coeFn_smul c (intervalMultiplier m f)] with u hcm hm hs
  change intervalMultiplier (c • m) f u = (c • intervalMultiplier m f) u
  rw [hcm, hs]
  simp only [ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul, hm]
  ring

private theorem physicalDenominator_pos (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (u : unitInterval) : 0 < 1-q*(u : ℝ) := by
  have hqu : q*(u : ℝ) ≤ q := mul_le_of_le_one_right hq0 u.property.2
  linarith

/-- The true reciprocal multiplier, on the whole original H. -/
def physicalResolventCoefficient (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) : C(unitInterval, ℂ) where
  toFun u := (((1-q*(u : ℝ))⁻¹ : ℝ) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    ((continuous_const.sub (continuous_const.mul continuous_subtype_val)).inv₀
      (fun u => (physicalDenominator_pos q hq0 hq1 u).ne'))

def physicalGreenResolvent (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :=
  intervalMultiplier (physicalResolventCoefficient q hq0 hq1)

/-- Left inverse of I-qM_u on the original H, with no omitted defect. -/
theorem physicalGreenResolvent_left_inverse (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    physicalGreenResolvent q hq0 hq1 * (1-(q : ℂ) • physicalRadialAdvance) = 1 := by
  rw [physicalGreenResolvent, physicalRadialAdvance,
    ← intervalMultiplier_smul, ← intervalMultiplier_one, ← intervalMultiplier_sub,
    ← intervalMultiplier_mul]
  congr 1
  ext u
  simp only [physicalResolventCoefficient, physicalRadialCoefficient, ContinuousMap.mul_apply,
    ContinuousMap.sub_apply, ContinuousMap.one_apply, ContinuousMap.smul_apply,
    ContinuousMap.coe_mk, smul_eq_mul]
  exact_mod_cast inv_mul_cancel₀ (physicalDenominator_pos q hq0 hq1 u).ne'

/-- Right inverse, independently available for vector reconstruction. -/
theorem physicalGreenResolvent_right_inverse (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (1-(q : ℂ) • physicalRadialAdvance) * physicalGreenResolvent q hq0 hq1 = 1 := by
  rw [physicalGreenResolvent, physicalRadialAdvance,
    ← intervalMultiplier_smul, ← intervalMultiplier_one, ← intervalMultiplier_sub,
    ← intervalMultiplier_mul]
  congr 1
  ext u
  simp only [physicalResolventCoefficient, physicalRadialCoefficient, ContinuousMap.mul_apply,
    ContinuousMap.sub_apply, ContinuousMap.one_apply, ContinuousMap.smul_apply,
    ContinuousMap.coe_mk, smul_eq_mul]
  exact_mod_cast mul_inv_cancel₀ (physicalDenominator_pos q hq0 hq1 u).ne'

theorem physicalGreenResolvent_norm_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ‖physicalGreenResolvent q hq0 hq1‖ ≤ (1-q)⁻¹ := by
  apply (intervalMultiplier_norm_le _).trans
  apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ (1-q)⁻¹)).mpr
  intro u
  simp only [physicalResolventCoefficient, ContinuousMap.coe_mk, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (inv_pos.mpr (physicalDenominator_pos q hq0 hq1 u))]
  apply inv_anti₀ (by linarith : 0 < 1-q)
  have hqu : q*(u : ℝ) ≤ q := mul_le_of_le_one_right hq0 u.property.2
  linarith

/-- The physical Green operator q M_u (I-q M_u)^(-2). -/
def physicalGreenOperator (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :=
  (q : ℂ) • (physicalRadialAdvance * (physicalGreenResolvent q hq0 hq1)^2)

/-- Reconstruction is a full Hilbert vector identity before pairing. -/
theorem physicalGreenResolvent_reconstruct (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (f : CanonicalCompletedNativeChiralCauchyCarrier) :
    ((physicalGreenResolvent q hq0 hq1)^2)
      (((1-(q : ℂ) • physicalRadialAdvance)^2 :
        CanonicalCompletedNativeChiralCauchyCarrier →L[ℂ] CanonicalCompletedNativeChiralCauchyCarrier) f) = f := by
  have hL := physicalGreenResolvent_left_inverse q hq0 hq1
  have he : (physicalGreenResolvent q hq0 hq1)^2 *
      (1-(q : ℂ) • physicalRadialAdvance)^2 = 1 := by
    calc
      _ = physicalGreenResolvent q hq0 hq1 *
        (physicalGreenResolvent q hq0 hq1 * (1-(q : ℂ) • physicalRadialAdvance)) *
        (1-(q : ℂ) • physicalRadialAdvance) := by noncomm_ring
      _ = 1 := by rw [hL]; simpa using hL
  exact congrArg (fun T : CanonicalCompletedNativeChiralCauchyCarrier →L[ℂ]
    CanonicalCompletedNativeChiralCauchyCarrier => T f) he

/-- The Green operator itself is the genuine physical coefficient q u/(1-q u)^2. -/
theorem physicalGreenOperator_as_multiplier (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    physicalGreenOperator q hq0 hq1 = intervalMultiplier
      ((q : ℂ) • (physicalRadialCoefficient * (physicalResolventCoefficient q hq0 hq1)^2)) := by
  simp only [physicalGreenOperator, physicalRadialAdvance, physicalGreenResolvent, pow_two,
    intervalMultiplier_mul, intervalMultiplier_smul]

/-- Positivity of Green on the original unsigned H, independently of either chiral pairing. -/
theorem physicalGreenOperator_isPositive (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (physicalGreenOperator q hq0 hq1).IsPositive := by
  rw [physicalGreenOperator_as_multiplier]
  apply intervalMultiplier_isPositive
  · intro u
    simp only [ContinuousMap.smul_apply, ContinuousMap.mul_apply, ContinuousMap.pow_apply,
      physicalRadialCoefficient, physicalResolventCoefficient, ContinuousMap.coe_mk,
      smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_pow, Complex.ofReal_re]
  · intro u
    simp only [ContinuousMap.smul_apply, ContinuousMap.mul_apply, ContinuousMap.pow_apply,
      physicalRadialCoefficient, physicalResolventCoefficient, ContinuousMap.coe_mk,
      smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_pow, Complex.ofReal_re]
    exact mul_nonneg hq0 (mul_nonneg u.property.1 (sq_nonneg _))

theorem physicalGreenOperator_isSelfAdjoint (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    IsSelfAdjoint (physicalGreenOperator q hq0 hq1) :=
  (physicalGreenOperator_isPositive q hq0 hq1).isSelfAdjoint

open CarrySelfAdjointOperator.NativeCauchyPorts
open CarrySelfAdjointOperator.FirstEdgeSewing

def physicalPairRadialAdvance : CanonicalCompletedNativeProjectiveChiralCarrier →L[ℂ]
    CanonicalCompletedNativeProjectiveChiralCarrier :=
  physicalRadialAdvance.prodMap physicalRadialAdvance

def physicalPairGreenResolvent (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    CanonicalCompletedNativeProjectiveChiralCarrier →L[ℂ]
      CanonicalCompletedNativeProjectiveChiralCarrier :=
  (physicalGreenResolvent q hq0 hq1).prodMap (physicalGreenResolvent q hq0 hq1)

/-- Both continuous legs enter the original Lp carrier through the same physical multiplier. -/
theorem continuousPairToSource_physical_advance (f : C(unitInterval, ℂ) × C(unitInterval, ℂ)) :
    continuousPairToSource (pairGeometricAdvance f) =
      physicalPairRadialAdvance (continuousPairToSource f) := by
  apply Prod.ext
  · change ContinuousMap.toLp 2 volume ℂ (physicalRadialCoefficient*f.1) =
      intervalMultiplier physicalRadialCoefficient (ContinuousMap.toLp 2 volume ℂ f.1)
    exact (intervalMultiplier_toLp _ _).symm
  · change ContinuousMap.toLp 2 volume ℂ (physicalRadialCoefficient*f.2) =
      intervalMultiplier physicalRadialCoefficient (ContinuousMap.toLp 2 volume ℂ f.2)
    exact (intervalMultiplier_toLp _ _).symm

def physicalCompletedFiniteSource (k : ℕ) (x : ℕ →₀ ℂ) :=
  continuousPairToSource (completedFiniteSynthesis k x)

def physicalCompletedFiniteResidual (k : ℕ) (x : ℕ →₀ ℂ) :=
  continuousPairToSource (completedFiniteResidual k x)

theorem physicalCompletedFiniteSource_original (k : ℕ) (x : ℕ →₀ ℂ) :
    physicalCompletedFiniteSource k x =
      Finsupp.linearCombination ℂ (canonicalCompletedNativeRadialProjectiveChiralState k) x :=
  completedFiniteSynthesis_to_original k x

theorem physicalCompletedFiniteResidual_original (k : ℕ) (x : ℕ →₀ ℂ) :
    physicalCompletedFiniteResidual k x = Finsupp.linearCombination ℂ (radialChiralAnalyticResidual k) x :=
  completedFiniteResidual_to_original_channels k x

/-- The bulk and two independently retained trace ports. -/
def physicalGreenBulkBoundary (q : ℝ) (k : ℕ) (x : ℕ →₀ ℂ) :=
  physicalPairRadialAdvance (physicalCompletedFiniteSource k (finiteTfvdBulk q x)) +
    ((q : ℂ)⁻¹*finiteTrace0 x) • canonicalCompletedNativeRadialProjectiveChiralState k 0 +
    (finiteTrace1 q x-finiteTrace0 x) • canonicalCompletedNativeRadialProjectiveChiralState k 1

/-- All residual terms from the original synthesis, before pairing. -/
def physicalGreenResidualNumerator (q : ℝ) (k : ℕ) (x : ℕ →₀ ℂ) :=
  physicalCompletedFiniteResidual k (finiteTfvdBulk q x) +
    (2 : ℂ) • physicalCompletedFiniteResidual k x -
    (q : ℂ) • (physicalPairRadialAdvance (physicalCompletedFiniteResidual k x) +
      physicalCompletedFiniteResidual k (coefficientShift x))

/-- The old certified numerator is transported to the genuine physical bounded operator. -/
theorem physicalCompletedFiniteGreen_numerator (q : ℝ) (k : ℕ) (x : ℕ →₀ ℂ) :
    (q : ℂ)⁻¹ • physicalCompletedFiniteSource k x -
      (2 : ℂ) • physicalPairRadialAdvance (physicalCompletedFiniteSource k x) +
      (q : ℂ) • physicalPairRadialAdvance (physicalPairRadialAdvance (physicalCompletedFiniteSource k x)) =
      physicalGreenBulkBoundary q k x + physicalGreenResidualNumerator q k x := by
  have hc := congrArg continuousPairToSource (completedFiniteGreen_corrected_numerator q k x)
  simp only [map_add, map_sub, map_smul, continuousPairToSource_physical_advance,
    completedContinuousPair_toSource] at hc
  unfold physicalGreenBulkBoundary physicalGreenResidualNumerator
    physicalCompletedFiniteSource physicalCompletedFiniteResidual
  rw [hc]
  module

/-- Both original legs are reconstructed; no Laguerre completeness is needed. -/
theorem physicalPairGreenResolvent_reconstruct (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (f : CanonicalCompletedNativeProjectiveChiralCarrier) :
    ((physicalPairGreenResolvent q hq0 hq1)^2)
      (((1-(q : ℂ) • physicalPairRadialAdvance)^2 :
        CanonicalCompletedNativeProjectiveChiralCarrier →L[ℂ]
          CanonicalCompletedNativeProjectiveChiralCarrier) f) = f := by
  apply Prod.ext
  · exact physicalGreenResolvent_reconstruct q hq0 hq1 f.1
  · exact physicalGreenResolvent_reconstruct q hq0 hq1 f.2

/-- Whole-source Green reconstruction with seed, two traces and every residual term. -/
theorem physicalCompletedFiniteGreen_reconstruct (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (k : ℕ) (x : ℕ →₀ ℂ) :
    physicalCompletedFiniteSource k x =
      (q : ℂ) • ((physicalPairGreenResolvent q hq0.le hq1)^2)
        (physicalGreenBulkBoundary q k x + physicalGreenResidualNumerator q k x) := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have he : ((1-(q : ℂ) • physicalPairRadialAdvance)^2 :
      CanonicalCompletedNativeProjectiveChiralCarrier →L[ℂ]
        CanonicalCompletedNativeProjectiveChiralCarrier) (physicalCompletedFiniteSource k x) =
      (q : ℂ) • (physicalGreenBulkBoundary q k x + physicalGreenResidualNumerator q k x) := by
    rw [← physicalCompletedFiniteGreen_numerator]
    simp only [pow_two, mul_apply_eq_comp, sub_apply,
      one_apply_eq_self, smul_apply, map_sub, map_smul,
      smul_sub, smul_add, smul_smul, mul_inv_cancel₀ hq, one_smul]
    module
  have hr := physicalPairGreenResolvent_reconstruct q hq0.le hq1 (physicalCompletedFiniteSource k x)
  rw [he, map_smul] at hr
  exact hr.symm

/-- The signed form sees two independent completed inputs, after full reconstruction. -/
theorem physicalCompletedFiniteGreen_signed_pairing (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (k : ℕ) (x y : ℕ →₀ ℂ) :
    canonicalCompletedNativeProjectiveChiralForm (physicalCompletedFiniteSource k x)
      (physicalCompletedFiniteSource k y) =
    canonicalCompletedNativeProjectiveChiralForm
      ((q : ℂ) • ((physicalPairGreenResolvent q hq0.le hq1)^2)
        (physicalGreenBulkBoundary q k x + physicalGreenResidualNumerator q k x))
      ((q : ℂ) • ((physicalPairGreenResolvent q hq0.le hq1)^2)
        (physicalGreenBulkBoundary q k y + physicalGreenResidualNumerator q k y)) := by
  rw [← physicalCompletedFiniteGreen_reconstruct q hq0 hq1 k x,
    ← physicalCompletedFiniteGreen_reconstruct q hq0 hq1 k y]

/-- Every cross survives the inverse Green operator, including the residual self-sector. -/
theorem physicalCompletedFiniteGreen_four_sectors (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (k : ℕ) (x y : ℕ →₀ ℂ) :
    let W := fun f : CanonicalCompletedNativeProjectiveChiralCarrier =>
      (q : ℂ) • ((physicalPairGreenResolvent q hq0.le hq1)^2) f
    canonicalCompletedNativeProjectiveChiralForm (physicalCompletedFiniteSource k x)
      (physicalCompletedFiniteSource k y) =
      canonicalCompletedNativeProjectiveChiralForm (W (physicalGreenBulkBoundary q k x))
        (W (physicalGreenBulkBoundary q k y)) +
      canonicalCompletedNativeProjectiveChiralForm (W (physicalGreenBulkBoundary q k x))
        (W (physicalGreenResidualNumerator q k y)) +
      canonicalCompletedNativeProjectiveChiralForm (W (physicalGreenResidualNumerator q k x))
        (W (physicalGreenBulkBoundary q k y)) +
      canonicalCompletedNativeProjectiveChiralForm (W (physicalGreenResidualNumerator q k x))
        (W (physicalGreenResidualNumerator q k y)) := by
  dsimp only
  rw [physicalCompletedFiniteGreen_signed_pairing q hq0 hq1 k x y]
  simp only [map_add, smul_add]
  exact completed_residual_four_sectors _ _ _ _


end
end CarrySelfAdjointOperator.NativeLaguerre
