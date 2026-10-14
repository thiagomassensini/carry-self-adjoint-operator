import CarrySelfAdjointOperator.NativePhysicalGreenResolvent
import CarrySelfAdjointOperator.NativeCauchyLaguerreSources
import CarrySelfAdjointOperator.NativeCauchyLaguerreResolventDefect
import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Actual responses of the unchanged physical interval multiplier

These responses are constructed from the original completed source vectors,
not from moment matrices. On the unit height disk the multiplier inverse is
explicit, its vector equation is exact, and its geometric prefixes converge
in both the response and energy sectors. The resulting cyclic readout is the
readout of multiplication by `u`; equality with the native height Weyl
function is not inserted. A literal incident-seed obstruction is retained.
-/

namespace CarrySelfAdjointOperator.NativeLaguerre
open Filter Topology MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate unitInterval lp
open ChiralReturn GammaMaterialSewing
noncomputable section
set_option autoImplicit false

local notation "H" => CanonicalCompletedNativeChiralCauchyCarrier

private theorem disk_square_lt_one {z : ℂ} (hz : ‖z‖ < 1) : ‖z‖ ^ 2 < 1 := by
  nlinarith [norm_nonneg z]

private theorem disk_product_norm_le (z : ℂ) (u : unitInterval) :
    ‖z ^ 2 * ((u : ℝ) : ℂ)‖ ≤ ‖z‖ ^ 2 := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg u.property.1]
  exact mul_le_of_le_one_right (sq_nonneg _) u.property.2

private theorem disk_denominator_ne_zero (z : ℂ) (hz : ‖z‖ < 1) (u : unitInterval) :
    1 - z ^ 2 * ((u : ℝ) : ℂ) ≠ 0 := by
  have ht := (disk_product_norm_le z u).trans_lt (disk_square_lt_one hz)
  intro h
  have he : z ^ 2 * ((u : ℝ) : ℂ) = 1 := by linear_combination -h
  rw [he, norm_one] at ht
  exact lt_irrefl _ ht

/-- Explicit reciprocal on the ORIGINAL interval, for complex height. -/
def diskResponseCoefficient (z : ℂ) (hz : ‖z‖ < 1) : C(unitInterval, ℂ) where
  toFun u := (1 - z ^ 2 * ((u : ℝ) : ℂ))⁻¹
  continuous_toFun :=
    (continuous_const.sub (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_subtype_val))).inv₀
        (disk_denominator_ne_zero z hz)

/-- Physical inverse of `I-z²M_u`, on the whole original L² carrier. -/
def diskPhysicalResolvent (z : ℂ) (hz : ‖z‖ < 1) : H →L[ℂ] H :=
  intervalMultiplier (diskResponseCoefficient z hz)

theorem diskPhysicalResolvent_left_inverse (z : ℂ) (hz : ‖z‖ < 1) :
    diskPhysicalResolvent z hz * (1 - z ^ 2 • physicalRadialAdvance) = 1 := by
  rw [diskPhysicalResolvent, physicalRadialAdvance,
    ← intervalMultiplier_smul, ← intervalMultiplier_one, ← intervalMultiplier_sub,
    ← intervalMultiplier_mul]
  congr 1
  ext u
  simp only [diskResponseCoefficient, physicalRadialCoefficient,
    ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply,
    ContinuousMap.smul_apply, ContinuousMap.coe_mk, smul_eq_mul]
  exact inv_mul_cancel₀ (disk_denominator_ne_zero z hz u)

theorem diskPhysicalResolvent_right_inverse (z : ℂ) (hz : ‖z‖ < 1) :
    (1 - z ^ 2 • physicalRadialAdvance) * diskPhysicalResolvent z hz = 1 := by
  rw [diskPhysicalResolvent, physicalRadialAdvance,
    ← intervalMultiplier_smul, ← intervalMultiplier_one, ← intervalMultiplier_sub,
    ← intervalMultiplier_mul]
  congr 1
  ext u
  simp only [diskResponseCoefficient, physicalRadialCoefficient,
    ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply,
    ContinuousMap.smul_apply, ContinuousMap.coe_mk, smul_eq_mul]
  exact mul_inv_cancel₀ (disk_denominator_ne_zero z hz u)

theorem diskPhysicalResolvent_norm_le (z : ℂ) (hz : ‖z‖ < 1) :
    ‖diskPhysicalResolvent z hz‖ ≤ (1 - ‖z‖ ^ 2)⁻¹ := by
  have hden : 0 < 1 - ‖z‖ ^ 2 := sub_pos.mpr (disk_square_lt_one hz)
  apply (intervalMultiplier_norm_le _).trans
  apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ (1 - ‖z‖ ^ 2)⁻¹)).mpr
  intro u
  change ‖(1 - z ^ 2 * ((u : ℝ) : ℂ))⁻¹‖ ≤ _
  rw [norm_inv]
  have hlow : 1 - ‖z‖ ^ 2 ≤ ‖1 - z ^ 2 * ((u : ℝ) : ℂ)‖ := by
    calc
      _ ≤ 1 - ‖z ^ 2 * ((u : ℝ) : ℂ)‖ := sub_le_sub_left (disk_product_norm_le z u) 1
      _ ≤ _ := by simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) (z ^ 2 * ((u : ℝ) : ℂ))
  exact inv_anti₀ (sub_pos.mpr (disk_square_lt_one hz)) hlow

/-- Response to a source supplied BEFORE applying the inverse. -/
def diskPhysicalResponse (z : ℂ) (hz : ‖z‖ < 1) (source : H) : H :=
  diskPhysicalResolvent z hz source

theorem diskPhysicalResponse_ae (z : ℂ) (hz : ‖z‖ < 1) (source : H) :
    (diskPhysicalResponse z hz source : unitInterval → ℂ) =ᵐ[volume]
      (fun u ↦ (1 - z ^ 2 * ((u : ℝ) : ℂ))⁻¹ * source u) :=
  intervalMultiplier_ae (diskResponseCoefficient z hz) source

theorem diskPhysicalResponse_equation (z : ℂ) (hz : ‖z‖ < 1) (source : H) :
    diskPhysicalResponse z hz source -
        z ^ 2 • physicalRadialAdvance (diskPhysicalResponse z hz source) = source := by
  have h := congrArg (fun T : H →L[ℂ] H => T source)
    (diskPhysicalResolvent_right_inverse z hz)
  simpa only [diskPhysicalResponse, mul_apply_eq_comp, sub_apply,
    one_apply_eq_self, smul_apply] using h

theorem diskPhysicalResponse_zero (source : H) :
    diskPhysicalResponse 0 (by norm_num) source = source := by
  simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_smul, sub_zero] using
    diskPhysicalResponse_equation 0 (by norm_num) source

/-- The genuine energy factor is multiplication by sqrt(u). -/
def physicalEnergyCoefficient : C(unitInterval, ℂ) where
  toFun u := ((Real.sqrt (u : ℝ) : ℝ) : ℂ)
  continuous_toFun := by fun_prop

def physicalEnergyFactor : H →L[ℂ] H := intervalMultiplier physicalEnergyCoefficient

theorem physicalEnergyFactor_isSelfAdjoint : IsSelfAdjoint physicalEnergyFactor :=
  intervalMultiplier_isSelfAdjoint _ (by intro u; simp [physicalEnergyCoefficient])

theorem physicalEnergyFactor_sq : physicalEnergyFactor ^ 2 = physicalRadialAdvance := by
  rw [physicalEnergyFactor, pow_two, ← intervalMultiplier_mul, physicalRadialAdvance]
  congr 1
  ext u
  change (Real.sqrt (u : ℝ) : ℂ) * (Real.sqrt (u : ℝ) : ℂ) = (u : ℝ)
  norm_cast
  nlinarith [Real.sq_sqrt u.property.1]

theorem physicalEnergyFactor_energy (x y : H) :
    inner ℂ (physicalRadialAdvance x) y =
      inner ℂ (physicalEnergyFactor x) (physicalEnergyFactor y) := by
  calc
    _ = inner ℂ (physicalEnergyFactor (physicalEnergyFactor x)) y := by
      rw [← physicalEnergyFactor_sq, pow_two, mul_apply_eq_comp]
    _ = _ := physicalEnergyFactor_isSelfAdjoint.isSymmetric _ _

/-- Full physical parity state. This is not identified with a native moment jet. -/
def diskPhysicalParityResponse (z : ℂ) (hz : ‖z‖ < 1) (source : H) : WithLp 2 (H × H) :=
  HeightResolventGreenDefect.parityState physicalEnergyFactor z
    (diskPhysicalResponse z hz source)

theorem diskPhysicalResponse_kernel_eq_gram
    (source : H) (z w : ℂ) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) (hsep : w ≠ conj z) :
    HeightResolventGreenDefect.readoutKernel source z w
        (diskPhysicalResponse z hz source) (diskPhysicalResponse w hw source) =
      inner ℂ (diskPhysicalParityResponse z hz source)
        (diskPhysicalParityResponse w hw source) :=
  HeightResolventGreenDefect.readoutKernel_eq_parityState_inner
    physicalRadialAdvance physicalEnergyFactor physicalEnergyFactor_energy
    source z w _ _ hsep
    (diskPhysicalResponse_equation z hz source) (diskPhysicalResponse_equation w hw source)

/-- Geometric approximants use the same source, before any scalar readout. -/
def diskPhysicalResponsePrefix (z : ℂ) (N : ℕ) (source : H) : H :=
  ∑ n ∈ Finset.range (N + 1), (z ^ 2) ^ n • (physicalRadialAdvance ^ n) source

theorem diskPhysicalResponsePrefix_equation (z : ℂ) (N : ℕ) (source : H) :
    diskPhysicalResponsePrefix z N source -
        z ^ 2 • physicalRadialAdvance (diskPhysicalResponsePrefix z N source) =
      source - (z ^ 2) ^ (N + 1) • (physicalRadialAdvance ^ (N + 1)) source := by
  induction N with
  | zero => simp [diskPhysicalResponsePrefix]
  | succ N ih =>
    have hp : diskPhysicalResponsePrefix z (N + 1) source =
        diskPhysicalResponsePrefix z N source +
          (z ^ 2) ^ (N + 1) • (physicalRadialAdvance ^ (N + 1)) source := by
      simp only [diskPhysicalResponsePrefix, Finset.sum_range_succ]
    rw [hp, map_add, map_smul]
    have hnext : physicalRadialAdvance ((physicalRadialAdvance ^ (N + 1)) source) =
        (physicalRadialAdvance ^ (N + 1 + 1)) source := by
      simp only [pow_succ', mul_apply_eq_comp]
    rw [hnext]
    calc
      _ = (diskPhysicalResponsePrefix z N source -
          z ^ 2 • physicalRadialAdvance (diskPhysicalResponsePrefix z N source)) +
          (z ^ 2) ^ (N + 1) • (physicalRadialAdvance ^ (N + 1)) source -
          z ^ 2 • ((z ^ 2) ^ (N + 1) •
            (physicalRadialAdvance ^ (N + 1 + 1)) source) := by module
      _ = _ := by rw [ih, pow_succ (z ^ 2) (N + 1)]; module

theorem physicalRadialAdvance_apply_norm_le (x : H) : ‖physicalRadialAdvance x‖ ≤ ‖x‖ := by
  exact (physicalRadialAdvance.le_opNorm x).trans
    (by simpa using mul_le_mul_of_nonneg_right physicalRadialAdvance_norm_le_one (norm_nonneg x))

theorem physicalRadialAdvance_pow_norm_le (N : ℕ) (x : H) :
    ‖(physicalRadialAdvance ^ N) x‖ ≤ ‖x‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact (physicalRadialAdvance_apply_norm_le _).trans ih

theorem diskPhysicalResponsePrefix_tail (z : ℂ) (hz : ‖z‖ < 1) (N : ℕ) (source : H) :
    diskPhysicalResponse z hz source - diskPhysicalResponsePrefix z N source =
      diskPhysicalResolvent z hz
        ((z ^ 2) ^ (N + 1) • (physicalRadialAdvance ^ (N + 1)) source) := by
  have h := congrArg (diskPhysicalResolvent z hz)
    (diskPhysicalResponsePrefix_equation z N source)
  have hi (x : H) : diskPhysicalResolvent z hz (x - z ^ 2 • physicalRadialAdvance x) = x := by
    have h' := congrArg (fun T : H →L[ℂ] H => T x)
      (diskPhysicalResolvent_left_inverse z hz)
    simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, smul_apply] using h'
  rw [hi, map_sub] at h
  change diskPhysicalResponsePrefix z N source = diskPhysicalResponse z hz source - _ at h
  rw [h]
  module

theorem diskPhysicalResponsePrefix_error_le (z : ℂ) (hz : ‖z‖ < 1) (N : ℕ) (source : H) :
    ‖diskPhysicalResponse z hz source - diskPhysicalResponsePrefix z N source‖ ≤
      (1 - ‖z‖ ^ 2)⁻¹ * (‖z‖ ^ 2) ^ (N + 1) * ‖source‖ := by
  rw [diskPhysicalResponsePrefix_tail]
  calc
    _ ≤ ‖diskPhysicalResolvent z hz‖ *
        ‖(z ^ 2) ^ (N + 1) • (physicalRadialAdvance ^ (N + 1)) source‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := by
      rw [norm_smul, norm_pow, norm_pow]
      have hR := diskPhysicalResolvent_norm_le z hz
      have hA := physicalRadialAdvance_pow_norm_le (N + 1) source
      have hpos : 0 ≤ (1 - ‖z‖ ^ 2)⁻¹ := (inv_pos.mpr (sub_pos.mpr (disk_square_lt_one hz))).le
      rw [mul_assoc]
      gcongr

theorem diskPhysicalResponsePrefix_tendsto (z : ℂ) (hz : ‖z‖ < 1) (source : H) :
    Tendsto (fun N ↦ diskPhysicalResponsePrefix z N source) atTop
      (nhds (diskPhysicalResponse z hz source)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg ‖z‖) (disk_square_lt_one hz)
  have hb : Tendsto (fun N : ℕ ↦
      (1 - ‖z‖ ^ 2)⁻¹ * (‖z‖ ^ 2) ^ (N + 1) * ‖source‖) atTop (nhds 0) := by
    simpa only [pow_succ (‖z‖ ^ 2), mul_zero, zero_mul] using
      ((tendsto_const_nhds (x := (1 - ‖z‖ ^ 2)⁻¹)).mul
        (hp.mul_const (‖z‖ ^ 2))).mul_const ‖source‖
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ by
    rw [norm_sub_rev]
    exact diskPhysicalResponsePrefix_error_le z hz N source) hb

theorem diskPhysicalEnergyPrefix_tendsto (z : ℂ) (hz : ‖z‖ < 1) (source : H) :
    Tendsto (fun N ↦ physicalEnergyFactor (diskPhysicalResponsePrefix z N source)) atTop
      (nhds (physicalEnergyFactor (diskPhysicalResponse z hz source))) :=
  physicalEnergyFactor.continuous.continuousAt.tendsto.comp
    (diskPhysicalResponsePrefix_tendsto z hz source)

/-- The three original channels enter the same physical response operator. -/
def diskCompletedSourceResponse (z : ℂ) (hz : ‖z‖ < 1)
    (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) (a : Fin 3) : H :=
  diskPhysicalResponse z hz (physicalSourceChannels k c r a : H)

theorem diskCompletedSourceResponse_equation (z : ℂ) (hz : ‖z‖ < 1)
    (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) (a : Fin 3) :
    diskCompletedSourceResponse z hz k c r a -
        z ^ 2 • physicalRadialAdvance (diskCompletedSourceResponse z hz k c r a) =
      (physicalSourceChannels k c r a : H) :=
  diskPhysicalResponse_equation z hz _

/-- Original source reconstruction survives the actual inverse, including
the native and completion companions and both chiral orientations. -/
theorem diskCompletedSourceResponse_original_legs (z : ℂ) (hz : ‖z‖ < 1)
    (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hs : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      CPFormal.Analytic.Cp.genuineCriticalStrip)
    (hp : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    diskPhysicalResponse z hz (physicalOriginalIncident k c r : H) =
      diskCompletedSourceResponse z hz k c r 1 +
        diskCompletedSourceResponse z hz k c r 2 +
        Complex.I • diskCompletedSourceResponse z hz k c r 0 ∧
    diskPhysicalResponse z hz (physicalOriginalReturned k c r : H) =
      diskCompletedSourceResponse z hz k c r 1 +
        diskCompletedSourceResponse z hz k c r 2 -
        Complex.I • diskCompletedSourceResponse z hz k c r 0 := by
  have h := nativeCoupledCompletion_originalSource_legs k c r hs hp
  constructor
  · have hi := congrArg (diskPhysicalResolvent z hz) h.2.1
    simpa [diskPhysicalResponse, diskCompletedSourceResponse,
      physicalOriginalIncident, physicalSourceChannels, physicalNativeCompanion,
      physicalCompletionCompanion, physicalSourceValue, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      map_add, map_smul] using hi
  · have ho := congrArg (diskPhysicalResolvent z hz) h.2.2
    simpa [diskPhysicalResponse, diskCompletedSourceResponse,
      physicalOriginalReturned, physicalSourceChannels, physicalNativeCompanion,
      physicalCompletionCompanion, physicalSourceValue, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      map_add, map_sub, map_smul] using ho

/-- Independent prefix orders preserve all nine ordered source crossings. -/
theorem diskCompletedSourceResponse_nine_crossings_tendsto
    (z w : ℂ) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1)
    (k l : ℕ) {N M : ℕ} (c : Fin N → ℂ) (d : Fin M → ℂ)
    (r s : ℝ) (a b : Fin 3) :
    Tendsto (fun p : ℕ × ℕ ↦
      inner ℂ
        (diskPhysicalResponsePrefix z p.1 (physicalSourceChannels k c r a : H))
        (diskPhysicalResponsePrefix w p.2 (physicalSourceChannels l d s b : H))) atTop
      (nhds (inner ℂ (diskCompletedSourceResponse z hz k c r a)
        (diskCompletedSourceResponse w hw l d s b))) := by
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  exact ((diskPhysicalResponsePrefix_tendsto z hz _).comp hfst).inner
    ((diskPhysicalResponsePrefix_tendsto w hw _).comp hsnd)

/-- The actual characteristic residual of the constructed physical response. -/
def diskPhysicalNativeResidual (z : ℂ) (hz : ‖z‖ < 1) (source : H) : ℂ :=
  deriv completedNativeOperatorCharacteristic z +
    2 * z * inner ℂ source (diskPhysicalResponse z hz source) *
      completedNativeOperatorCharacteristic z

/-- The vector residual is now proved zero. The native characteristic
residual remains explicit, rather than being assumed to vanish. -/
theorem diskPhysicalResponse_native_kernel_defect
    (source : H) (z w : ℂ) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0) (hsep : w ≠ conj z) :
    HeightResolventGreenDefect.characteristicKernel
        (completedNativeOperatorCharacteristic z) (completedNativeOperatorCharacteristic w)
        (deriv completedNativeOperatorCharacteristic z) (deriv completedNativeOperatorCharacteristic w)
        z w - inner ℂ (diskPhysicalParityResponse z hz source)
          (diskPhysicalParityResponse w hw source) =
      (-diskPhysicalNativeResidual w hw source / completedNativeOperatorCharacteristic w +
        conj (diskPhysicalNativeResidual z hz source / completedNativeOperatorCharacteristic z)) /
          (2 * (w - conj z)) := by
  rw [← diskPhysicalResponse_kernel_eq_gram source z w hz hw hsep]
  exact HeightResolventGreenDefect.characteristicKernel_sub_readoutKernel source z w
    _ _ _ _ _ _ hzF hwF hsep

/-- Multiplication by u preserves the existing closed Cauchy span. -/
theorem physicalRadialAdvance_mem_cauchyClosure (x : PhysicalCauchySpace) :
    physicalRadialAdvance (x : H) ∈ physicalCauchyClosure := by
  refine physicalCauchyEmbedding_dense.induction_on x
    (physicalCauchySpan.isClosed_topologicalClosure.preimage
      (physicalRadialAdvance.continuous.comp continuous_subtype_val)) ?_
  intro c
  change physicalRadialAdvance (physicalCauchySynthesis c) ∈ physicalCauchyClosure
  simp only [physicalCauchySynthesis, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul, physicalRadialAdvance_feature]
  apply physicalCauchyClosure.sum_mem
  intro j _
  exact physicalCauchyClosure.smul_mem _ (by
    simpa only [physicalCauchyFeature_coe] using (physicalCauchyFeature (j + 1)).property)

theorem diskPhysicalResponsePrefix_mem_cauchyClosure (z : ℂ) (N : ℕ)
    (source : PhysicalCauchySpace) :
    diskPhysicalResponsePrefix z N (source : H) ∈ physicalCauchyClosure := by
  have hpow (n : ℕ) : (physicalRadialAdvance ^ n) (source : H) ∈ physicalCauchyClosure := by
    induction n with
    | zero => exact source.property
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      exact physicalRadialAdvance_mem_cauchyClosure ⟨_, ih⟩
  exact physicalCauchyClosure.sum_mem fun n _ ↦ physicalCauchyClosure.smul_mem _ (hpow n)

theorem diskPhysicalResponse_mem_cauchyClosure (z : ℂ) (hz : ‖z‖ < 1)
    (source : PhysicalCauchySpace) :
    diskPhysicalResponse z hz (source : H) ∈ physicalCauchyClosure :=
  physicalCauchySpan.isClosed_topologicalClosure.mem_of_tendsto
    (diskPhysicalResponsePrefix_tendsto z hz (source : H))
    (Eventually.of_forall fun N ↦ diskPhysicalResponsePrefix_mem_cauchyClosure z N source)

/-- A genuinely constructed vector on the original closed physical carrier. -/
def diskCauchyResponse (z : ℂ) (hz : ‖z‖ < 1) (source : PhysicalCauchySpace) :
    PhysicalCauchySpace :=
  ⟨diskPhysicalResponse z hz (source : H), diskPhysicalResponse_mem_cauchyClosure z hz source⟩

/-- The existing Laguerre observations now apply to this concrete response. -/
theorem diskCauchyResponse_laguerre_coordinate
    (z : ℂ) (hz : ‖z‖ < 1) (source : PhysicalCauchySpace) (r : ℕ) :
    cauchyLaguerreIsometry (diskCauchyResponse z hz source) r =
      inner ℂ (laguerreMode r) (diskPhysicalResponse z hz (source : H)) :=
  cauchyLaguerreIsometry_coordinate _ _

/-- Exact zeroth cyclic readout of the literal original incident seed. -/
theorem diskPhysicalIncidentSeed_zero_readout (k : ℕ) :
    inner ℂ (completedNativeRadialChiralCauchyState k 0)
      (diskPhysicalResponse 0 (by norm_num) (completedNativeRadialChiralCauchyState k 0)) =
        ((((k : ℝ) + 1) / 2 : ℝ) : ℂ) := by
  rw [diskPhysicalResponse_zero, inner_completedNativeRadialChiralCauchyState]
  norm_num
  ring

theorem diskPhysicalIncidentSeed_zero_ne_nativeMoment (k : ℕ) :
    inner ℂ (completedNativeRadialChiralCauchyState k 0)
      (diskPhysicalResponse 0 (by norm_num) (completedNativeRadialChiralCauchyState k 0)) ≠
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [diskPhysicalIncidentSeed_zero_readout]
  intro h
  have he := Complex.ofReal_injective h
  have hb := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

/-- Every coefficient of the constructed seed response comes from the
original interval multiplier and original half-density. -/
theorem physicalRadialAdvance_pow_seed (k n : ℕ) :
    (physicalRadialAdvance ^ n) (completedNativeRadialChiralCauchyState k 0) =
      completedNativeRadialChiralCauchyState k n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', mul_apply_eq_comp, ih, physicalRadialAdvance_state]

theorem diskPhysicalIncidentSeed_prefix_readout (z : ℂ) (N k : ℕ) :
    inner ℂ (completedNativeRadialChiralCauchyState k 0)
      (diskPhysicalResponsePrefix z N (completedNativeRadialChiralCauchyState k 0)) =
        ∑ n ∈ Finset.range (N + 1), (z ^ 2) ^ n *
          ((((k : ℝ) + 1) / ((n : ℝ) + 2) : ℝ) : ℂ) := by
  simp only [diskPhysicalResponsePrefix, inner_sum, inner_smul_right,
    physicalRadialAdvance_pow_seed, inner_completedNativeRadialChiralCauchyState]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  push_cast
  ring

/-- The value port at the Taylor center is supplied by the ORIGINAL
completed characteristic and its existing positive HB coordinate. -/
def centeredCompletedValueSource : H :=
  (completedNativeOperatorCharacteristic 0 /
    completedNativePositiveHermiteBiehlerCoordinate 0) • completedNativeChiralCauchyFeature 0

theorem centeredCompletedValueSource_eq : centeredCompletedValueSource =
    -Complex.I • completedNativeChiralCauchyFeature 0 := by
  have hF := completedNativeOperatorCharacteristic_zero_ne_zero
  unfold centeredCompletedValueSource
  congr 1
  rw [completedNativePositiveHermiteBiehlerCoordinate_zero]
  field_simp [hF]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem centeredCompletedValueSource_zero_readout :
    inner ℂ centeredCompletedValueSource
      (diskPhysicalResponse 0 (by norm_num) centeredCompletedValueSource) = (1 / 2 : ℂ) := by
  rw [diskPhysicalResponse_zero, centeredCompletedValueSource_eq,
    inner_smul_left, inner_smul_right, inner_completedNativeChiralCauchyFeature]
  norm_num
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The actual completed value port also fails the unmodified multiplier
readout at order zero. This is a no-go for this candidate, not the theory. -/
theorem centeredCompletedValueSource_zero_ne_nativeMoment :
    inner ℂ centeredCompletedValueSource
      (diskPhysicalResponse 0 (by norm_num) centeredCompletedValueSource) ≠
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [centeredCompletedValueSource_zero_readout]
  intro h
  have he := congrArg Complex.re h
  have hb := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  norm_num at he
  linarith

/-- Changing the operator alone cannot repair this source: every exact
quadratic response has the same vector at height zero. -/
theorem centeredCompletedValueSource_not_native_cyclic_response
    (x jx : H)
    (hx : x - (0 : ℂ) ^ 2 • jx = centeredCompletedValueSource) :
    inner ℂ centeredCompletedValueSource x ≠
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_smul, sub_zero] at hx
  rw [hx]
  simpa only [diskPhysicalResponse_zero] using
    centeredCompletedValueSource_zero_ne_nativeMoment

end
end CarrySelfAdjointOperator.NativeLaguerre
