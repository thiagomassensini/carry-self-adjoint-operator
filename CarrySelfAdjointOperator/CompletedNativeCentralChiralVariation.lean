import CarrySelfAdjointOperator.CompletedNativeCausalLegChiralBridge
import CarrySelfAdjointOperator.CompletedGreenForwardDifferenceVectorLimit
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-!
# Central first variation of the completed chiral balance

The positive and negative normalized chiral energies both equal `1 / 4` at
the centered height.  Their equality at the center does not erase the
completed logarithmic moment: the first transverse variation of their signed
difference is exactly twice the zeroth moment.

This is a division-free statement before taking the punctured limit.  Away
from the center, the signed energy difference divided by `2y` is the diagonal
completed-native `dslope`; joint continuity of the analytic divided
difference supplies the removable value at the center.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

/-- Signed difference between the two normalized chiral energies on the
transverse line `z = i y`. -/
def completedNativeCentralChiralEnergyDifference (y : ℝ) : ℝ :=
  ‖completedNativeNormalizedPositiveChiralTraceState
      (Complex.I * (y : ℂ))‖ ^ 2 -
    ‖completedNativeNormalizedNegativeChiralTraceState
      (Complex.I * (y : ℂ))‖ ^ 2

/-- The two chiral energies agree at the centered height. -/
@[simp] theorem completedNativeCentralChiralEnergyDifference_zero :
    completedNativeCentralChiralEnergyDifference 0 = 0 := by
  simp [completedNativeCentralChiralEnergyDifference,
    norm_sq_completedNativeNormalizedPositiveChiralTraceState_zero,
    norm_sq_completedNativeNormalizedNegativeChiralTraceState_zero]

/-- Off the center, the radial signed chiral quotient is exactly the diagonal
completed-native divided slope. -/
theorem completedNativeCentralChiralEnergyDifference_div_eq_dslope
    {y : ℝ} (hy : y ≠ 0)
    (hyStrip : operatorHeightParameter (Complex.I * (y : ℂ)) ∈
      CPFormal.Analytic.Cp.genuineCriticalStrip)
    (hyF : completedNativeOperatorCharacteristic
      (Complex.I * (y : ℂ)) ≠ 0) :
    ((completedNativeCentralChiralEnergyDifference y : ℂ) /
        ((2 * y : ℝ) : ℂ)) =
      canonicalCompletedNativePolarizedDslopeKernel
        (Complex.I * (y : ℂ)) (Complex.I * (y : ℂ)) := by
  rw [completedNativePolarizedDslopeKernel_diagonal_eq_chiralNormDifference
    hyStrip hyF]
  · simp [completedNativeCentralChiralEnergyDifference, Complex.mul_im]
  · simpa using hy

private theorem completedNativeGreenNormalizedResponse_deriv_zero_eq_moment_zero :
    deriv
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  have h := completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical 0
  simpa [completedNativeGreenResponseTaylorCoefficient,
    iteratedDeriv_one] using h

/-- The punctured complex quotient of the signed chiral energies has the
canonical zeroth moment as its removable central value. -/
theorem completedNativeCentralChiralEnergyDifference_div_tendsto_moment_zero :
    Filter.Tendsto
      (fun y : ℝ =>
        ((completedNativeCentralChiralEnergyDifference y : ℂ) /
          ((2 * y : ℝ) : ℂ)))
      (nhdsWithin 0 {0}ᶜ)
      (nhds (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) := by
  let point : ℝ → ℂ := fun y => Complex.I * (y : ℂ)
  have hpoint : Filter.Tendsto point (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have hcontinuous : ContinuousAt point 0 := by
      fun_prop
    simpa [point] using
      hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hconj : Filter.Tendsto (fun y => conj (point y))
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    simpa [Function.comp_def] using
      Complex.continuous_conj.continuousAt.tendsto.comp hpoint
  have hpair : Filter.Tendsto (fun y => (conj (point y), point y))
      (nhdsWithin 0 {0}ᶜ) (nhds (0, 0)) :=
    hconj.prodMk_nhds hpoint
  have hkernel :=
    (completedGreenDslope_tendsto_prod_of_analyticAt
      completedNativeGreenNormalizedResponse_analyticAt).comp hpair
  rw [completedNativeGreenNormalizedResponse_deriv_zero_eq_moment_zero]
    at hkernel
  have hdomain : ∀ᶠ y : ℝ in nhdsWithin 0 {0}ᶜ,
      point y ∈ completedNativeHeightDomain := by
    exact hpoint.eventually
      (isOpen_completedNativeHeightDomain.mem_nhds
        zero_mem_completedNativeHeightDomain)
  have hnonzero : ∀ᶠ y : ℝ in nhdsWithin 0 {0}ᶜ,
      completedNativeOperatorCharacteristic (point y) ≠ 0 := by
    have hcenter : ∀ᶠ z : ℂ in nhds 0,
        completedNativeOperatorCharacteristic z ≠ 0 :=
      completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
        completedNativeOperatorCharacteristic_zero_ne_zero
    exact hpoint.eventually hcenter
  have hyne : ∀ᶠ y : ℝ in nhdsWithin 0 {0}ᶜ, y ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa using hy
  have heq :
      (fun y : ℝ =>
        ((completedNativeCentralChiralEnergyDifference y : ℂ) /
          ((2 * y : ℝ) : ℂ))) =ᶠ[nhdsWithin 0 {0}ᶜ]
        (fun y => canonicalCompletedNativePolarizedDslopeKernel
          (point y) (point y)) := by
    filter_upwards [hyne, hdomain, hnonzero] with y hy hdom hF
    exact completedNativeCentralChiralEnergyDifference_div_eq_dslope hy
      (by simpa [completedNativeHeightDomain] using hdom) hF
  exact hkernel.congr' heq.symm

/-- Real form of the same removable quotient. -/
theorem completedNativeCentralChiralEnergyDifference_real_div_tendsto_moment_zero :
    Filter.Tendsto
      (fun y : ℝ => completedNativeCentralChiralEnergyDifference y / (2 * y))
      (nhdsWithin 0 {0}ᶜ)
      (nhds (canonicalCompletedNativeLogDerivativeMoment 0)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    completedNativeCentralChiralEnergyDifference_div_tendsto_moment_zero
  convert h using 1
  · funext y
    simp only [Function.comp_apply, Complex.div_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.normSq_apply]
    by_cases hy : y = 0
    · simp [hy]
    · field_simp [hy]
      ring
  · simp

/-- The first transverse variation of the signed chiral energy is exactly
twice the zeroth completed-native logarithmic moment. -/
theorem hasDerivAt_completedNativeCentralChiralEnergyDifference :
    HasDerivAt completedNativeCentralChiralEnergyDifference
      (2 * canonicalCompletedNativeLogDerivativeMoment 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hscaled : Filter.Tendsto
      (fun y : ℝ => 2 *
        (completedNativeCentralChiralEnergyDifference y / (2 * y)))
      (nhdsWithin 0 {0}ᶜ)
      (nhds (2 * canonicalCompletedNativeLogDerivativeMoment 0)) :=
    tendsto_const_nhds.mul
      completedNativeCentralChiralEnergyDifference_real_div_tendsto_moment_zero
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyne : y ≠ 0 := by simpa using hy
  simp only [zero_add, completedNativeCentralChiralEnergyDifference_zero,
    sub_zero, smul_eq_mul]
  field_simp [hyne]

/-- Derivative spelling of the central chiral first variation. -/
theorem deriv_completedNativeCentralChiralEnergyDifference_zero :
    deriv completedNativeCentralChiralEnergyDifference 0 =
      2 * canonicalCompletedNativeLogDerivativeMoment 0 := by
  exact hasDerivAt_completedNativeCentralChiralEnergyDifference.deriv

/-- The already identified radial curvature is the characteristic-weighted
first variation of the complete signed chiral energy. -/
theorem
    completedNativeVerticalModulusEnergy_secondDerivative_zero_eq_chiralVariation :
    iteratedDeriv 2 (completedNativeVerticalModulusEnergy 0) 0 =
      2 * ‖completedNativeOperatorCharacteristic 0‖ ^ 2 *
        deriv completedNativeCentralChiralEnergyDifference 0 := by
  rw [completedNativeVerticalModulusEnergy_secondDerivative_zero_eq_moment_zero,
    deriv_completedNativeCentralChiralEnergyDifference_zero]
  ring

/-- Nonnegative central chiral separation is exactly nonnegativity of the
first canonical moment. -/
theorem deriv_completedNativeCentralChiralEnergyDifference_zero_nonneg_iff :
    0 ≤ deriv completedNativeCentralChiralEnergyDifference 0 ↔
      0 ≤ canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [deriv_completedNativeCentralChiralEnergyDifference_zero]
  norm_num

/-- Strict infinitesimal Hermite--Biehler dominance at the center is exactly
strict positivity of the first canonical moment. -/
theorem deriv_completedNativeCentralChiralEnergyDifference_zero_pos_iff :
    0 < deriv completedNativeCentralChiralEnergyDifference 0 ↔
      0 < canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [deriv_completedNativeCentralChiralEnergyDifference_zero]
  norm_num

end

end CarrySelfAdjointOperator
