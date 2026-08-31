import CarrySelfAdjointOperator.CompletedNativeCentralCarryTiltSensitivity
import CPFormal.Analytic.CpBracketHolomorphic
import CPFormal.Analytic.CpGenuineFirstOrthogonalGreenLimit
import Mathlib.Tactic

/-!
# Central first variation of the finite Green bulk

The bracket-coupled finite Green identity already separates the oriented bulk
from its literal boundary return.  Along the centered real displacement it is

`bulk M delta = 2 * delta * finiteRadialGreenEnergy 3 M (1/2 + delta)`.

This file differentiates that exact identity at `delta = 0`.  The resulting
first variation is twice the strictly positive finite radial energy.  No
boundary term is discarded and no completed-native moment is assumed.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Canonical real spectral displacement through the half-abscissa. -/
def canonicalCentralRealSpectralParameter (delta : ℝ) : ℂ :=
  (((1 : ℝ) / 2 + delta : ℝ) : ℂ)

@[simp] theorem canonicalCentralRealSpectralParameter_re (delta : ℝ) :
    (canonicalCentralRealSpectralParameter delta).re = (1 : ℝ) / 2 + delta :=
  rfl

@[simp] theorem canonicalCentralRealSpectralParameter_zero :
    canonicalCentralRealSpectralParameter 0 = (1 / 2 : ℂ) := by
  norm_num [canonicalCentralRealSpectralParameter]

@[simp] theorem criticalDisplacement_canonicalCentralRealSpectralParameter
    (delta : ℝ) :
    criticalDisplacement (canonicalCentralRealSpectralParameter delta).re =
      delta := by
  unfold canonicalCentralRealSpectralParameter criticalDisplacement
  simp

/-- The finite bracket-coupled Green bulk after retaining the boundary as a
separate channel. -/
def finiteCanonicalBracketCoupledGreenBulk (M : ℕ) (delta : ℝ) : ℝ :=
  finiteBracketCoupledCpGreenFlux 3 M
      (canonicalCentralRealSpectralParameter delta) -
    finiteBracketCoupledSignedBoundary M
      (canonicalCentralRealSpectralParameter delta)

/-- Exact division-free radial factorization of the finite bulk. -/
theorem finiteCanonicalBracketCoupledGreenBulk_eq_radialEnergy
    (M : ℕ) (delta : ℝ) :
    finiteCanonicalBracketCoupledGreenBulk M delta =
      2 * delta * finiteRadialGreenEnergy 3 M
        (canonicalCentralRealSpectralParameter delta) := by
  have h := finiteBracketCoupledCpGreen_identity 3 M (by norm_num)
    (canonicalCentralRealSpectralParameter delta)
  unfold finiteCanonicalBracketCoupledGreenBulk
  rw [h, criticalDisplacement_canonicalCentralRealSpectralParameter]
  ring

/-- The same bulk written before the removable radial quotient is formed. -/
theorem finiteCanonicalBracketCoupledGreenBulk_eq_radialDifference
    (M : ℕ) (delta : ℝ) :
    finiteCanonicalBracketCoupledGreenBulk M delta =
      cpRadialDifference 3 delta *
        (finiteReflectedGradientPairing M
          (canonicalCentralRealSpectralParameter delta)).re := by
  rw [finiteCanonicalBracketCoupledGreenBulk_eq_radialEnergy]
  unfold finiteRadialGreenEnergy
  rw [criticalDisplacement_canonicalCentralRealSpectralParameter]
  calc
    2 * delta *
          (cpRadialCofactor 3 delta *
            (finiteReflectedGradientPairing M
              (canonicalCentralRealSpectralParameter delta)).re) =
        (2 * delta * cpRadialCofactor 3 delta) *
          (finiteReflectedGradientPairing M
            (canonicalCentralRealSpectralParameter delta)).re := by ring
    _ = cpRadialDifference 3 delta *
          (finiteReflectedGradientPairing M
            (canonicalCentralRealSpectralParameter delta)).re := by
      rw [← cpRadialDifference_eq_two_mul_delta_mul_cofactor]

@[simp] theorem finiteCanonicalBracketCoupledGreenBulk_zero (M : ℕ) :
    finiteCanonicalBracketCoupledGreenBulk M 0 = 0 := by
  rw [finiteCanonicalBracketCoupledGreenBulk_eq_radialEnergy]
  ring

/-- Exact centered derivative of the radial difference. -/
theorem hasDerivAt_cpRadialDifference_three_zero :
    HasDerivAt (cpRadialDifference 3) (2 * Real.log 3) 0 := by
  have hpos : (0 : ℝ) < 3 := by norm_num
  have hforward :=
    (Real.hasStrictDerivAt_const_rpow hpos 0).hasDerivAt
  have houter : HasDerivAt (fun delta : ℝ ↦ (3 : ℝ) ^ delta)
      (Real.log 3) (-0) := by
    simpa using hforward
  have hbackward := houter.comp 0 (hasDerivAt_neg' (0 : ℝ))
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hsub := hforward.tendsto_slope_zero.sub
    hbackward.tendsto_slope_zero
  have hquotient : Filter.Tendsto
      (fun delta : ℝ ↦ delta⁻¹ *
        ((3 : ℝ) ^ delta - (3 : ℝ) ^ (-delta)))
      (nhdsWithin 0 {0}ᶜ) (nhds (2 * Real.log 3)) := by
    convert hsub using 1
    · funext delta
      simp only [Function.comp_apply, zero_add, Real.rpow_zero,
        smul_eq_mul]
      ring
    · norm_num
      ring
  simpa [slope, cpRadialDifference, smul_eq_mul] using hquotient

@[simp] theorem reflectedParameter_canonicalCentralRealSpectralParameter
    (delta : ℝ) :
    reflectedParameter (canonicalCentralRealSpectralParameter delta) =
      canonicalCentralRealSpectralParameter (-delta) := by
  apply Complex.ext
  · simp [reflectedParameter, canonicalCentralRealSpectralParameter]
    ring
  · simp [reflectedParameter, canonicalCentralRealSpectralParameter]

/-- The finite reflected gradient pairing is differentiable along the real
central displacement. -/
theorem differentiableAt_finiteReflectedGradientPairing_centralReal
    (M : ℕ) :
    DifferentiableAt ℝ
      (fun delta : ℝ ↦
        finiteReflectedGradientPairing M
          (canonicalCentralRealSpectralParameter delta)) 0 := by
  have hparameter : Differentiable ℝ canonicalCentralRealSpectralParameter := by
    unfold canonicalCentralRealSpectralParameter
    fun_prop
  have hparameterNeg : Differentiable ℝ
      (fun delta : ℝ ↦ canonicalCentralRealSpectralParameter (-delta)) := by
    fun_prop
  have hterm (n : ℕ) (hn : 0 < n) : Differentiable ℝ
      (fun delta : ℝ ↦
        natDirichletTerm (canonicalCentralRealSpectralParameter delta) n) := by
    unfold natDirichletTerm
    exact
      (differentiable_dirichletTerm_in_parameter
        (show (0 : ℤ) < (n : ℤ) by exact_mod_cast hn)).restrictScalars ℝ |>.comp
          hparameter
  have htermNeg (n : ℕ) (hn : 0 < n) : Differentiable ℝ
      (fun delta : ℝ ↦
        natDirichletTerm
          (canonicalCentralRealSpectralParameter (-delta)) n) := by
    unfold natDirichletTerm
    exact
      (differentiable_dirichletTerm_in_parameter
        (show (0 : ℤ) < (n : ℤ) by exact_mod_cast hn)).restrictScalars ℝ |>.comp
          hparameterNeg
  have hgradient (n : ℕ) : Differentiable ℝ
      (fun delta : ℝ ↦ positiveDirichletGradient
        (canonicalCentralRealSpectralParameter delta) n) := by
    unfold positiveDirichletGradient
    exact (hterm (n + 2) (by omega)).sub (hterm (n + 1) (by omega))
  have hgradientNeg (n : ℕ) : Differentiable ℝ
      (fun delta : ℝ ↦ positiveDirichletGradient
        (canonicalCentralRealSpectralParameter (-delta)) n) := by
    unfold positiveDirichletGradient
    exact (htermNeg (n + 2) (by omega)).sub
      (htermNeg (n + 1) (by omega))
  have hsum : Differentiable ℝ
      (fun delta : ℝ ↦
        ∑ n ∈ Finset.range M,
          (starRingEnd ℂ)
              (positiveDirichletGradient
                (canonicalCentralRealSpectralParameter delta) n) *
            positiveDirichletGradient
              (canonicalCentralRealSpectralParameter (-delta)) n) := by
    exact Differentiable.fun_sum fun n _hn ↦
      (Complex.differentiable_conj.comp (hgradient n)).mul
        (hgradientNeg n)
  apply Differentiable.differentiableAt
  rw [show (fun delta : ℝ ↦
      finiteReflectedGradientPairing M
        (canonicalCentralRealSpectralParameter delta)) =
      fun delta : ℝ ↦
        ∑ n ∈ Finset.range M,
          (starRingEnd ℂ)
              (positiveDirichletGradient
                (canonicalCentralRealSpectralParameter delta) n) *
            positiveDirichletGradient
              (canonicalCentralRealSpectralParameter (-delta)) n by
    funext delta
    unfold finiteReflectedGradientPairing
    rw [reflectedParameter_canonicalCentralRealSpectralParameter]]
  exact hsum

/-- The first variation of the complete finite bulk is exactly twice its
centered radial Green energy. -/
theorem hasDerivAt_finiteCanonicalBracketCoupledGreenBulk_zero (M : ℕ) :
    HasDerivAt (finiteCanonicalBracketCoupledGreenBulk M)
      (2 * finiteRadialGreenEnergy 3 M (1 / 2 : ℂ)) 0 := by
  have hpairComplex :=
    differentiableAt_finiteReflectedGradientPairing_centralReal M
  have hpair : Filter.Tendsto
      (fun delta : ℝ ↦
        (finiteReflectedGradientPairing M
          (canonicalCentralRealSpectralParameter delta)).re)
      (nhdsWithin 0 {0}ᶜ)
      (nhds
        (finiteReflectedGradientPairing M
          (canonicalCentralRealSpectralParameter 0)).re) := by
    have hcomplex : Filter.Tendsto
        (fun delta : ℝ ↦
          finiteReflectedGradientPairing M
            (canonicalCentralRealSpectralParameter delta))
        (nhdsWithin 0 {0}ᶜ)
        (nhds
          (finiteReflectedGradientPairing M
            (canonicalCentralRealSpectralParameter 0))) :=
      hpairComplex.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  have hradial :=
    hasDerivAt_cpRadialDifference_three_zero.tendsto_slope_zero
  have hproduct := hradial.mul hpair
  have hcenterEnergy :
      finiteRadialGreenEnergy 3 M (1 / 2 : ℂ) =
        Real.log 3 *
          (finiteReflectedGradientPairing M
            (canonicalCentralRealSpectralParameter 0)).re := by
    unfold finiteRadialGreenEnergy cpRadialCofactor
      canonicalCentralRealSpectralParameter criticalDisplacement
    norm_num
  rw [hasDerivAt_iff_tendsto_slope_zero]
  rw [hcenterEnergy]
  convert hproduct using 1
  · funext delta
    simp only [zero_add, finiteCanonicalBracketCoupledGreenBulk_zero,
      sub_zero, smul_eq_mul]
    rw [finiteCanonicalBracketCoupledGreenBulk_eq_radialDifference]
    simp [cpRadialDifference]
    ring
  · ring

/-- Every nonempty finite Green bulk has strictly positive centered first
variation. -/
theorem deriv_finiteCanonicalBracketCoupledGreenBulk_zero_pos
    {M : ℕ} (hM : 0 < M) :
    0 < deriv (finiteCanonicalBracketCoupledGreenBulk M) 0 := by
  rw [(hasDerivAt_finiteCanonicalBracketCoupledGreenBulk_zero M).deriv]
  exact mul_pos (by norm_num)
    (finiteRadialGreenEnergy_pos 3 M (by norm_num) hM
      (by
        constructor <;>
          norm_num [genuineCriticalStrip]))

/-! ## Global positive bulk sensitivity -/

/-- Infinite C3 Green-bulk sensitivity at the centered displacement. -/
def canonicalCentralInfiniteGreenBulkFirstVariation : ℝ :=
  2 * Real.log 3 * infiniteReflectedGreenEnergy (1 / 2 : ℂ)

/-- The limit just constructed is exactly the existing canonical infinite C3
radial energy at the centered spectral parameter. -/
theorem canonicalCentralInfiniteGreenBulkFirstVariation_eq_radialEnergy :
    canonicalCentralInfiniteGreenBulkFirstVariation =
      canonicalCompletedC3InfiniteRadialGreenEnergy (1 / 2 : ℂ) := by
  unfold canonicalCentralInfiniteGreenBulkFirstVariation
    canonicalCompletedC3InfiniteRadialGreenEnergy cpRadialCofactor
    criticalDisplacement
  norm_num

/-- The global bulk sensitivity is strictly positive. -/
theorem canonicalCentralInfiniteGreenBulkFirstVariation_pos :
    0 < canonicalCentralInfiniteGreenBulkFirstVariation := by
  have hstrip : (1 / 2 : ℂ) ∈ genuineCriticalStrip := by
    constructor <;> norm_num [genuineCriticalStrip]
  unfold canonicalCentralInfiniteGreenBulkFirstVariation
  exact mul_pos
    (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
    (infiniteReflectedGreenEnergy_pos hstrip)

/-- The strictly positive finite bulk variations converge to the strictly
positive global Green-bulk variation. -/
theorem deriv_finiteCanonicalBracketCoupledGreenBulk_zero_tendsto_infinite :
    Filter.Tendsto
      (fun M : ℕ ↦ deriv (finiteCanonicalBracketCoupledGreenBulk M) 0)
      Filter.atTop
      (nhds canonicalCentralInfiniteGreenBulkFirstVariation) := by
  have hstrip : (1 / 2 : ℂ) ∈ genuineCriticalStrip := by
    constructor <;> norm_num [genuineCriticalStrip]
  have henergy :=
    (finiteReflectedGradientPairing_re_tendsto_infiniteEnergy hstrip).const_mul
      (2 * Real.log 3)
  unfold canonicalCentralInfiniteGreenBulkFirstVariation
  refine henergy.congr' (Filter.Eventually.of_forall fun M ↦ ?_)
  change 2 * Real.log 3 *
      (finiteReflectedGradientPairing M (1 / 2 : ℂ)).re =
    deriv (finiteCanonicalBracketCoupledGreenBulk M) 0
  rw [(hasDerivAt_finiteCanonicalBracketCoupledGreenBulk_zero M).deriv]
  unfold finiteRadialGreenEnergy cpRadialCofactor criticalDisplacement
  norm_num
  ring

/-- Existing-name spelling of the same cutoff passage. -/
theorem deriv_finiteCanonicalBracketCoupledGreenBulk_zero_tendsto_radialEnergy :
    Filter.Tendsto
      (fun M : ℕ ↦ deriv (finiteCanonicalBracketCoupledGreenBulk M) 0)
      Filter.atTop
      (nhds (canonicalCompletedC3InfiniteRadialGreenEnergy (1 / 2 : ℂ))) := by
  rw [← canonicalCentralInfiniteGreenBulkFirstVariation_eq_radialEnergy]
  exact deriv_finiteCanonicalBracketCoupledGreenBulk_zero_tendsto_infinite

end

end CarrySelfAdjointOperator
