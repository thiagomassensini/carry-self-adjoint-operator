import CarrySelfAdjointOperator.CompletedC3CentralLedgerChannelDerivative
import CarrySelfAdjointOperator.CompletedNativeCentralCarryAtlasEnergy
import Mathlib.Tactic

/-!
# Chart-free audit of the completed C3 central sewing gate

The central channel audit leaves one equality involving the raw C3 response,
the `xi - chart` replacement, and the retained residual square.  At first
order the raw response is `chart + native`, so the chart cancels exactly.

This file records that cancellation before inspecting whether the two sides
of the resulting chart-free balance already share a geometric realization.
No theta representation, zero hypothesis, confinement input, new carrier,
return operator, higher-order statement, or `h₁` gate is used.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-! ## Exact chart cancellation -/

/-- First-order instance of the existing raw factor-response decomposition. -/
theorem canonicalCompletedC3RawHeightResponseTaylorCoefficient_one_eq_chart_add_native :
    canonicalCompletedC3RawHeightResponseTaylorCoefficient 1 =
      canonicalC3ChartFactorResponseTaylorCoefficient 1 +
        nativeHeightScalarResponseTaylorCoefficient 1 := by
  exact canonicalCompletedC3RawHeightResponseTaylorCoefficient_eq_factors 1

/-- First response coefficient of any nonvanishing analytic factor, written
as its normalized logarithmic curvature. -/
theorem completedGreenFactorResponseTaylorCoefficient_one_eq_logCurvature
    (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0) (hF0 : F 0 ≠ 0) :
    iteratedDeriv 1
          (completedGreenNormalizedResponse F (fun z => -deriv F z)) 0 /
        (1 : ℕ).factorial =
      -(1 / 2 : ℂ) *
        ((iteratedDeriv 2 F 0 * F 0 - deriv F 0 ^ 2) / F 0 ^ 2) := by
  unfold completedGreenNormalizedResponse
  simp only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, div_one]
  have hderivF : HasDerivAt (deriv F) (iteratedDeriv 2 F 0) 0 := by
    simpa [iteratedDeriv_succ] using
      hF.deriv.differentiableAt.hasDerivAt
  have hnum : HasDerivAt (fun z => -deriv F z)
      (-iteratedDeriv 2 F 0) 0 := hderivF.neg
  have hden : HasDerivAt (fun z => (2 : ℂ) * F z)
      (2 * deriv F 0) 0 :=
    hF.differentiableAt.hasDerivAt.const_mul 2
  have hquot := hnum.div hden (mul_ne_zero (by norm_num) hF0)
  change deriv ((fun z => -deriv F z) / (fun z => (2 : ℂ) * F z)) 0 = _
  rw [hquot.deriv]
  field_simp [hF0]
  ring

/-- Native first response coefficient as the exact native logarithmic
curvature. -/
theorem nativeHeightScalarResponseTaylorCoefficient_one_eq_logCurvature :
    nativeHeightScalarResponseTaylorCoefficient 1 =
      -(1 / 2 : ℂ) *
        ((iteratedDeriv 2 nativeHeightScalar 0 * nativeHeightScalar 0 -
            deriv nativeHeightScalar 0 ^ 2) /
          nativeHeightScalar 0 ^ 2) := by
  exact completedGreenFactorResponseTaylorCoefficient_one_eq_logCurvature
    nativeHeightScalar nativeHeightScalar_analyticAt_zero
      nativeHeightScalar_zero_ne_zero

/-- Xi-completion first response coefficient as the exact completion
logarithmic curvature. -/
theorem nativeXiCompletionResponseTaylorCoefficient_one_eq_logCurvature :
    nativeXiCompletionResponseTaylorCoefficient 1 =
      -(1 / 2 : ℂ) *
        ((iteratedDeriv 2 nativeXiCompletionFactor 0 *
              nativeXiCompletionFactor 0 -
            deriv nativeXiCompletionFactor 0 ^ 2) /
          nativeXiCompletionFactor 0 ^ 2) := by
  exact completedGreenFactorResponseTaylorCoefficient_one_eq_logCurvature
    nativeXiCompletionFactor nativeXiCompletionFactor_analyticAt_zero
      (nativeXiCompletionFactor_ne_zero zero_mem_completedNativeHeightDomain)

/-- The central ledger sewing is equivalent to the chart-free balance between
the raw TFVD defect and the xi-completion channel after the retained residual
square.  This uses only the two exact factor-response decompositions. -/
theorem
    deriv_fixedCenterChannelSeparatedLedger_eq_dressedGram_re_iff_chartFreeBalance
    (M : ℕ) :
    (deriv
        (canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M) 0).re =
        (canonicalCompletedC3RealAxisPositiveKernel 0 0).re ↔
      (inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re -
          (nativeHeightScalarResponseTaylorCoefficient 1).re =
        (nativeXiCompletionResponseTaylorCoefficient 1).re -
          ‖canonicalCompletedC3RealAxisResidualState 0‖ ^ 2 := by
  rw [
    deriv_fixedCenterChannelSeparatedLedger_eq_dressedGram_re_iff_rawMismatch_eq_completionCurvature_sub_residual,
    canonicalCompletedC3RawHeightResponseTaylorCoefficient_one_eq_chart_add_native]
  simp only [Complex.add_re, Complex.sub_re]
  constructor <;> intro h <;> linarith

/-- The chart-free balance is exactly the original dressed central moment
identity.  In particular, chart cancellation neither strengthens nor weakens
the gate and introduces no new assumption. -/
theorem canonicalCompletedC3CentralChartFreeBalance_iff_dressedMoment :
    ((inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re -
          (nativeHeightScalarResponseTaylorCoefficient 1).re =
        (nativeXiCompletionResponseTaylorCoefficient 1).re -
          ‖canonicalCompletedC3RealAxisResidualState 0‖ ^ 2) ↔
      (inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re +
          ‖canonicalCompletedC3RealAxisResidualState 0‖ ^ 2 =
        canonicalCompletedNativeLogDerivativeMoment 0 := by
  have hfactor := congrArg Complex.re
    canonicalCompletedNativeLogDerivativeMoment_zero_eq_factorResponseCoefficients
  simp only [Complex.ofReal_re, Complex.add_re] at hfactor
  constructor <;> intro h <;> linarith

/-- Fully reduced form of the central sewing equivalence. -/
theorem
    deriv_fixedCenterChannelSeparatedLedger_eq_dressedGram_re_iff_dressedMoment
    (M : ℕ) :
    (deriv
        (canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M) 0).re =
        (canonicalCompletedC3RealAxisPositiveKernel 0 0).re ↔
      (inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re +
          ‖canonicalCompletedC3RealAxisResidualState 0‖ ^ 2 =
        canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [
    deriv_fixedCenterChannelSeparatedLedger_eq_dressedGram_re_iff_chartFreeBalance,
    canonicalCompletedC3CentralChartFreeBalance_iff_dressedMoment]

/-! ## Existing geometric realizations of the four terms -/

/-- The raw central TFVD Gram contains exactly the ordinary reflected Green
energy and the centered logarithmic-gradient energy. -/
theorem
    inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet_zero_zero_re_eq_reflectedGreen_add_logJet :
    (inner ℂ
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re =
      infiniteReflectedGreenEnergy (1 / 2 : ℂ) +
        ‖canonicalCompletedC3LogJetState
            (1 / 2 : ℂ) (by norm_num)‖ ^ 2 := by
  rw [inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet_zero_zero]
  simp only [Complex.add_re]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  norm_cast
  change
    ‖canonicalCentralCompletedDirichletGradientState‖ ^ 2 +
        ‖canonicalCompletedC3LogJetState
          (1 / 2 : ℂ) (by norm_num)‖ ^ 2 = _
  rw [← infiniteReflectedGreenEnergy_half_eq_gradient_norm_sq]

/-- After all already-proved geometric identifications are used, the
chart-free balance is precisely an equality between the ordinary Green
energy plus log-jet energy minus the native curvature and the xi curvature
minus the square of that same ordinary Green energy. -/
theorem canonicalCompletedC3CentralChartFreeBalance_iff_greenLogXiNative :
    ((inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re -
          (nativeHeightScalarResponseTaylorCoefficient 1).re =
        (nativeXiCompletionResponseTaylorCoefficient 1).re -
          ‖canonicalCompletedC3RealAxisResidualState 0‖ ^ 2) ↔
      infiniteReflectedGreenEnergy (1 / 2 : ℂ) +
            ‖canonicalCompletedC3LogJetState
                (1 / 2 : ℂ) (by norm_num)‖ ^ 2 -
          (nativeHeightScalarResponseTaylorCoefficient 1).re =
        (nativeXiCompletionResponseTaylorCoefficient 1).re -
          infiniteReflectedGreenEnergy (1 / 2 : ℂ) ^ 2 := by
  rw [
    inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet_zero_zero_re_eq_reflectedGreen_add_logJet,
    canonicalCompletedC3RealAxisResidualState_zero_norm_sq_eq_energy_sq]

/-- Both sides of the chart-free gate with the two scalar response
coefficients unfolded into their factor curvatures.  This is the requested
native/TFVD versus xi/residual comparison with no chart term left. -/
theorem
    canonicalCompletedC3CentralChartFreeBalance_iff_explicitFactorCurvatures :
    ((inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re -
          (nativeHeightScalarResponseTaylorCoefficient 1).re =
        (nativeXiCompletionResponseTaylorCoefficient 1).re -
          ‖canonicalCompletedC3RealAxisResidualState 0‖ ^ 2) ↔
      infiniteReflectedGreenEnergy (1 / 2 : ℂ) +
            ‖canonicalCompletedC3LogJetState
                (1 / 2 : ℂ) (by norm_num)‖ ^ 2 -
          (-(1 / 2 : ℂ) *
            ((iteratedDeriv 2 nativeHeightScalar 0 * nativeHeightScalar 0 -
                deriv nativeHeightScalar 0 ^ 2) /
              nativeHeightScalar 0 ^ 2)).re =
        (-(1 / 2 : ℂ) *
          ((iteratedDeriv 2 nativeXiCompletionFactor 0 *
                nativeXiCompletionFactor 0 -
              deriv nativeXiCompletionFactor 0 ^ 2) /
            nativeXiCompletionFactor 0 ^ 2)).re -
          infiniteReflectedGreenEnergy (1 / 2 : ℂ) ^ 2 := by
  rw [canonicalCompletedC3CentralChartFreeBalance_iff_greenLogXiNative,
    nativeHeightScalarResponseTaylorCoefficient_one_eq_logCurvature,
    nativeXiCompletionResponseTaylorCoefficient_one_eq_logCurvature]

/-- Equivalent dressed-moment form after expanding every carrier coordinate
already realized in the repository.  This is the first scalar identity not
supplied by an existing sewing theorem. -/
theorem canonicalCompletedC3CentralDressedMoment_iff_greenLogEnergyIdentity :
    ((inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re +
          ‖canonicalCompletedC3RealAxisResidualState 0‖ ^ 2 =
        canonicalCompletedNativeLogDerivativeMoment 0) ↔
      infiniteReflectedGreenEnergy (1 / 2 : ℂ) +
          ‖canonicalCompletedC3LogJetState
              (1 / 2 : ℂ) (by norm_num)‖ ^ 2 +
          infiniteReflectedGreenEnergy (1 / 2 : ℂ) ^ 2 =
        canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [
    inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet_zero_zero_re_eq_reflectedGreen_add_logJet,
    canonicalCompletedC3RealAxisResidualState_zero_norm_sq_eq_energy_sq]

/-- Final center-only reduction with the analytic side opened into the exact
xi/native product curvatures.  No hypothesis is introduced: the central
sewing holds exactly when this displayed scalar equality holds. -/
theorem
    deriv_fixedCenterChannelSeparatedLedger_eq_dressedGram_re_iff_explicitGreenLogProductCurvature
    (M : ℕ) :
    (deriv
        (canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator M) 0).re =
        (canonicalCompletedC3RealAxisPositiveKernel 0 0).re ↔
      infiniteReflectedGreenEnergy (1 / 2 : ℂ) +
          ‖canonicalCompletedC3LogJetState
              (1 / 2 : ℂ) (by norm_num)‖ ^ 2 +
          infiniteReflectedGreenEnergy (1 / 2 : ℂ) ^ 2 =
        (-(1 / 2 : ℂ) *
          ((iteratedDeriv 2 nativeXiCompletionFactor 0 *
                    nativeXiCompletionFactor 0 -
                  deriv nativeXiCompletionFactor 0 ^ 2) /
                nativeXiCompletionFactor 0 ^ 2 +
            (iteratedDeriv 2 nativeHeightScalar 0 * nativeHeightScalar 0 -
                  deriv nativeHeightScalar 0 ^ 2) /
                nativeHeightScalar 0 ^ 2)).re := by
  rw [
    deriv_fixedCenterChannelSeparatedLedger_eq_dressedGram_re_iff_dressedMoment,
    canonicalCompletedC3CentralDressedMoment_iff_greenLogEnergyIdentity]
  have hcurvature := congrArg Complex.re
    canonicalCompletedNativeLogDerivativeMoment_zero_eq_factorLogCurvatures
  simp only [Complex.ofReal_re] at hcurvature
  rw [hcurvature]

end

end CarrySelfAdjointOperator
