import CarrySelfAdjointOperator.CompletedC3SymplecticGammaNormalizedKernelJets
import CarrySelfAdjointOperator.CompletedC3SymplecticCrossingNormalAudit
import Mathlib.Tactic

open scoped ComplexConjugate ComplexOrder InnerProductSpace RealInnerProductSpace Topology

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section

@[simp] theorem
    completedGreenKernelTwoStepShiftedForwardDifference_zero_zero
    (kernel : ℂ → ℂ → ℂ) (h g : ℂ) :
    completedGreenKernelTwoStepShiftedForwardDifference
        kernel h g 0 0 = kernel h g := by
  simp [completedGreenKernelTwoStepShiftedForwardDifference,
    completedGreenKernelTwoStepShiftedRawDifference,
    completedGreenForwardDifference]

def CanonicalCompletedC3SymplecticNormalizedLedgerZerothFlatness : Prop :=
  Tendsto
    (fun steps : ℕ × ℕ =>
      completedGreenKernelTwoStepShiftedForwardDifference
        canonicalCompletedC3TotalNormalizedExplicitLedgerKernel
        (canonicalCompletedC3RadialSecondStep steps.1)
        (canonicalCompletedC3RadialSecondStep steps.2) 0 0)
    Filter.atTop
    (nhds 0)

theorem
    canonicalCompletedC3SymplecticNormalizedLedgerZerothFlatness_iff_gammaKernel_tendsto :
    CanonicalCompletedC3SymplecticNormalizedLedgerZerothFlatness ↔
      Tendsto
        (fun steps : ℕ × ℕ =>
          canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
            (canonicalCompletedC3RadialSecondStep steps.1)
            (canonicalCompletedC3RadialSecondStep steps.2))
        Filter.atTop
        (nhds
          (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) := by
  unfold CanonicalCompletedC3SymplecticNormalizedLedgerZerothFlatness
  have hcoeff :
      polarizedGreenMomentCoefficient
          canonicalCompletedNativeLogDerivativeMoment 0 0 =
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
    simpa using
      (polarizedGreenMomentCoefficient_even_even
        canonicalCompletedNativeLogDerivativeMoment 0 0)
  constructor
  · intro hflat
    have hledger :
        Tendsto
          (fun steps : ℕ × ℕ =>
            canonicalCompletedC3TotalNormalizedExplicitLedgerKernel
              (canonicalCompletedC3RadialSecondStep steps.1)
              (canonicalCompletedC3RadialSecondStep steps.2))
          Filter.atTop
          (nhds 0) := by
      simpa only [completedGreenKernelTwoStepShiftedForwardDifference_zero_zero]
        using hflat
    have hsum :=
      hledger.add (completedNativePolarizedDslope_shiftedRadial_tendsto 0 0)
    simp only [completedGreenKernelTwoStepShiftedForwardDifference_zero_zero]
      at hsum
    have hgamma :
        Tendsto
          (fun steps : ℕ × ℕ =>
            canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
              (canonicalCompletedC3RadialSecondStep steps.1)
              (canonicalCompletedC3RadialSecondStep steps.2))
          Filter.atTop
          (nhds (0 +
            polarizedGreenMomentCoefficient
              canonicalCompletedNativeLogDerivativeMoment 0 0)) := by
      apply hsum.congr'
      filter_upwards [
        canonicalCompletedC3SymplecticRadialNormalizedLedgerJet_eventually_eq
          0 0
      ] with steps hsteps
      have hsteps' :
          canonicalCompletedC3TotalNormalizedExplicitLedgerKernel
              (canonicalCompletedC3RadialSecondStep steps.1)
              (canonicalCompletedC3RadialSecondStep steps.2) =
            canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
              (canonicalCompletedC3RadialSecondStep steps.1)
              (canonicalCompletedC3RadialSecondStep steps.2) -
            canonicalCompletedNativePolarizedDslopeKernel
              (canonicalCompletedC3RadialSecondStep steps.1)
              (canonicalCompletedC3RadialSecondStep steps.2) := by
        simpa only [completedGreenKernelTwoStepShiftedForwardDifference_zero_zero]
          using hsteps
      rw [hsteps']
      ring
    simpa only [hcoeff, zero_add] using hgamma
  · intro hgamma
    have hsub :=
      hgamma.sub (completedNativePolarizedDslope_shiftedRadial_tendsto 0 0)
    simp only [completedGreenKernelTwoStepShiftedForwardDifference_zero_zero]
      at hsub
    have hledger :
        Tendsto
          (fun steps : ℕ × ℕ =>
            canonicalCompletedC3TotalNormalizedExplicitLedgerKernel
              (canonicalCompletedC3RadialSecondStep steps.1)
              (canonicalCompletedC3RadialSecondStep steps.2))
          Filter.atTop
          (nhds (
            (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) -
              polarizedGreenMomentCoefficient
                canonicalCompletedNativeLogDerivativeMoment 0 0)) := by
      apply hsub.congr'
      filter_upwards [
        canonicalCompletedC3SymplecticRadialNormalizedLedgerJet_eventually_eq
          0 0
      ] with steps hsteps
      have hsteps' :
          canonicalCompletedC3TotalNormalizedExplicitLedgerKernel
              (canonicalCompletedC3RadialSecondStep steps.1)
              (canonicalCompletedC3RadialSecondStep steps.2) =
            canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
              (canonicalCompletedC3RadialSecondStep steps.1)
              (canonicalCompletedC3RadialSecondStep steps.2) -
            canonicalCompletedNativePolarizedDslopeKernel
              (canonicalCompletedC3RadialSecondStep steps.1)
              (canonicalCompletedC3RadialSecondStep steps.2) := by
        simpa only [completedGreenKernelTwoStepShiftedForwardDifference_zero_zero]
          using hsteps
      exact hsteps'.symm
    simpa only [completedGreenKernelTwoStepShiftedForwardDifference_zero_zero,
      hcoeff, sub_self] using hledger

theorem
    canonicalCompletedC3NormalizedSymplecticGammaKernel_diagonal_tendsto_h0_of_zeroth
    (hgamma :
      Tendsto
        (fun steps : ℕ × ℕ =>
          canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
            (canonicalCompletedC3RadialSecondStep steps.1)
            (canonicalCompletedC3RadialSecondStep steps.2))
        Filter.atTop
        (nhds
          (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ))) :
    Tendsto
      (fun k : ℕ =>
        canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
          (canonicalCompletedC3RadialSecondStep k)
          (canonicalCompletedC3RadialSecondStep k))
      Filter.atTop
      (nhds
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) := by
  have hdiag : Tendsto (fun k : ℕ => (k, k)) Filter.atTop Filter.atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_id.prodMk tendsto_id
  simpa only [Function.comp_def] using hgamma.comp hdiag

theorem
    canonicalCompletedC3NormalizedSymplecticGammaState_radial_norm_sq_tendsto_h0_of_zeroth
    (hflat :
      CanonicalCompletedC3SymplecticNormalizedLedgerZerothFlatness) :
    Tendsto
      (fun k : ℕ =>
        (((‖canonicalCompletedC3NormalizedSymplecticGammaState
          (canonicalCompletedC3RadialSecondStep k)
          (by
            simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
              using canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)‖ : ℝ) : ℂ) ^ 2))
      Filter.atTop
      (nhds
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) := by
  have hgamma :=
    (canonicalCompletedC3SymplecticNormalizedLedgerZerothFlatness_iff_gammaKernel_tendsto).1
      hflat
  have hdiag :=
    canonicalCompletedC3NormalizedSymplecticGammaKernel_diagonal_tendsto_h0_of_zeroth
      hgamma
  apply hdiag.congr'
  filter_upwards with k
  have hk :
      (canonicalCompletedC3RadialSecondStep k).im ≠ 0 := by
    simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
      using canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0
  rw [canonicalCompletedC3TotalNormalizedSymplecticGammaKernel_of_offAxis
      _ _ hk hk,
    canonicalCompletedC3NormalizedSymplecticGammaKernel_eq_inner _ _ hk hk]
  simp [inner_self_eq_norm_sq_to_K]

/-
Objective 6 audit result over the imported modules:

OUTCOME C:
zeroth-order Gamma radial limit remains an independent spectral gate.

No imported theorem was found proving the diagonal normalized Gamma limit, a
radial limit for `canonicalCompletedC3NormalizedSymplecticGammaState`, or an
incompatible negation/divergence statement.  In particular, no continuity
argument for the source is used here.
-/

end

end CarrySelfAdjointOperator
