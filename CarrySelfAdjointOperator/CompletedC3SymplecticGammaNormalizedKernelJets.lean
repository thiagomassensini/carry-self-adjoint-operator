import CarrySelfAdjointOperator.CompletedC3SymplecticGammaNormalizedKernelLedger
import CarrySelfAdjointOperator.CompletedNativeRadialTiltSamplePositivity
import Mathlib.Tactic

open scoped ComplexConjugate ComplexOrder InnerProductSpace RealInnerProductSpace Topology

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section

def canonicalCompletedC3TotalNormalizedSymplecticGammaState
    (z : ℂ) : CarryGammaComplexNaimark :=
  if hz : z.im ≠ 0 then
    canonicalCompletedC3NormalizedSymplecticGammaState z hz
  else
    0

def canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
    (z w : ℂ) : ℂ :=
  inner ℂ
    (canonicalCompletedC3TotalNormalizedSymplecticGammaState z)
    (canonicalCompletedC3TotalNormalizedSymplecticGammaState w)

theorem canonicalCompletedC3TotalNormalizedSymplecticGammaKernel_of_offAxis
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3TotalNormalizedSymplecticGammaKernel z w =
      canonicalCompletedC3NormalizedSymplecticGammaKernel z w hz hw := by
  simp [canonicalCompletedC3TotalNormalizedSymplecticGammaKernel,
    canonicalCompletedC3TotalNormalizedSymplecticGammaState, hz, hw,
    canonicalCompletedC3NormalizedSymplecticGammaKernel_eq_inner]

def canonicalCompletedC3TotalNormalizedExplicitLedgerKernel
    (z w : ℂ) : ℂ :=
  if hz : z.im ≠ 0 then
    if hw : w.im ≠ 0 then
      canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS
        z w hz hw /
        (
          (w - conj z) *
            mixedHermitianWeight nativeXiCompletionFactor w z *
            canonicalCompletedC3RawHeightCharacteristicWeight z w
        )
    else
      0
  else
    0

theorem canonicalCompletedC3TotalNormalizedExplicitLedgerKernel_of_offAxis
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3TotalNormalizedExplicitLedgerKernel z w =
      canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS
        z w hz hw /
        (
          (w - conj z) *
            mixedHermitianWeight nativeXiCompletionFactor w z *
            canonicalCompletedC3RawHeightCharacteristicWeight z w
        ) := by
  simp [canonicalCompletedC3TotalNormalizedExplicitLedgerKernel, hz, hw]

theorem
    canonicalCompletedC3TotalNormalizedExplicitLedgerKernel_eq_kernelGap_stencil_eventually
    (p q : ℕ) :
    ∀ᶠ steps : ℕ × ℕ in Filter.atTop,
      ∀ i ∈ Finset.range (p + 1),
        ∀ j ∈ Finset.range (q + 1),
          canonicalCompletedC3TotalNormalizedExplicitLedgerKernel
              (canonicalCompletedC3RadialTiltPoint steps.1 i)
              (canonicalCompletedC3RadialTiltPoint steps.2 j) =
            canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
              (canonicalCompletedC3RadialTiltPoint steps.1 i)
              (canonicalCompletedC3RadialTiltPoint steps.2 j) -
            canonicalCompletedNativePolarizedDslopeKernel
              (canonicalCompletedC3RadialTiltPoint steps.1 i)
              (canonicalCompletedC3RadialTiltPoint steps.2 j) := by
  filter_upwards [
    canonicalCompletedC3SymplecticRadialNormalizedKernelLedger_stencil_eventually
      p q
  ] with steps hsteps
  intro i hi j hj
  rw [canonicalCompletedC3TotalNormalizedExplicitLedgerKernel_of_offAxis,
    canonicalCompletedC3TotalNormalizedSymplecticGammaKernel_of_offAxis]
  exact hsteps i hi j hj

theorem completedGreenKernelTwoStepShiftedForwardDifference_sub
    (kernel kernel' : ℂ → ℂ → ℂ)
    (h g : ℂ) (p q : ℕ) :
    completedGreenKernelTwoStepShiftedForwardDifference
        (fun z w => kernel z w - kernel' z w) h g p q =
      completedGreenKernelTwoStepShiftedForwardDifference kernel h g p q -
        completedGreenKernelTwoStepShiftedForwardDifference kernel' h g p q := by
  have hiter_sub :
      ∀ (f f' : ℂ → ℂ) (h : ℂ) (n : ℕ),
        (completedGreenForwardDifference h)^[n]
            (fun z => f z - f' z) =
          fun z =>
            (completedGreenForwardDifference h)^[n] f z -
              (completedGreenForwardDifference h)^[n] f' z := by
    intro f f' h n
    induction n with
    | zero =>
        rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', ih]
        funext z
        simp [completedGreenForwardDifference]
        abel
  have hinner :
      (fun w =>
        (completedGreenForwardDifference g)^[q]
          (fun z => kernel w z - kernel' w z) g) =
        (fun w =>
          (completedGreenForwardDifference g)^[q] (kernel w) g -
            (completedGreenForwardDifference g)^[q] (kernel' w) g) := by
    funext w
    exact congrFun (hiter_sub (kernel w) (kernel' w) g q) g
  have houter :
      (completedGreenForwardDifference h)^[p]
          (fun w =>
            (completedGreenForwardDifference g)^[q] (kernel w) g -
              (completedGreenForwardDifference g)^[q] (kernel' w) g) =
        (completedGreenForwardDifference h)^[p]
            (fun w =>
              (completedGreenForwardDifference g)^[q] (kernel w) g) -
          (completedGreenForwardDifference h)^[p]
            (fun w =>
              (completedGreenForwardDifference g)^[q] (kernel' w) g) := by
    exact hiter_sub
      (fun w => (completedGreenForwardDifference g)^[q] (kernel w) g)
      (fun w => (completedGreenForwardDifference g)^[q] (kernel' w) g)
      h p
  unfold completedGreenKernelTwoStepShiftedForwardDifference
    completedGreenKernelTwoStepShiftedRawDifference
  rw [hinner, houter]
  simp only [Pi.sub_apply]
  ring

theorem
    canonicalCompletedC3SymplecticRadialNormalizedLedgerJet_eventually_eq
    (p q : ℕ) :
    ∀ᶠ steps : ℕ × ℕ in Filter.atTop,
      completedGreenKernelTwoStepShiftedForwardDifference
          canonicalCompletedC3TotalNormalizedExplicitLedgerKernel
          (canonicalCompletedC3RadialSecondStep steps.1)
          (canonicalCompletedC3RadialSecondStep steps.2) p q =
        completedGreenKernelTwoStepShiftedForwardDifference
          canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
          (canonicalCompletedC3RadialSecondStep steps.1)
          (canonicalCompletedC3RadialSecondStep steps.2) p q -
        completedGreenKernelTwoStepShiftedForwardDifference
          canonicalCompletedNativePolarizedDslopeKernel
          (canonicalCompletedC3RadialSecondStep steps.1)
          (canonicalCompletedC3RadialSecondStep steps.2) p q := by
  filter_upwards [
    canonicalCompletedC3TotalNormalizedExplicitLedgerKernel_eq_kernelGap_stencil_eventually
      p q
  ] with steps hstencil
  calc
    completedGreenKernelTwoStepShiftedForwardDifference
          canonicalCompletedC3TotalNormalizedExplicitLedgerKernel
          (canonicalCompletedC3RadialSecondStep steps.1)
          (canonicalCompletedC3RadialSecondStep steps.2) p q =
        completedGreenKernelTwoStepShiftedForwardDifference
          (fun z w =>
            canonicalCompletedC3TotalNormalizedSymplecticGammaKernel z w -
              canonicalCompletedNativePolarizedDslopeKernel z w)
          (canonicalCompletedC3RadialSecondStep steps.1)
          (canonicalCompletedC3RadialSecondStep steps.2) p q := by
      apply completedGreenKernelTwoStepShiftedForwardDifference_eq_of_eq_on_grid
      intro i hi j hj
      rw [← canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul,
        ← canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul]
      exact hstencil i hi j hj
    _ =
        completedGreenKernelTwoStepShiftedForwardDifference
          canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
          (canonicalCompletedC3RadialSecondStep steps.1)
          (canonicalCompletedC3RadialSecondStep steps.2) p q -
        completedGreenKernelTwoStepShiftedForwardDifference
          canonicalCompletedNativePolarizedDslopeKernel
          (canonicalCompletedC3RadialSecondStep steps.1)
          (canonicalCompletedC3RadialSecondStep steps.2) p q := by
      exact completedGreenKernelTwoStepShiftedForwardDifference_sub
        canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
        canonicalCompletedNativePolarizedDslopeKernel
        (canonicalCompletedC3RadialSecondStep steps.1)
        (canonicalCompletedC3RadialSecondStep steps.2) p q

def CanonicalCompletedC3SymplecticNormalizedLedgerJetFlatness : Prop :=
  ∀ p q : ℕ,
    Tendsto
      (fun steps : ℕ × ℕ =>
        completedGreenKernelTwoStepShiftedForwardDifference
          canonicalCompletedC3TotalNormalizedExplicitLedgerKernel
          (canonicalCompletedC3RadialSecondStep steps.1)
          (canonicalCompletedC3RadialSecondStep steps.2) p q)
      Filter.atTop
      (nhds 0)

theorem
    canonicalCompletedC3SymplecticNormalizedLedgerJetFlatness_iff_gammaJets_tendsto :
    CanonicalCompletedC3SymplecticNormalizedLedgerJetFlatness ↔
      ∀ p q : ℕ,
        Tendsto
          (fun steps : ℕ × ℕ =>
            completedGreenKernelTwoStepShiftedForwardDifference
              canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
              (canonicalCompletedC3RadialSecondStep steps.1)
              (canonicalCompletedC3RadialSecondStep steps.2) p q)
          Filter.atTop
          (nhds
            (polarizedGreenMomentCoefficient
              canonicalCompletedNativeLogDerivativeMoment p q)) := by
  unfold CanonicalCompletedC3SymplecticNormalizedLedgerJetFlatness
  constructor
  · intro hflat p q
    have hsum :=
      (hflat p q).add (completedNativePolarizedDslope_shiftedRadial_tendsto p q)
    have hgamma :
        Tendsto
          (fun steps : ℕ × ℕ =>
            completedGreenKernelTwoStepShiftedForwardDifference
                canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
                (canonicalCompletedC3RadialSecondStep steps.1)
                (canonicalCompletedC3RadialSecondStep steps.2) p q)
          Filter.atTop
          (nhds (0 +
            polarizedGreenMomentCoefficient
              canonicalCompletedNativeLogDerivativeMoment p q)) := by
      apply hsum.congr'
      filter_upwards [
        canonicalCompletedC3SymplecticRadialNormalizedLedgerJet_eventually_eq
          p q
      ] with steps hsteps
      rw [hsteps]
      ring
    simpa only [zero_add] using hgamma
  · intro hgamma p q
    have hsub :=
      (hgamma p q).sub (completedNativePolarizedDslope_shiftedRadial_tendsto p q)
    have hledger :
        Tendsto
          (fun steps : ℕ × ℕ =>
            completedGreenKernelTwoStepShiftedForwardDifference
                canonicalCompletedC3TotalNormalizedExplicitLedgerKernel
                (canonicalCompletedC3RadialSecondStep steps.1)
                (canonicalCompletedC3RadialSecondStep steps.2) p q)
          Filter.atTop
          (nhds (
            polarizedGreenMomentCoefficient
              canonicalCompletedNativeLogDerivativeMoment p q -
            polarizedGreenMomentCoefficient
              canonicalCompletedNativeLogDerivativeMoment p q)) := by
      apply hsub.congr'
      filter_upwards [
        canonicalCompletedC3SymplecticRadialNormalizedLedgerJet_eventually_eq
          p q
      ] with steps hsteps
      exact hsteps.symm
    simpa only [sub_self] using hledger

end

end CarrySelfAdjointOperator
