import CarrySelfAdjointOperator.CompletedC3SymplecticGammaExplicitCompletedLedgerAPI
import CarrySelfAdjointOperator.CompletedC3ChiralCrossedChartBridge
import CarrySelfAdjointOperator.CompletedNativeRadialTiltSamplePositivity
import Mathlib.Tactic

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite
open Filter Topology

noncomputable section

theorem
canonicalCompletedC3WeightedCompletedWronskian_eq_separation_mul_dslope
    (z w : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    mixedHermitianWeight canonicalC3ChartFactorHeight w z *
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
          w z =
      mixedHermitianWeight canonicalC3ChartFactorHeight w z *
        canonicalCompletedC3GammaCharacteristicWeight z w *
        ((w - conj z) *
          canonicalCompletedNativePolarizedDslopeKernel z w) := by
  have hcross :=
    completedFNegFPrimeWronskian_crossedChartIdentity
      (z := w) (w := z) hwStrip hzStrip
  have hdslope :=
    canonicalCompletedC3Dslope_crossedChartIdentity
      1 hzStrip hwStrip hzF hwF hsep
  exact hcross.trans hdslope.symm

theorem
canonicalCompletedC3WeightedSymplecticGammaBoundary_sub_completedWronskian_eq_separation_mul_kernelDifference
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    mixedHermitianWeight nativeXiCompletionFactor w z *
          canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
        mixedHermitianWeight canonicalC3ChartFactorHeight w z *
          completedGreenWronskian
            completedNativeOperatorCharacteristic
            (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
            w z =
      (w - conj z) *
        (
          mixedHermitianWeight nativeXiCompletionFactor w z *
            canonicalCompletedC3SymplecticGammaKernel z w hz hw -
          mixedHermitianWeight canonicalC3ChartFactorHeight w z *
            canonicalCompletedC3GammaCharacteristicWeight z w *
            canonicalCompletedNativePolarizedDslopeKernel z w
        ) := by
  rw [
    canonicalCompletedC3SymplecticGammaBoundaryReadout_eq_kernel,
    canonicalCompletedC3WeightedCompletedWronskian_eq_separation_mul_dslope
      z w hzStrip hwStrip hzF hwF hsep
  ]
  ring

theorem
canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS_eq_separation_mul_kernelDifference
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS
        z w hz hw =
      (w - conj z) *
        (
          mixedHermitianWeight nativeXiCompletionFactor w z *
            canonicalCompletedC3SymplecticGammaKernel z w hz hw -
          mixedHermitianWeight canonicalC3ChartFactorHeight w z *
            canonicalCompletedC3GammaCharacteristicWeight z w *
            canonicalCompletedNativePolarizedDslopeKernel z w
        ) := by
  exact
    (canonicalCompletedC3WeightedSymplecticGammaBoundary_sub_completedWronskian_eq_explicitRHS
      z w hz hw hzStrip hwStrip).symm.trans
      (canonicalCompletedC3WeightedSymplecticGammaBoundary_sub_completedWronskian_eq_separation_mul_kernelDifference
        z w hz hw hzStrip hwStrip hzF hwF hsep)

theorem
canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS_div_separation_eq_kernelDifference
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS
        z w hz hw / (w - conj z) =
      mixedHermitianWeight nativeXiCompletionFactor w z *
          canonicalCompletedC3SymplecticGammaKernel z w hz hw -
        mixedHermitianWeight canonicalC3ChartFactorHeight w z *
          canonicalCompletedC3GammaCharacteristicWeight z w *
          canonicalCompletedNativePolarizedDslopeKernel z w := by
  rw [
    canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS_eq_separation_mul_kernelDifference
      z w hz hw hzStrip hwStrip hzF hwF hsep
  ]
  field_simp [sub_ne_zero.mpr hsep]

theorem
canonicalCompletedC3RadialTiltPair_eventually_admissible
    (i j : ℕ) :
    ∀ᶠ steps : ℕ × ℕ in Filter.atTop,
      operatorHeightParameter
          (canonicalCompletedC3RadialTiltPoint steps.1 i) ∈
        genuineCriticalStrip ∧
      completedNativeOperatorCharacteristic
          (canonicalCompletedC3RadialTiltPoint steps.1 i) ≠ 0 ∧
      operatorHeightParameter
          (canonicalCompletedC3RadialTiltPoint steps.2 j) ∈
        genuineCriticalStrip ∧
      completedNativeOperatorCharacteristic
          (canonicalCompletedC3RadialTiltPoint steps.2 j) ≠ 0 := by
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  filter_upwards [
    hfst.eventually
      (canonicalCompletedC3RadialTiltPoint_eventually_admissible i),
    hsnd.eventually
      (canonicalCompletedC3RadialTiltPoint_eventually_admissible j)
  ] with steps hi hj
  exact ⟨hi.1, hi.2, hj.1, hj.2⟩

theorem
canonicalCompletedC3SymplecticRadialExplicitLedgerRHS_div_separation_eventually
    (i j : ℕ) :
    ∀ᶠ steps : ℕ × ℕ in Filter.atTop,
      canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS
          (canonicalCompletedC3RadialTiltPoint steps.1 i)
          (canonicalCompletedC3RadialTiltPoint steps.2 j)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j) /
          (canonicalCompletedC3RadialTiltPoint steps.2 j -
            conj (canonicalCompletedC3RadialTiltPoint steps.1 i)) =
        mixedHermitianWeight nativeXiCompletionFactor
            (canonicalCompletedC3RadialTiltPoint steps.2 j)
            (canonicalCompletedC3RadialTiltPoint steps.1 i) *
          canonicalCompletedC3SymplecticGammaKernel
            (canonicalCompletedC3RadialTiltPoint steps.1 i)
            (canonicalCompletedC3RadialTiltPoint steps.2 j)
            (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
            (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j) -
        mixedHermitianWeight canonicalC3ChartFactorHeight
            (canonicalCompletedC3RadialTiltPoint steps.2 j)
            (canonicalCompletedC3RadialTiltPoint steps.1 i) *
          canonicalCompletedC3GammaCharacteristicWeight
            (canonicalCompletedC3RadialTiltPoint steps.1 i)
            (canonicalCompletedC3RadialTiltPoint steps.2 j) *
          canonicalCompletedNativePolarizedDslopeKernel
            (canonicalCompletedC3RadialTiltPoint steps.1 i)
            (canonicalCompletedC3RadialTiltPoint steps.2 j) := by
  filter_upwards [
    canonicalCompletedC3RadialTiltPair_eventually_admissible i j
  ] with steps hadmissible
  have hsep0 :
      canonicalCompletedC3RadialTiltPoint steps.2 j -
          conj (canonicalCompletedC3RadialTiltPoint steps.1 i) ≠ 0 :=
    canonicalCompletedC3RadialTilt_separation_ne_zero_twoStep
      steps.1 steps.2 i j
  have hsep :
      canonicalCompletedC3RadialTiltPoint steps.2 j ≠
        conj (canonicalCompletedC3RadialTiltPoint steps.1 i) :=
    sub_ne_zero.mp hsep0
  exact canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS_div_separation_eq_kernelDifference
    (z := canonicalCompletedC3RadialTiltPoint steps.1 i)
    (w := canonicalCompletedC3RadialTiltPoint steps.2 j)
    (hz := canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
    (hw := canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j)
    (hzStrip := hadmissible.1)
    (hwStrip := hadmissible.2.2.1)
    (hzF := hadmissible.2.1)
    (hwF := hadmissible.2.2.2)
    hsep

end

end CarrySelfAdjointOperator
