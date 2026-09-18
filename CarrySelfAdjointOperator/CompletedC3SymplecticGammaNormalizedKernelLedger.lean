import CarrySelfAdjointOperator.CompletedC3SymplecticGammaRadialKernelLedger
import CarrySelfAdjointOperator.CompletedC3NormalizedAllOrderSymplecticGamma
import CarrySelfAdjointOperator.NativeBoundaryArchimedeanDressingSeparation
import CarrySelfAdjointOperator.CompletedC3AllOrderChartResponseCorrection
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

open scoped ComplexConjugate ComplexOrder InnerProductSpace RealInnerProductSpace Topology

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section

theorem canonicalCompletedC3RawHeightValue_eq_chart_mul_nativeHeightScalar
    {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawHeightValue z =
      canonicalC3ChartFactorHeight z * nativeHeightScalar z := by
  rw [
    canonicalCompletedC3RawHeightValue_eq_chart_mul_normalized hzStrip,
    canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar
      hzStrip
  ]

theorem canonicalCompletedC3_chartGammaWeight_eq_xiRawHeightWeight
    (z w : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedHermitianWeight canonicalC3ChartFactorHeight w z *
        canonicalCompletedC3GammaCharacteristicWeight z w =
      mixedHermitianWeight nativeXiCompletionFactor w z *
        canonicalCompletedC3RawHeightCharacteristicWeight z w := by
  unfold mixedHermitianWeight
    canonicalCompletedC3GammaCharacteristicWeight
    canonicalCompletedC3RawHeightCharacteristicWeight
  rw [
    completedNativeOperatorCharacteristic_eq_nativeXiCompletionFactor_mul_nativeHeightScalar,
    completedNativeOperatorCharacteristic_eq_nativeXiCompletionFactor_mul_nativeHeightScalar,
    canonicalCompletedC3RawHeightValue_eq_chart_mul_nativeHeightScalar hzStrip,
    canonicalCompletedC3RawHeightValue_eq_chart_mul_nativeHeightScalar hwStrip
  ]
  simp only [map_mul]
  ring

theorem canonicalCompletedC3RawHeightValue_ne_zero
    {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0) :
    canonicalCompletedC3RawHeightValue z ≠ 0 := by
  have hxi : nativeXiCompletionFactor z ≠ 0 :=
    nativeXiCompletionFactor_ne_zero hzStrip
  have hnative : nativeHeightScalar z ≠ 0 := by
    intro hzero
    apply hzF
    rw [
      completedNativeOperatorCharacteristic_eq_nativeXiCompletionFactor_mul_nativeHeightScalar,
      hzero,
      mul_zero
    ]
  have hchart : canonicalC3ChartFactorHeight z ≠ 0 :=
    canonicalC3ChartFactorHeight_ne_zero hzStrip
  rw [canonicalCompletedC3RawHeightValue_eq_chart_mul_nativeHeightScalar hzStrip]
  exact mul_ne_zero hchart hnative

theorem canonicalCompletedC3RawHeightCharacteristicWeight_ne_zero
    {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0) :
    canonicalCompletedC3RawHeightCharacteristicWeight z w ≠ 0 := by
  have hzRaw :
      canonicalCompletedC3RawHeightValue z ≠ 0 :=
    canonicalCompletedC3RawHeightValue_ne_zero hzStrip hzF
  have hwRaw :
      canonicalCompletedC3RawHeightValue w ≠ 0 :=
    canonicalCompletedC3RawHeightValue_ne_zero hwStrip hwF
  have hzRawStar :
      conj (canonicalCompletedC3RawHeightValue z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hzRaw
  unfold canonicalCompletedC3RawHeightCharacteristicWeight
  exact mul_ne_zero (mul_ne_zero (by norm_num) hzRawStar) hwRaw

theorem canonicalCompletedC3XiMixedHermitianWeight_ne_zero
    {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedHermitianWeight nativeXiCompletionFactor w z ≠ 0 := by
  unfold mixedHermitianWeight
  exact mul_ne_zero
    (nativeXiCompletionFactor_ne_zero hwStrip)
    ((map_ne_zero (starRingEnd ℂ)).2
      (nativeXiCompletionFactor_ne_zero hzStrip))

def canonicalCompletedC3NormalizedSymplecticGammaState
    (z : ℂ) (hz : z.im ≠ 0) : CarryGammaComplexNaimark :=
  ((((Real.sqrt 2 : ℝ) : ℂ) *
      canonicalCompletedC3RawHeightValue z)⁻¹) •
    canonicalCompletedC3SymplecticGammaState z hz

def canonicalCompletedC3NormalizedSymplecticGammaKernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  canonicalCompletedC3SymplecticGammaKernel z w hz hw /
    canonicalCompletedC3RawHeightCharacteristicWeight z w

theorem canonicalCompletedC3NormalizedSymplecticGammaKernel_eq_inner
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3NormalizedSymplecticGammaKernel z w hz hw =
      inner ℂ
        (canonicalCompletedC3NormalizedSymplecticGammaState z hz)
        (canonicalCompletedC3NormalizedSymplecticGammaState w hw) := by
  unfold canonicalCompletedC3NormalizedSymplecticGammaKernel
    canonicalCompletedC3RawHeightCharacteristicWeight
    canonicalCompletedC3NormalizedSymplecticGammaState
    canonicalCompletedC3SymplecticGammaKernel
  have hsqrt_sq : (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hsqrt_inv_sq : (2 : ℂ)⁻¹ =
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
        ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [← hsqrt_sq, ← inv_pow, pow_two]
  rw [inner_smul_left, inner_smul_right]
  simp only [map_inv₀, map_mul, Complex.conj_ofReal]
  simp only [div_eq_mul_inv, mul_inv]
  rw [hsqrt_inv_sq]
  ring

theorem canonicalCompletedC3NormalizedSymplecticGammaKernel_posSemidef
    {ι : Type*} [Finite ι]
    (point : ι → ℂ)
    (hoffAxis : ∀ i, (point i).im ≠ 0) :
    (Matrix.of fun i j =>
      canonicalCompletedC3NormalizedSymplecticGammaKernel
        (point i) (point j) (hoffAxis i) (hoffAxis j)).PosSemidef := by
  rw [show (Matrix.of fun i j =>
      canonicalCompletedC3NormalizedSymplecticGammaKernel
        (point i) (point j) (hoffAxis i) (hoffAxis j)) =
      Matrix.gram ℂ (fun i =>
        canonicalCompletedC3NormalizedSymplecticGammaState
          (point i) (hoffAxis i)) by
    ext i j
    exact
      canonicalCompletedC3NormalizedSymplecticGammaKernel_eq_inner
        (point i) (point j) (hoffAxis i) (hoffAxis j)]
  exact Matrix.posSemidef_gram ℂ _

theorem
canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS_div_fullWeight_eq_normalizedKernel_sub_dslope
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS z w hz hw /
        (
          (w - conj z) *
            mixedHermitianWeight nativeXiCompletionFactor w z *
            canonicalCompletedC3RawHeightCharacteristicWeight z w
        ) =
      canonicalCompletedC3NormalizedSymplecticGammaKernel z w hz hw -
        canonicalCompletedNativePolarizedDslopeKernel z w := by
  rw [
    canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS_eq_separation_mul_kernelDifference
      z w hz hw hzStrip hwStrip hzF hwF hsep,
    canonicalCompletedC3_chartGammaWeight_eq_xiRawHeightWeight
      z w hzStrip hwStrip
  ]
  unfold canonicalCompletedC3NormalizedSymplecticGammaKernel
  have hxiWeight :
      mixedHermitianWeight nativeXiCompletionFactor w z ≠ 0 :=
    canonicalCompletedC3XiMixedHermitianWeight_ne_zero hzStrip hwStrip
  have hrawWeight :
      canonicalCompletedC3RawHeightCharacteristicWeight z w ≠ 0 :=
    canonicalCompletedC3RawHeightCharacteristicWeight_ne_zero
      hzStrip hwStrip hzF hwF
  have hseparation : w - conj z ≠ 0 :=
    sub_ne_zero.mpr hsep
  field_simp [hxiWeight, hrawWeight, hseparation]

theorem
canonicalCompletedC3SymplecticRadialNormalizedKernelLedger_eventually
    (i j : ℕ) :
    ∀ᶠ steps : ℕ × ℕ in Filter.atTop,
      canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS
          (canonicalCompletedC3RadialTiltPoint steps.1 i)
          (canonicalCompletedC3RadialTiltPoint steps.2 j)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j) /
        (
          (canonicalCompletedC3RadialTiltPoint steps.2 j -
              conj (canonicalCompletedC3RadialTiltPoint steps.1 i)) *
          mixedHermitianWeight nativeXiCompletionFactor
            (canonicalCompletedC3RadialTiltPoint steps.2 j)
            (canonicalCompletedC3RadialTiltPoint steps.1 i) *
          canonicalCompletedC3RawHeightCharacteristicWeight
            (canonicalCompletedC3RadialTiltPoint steps.1 i)
            (canonicalCompletedC3RadialTiltPoint steps.2 j)
        ) =
      canonicalCompletedC3NormalizedSymplecticGammaKernel
        (canonicalCompletedC3RadialTiltPoint steps.1 i)
        (canonicalCompletedC3RadialTiltPoint steps.2 j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j) -
        canonicalCompletedNativePolarizedDslopeKernel
          (canonicalCompletedC3RadialTiltPoint steps.1 i)
          (canonicalCompletedC3RadialTiltPoint steps.2 j) := by
  filter_upwards [
    canonicalCompletedC3RadialTiltPair_eventually_admissible i j
  ] with steps hadmissible
  have hsep :
      canonicalCompletedC3RadialTiltPoint steps.2 j ≠
        conj (canonicalCompletedC3RadialTiltPoint steps.1 i) :=
    sub_ne_zero.mp
      (canonicalCompletedC3RadialTilt_separation_ne_zero_twoStep
        steps.1 steps.2 i j)
  exact
    canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS_div_fullWeight_eq_normalizedKernel_sub_dslope
      (z := canonicalCompletedC3RadialTiltPoint steps.1 i)
      (w := canonicalCompletedC3RadialTiltPoint steps.2 j)
      (hz := canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
      (hw := canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j)
      (hzStrip := hadmissible.1)
      (hwStrip := hadmissible.2.2.1)
      (hzF := hadmissible.2.1)
      (hwF := hadmissible.2.2.2)
      hsep

theorem
canonicalCompletedC3SymplecticRadialNormalizedKernelLedger_stencil_eventually
    (p q : ℕ) :
    ∀ᶠ steps : ℕ × ℕ in Filter.atTop,
      ∀ i ∈ Finset.range (p + 1),
        ∀ j ∈ Finset.range (q + 1),
          canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS
              (canonicalCompletedC3RadialTiltPoint steps.1 i)
              (canonicalCompletedC3RadialTiltPoint steps.2 j)
              (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
              (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j) /
            (
              (canonicalCompletedC3RadialTiltPoint steps.2 j -
                  conj (canonicalCompletedC3RadialTiltPoint steps.1 i)) *
              mixedHermitianWeight nativeXiCompletionFactor
                (canonicalCompletedC3RadialTiltPoint steps.2 j)
                (canonicalCompletedC3RadialTiltPoint steps.1 i) *
              canonicalCompletedC3RawHeightCharacteristicWeight
                (canonicalCompletedC3RadialTiltPoint steps.1 i)
                (canonicalCompletedC3RadialTiltPoint steps.2 j)
            ) =
          canonicalCompletedC3NormalizedSymplecticGammaKernel
            (canonicalCompletedC3RadialTiltPoint steps.1 i)
            (canonicalCompletedC3RadialTiltPoint steps.2 j)
            (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
            (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j) -
            canonicalCompletedNativePolarizedDslopeKernel
              (canonicalCompletedC3RadialTiltPoint steps.1 i)
              (canonicalCompletedC3RadialTiltPoint steps.2 j) := by
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hstrip :=
    canonicalCompletedC3RadialTiltStencil_eventually_mem_genuineCriticalStrip p q
  have hi : ∀ᶠ k : ℕ in atTop,
      ∀ i ∈ Finset.range (p + 1),
        canonicalCompletedC3RadialTiltPoint k i ∈
            completedNativeHeightDomain ∧
          completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 :=
    (Finset.range (p + 1)).eventually_all.2 fun i hi =>
      canonicalCompletedC3RadialTiltPoint_eventually_admissible i
  have hj : ∀ᶠ k : ℕ in atTop,
      ∀ j ∈ Finset.range (q + 1),
        canonicalCompletedC3RadialTiltPoint k j ∈
            completedNativeHeightDomain ∧
          completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k j) ≠ 0 :=
    (Finset.range (q + 1)).eventually_all.2 fun j hj =>
      canonicalCompletedC3RadialTiltPoint_eventually_admissible j
  filter_upwards [
    hstrip,
    hfst.eventually hi,
    hsnd.eventually hj
  ] with steps hstrip hfirst hsecond
  intro i hi j hj
  have hsep :
      canonicalCompletedC3RadialTiltPoint steps.2 j ≠
        conj (canonicalCompletedC3RadialTiltPoint steps.1 i) :=
    sub_ne_zero.mp
      (canonicalCompletedC3RadialTilt_separation_ne_zero_twoStep
        steps.1 steps.2 i j)
  exact
    canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS_div_fullWeight_eq_normalizedKernel_sub_dslope
      (z := canonicalCompletedC3RadialTiltPoint steps.1 i)
      (w := canonicalCompletedC3RadialTiltPoint steps.2 j)
      (hz := canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
      (hw := canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j)
      (hzStrip := (hstrip i hi j hj).1)
      (hwStrip := (hstrip i hi j hj).2)
      (hzF := (hfirst i hi).2)
      (hwF := (hsecond j hj).2)
      hsep

end

end CarrySelfAdjointOperator
