import CarrySelfAdjointOperator.CompletedC3SymplecticGammaExplicitCompletedLedger
import CarrySelfAdjointOperator.CompletedC3SymplecticGammaRadialAdmissibility
import Mathlib.Tactic

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite

noncomputable section

def canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  mixedHermitianWeight nativeXiCompletionFactor w z *
      { re :=
          -(
            @inner ℝ RealifiedCameraComplexification _
                (canonicalCompletedC3SymplecticGammaCameraSource z :
                  RealifiedCameraComplexification)
                (canonicalRealifiedCameraWeylTraceDefect w hw
                  (canonicalCompletedC3SymplecticGammaCameraSource w :
                    RealifiedCameraComplexification)) -
            @inner ℝ RealifiedCameraComplexification _
                (canonicalRealifiedCameraWeylTraceDefect z hz
                  (canonicalCompletedC3SymplecticGammaCameraSource z :
                    RealifiedCameraComplexification))
                (canonicalCompletedC3SymplecticGammaCameraSource w :
                  RealifiedCameraComplexification)
          ) -
          2 * (canonicalCompletedC3SymplecticCameraComplexGreenReadout z w).re
        im :=
          @inner ℝ RealifiedCameraComplexification _
              (canonicalCompletedC3SymplecticGammaCameraSource z :
                RealifiedCameraComplexification)
              (canonicalRealifiedCameraWeylTraceDefect w hw
                (canonicalRealifiedCameraQuarterTurn
                  (canonicalCompletedC3SymplecticGammaCameraSource w :
                    RealifiedCameraComplexification))) -
            @inner ℝ RealifiedCameraComplexification _
                (canonicalRealifiedCameraWeylTraceDefect z hz
                  (canonicalCompletedC3SymplecticGammaCameraSource z :
                    RealifiedCameraComplexification))
                (canonicalRealifiedCameraQuarterTurn
                  (canonicalCompletedC3SymplecticGammaCameraSource w :
                    RealifiedCameraComplexification)) +
            NativeCarryC3Crosswalk.realifiedGreenSkew
              (canonicalCompletedC3SymplecticGammaCameraSource z)
              (canonicalC3SymplecticCameraPacking
                (Complex.I • canonicalCompletedOperatorC3State w -
                  NativeCarrySpectralWeyl.Boundary.weylChartRotation
                    (𝕜 := ℂ) (canonicalCompletedOperatorC3State w))) } +
    mixedHermitianWeight nativeXiCompletionFactor w z *
      (canonicalCompletedC3SymplecticCameraComplexGreenReadout z w -
        canonicalCompletedC3SymplecticCameraComplexGreenReadout z (conj w)) -
    mixedHermitianWeight nativeXiCompletionFactor w z *
      canonicalC3FiniteMixedHeightStructuralDefect 1
        (operatorHeightParameter w) (operatorHeightParameter z) -
    mixedHermitianWeight nativeXiCompletionFactor w z *
      canonicalC3MixedHeightTailCompletionDefect 1 w z -
    canonicalCompletedC3ArchimedeanChartMixedChannel w z

theorem
canonicalCompletedC3WeightedSymplecticGammaBoundary_sub_completedWronskian_eq_explicitRHS
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedHermitianWeight nativeXiCompletionFactor w z *
        canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
      mixedHermitianWeight canonicalC3ChartFactorHeight w z *
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
          w z =
      canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS z w hz hw := by
  simpa [canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS] using
    (canonicalCompletedC3WeightedSymplecticGammaBoundary_sub_completedWronskian_eq_explicit
      (z := z) (w := w) hz hw hzStrip hwStrip)

theorem
canonicalCompletedC3SymplecticRadialWeightedLedger_eventually
    (i j : ℕ) :
    ∀ᶠ steps : ℕ × ℕ in Filter.atTop,
      mixedHermitianWeight nativeXiCompletionFactor
          (canonicalCompletedC3RadialTiltPoint steps.2 j)
          (canonicalCompletedC3RadialTiltPoint steps.1 i) *
          canonicalCompletedC3SymplecticGammaBoundaryReadout
            (canonicalCompletedC3RadialTiltPoint steps.1 i)
            (canonicalCompletedC3RadialTiltPoint steps.2 j)
            (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
            (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j) -
        mixedHermitianWeight canonicalC3ChartFactorHeight
            (canonicalCompletedC3RadialTiltPoint steps.2 j)
            (canonicalCompletedC3RadialTiltPoint steps.1 i) *
          completedGreenWronskian
            completedNativeOperatorCharacteristic
            (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
            (canonicalCompletedC3RadialTiltPoint steps.2 j)
            (canonicalCompletedC3RadialTiltPoint steps.1 i) =
      canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS
        (canonicalCompletedC3RadialTiltPoint steps.1 i)
        (canonicalCompletedC3RadialTiltPoint steps.2 j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j) := by
  filter_upwards [
    canonicalCompletedC3RadialTiltPair_eventually_mem_genuineCriticalStrip i j
  ] with steps hstrip
  exact canonicalCompletedC3WeightedSymplecticGammaBoundary_sub_completedWronskian_eq_explicitRHS
    (z := canonicalCompletedC3RadialTiltPoint steps.1 i)
    (w := canonicalCompletedC3RadialTiltPoint steps.2 j)
    (hz := canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
    (hw := canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j)
    (hzStrip := hstrip.1)
    (hwStrip := hstrip.2)

theorem
canonicalCompletedC3SymplecticRadialWeightedLedger_stencil_eventually
    (p q : ℕ) :
    ∀ᶠ steps : ℕ × ℕ in Filter.atTop,
      ∀ i ∈ Finset.range (p + 1),
        ∀ j ∈ Finset.range (q + 1),
          mixedHermitianWeight nativeXiCompletionFactor
              (canonicalCompletedC3RadialTiltPoint steps.2 j)
              (canonicalCompletedC3RadialTiltPoint steps.1 i) *
              canonicalCompletedC3SymplecticGammaBoundaryReadout
                (canonicalCompletedC3RadialTiltPoint steps.1 i)
                (canonicalCompletedC3RadialTiltPoint steps.2 j)
                (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
                (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j) -
            mixedHermitianWeight canonicalC3ChartFactorHeight
                (canonicalCompletedC3RadialTiltPoint steps.2 j)
                (canonicalCompletedC3RadialTiltPoint steps.1 i) *
              completedGreenWronskian
                completedNativeOperatorCharacteristic
                (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
                (canonicalCompletedC3RadialTiltPoint steps.2 j)
                (canonicalCompletedC3RadialTiltPoint steps.1 i) =
          canonicalCompletedC3WeightedSymplecticGammaExplicitLedgerRHS
            (canonicalCompletedC3RadialTiltPoint steps.1 i)
            (canonicalCompletedC3RadialTiltPoint steps.2 j)
            (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
            (canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j) := by
  filter_upwards [
    canonicalCompletedC3RadialTiltStencil_eventually_mem_genuineCriticalStrip p q
  ] with steps hstrip
  intro i hi j hj
  exact canonicalCompletedC3WeightedSymplecticGammaBoundary_sub_completedWronskian_eq_explicitRHS
    (z := canonicalCompletedC3RadialTiltPoint steps.1 i)
    (w := canonicalCompletedC3RadialTiltPoint steps.2 j)
    (hz := canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.1 i)
    (hw := canonicalCompletedC3RadialTiltPoint_im_ne_zero steps.2 j)
    (hzStrip := (hstrip i hi j hj).1)
    (hwStrip := (hstrip i hi j hj).2)

end

end CarrySelfAdjointOperator
