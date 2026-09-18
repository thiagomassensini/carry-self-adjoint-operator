import CarrySelfAdjointOperator.CompletedC3SymplecticGammaWeylComplexResidual
import CarrySelfAdjointOperator.CompletedC3SymplecticGammaReflectionLedger
import CarrySelfAdjointOperator.CompletedC3SymplecticGammaCompletedWronskianBridge

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite

noncomputable section

theorem
canonicalCompletedC3SymplecticGammaBoundary_sub_reflectedStaticGreen_eq
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
        canonicalCompletedC3SymplecticCameraComplexGreenReadout z (conj w) =
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
                    (𝕜 := ℂ)
                    (canonicalCompletedOperatorC3State w))) } +
      (canonicalCompletedC3SymplecticCameraComplexGreenReadout z w -
        canonicalCompletedC3SymplecticCameraComplexGreenReadout z (conj w)) := by
  calc
    canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
          canonicalCompletedC3SymplecticCameraComplexGreenReadout z (conj w) =
        (canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
            canonicalCompletedC3SymplecticCameraComplexGreenReadout z w) +
          (canonicalCompletedC3SymplecticCameraComplexGreenReadout z w -
            canonicalCompletedC3SymplecticCameraComplexGreenReadout z (conj w)) := by
      ring
    _ = _ := by
      rw [canonicalCompletedC3SymplecticGammaBoundary_sub_staticGreen_eq_complex]

theorem
canonicalCompletedC3WeightedSymplecticGammaBoundary_sub_completedWronskian_eq_explicit
    {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedHermitianWeight nativeXiCompletionFactor w z *
        canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
      mixedHermitianWeight canonicalC3ChartFactorHeight w z *
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
          w z =
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
                      (𝕜 := ℂ)
                      (canonicalCompletedOperatorC3State w))) } +
      mixedHermitianWeight nativeXiCompletionFactor w z *
        (canonicalCompletedC3SymplecticCameraComplexGreenReadout z w -
          canonicalCompletedC3SymplecticCameraComplexGreenReadout z (conj w)) -
      mixedHermitianWeight nativeXiCompletionFactor w z *
        canonicalC3FiniteMixedHeightStructuralDefect 1
          (operatorHeightParameter w) (operatorHeightParameter z) -
      mixedHermitianWeight nativeXiCompletionFactor w z *
        canonicalC3MixedHeightTailCompletionDefect 1 w z -
      canonicalCompletedC3ArchimedeanChartMixedChannel w z := by
  have hbridge :=
    canonicalCompletedC3WeightedSymplecticGammaBoundary_sub_completedWronskian
      hz hw hzStrip hwStrip
  rw [canonicalCompletedC3SymplecticGammaBoundary_sub_reflectedStaticGreen_eq
      z w hz hw] at hbridge
  convert hbridge using 1 <;> ring

end

end CarrySelfAdjointOperator
