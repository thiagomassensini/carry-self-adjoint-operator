import CarrySelfAdjointOperator.CompletedC3SymplecticGammaWeylRealChannel
import CarrySelfAdjointOperator.CompletedC3SymplecticGammaWeylImagResidual

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator
open NativeCarrySpectralWeyl.Infinite

noncomputable section

theorem
canonicalCompletedC3SymplecticGammaBoundary_sub_staticGreen_eq_complex
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
        canonicalCompletedC3SymplecticCameraComplexGreenReadout z w =
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
                    (canonicalCompletedOperatorC3State w))) } := by
  apply Complex.ext
  · simpa only [Complex.sub_re] using
      (canonicalCompletedC3SymplecticGammaBoundary_sub_staticGreen_re_eq
        z w hz hw)
  · exact
      canonicalCompletedC3SymplecticGammaBoundary_sub_staticGreen_im_eq_packed
        z w hz hw

end

end CarrySelfAdjointOperator
