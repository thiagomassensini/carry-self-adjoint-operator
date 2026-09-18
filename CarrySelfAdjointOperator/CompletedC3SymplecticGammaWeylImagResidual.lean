import CarrySelfAdjointOperator.CompletedC3SymplecticGammaWeylImagChannel
import CarrySelfAdjointOperator.CompletedC3SymplecticWeylTraceDefect
import CarrySelfAdjointOperator.CompletedC3SymplecticGammaState
import Mathlib.Tactic

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

theorem
canonicalRealifiedCameraQuarterTurn_canonicalC3SymplecticCameraPacking
    (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3) :
    canonicalRealifiedCameraQuarterTurn
        (canonicalC3SymplecticCameraPacking x) =
      - canonicalC3SymplecticCameraPacking
          (weylChartRotation (𝕜 := ℂ) x) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp [canonicalRealifiedCameraQuarterTurn,
      canonicalC3SymplecticCameraPacking_apply, weylChartRotation_apply]
  · simp [canonicalRealifiedCameraQuarterTurn,
      canonicalC3SymplecticCameraPacking_apply, weylChartRotation_apply]

theorem
canonicalCompletedC3SymplecticGammaBoundary_sub_staticGreen_im_eq
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    (canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
        canonicalCompletedC3SymplecticCameraComplexGreenReadout z w).im =
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
          (canonicalRealifiedCameraQuarterTurn
              (canonicalCompletedC3SymplecticGammaCameraSource w : RealifiedCameraComplexification) +
            canonicalC3SymplecticCameraPacking
              (Complex.I • canonicalCompletedOperatorC3State w)) := by
  have hdynamic :=
    canonicalCompletedC3SymplecticGammaBoundaryReadout_im_eq_greenForm_dynamic_quarterTurn
      z w hz hw
  have hdefect :=
    greenForm_dynamic_sub_static_eq_weylTraceDefects
      z w hz hw
      (canonicalCompletedC3SymplecticGammaCameraSource z)
      (canonicalRealifiedCameraQuarterTurn
        (canonicalCompletedC3SymplecticGammaCameraSource w : RealifiedCameraComplexification))
  have hboundary :
      (canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw).im =
        (greenForm (𝕜 := ℝ)
          (allBasesCauchyBlock z hz
            (canonicalCompletedC3SymplecticGammaCameraSource z),
            canonicalCompletedC3SymplecticGammaCameraSource z)
          (allBasesCauchyBlock w hw
            (canonicalRealifiedCameraQuarterTurn
              (canonicalCompletedC3SymplecticGammaCameraSource w :
                RealifiedCameraComplexification)),
            canonicalRealifiedCameraQuarterTurn
              (canonicalCompletedC3SymplecticGammaCameraSource w :
                RealifiedCameraComplexification)) -
          NativeCarryC3Crosswalk.realifiedGreenSkew
            (canonicalCompletedC3SymplecticGammaCameraSource z)
            (canonicalRealifiedCameraQuarterTurn
              (canonicalCompletedC3SymplecticGammaCameraSource w :
                RealifiedCameraComplexification))) +
        NativeCarryC3Crosswalk.realifiedGreenSkew
          (canonicalCompletedC3SymplecticGammaCameraSource z)
          (canonicalRealifiedCameraQuarterTurn
            (canonicalCompletedC3SymplecticGammaCameraSource w :
              RealifiedCameraComplexification)) := by
    rw [hdynamic]
    ring
  unfold canonicalCompletedC3SymplecticCameraComplexGreenReadout
  simp only [Complex.sub_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, zero_sub]
  rw [hboundary, hdefect]
  simp only [NativeCarryC3Crosswalk.realifiedGreenSkew,
    WithLp.add_fst, WithLp.add_snd, inner_add_right]
  ring

theorem
canonicalCompletedC3SymplecticGammaBoundary_sub_staticGreen_im_eq_packed
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    (canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
        canonicalCompletedC3SymplecticCameraComplexGreenReadout z w).im =
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
              weylChartRotation (𝕜 := ℂ)
                (canonicalCompletedOperatorC3State w))) := by
  have hvector :
      canonicalRealifiedCameraQuarterTurn
          (canonicalCompletedC3SymplecticGammaCameraSource w :
            RealifiedCameraComplexification) +
        canonicalC3SymplecticCameraPacking
          (Complex.I • canonicalCompletedOperatorC3State w) =
      canonicalC3SymplecticCameraPacking
        (Complex.I • canonicalCompletedOperatorC3State w -
          weylChartRotation (𝕜 := ℂ)
            (canonicalCompletedOperatorC3State w)) := by
    unfold canonicalCompletedC3SymplecticGammaCameraSource
    rw [canonicalRealifiedCameraQuarterTurn_canonicalC3SymplecticCameraPacking]
    rw [map_sub]
    abel
  rw [canonicalCompletedC3SymplecticGammaBoundary_sub_staticGreen_im_eq]
  rw [hvector]

end

end CarrySelfAdjointOperator
