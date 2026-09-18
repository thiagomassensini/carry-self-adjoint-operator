import CarrySelfAdjointOperator.CompletedC3SymplecticGammaState
import CarrySelfAdjointOperator.CompletedC3SymplecticWeylTraceDefect
import Mathlib.Tactic

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

theorem
canonicalCompletedC3NegGammaBoundary_sub_staticGreen_re_eq_weylTraceDefects
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    (-canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
        canonicalCompletedC3SymplecticCameraComplexGreenReadout z w).re =
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
            RealifiedCameraComplexification) := by
  have hboundary :
      (canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw).re =
        -greenForm (𝕜 := ℝ)
          (allBasesCauchyBlock z hz
            (canonicalCompletedC3SymplecticGammaCameraSource z),
            canonicalCompletedC3SymplecticGammaCameraSource z)
          (allBasesCauchyBlock w hw
            (canonicalCompletedC3SymplecticGammaCameraSource w),
            canonicalCompletedC3SymplecticGammaCameraSource w) := by
    unfold canonicalCompletedC3SymplecticGammaBoundaryReadout
      carryGammaPolarizedBoundaryReadout
      carryGammaComplexCauchyReadout
    simp only [Complex.sub_re, RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_re, greenForm,
      WithLp.prod_inner_apply, RealHilbertComplexification.re,
      RealHilbertComplexification.im]
    simp only [real_inner_comm]
    ring

  have hstatic :
      (canonicalCompletedC3SymplecticCameraComplexGreenReadout z w).re =
        NativeCarryC3Crosswalk.realifiedGreenSkew
          (canonicalCompletedC3SymplecticGammaCameraSource z)
          (canonicalCompletedC3SymplecticGammaCameraSource w) := by
    unfold canonicalCompletedC3SymplecticCameraComplexGreenReadout
    simp

  simp only [Complex.sub_re, Complex.neg_re]
  rw [hboundary, hstatic]
  have h := greenForm_dynamic_sub_static_eq_weylTraceDefects
    z w hz hw
      (canonicalCompletedC3SymplecticGammaCameraSource z)
      (canonicalCompletedC3SymplecticGammaCameraSource w)
  simpa only [neg_neg] using h
theorem
canonicalCompletedC3SymplecticGammaBoundary_sub_staticGreen_re_eq
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    (canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
        canonicalCompletedC3SymplecticCameraComplexGreenReadout z w).re =
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
      2 * (canonicalCompletedC3SymplecticCameraComplexGreenReadout z w).re := by
  have h :=
    canonicalCompletedC3NegGammaBoundary_sub_staticGreen_re_eq_weylTraceDefects
      z w hz hw
  simp only [Complex.sub_re, Complex.neg_re] at h ⊢
  linarith

theorem
canonicalCompletedC3SymplecticGammaBoundary_sub_reflectedStaticGreen_re_eq
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    (canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
        canonicalCompletedC3SymplecticCameraComplexGreenReadout z (conj w)).re =
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
      (canonicalCompletedC3SymplecticCameraComplexGreenReadout z w).re -
      (canonicalCompletedC3SymplecticCameraComplexGreenReadout
        z (conj w)).re := by
  have h :=
    canonicalCompletedC3NegGammaBoundary_sub_staticGreen_re_eq_weylTraceDefects
      z w hz hw
  simp only [Complex.sub_re, Complex.neg_re] at h ⊢
  linarith
end

end CarrySelfAdjointOperator
