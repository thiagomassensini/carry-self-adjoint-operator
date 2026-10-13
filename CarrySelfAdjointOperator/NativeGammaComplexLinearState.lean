import CarrySelfAdjointOperator.NativeGammaNaimarkComplexProjection

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Boundary
noncomputable section
set_option autoImplicit false

def nativeComplexContinuousBlock {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (A B : E →L[ℝ] F) :
    RealHilbertComplexification E →ₗ[ℂ] RealHilbertComplexification F where
  toFun u := realifiedContinuousLinearBlock A B u
  map_add' := by intro u v; exact (realifiedContinuousLinearBlock A B).map_add u v
  map_smul' := by
    intro c u
    have hre (v : RealHilbertComplexification E) :
        RealHilbertComplexification.re (realifiedContinuousLinearBlock A B v) =
          A (RealHilbertComplexification.re v) - B (RealHilbertComplexification.im v) :=
      realifiedContinuousLinearBlock_fst A B v
    have him (v : RealHilbertComplexification E) :
        RealHilbertComplexification.im (realifiedContinuousLinearBlock A B v) =
          B (RealHilbertComplexification.re v) + A (RealHilbertComplexification.im v) :=
      realifiedContinuousLinearBlock_snd A B v
    apply RealHilbertComplexification.ext <;>
      simp only [hre, him, RealHilbertComplexification.re_smul, RealHilbertComplexification.im_smul,
        map_sub, map_add, map_smul, RingHom.id_apply] <;> module

def nativeComplexGamma (z : ℂ) (hz : z.im ≠ 0) :
    CarryGammaComplexCamera →ₗ[ℂ] CarryGammaComplexNaimark :=
  (nativeComplexContinuousBlock (logarithmicResolventRealOperator z hz)
    (logarithmicResolventImaginaryOperator z hz)).comp nativeComplexNaimarkPort

theorem nativeComplexGamma_eq_original (z : ℂ) (hz : z.im ≠ 0) (u : CarryGammaComplexCamera) :
    nativeComplexGamma z hz u = carryGammaComplexState z hz u := by
  change realifiedContinuousLinearBlock _ _ (nativeComplexNaimarkPort u) = _
  rw [nativeComplexNaimarkPort_eq_original]
  rfl

theorem carryGammaComplexState_complex_smul (z : ℂ) (hz : z.im ≠ 0)
    (a : ℂ) (u : CarryGammaComplexCamera) :
    carryGammaComplexState z hz (a • u) = a • carryGammaComplexState z hz u := by
  simp only [← nativeComplexGamma_eq_original, map_smul]

theorem carryGammaComplexState_re (z : ℂ) (hz : z.im ≠ 0) (u : CarryGammaComplexCamera) :
    RealHilbertComplexification.re (carryGammaComplexState z hz u) =
      logarithmicResolventRealOperator z hz (naimarkIsometry (RealHilbertComplexification.re u)) -
      logarithmicResolventImaginaryOperator z hz (naimarkIsometry (RealHilbertComplexification.im u)) := by
  change (carryGammaSource z hz u).fst = _
  exact carryGammaSource_fst z hz u

theorem carryGammaComplexState_im (z : ℂ) (hz : z.im ≠ 0) (u : CarryGammaComplexCamera) :
    RealHilbertComplexification.im (carryGammaComplexState z hz u) =
      logarithmicResolventImaginaryOperator z hz (naimarkIsometry (RealHilbertComplexification.re u)) +
      logarithmicResolventRealOperator z hz (naimarkIsometry (RealHilbertComplexification.im u)) := by
  change (carryGammaSource z hz u).snd = _
  exact carryGammaSource_snd z hz u

end
end CarrySelfAdjointOperator.GammaMaterialSewing
