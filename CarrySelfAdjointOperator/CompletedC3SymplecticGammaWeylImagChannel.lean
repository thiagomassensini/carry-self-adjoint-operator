import CarrySelfAdjointOperator.CompletedC3SymplecticGammaState
import CarrySelfAdjointOperator.CompletedC3SymplecticWeylTraceDefect
import Mathlib.Tactic

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

theorem allBasesCauchyBlock_commutes_canonicalRealifiedCameraQuarterTurn
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u : RealifiedCameraComplexification) :
    allBasesCauchyBlock lambda hlambda
        (canonicalRealifiedCameraQuarterTurn u) =
      canonicalRealifiedCameraQuarterTurn
        (allBasesCauchyBlock lambda hlambda u) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (allBasesCauchyBlock lambda hlambda
        (canonicalRealifiedCameraQuarterTurn u)).fst =
      (canonicalRealifiedCameraQuarterTurn
        (allBasesCauchyBlock lambda hlambda u)).fst
    simp only [allBasesCauchyBlock_fst,
      canonicalRealifiedCameraQuarterTurn_fst, map_neg,
      canonicalRealifiedCameraQuarterTurn_snd,
      allBasesCauchyBlock_snd, neg_add_rev]
    abel
  · change (allBasesCauchyBlock lambda hlambda
        (canonicalRealifiedCameraQuarterTurn u)).snd =
      (canonicalRealifiedCameraQuarterTurn
        (allBasesCauchyBlock lambda hlambda u)).snd
    simp only [allBasesCauchyBlock_snd,
      canonicalRealifiedCameraQuarterTurn_fst, map_neg,
      canonicalRealifiedCameraQuarterTurn_snd,
      allBasesCauchyBlock_fst]
    abel

theorem
canonicalCompletedC3SymplecticGammaBoundaryReadout_im_eq_greenForm_dynamic_quarterTurn
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    (canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw).im =
      greenForm (𝕜 := ℝ)
        (allBasesCauchyBlock z hz
          (canonicalCompletedC3SymplecticGammaCameraSource z),
          canonicalCompletedC3SymplecticGammaCameraSource z)
        (allBasesCauchyBlock w hw
          (canonicalRealifiedCameraQuarterTurn
            (canonicalCompletedC3SymplecticGammaCameraSource w)),
          canonicalRealifiedCameraQuarterTurn
            (canonicalCompletedC3SymplecticGammaCameraSource w)) := by
  have hquarter_fst (u : RealifiedCameraComplexification) :
      (canonicalRealifiedCameraQuarterTurn u).ofLp.1 = -u.ofLp.2 := by
    change (canonicalRealifiedCameraQuarterTurn u).fst = -u.snd
    exact canonicalRealifiedCameraQuarterTurn_fst u
  have hquarter_snd (u : RealifiedCameraComplexification) :
      (canonicalRealifiedCameraQuarterTurn u).ofLp.2 = u.ofLp.1 := by
    change (canonicalRealifiedCameraQuarterTurn u).snd = u.fst
    exact canonicalRealifiedCameraQuarterTurn_snd u
  unfold canonicalCompletedC3SymplecticGammaBoundaryReadout
    carryGammaPolarizedBoundaryReadout
    carryGammaComplexCauchyReadout
  simp only [Complex.sub_im, RealHilbertComplexification.inner_apply,
    RealHilbertComplexification.complexInner_im]
  rw [allBasesCauchyBlock_commutes_canonicalRealifiedCameraQuarterTurn]
  simp only [greenForm, WithLp.prod_inner_apply,
    hquarter_fst, hquarter_snd,
    RealHilbertComplexification.re,
    RealHilbertComplexification.im,
    inner_neg_right]
  ring
end

end CarrySelfAdjointOperator
