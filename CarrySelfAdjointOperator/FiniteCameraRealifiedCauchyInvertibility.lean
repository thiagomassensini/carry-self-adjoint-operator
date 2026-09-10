import CarrySelfAdjointOperator.FiniteCameraLogarithmicMomentCrosswalk
import NativeCarrySpectralWeyl.Infinite.ComplexifiedResolvent
import Mathlib.Tactic

open scoped BigOperators ENNReal MeasureTheory RealInnerProductSpace Matrix MatrixOrder
open Set MeasureTheory Filter

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 2000000

abbrev FiniteCameraCoordinates (ι : Type*) := EuclideanSpace ℝ ι
abbrev FiniteCameraRealification (ι : Type*) :=
  WithLp 2 (FiniteCameraCoordinates ι × FiniteCameraCoordinates ι)

def finiteCameraMatrixMulVec
    {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) :
    FiniteCameraCoordinates ι →ₗ[ℝ] FiniteCameraCoordinates ι where
  toFun u := WithLp.toLp 2 (M *ᵥ u.ofLp)
  map_add' u v := by
    apply (WithLp.ext_iff 2).2
    exact Matrix.mulVec_add M u.ofLp v.ofLp
  map_smul' a u := by
    apply (WithLp.ext_iff 2).2
    exact Matrix.mulVec_smul M a u.ofLp

def finiteCameraNaimarkSynthesisLinear
    {ι : Type*} [Fintype ι]
    (camera : ι → CameraIndex) :
    FiniteCameraCoordinates ι →ₗ[ℝ] NaimarkSpace where
  toFun u := finiteCameraNaimarkSynthesis camera u.ofLp
  map_add' u v := by
    change finiteCameraNaimarkSynthesis camera (u.ofLp + v.ofLp) = _
    simp only [finiteCameraNaimarkSynthesis, Pi.add_apply, add_smul,
      Finset.sum_add_distrib]
  map_smul' a u := by
    change finiteCameraNaimarkSynthesis camera (a • u.ofLp) = _
    simp only [finiteCameraNaimarkSynthesis, Pi.smul_apply,
      smul_eq_mul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_smul]
    simp

def finiteCameraWhitenedNaimarkSynthesisLinear
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ) :
    FiniteCameraCoordinates ι →ₗ[ℝ] NaimarkSpace :=
  (finiteCameraNaimarkSynthesisLinear camera).comp
    (finiteCameraMatrixMulVec (positiveInverseSqrt G))

def finiteCameraWhitenedNaimarkSynthesisContinuous
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ) :
    FiniteCameraCoordinates ι →L[ℝ] NaimarkSpace :=
  LinearMap.toContinuousLinearMap
    (finiteCameraWhitenedNaimarkSynthesisLinear camera G)

@[simp] theorem finiteCameraWhitenedNaimarkSynthesisContinuous_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (u : FiniteCameraCoordinates ι) :
    finiteCameraWhitenedNaimarkSynthesisContinuous camera G u =
      finiteCameraWhitenedNaimarkSynthesis camera G u.ofLp := rfl

theorem finiteCameraWhitenedNaimarkSynthesisContinuous_inner
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (hGram : finiteCameraNaimarkGramMatrix camera = G)
    (hG : G.PosDef)
    (u v : FiniteCameraCoordinates ι) :
    inner ℝ (finiteCameraWhitenedNaimarkSynthesisContinuous camera G u)
      (finiteCameraWhitenedNaimarkSynthesisContinuous camera G v) =
      inner ℝ u v := by
  rw [finiteCameraWhitenedNaimarkSynthesisContinuous_apply,
    finiteCameraWhitenedNaimarkSynthesisContinuous_apply,
    finiteCameraWhitenedNaimarkSynthesis_inner camera G hGram hG]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  exact dotProduct_comm _ _

theorem finiteCameraWhitenedNaimarkSynthesisContinuous_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (hGram : finiteCameraNaimarkGramMatrix camera = G)
    (hG : G.PosDef) :
    Function.Injective (finiteCameraWhitenedNaimarkSynthesisContinuous camera G) := by
  intro u v huv
  have hz : u - v = 0 := by
    by_contra hne
    have hinner := finiteCameraWhitenedNaimarkSynthesisContinuous_inner
      camera G hGram hG (u - v) (u - v)
    rw [map_sub, huv, sub_self, inner_zero_left] at hinner
    have hzero : inner ℝ (u - v) (u - v) = 0 := hinner.symm
    exact hne (inner_self_eq_zero.mp hzero)
  exact sub_eq_zero.mp hz

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

 def finiteCameraCauchyRealPart
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    FiniteCameraCoordinates ι →L[ℝ] FiniteCameraCoordinates ι :=
  (finiteCameraWhitenedNaimarkSynthesisContinuous camera G).adjoint ∘L
    (logarithmicResolventRealOperator lambda hlambda ∘L
      finiteCameraWhitenedNaimarkSynthesisContinuous camera G)

def finiteCameraCauchyImaginaryPart
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    FiniteCameraCoordinates ι →L[ℝ] FiniteCameraCoordinates ι :=
  (finiteCameraWhitenedNaimarkSynthesisContinuous camera G).adjoint ∘L
    (logarithmicResolventImaginaryOperator lambda hlambda ∘L
      finiteCameraWhitenedNaimarkSynthesisContinuous camera G)

theorem finiteCameraCauchyRealPart_inner
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u v : FiniteCameraCoordinates ι) :
    inner ℝ u (finiteCameraCauchyRealPart camera G lambda hlambda v) =
      inner ℝ (finiteCameraWhitenedNaimarkSynthesisContinuous camera G u)
        (logarithmicResolventRealOperator lambda hlambda
          (finiteCameraWhitenedNaimarkSynthesisContinuous camera G v)) := by
  rw [finiteCameraCauchyRealPart, ContinuousLinearMap.comp_apply]
  exact (finiteCameraWhitenedNaimarkSynthesisContinuous camera G).adjoint_inner_right
    u (logarithmicResolventRealOperator lambda hlambda
      (finiteCameraWhitenedNaimarkSynthesisContinuous camera G v))

theorem finiteCameraCauchyImaginaryPart_inner
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u v : FiniteCameraCoordinates ι) :
    inner ℝ u (finiteCameraCauchyImaginaryPart camera G lambda hlambda v) =
      inner ℝ (finiteCameraWhitenedNaimarkSynthesisContinuous camera G u)
        (logarithmicResolventImaginaryOperator lambda hlambda
          (finiteCameraWhitenedNaimarkSynthesisContinuous camera G v)) := by
  rw [finiteCameraCauchyImaginaryPart, ContinuousLinearMap.comp_apply]
  exact (finiteCameraWhitenedNaimarkSynthesisContinuous camera G).adjoint_inner_right
    u (logarithmicResolventImaginaryOperator lambda hlambda
      (finiteCameraWhitenedNaimarkSynthesisContinuous camera G v))

theorem finiteCameraCauchyImaginaryPart_inner_nonpos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    {lambda : ℂ} (hlambda : 0 < lambda.im)
    (u : FiniteCameraCoordinates ι) :
    inner ℝ u (finiteCameraCauchyImaginaryPart camera G lambda hlambda.ne' u) ≤ 0 := by
  rw [finiteCameraCauchyImaginaryPart_inner]
  exact logarithmicResolventImaginaryOperator_inner_nonpos hlambda
    (finiteCameraWhitenedNaimarkSynthesisContinuous camera G u)

theorem finiteCameraCauchyImaginaryPart_inner_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    {lambda : ℂ} (hlambda : lambda.im < 0)
    (u : FiniteCameraCoordinates ι) :
    0 ≤ inner ℝ u (finiteCameraCauchyImaginaryPart camera G lambda hlambda.ne u) := by
  rw [finiteCameraCauchyImaginaryPart_inner]
  exact logarithmicResolventImaginaryOperator_inner_nonneg hlambda
    (finiteCameraWhitenedNaimarkSynthesisContinuous camera G u)

theorem finiteCameraCauchyImaginaryPart_inner_neg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (hGram : finiteCameraNaimarkGramMatrix camera = G)
    (hG : G.PosDef) {lambda : ℂ} (hlambda : 0 < lambda.im)
    {u : FiniteCameraCoordinates ι} (hu : u ≠ 0) :
    inner ℝ u (finiteCameraCauchyImaginaryPart camera G lambda hlambda.ne' u) < 0 := by
  rw [finiteCameraCauchyImaginaryPart_inner]
  apply logarithmicResolventImaginaryOperator_inner_neg hlambda
  intro hz
  apply hu
  apply finiteCameraWhitenedNaimarkSynthesisContinuous_injective camera G hGram hG
  exact hz.trans (map_zero (finiteCameraWhitenedNaimarkSynthesisContinuous camera G)).symm

theorem finiteCameraCauchyImaginaryPart_inner_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (hGram : finiteCameraNaimarkGramMatrix camera = G)
    (hG : G.PosDef) {lambda : ℂ} (hlambda : lambda.im < 0)
    {u : FiniteCameraCoordinates ι} (hu : u ≠ 0) :
    0 < inner ℝ u (finiteCameraCauchyImaginaryPart camera G lambda hlambda.ne u) := by
  rw [finiteCameraCauchyImaginaryPart_inner]
  apply logarithmicResolventImaginaryOperator_inner_pos hlambda
  intro hz
  apply hu
  apply finiteCameraWhitenedNaimarkSynthesisContinuous_injective camera G hGram hG
  exact hz.trans (map_zero (finiteCameraWhitenedNaimarkSynthesisContinuous camera G)).symm

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 2000000

theorem finiteCameraCauchyRealPart_inner_swap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u v : FiniteCameraCoordinates ι) :
    inner ℝ u (finiteCameraCauchyRealPart camera G lambda hlambda v) =
      inner ℝ v (finiteCameraCauchyRealPart camera G lambda hlambda u) := by
  have hR := (logarithmicResolventRealOperator_isSelfAdjoint lambda hlambda).isSymmetric
  calc
    inner ℝ u (finiteCameraCauchyRealPart camera G lambda hlambda v) =
        inner ℝ (finiteCameraWhitenedNaimarkSynthesisContinuous camera G u)
          (logarithmicResolventRealOperator lambda hlambda
            (finiteCameraWhitenedNaimarkSynthesisContinuous camera G v)) :=
      finiteCameraCauchyRealPart_inner camera G lambda hlambda u v
    _ = inner ℝ (logarithmicResolventRealOperator lambda hlambda
          (finiteCameraWhitenedNaimarkSynthesisContinuous camera G u))
        (finiteCameraWhitenedNaimarkSynthesisContinuous camera G v) :=
      (hR.apply_clm _ _).symm
    _ = inner ℝ (finiteCameraWhitenedNaimarkSynthesisContinuous camera G v)
        (logarithmicResolventRealOperator lambda hlambda
          (finiteCameraWhitenedNaimarkSynthesisContinuous camera G u)) :=
      real_inner_comm _ _
    _ = inner ℝ v (finiteCameraCauchyRealPart camera G lambda hlambda u) :=
      (finiteCameraCauchyRealPart_inner camera G lambda hlambda v u).symm


def finiteCameraRealifiedCauchyBlock
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    FiniteCameraRealification ι →L[ℝ] FiniteCameraRealification ι :=
  realifiedContinuousLinearBlock
    (finiteCameraCauchyRealPart camera G lambda hlambda)
    (finiteCameraCauchyImaginaryPart camera G lambda hlambda)

@[simp] theorem finiteCameraRealifiedCauchyBlock_fst
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (z : FiniteCameraRealification ι) :
    (finiteCameraRealifiedCauchyBlock camera G lambda hlambda z).fst =
      finiteCameraCauchyRealPart camera G lambda hlambda z.fst -
        finiteCameraCauchyImaginaryPart camera G lambda hlambda z.snd := by
  exact realifiedContinuousLinearBlock_fst _ _ _

@[simp] theorem finiteCameraRealifiedCauchyBlock_snd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (z : FiniteCameraRealification ι) :
    (finiteCameraRealifiedCauchyBlock camera G lambda hlambda z).snd =
      finiteCameraCauchyImaginaryPart camera G lambda hlambda z.fst +
        finiteCameraCauchyRealPart camera G lambda hlambda z.snd := by
  exact realifiedContinuousLinearBlock_snd _ _ _


theorem finiteCameraRealifiedCauchyBlock_skewQuadratic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (z : FiniteCameraRealification ι) :
    inner ℝ z.fst (finiteCameraRealifiedCauchyBlock camera G lambda hlambda z).snd -
        inner ℝ z.snd (finiteCameraRealifiedCauchyBlock camera G lambda hlambda z).fst =
      inner ℝ z.fst (finiteCameraCauchyImaginaryPart camera G lambda hlambda z.fst) +
        inner ℝ z.snd (finiteCameraCauchyImaginaryPart camera G lambda hlambda z.snd) := by
  rw [finiteCameraRealifiedCauchyBlock_fst,
    finiteCameraRealifiedCauchyBlock_snd]
  simp only [inner_add_right, inner_sub_right]
  have hA := finiteCameraCauchyRealPart_inner_swap camera G lambda hlambda z.fst z.snd
  linarith

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 2000000

theorem finiteCameraRealification_fst_ne_or_snd_ne
    {ι : Type*} [Fintype ι]
    {z : FiniteCameraRealification ι} (hz : z ≠ 0) :
    z.fst ≠ 0 ∨ z.snd ≠ 0 := by
  by_cases hfst : z.fst = 0
  · right
    intro hsnd
    apply hz
    apply (WithLp.ext_iff 2).2
    exact Prod.ext hfst hsnd
  · exact Or.inl hfst

theorem finiteCameraRealifiedCauchyBlock_skewQuadratic_neg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (hGram : finiteCameraNaimarkGramMatrix camera = G)
    (hG : G.PosDef) {lambda : ℂ} (hlambda : 0 < lambda.im)
    {z : FiniteCameraRealification ι} (hz : z ≠ 0) :
    inner ℝ z.fst
        (finiteCameraRealifiedCauchyBlock camera G lambda (ne_of_gt hlambda) z).snd -
        inner ℝ z.snd
        (finiteCameraRealifiedCauchyBlock camera G lambda (ne_of_gt hlambda) z).fst < 0 := by
  rw [finiteCameraRealifiedCauchyBlock_skewQuadratic]
  rcases finiteCameraRealification_fst_ne_or_snd_ne hz with hfst | hsnd
  · have hstrict := finiteCameraCauchyImaginaryPart_inner_neg
      camera G hGram hG hlambda hfst
    have hnonpos := finiteCameraCauchyImaginaryPart_inner_nonpos camera G hlambda z.snd
    linarith
  · have hnonpos := finiteCameraCauchyImaginaryPart_inner_nonpos camera G hlambda z.fst
    have hstrict := finiteCameraCauchyImaginaryPart_inner_neg
      camera G hGram hG hlambda hsnd
    linarith

theorem finiteCameraRealifiedCauchyBlock_skewQuadratic_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (hGram : finiteCameraNaimarkGramMatrix camera = G)
    (hG : G.PosDef) {lambda : ℂ} (hlambda : lambda.im < 0)
    {z : FiniteCameraRealification ι} (hz : z ≠ 0) :
    0 < inner ℝ z.fst
        (finiteCameraRealifiedCauchyBlock camera G lambda (ne_of_lt hlambda) z).snd -
        inner ℝ z.snd
        (finiteCameraRealifiedCauchyBlock camera G lambda (ne_of_lt hlambda) z).fst := by
  rw [finiteCameraRealifiedCauchyBlock_skewQuadratic]
  rcases finiteCameraRealification_fst_ne_or_snd_ne hz with hfst | hsnd
  · have hstrict := finiteCameraCauchyImaginaryPart_inner_pos
      camera G hGram hG hlambda hfst
    have hnonneg := finiteCameraCauchyImaginaryPart_inner_nonneg camera G hlambda z.snd
    linarith
  · have hnonneg := finiteCameraCauchyImaginaryPart_inner_nonneg camera G hlambda z.fst
    have hstrict := finiteCameraCauchyImaginaryPart_inner_pos
      camera G hGram hG hlambda hsnd
    linarith

theorem finiteCameraRealifiedCauchyBlock_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (hGram : finiteCameraNaimarkGramMatrix camera = G)
    (hG : G.PosDef) {lambda : ℂ} (hlambda : lambda.im ≠ 0) :
    Function.Injective (finiteCameraRealifiedCauchyBlock camera G lambda hlambda) := by
  intro z w hzw
  have hsub : z - w = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hlambda with hlower | hupper
    · have hs := finiteCameraRealifiedCauchyBlock_skewQuadratic_pos
        camera G hGram hG hlower hne
      have hkernel : finiteCameraRealifiedCauchyBlock camera G lambda (ne_of_lt hlower)
          (z - w) = 0 := by
        rw [map_sub, hzw, sub_self]
      rw [hkernel] at hs
      simp at hs
    · have hs := finiteCameraRealifiedCauchyBlock_skewQuadratic_neg
        camera G hGram hG hupper hne
      have hkernel : finiteCameraRealifiedCauchyBlock camera G lambda (ne_of_gt hupper)
          (z - w) = 0 := by
        rw [map_sub, hzw, sub_self]
      rw [hkernel] at hs
      simp at hs
  exact sub_eq_zero.mp hsub

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 2000000

theorem finiteCameraRealifiedCauchyBlock_surjective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (hGram : finiteCameraNaimarkGramMatrix camera = G)
    (hG : G.PosDef) {lambda : ℂ} (hlambda : lambda.im ≠ 0) :
    Function.Surjective (finiteCameraRealifiedCauchyBlock camera G lambda hlambda) := by
  apply (LinearMap.injective_iff_surjective).mp
  exact finiteCameraRealifiedCauchyBlock_injective camera G hGram hG hlambda

theorem finiteCameraRealifiedCauchyBlock_bijective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (hGram : finiteCameraNaimarkGramMatrix camera = G)
    (hG : G.PosDef) {lambda : ℂ} (hlambda : lambda.im ≠ 0) :
    Function.Bijective (finiteCameraRealifiedCauchyBlock camera G lambda hlambda) :=
  ⟨finiteCameraRealifiedCauchyBlock_injective camera G hGram hG hlambda,
    finiteCameraRealifiedCauchyBlock_surjective camera G hGram hG hlambda⟩

def finiteCameraRealifiedCauchyEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (hGram : finiteCameraNaimarkGramMatrix camera = G)
    (hG : G.PosDef) :
    FiniteCameraRealification ι ≃ₗ[ℝ] FiniteCameraRealification ι :=
  LinearEquiv.ofBijective
    (finiteCameraRealifiedCauchyBlock camera G lambda hlambda).toLinearMap
    (finiteCameraRealifiedCauchyBlock_bijective camera G hGram hG hlambda)

def finiteCameraIntrinsicWeylEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (hGram : finiteCameraNaimarkGramMatrix camera = G)
    (hG : G.PosDef) :
    FiniteCameraRealification ι ≃ₗ[ℝ] FiniteCameraRealification ι :=
  (finiteCameraRealifiedCauchyEquiv camera G lambda hlambda hGram hG).symm

def finiteCameraIntrinsicWeylBlock
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (hGram : finiteCameraNaimarkGramMatrix camera = G)
    (hG : G.PosDef) :
    FiniteCameraRealification ι →L[ℝ] FiniteCameraRealification ι :=
  LinearMap.toContinuousLinearMap
    (finiteCameraIntrinsicWeylEquiv camera G lambda hlambda hGram hG).toLinearMap

theorem finiteCameraIntrinsicWeylBlock_comp_cauchy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (hGram : finiteCameraNaimarkGramMatrix camera = G)
    (hG : G.PosDef) (z : FiniteCameraRealification ι) :
    finiteCameraIntrinsicWeylBlock camera G lambda hlambda hGram hG
      (finiteCameraRealifiedCauchyBlock camera G lambda hlambda z) = z := by
  change (finiteCameraIntrinsicWeylEquiv camera G lambda hlambda hGram hG)
      ((finiteCameraRealifiedCauchyEquiv camera G lambda hlambda hGram hG) z) = z
  exact (finiteCameraRealifiedCauchyEquiv camera G lambda hlambda hGram hG).symm_apply_apply z

theorem finiteCameraRealifiedCauchyBlock_comp_intrinsicWeyl
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (hGram : finiteCameraNaimarkGramMatrix camera = G)
    (hG : G.PosDef) (z : FiniteCameraRealification ι) :
    finiteCameraRealifiedCauchyBlock camera G lambda hlambda
      (finiteCameraIntrinsicWeylBlock camera G lambda hlambda hGram hG z) = z := by
  change (finiteCameraRealifiedCauchyEquiv camera G lambda hlambda hGram hG)
      ((finiteCameraIntrinsicWeylEquiv camera G lambda hlambda hGram hG) z) = z
  exact (finiteCameraRealifiedCauchyEquiv camera G lambda hlambda hGram hG).apply_symm_apply z

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 2000000

def finiteCameraRealifiedNaimarkEmbedding
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ) :
    FiniteCameraRealification ι →L[ℝ] RealifiedNaimarkComplexification :=
  realifiedContinuousLinearBlock
    (finiteCameraWhitenedNaimarkSynthesisContinuous camera G) 0

@[simp] theorem finiteCameraRealifiedNaimarkEmbedding_fst
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (z : FiniteCameraRealification ι) :
    (finiteCameraRealifiedNaimarkEmbedding camera G z).fst =
      finiteCameraWhitenedNaimarkSynthesisContinuous camera G z.fst := by
  simp [finiteCameraRealifiedNaimarkEmbedding]

@[simp] theorem finiteCameraRealifiedNaimarkEmbedding_snd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (z : FiniteCameraRealification ι) :
    (finiteCameraRealifiedNaimarkEmbedding camera G z).snd =
      finiteCameraWhitenedNaimarkSynthesisContinuous camera G z.snd := by
  simp [finiteCameraRealifiedNaimarkEmbedding]

def finiteCameraRealifiedCauchyCompression
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    FiniteCameraRealification ι →L[ℝ] FiniteCameraRealification ι :=
  (finiteCameraRealifiedNaimarkEmbedding camera G).adjoint ∘L
    (logarithmicResolventBlock lambda hlambda ∘L
      finiteCameraRealifiedNaimarkEmbedding camera G)

theorem finiteCameraRealifiedCauchyCompression_inner
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (z w : FiniteCameraRealification ι) :
    inner ℝ z (finiteCameraRealifiedCauchyCompression camera G lambda hlambda w) =
      inner ℝ (finiteCameraRealifiedNaimarkEmbedding camera G z)
        (logarithmicResolventBlock lambda hlambda
          (finiteCameraRealifiedNaimarkEmbedding camera G w)) := by
  rw [finiteCameraRealifiedCauchyCompression, ContinuousLinearMap.comp_apply]
  exact (finiteCameraRealifiedNaimarkEmbedding camera G).adjoint_inner_right
    z (logarithmicResolventBlock lambda hlambda
      (finiteCameraRealifiedNaimarkEmbedding camera G w))

theorem finiteCameraRealifiedCauchyBlock_inner_ambient
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (camera : ι → CameraIndex) (G : Matrix ι ι ℝ)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (z w : FiniteCameraRealification ι) :
    inner ℝ z (finiteCameraRealifiedCauchyBlock camera G lambda hlambda w) =
      inner ℝ (finiteCameraRealifiedNaimarkEmbedding camera G z)
        (logarithmicResolventBlock lambda hlambda
          (finiteCameraRealifiedNaimarkEmbedding camera G w)) := by
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change
    inner ℝ z.fst (finiteCameraRealifiedCauchyBlock camera G lambda hlambda w).fst +
        inner ℝ z.snd (finiteCameraRealifiedCauchyBlock camera G lambda hlambda w).snd =
      inner ℝ (finiteCameraRealifiedNaimarkEmbedding camera G z).fst
        (logarithmicResolventBlock lambda hlambda
          (finiteCameraRealifiedNaimarkEmbedding camera G w)).fst +
        inner ℝ (finiteCameraRealifiedNaimarkEmbedding camera G z).snd
        (logarithmicResolventBlock lambda hlambda
          (finiteCameraRealifiedNaimarkEmbedding camera G w)).snd
  rw [finiteCameraRealifiedNaimarkEmbedding_fst,
    finiteCameraRealifiedNaimarkEmbedding_snd,
    logarithmicResolventBlock_fst,
    logarithmicResolventBlock_snd,
    finiteCameraRealifiedNaimarkEmbedding_fst,
    finiteCameraRealifiedNaimarkEmbedding_snd]
  rw [finiteCameraRealifiedCauchyBlock_fst,
    finiteCameraRealifiedCauchyBlock_snd]
  simp only [inner_add_right, inner_sub_right]
  rw [finiteCameraCauchyRealPart_inner,
    finiteCameraCauchyImaginaryPart_inner,
    finiteCameraCauchyImaginaryPart_inner,
    finiteCameraCauchyRealPart_inner]

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 2000000

abbrev SixCameraRealification := FiniteCameraRealification (Fin 6)

def sixCameraRealifiedCauchyBlock
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    SixCameraRealification →L[ℝ] SixCameraRealification :=
  finiteCameraRealifiedCauchyBlock atlasSixCameraIndex sixCameraGram lambda hlambda

theorem sixCameraRealifiedCauchyBlock_injective
    {lambda : ℂ} (hlambda : lambda.im ≠ 0) :
    Function.Injective (sixCameraRealifiedCauchyBlock lambda hlambda) := by
  exact finiteCameraRealifiedCauchyBlock_injective atlasSixCameraIndex sixCameraGram
    finiteCameraNaimarkGramMatrix_six_eq sixCameraGram_posDef hlambda

theorem sixCameraRealifiedCauchyBlock_surjective
    {lambda : ℂ} (hlambda : lambda.im ≠ 0) :
    Function.Surjective (sixCameraRealifiedCauchyBlock lambda hlambda) := by
  exact finiteCameraRealifiedCauchyBlock_surjective atlasSixCameraIndex sixCameraGram
    finiteCameraNaimarkGramMatrix_six_eq sixCameraGram_posDef hlambda

theorem sixCameraRealifiedCauchyBlock_bijective
    {lambda : ℂ} (hlambda : lambda.im ≠ 0) :
    Function.Bijective (sixCameraRealifiedCauchyBlock lambda hlambda) := by
  exact finiteCameraRealifiedCauchyBlock_bijective atlasSixCameraIndex sixCameraGram
    finiteCameraNaimarkGramMatrix_six_eq sixCameraGram_posDef hlambda

def sixCameraRealifiedCauchyEquiv
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    SixCameraRealification ≃ₗ[ℝ] SixCameraRealification :=
  finiteCameraRealifiedCauchyEquiv atlasSixCameraIndex sixCameraGram lambda hlambda
    finiteCameraNaimarkGramMatrix_six_eq sixCameraGram_posDef

def sixCameraIntrinsicWeylEquiv
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    SixCameraRealification ≃ₗ[ℝ] SixCameraRealification :=
  sixCameraRealifiedCauchyEquiv lambda hlambda |>.symm

def sixCameraIntrinsicWeylBlock
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    SixCameraRealification →L[ℝ] SixCameraRealification :=
  LinearMap.toContinuousLinearMap (sixCameraIntrinsicWeylEquiv lambda hlambda).toLinearMap

theorem sixCameraIntrinsicWeylBlock_comp_cauchy
    {lambda : ℂ} (hlambda : lambda.im ≠ 0) (z : SixCameraRealification) :
    sixCameraIntrinsicWeylBlock lambda hlambda
      (sixCameraRealifiedCauchyBlock lambda hlambda z) = z := by
  change (sixCameraIntrinsicWeylEquiv lambda hlambda)
      ((sixCameraRealifiedCauchyEquiv lambda hlambda) z) = z
  exact (sixCameraRealifiedCauchyEquiv lambda hlambda).symm_apply_apply z

theorem sixCameraRealifiedCauchyBlock_comp_intrinsicWeyl
    {lambda : ℂ} (hlambda : lambda.im ≠ 0) (z : SixCameraRealification) :
    sixCameraRealifiedCauchyBlock lambda hlambda
      (sixCameraIntrinsicWeylBlock lambda hlambda z) = z := by
  change (sixCameraRealifiedCauchyEquiv lambda hlambda)
      ((sixCameraIntrinsicWeylEquiv lambda hlambda) z) = z
  exact (sixCameraRealifiedCauchyEquiv lambda hlambda).apply_symm_apply z

end
end CarrySelfAdjointOperator
