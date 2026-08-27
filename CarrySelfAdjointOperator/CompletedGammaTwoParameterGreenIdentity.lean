import CarrySelfAdjointOperator.RealLinearPMapComplexification
import NativeCarrySpectralWeyl.Boundary.GammaField
import Mathlib.Tactic

/-!
# Polarized two-parameter identity for the carry gamma field

The realified carry gamma field retains both quadratures of the camera source
and of the ambient Naimark state.  This file equips that same `L2` product
with its canonical complex Hilbert structure and polarizes the source-relation
Green identity at two independent spectral parameters.

For the resolvent convention `(lambda - Y)^(-1)`, the compressed Cauchy
readout is anti-Herglotz.  After the canonical minus rotation, its divided
difference is exactly the positive Hilbert Gram of the two gamma states.  No
quadrature, camera, provenance, or residual coordinate is projected away.
-/

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

abbrev CarryGammaComplexCamera :=
  RealHilbertComplexification CameraHilbert

abbrev CarryGammaComplexNaimark :=
  RealHilbertComplexification NaimarkSpace

/-- The existing realified gamma field, read in the canonical complex Hilbert
structure on the same two-quadrature carrier. -/
def carryGammaComplexState
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (source : CarryGammaComplexCamera) : CarryGammaComplexNaimark :=
  carryGammaSource lambda hlambda source

/-- The compressed Cauchy boundary value in the same complexified camera
carrier. -/
def carryGammaComplexCauchyReadout
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (source : CarryGammaComplexCamera) : CarryGammaComplexCamera :=
  allBasesCauchyBlock lambda hlambda source

/-- Two independent gamma states satisfy the fully polarized Weyl identity.
Both real quadratures are retained.  The right side is the boundary readout;
the left side is the complex Hilbert product of the same two ambient states. -/
theorem carryGammaComplex_twoParameter_greenIdentity
    (lambda mu : ℂ) (hlambda : lambda.im ≠ 0) (hmu : mu.im ≠ 0)
    (u v : CarryGammaComplexCamera) :
    (conj lambda - mu) *
        inner ℂ
          (carryGammaComplexState lambda hlambda u)
          (carryGammaComplexState mu hmu v) =
      inner ℂ u (carryGammaComplexCauchyReadout mu hmu v) -
        inner ℂ (carryGammaComplexCauchyReadout lambda hlambda u) v := by
  let f : CarryGammaComplexNaimark := carryGammaSource lambda hlambda u
  let g : CarryGammaComplexNaimark := carryGammaSource mu hmu v

  have hLambdaFst :
      lambda.re • f.fst - lambda.im • f.snd =
        logarithmicMultiplication (carryGammaIntoDomain lambda hlambda u).1 +
          naimarkIsometry u.fst := by
    have h := congrArg WithLp.fst
      (carryGammaSource_defect_equation lambda hlambda u)
    simpa only [f, realifiedNaimarkScalar_fst, WithLp.add_fst,
      realifiedLogarithmicMultiplication_fst,
      realifiedNaimarkPort_fst] using h
  have hLambdaSnd :
      lambda.im • f.fst + lambda.re • f.snd =
        logarithmicMultiplication (carryGammaIntoDomain lambda hlambda u).2 +
          naimarkIsometry u.snd := by
    have h := congrArg WithLp.snd
      (carryGammaSource_defect_equation lambda hlambda u)
    simpa only [f, realifiedNaimarkScalar_snd, WithLp.add_snd,
      realifiedLogarithmicMultiplication_snd,
      realifiedNaimarkPort_snd] using h
  have hMuFst :
      mu.re • g.fst - mu.im • g.snd =
        logarithmicMultiplication (carryGammaIntoDomain mu hmu v).1 +
          naimarkIsometry v.fst := by
    have h := congrArg WithLp.fst
      (carryGammaSource_defect_equation mu hmu v)
    simpa only [g, realifiedNaimarkScalar_fst, WithLp.add_fst,
      realifiedLogarithmicMultiplication_fst,
      realifiedNaimarkPort_fst] using h
  have hMuSnd :
      mu.im • g.fst + mu.re • g.snd =
        logarithmicMultiplication (carryGammaIntoDomain mu hmu v).2 +
          naimarkIsometry v.snd := by
    have h := congrArg WithLp.snd
      (carryGammaSource_defect_equation mu hmu v)
    simpa only [g, realifiedNaimarkScalar_snd, WithLp.add_snd,
      realifiedLogarithmicMultiplication_snd,
      realifiedNaimarkPort_snd] using h

  have h11 := carrySourceRelation_weyl_green_identity
    (carrySourceRelationElement
      (carryGammaIntoDomain lambda hlambda u).1 u.fst)
    (carrySourceRelationElement
      (carryGammaIntoDomain mu hmu v).1 v.fst)
  have h12 := carrySourceRelation_weyl_green_identity
    (carrySourceRelationElement
      (carryGammaIntoDomain lambda hlambda u).1 u.fst)
    (carrySourceRelationElement
      (carryGammaIntoDomain mu hmu v).2 v.snd)
  have h21 := carrySourceRelation_weyl_green_identity
    (carrySourceRelationElement
      (carryGammaIntoDomain lambda hlambda u).2 u.snd)
    (carrySourceRelationElement
      (carryGammaIntoDomain mu hmu v).1 v.fst)
  have h22 := carrySourceRelation_weyl_green_identity
    (carrySourceRelationElement
      (carryGammaIntoDomain lambda hlambda u).2 u.snd)
    (carrySourceRelationElement
      (carryGammaIntoDomain mu hmu v).2 v.snd)
  simp only [coe_carrySourceRelationElement,
    carryWeylBoundaryMap_element,
    carryGammaIntoDomain_fst_coe,
    carryGammaIntoDomain_snd_coe] at h11 h12 h21 h22
  rw [← hLambdaFst, ← hMuFst] at h11
  rw [← hLambdaFst, ← hMuSnd] at h12
  rw [← hLambdaSnd, ← hMuFst] at h21
  rw [← hLambdaSnd, ← hMuSnd] at h22

  have hCauchyLambda :
      realifiedNaimarkAdjoint f =
        allBasesCauchyBlock lambda hlambda u := by
    simpa only [f, carryDefectGammaZero,
      ContinuousLinearMap.comp_apply] using
      (carryDefectGammaZero_apply lambda hlambda u)
  have hCauchyMu :
      realifiedNaimarkAdjoint g =
        allBasesCauchyBlock mu hmu v := by
    simpa only [g, carryDefectGammaZero,
      ContinuousLinearMap.comp_apply] using
      (carryDefectGammaZero_apply mu hmu v)
  have hCauchyLambdaFst := congrArg WithLp.fst hCauchyLambda
  have hCauchyLambdaSnd := congrArg WithLp.snd hCauchyLambda
  have hCauchyMuFst := congrArg WithLp.fst hCauchyMu
  have hCauchyMuSnd := congrArg WithLp.snd hCauchyMu
  simp only [realifiedNaimarkAdjoint_fst] at hCauchyLambdaFst hCauchyMuFst
  simp only [realifiedNaimarkAdjoint_snd] at hCauchyLambdaSnd hCauchyMuSnd
  rw [hCauchyLambdaFst, hCauchyMuFst] at h11
  rw [hCauchyLambdaFst, hCauchyMuSnd] at h12
  rw [hCauchyLambdaSnd, hCauchyMuFst] at h21
  rw [hCauchyLambdaSnd, hCauchyMuSnd] at h22
  simp only [greenForm] at h11 h12 h21 h22

  change
    inner ℝ (lambda.re • f.fst - lambda.im • f.snd) g.fst -
        inner ℝ f.fst (mu.re • g.fst - mu.im • g.snd) = _ at h11
  change
    inner ℝ (lambda.re • f.fst - lambda.im • f.snd) g.snd -
        inner ℝ f.fst (mu.im • g.fst + mu.re • g.snd) = _ at h12
  change
    inner ℝ (lambda.im • f.fst + lambda.re • f.snd) g.fst -
        inner ℝ f.snd (mu.re • g.fst - mu.im • g.snd) = _ at h21
  change
    inner ℝ (lambda.im • f.fst + lambda.re • f.snd) g.snd -
        inner ℝ f.snd (mu.im • g.fst + mu.re • g.snd) = _ at h22
  simp only [inner_sub_left, inner_add_left, inner_sub_right,
    inner_add_right, real_inner_smul_left, real_inner_smul_right] at h11 h12 h21 h22

  change (conj lambda - mu) * inner ℂ f g =
    inner ℂ u (carryGammaComplexCauchyReadout mu hmu v) -
      inner ℂ (carryGammaComplexCauchyReadout lambda hlambda u) v
  have hfgRe : (inner ℂ f g).re =
      inner ℝ f.fst g.fst + inner ℝ f.snd g.snd := by
    simp only [RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_re]
    rfl
  have hfgIm : (inner ℂ f g).im =
      inner ℝ f.fst g.snd - inner ℝ f.snd g.fst := by
    simp only [RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_im]
    rfl
  have huMuRe :
      (inner ℂ u (carryGammaComplexCauchyReadout mu hmu v)).re =
        inner ℝ u.fst (allBasesCauchyBlock mu hmu v).fst +
          inner ℝ u.snd (allBasesCauchyBlock mu hmu v).snd := by
    simp only [RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_re]
    rfl
  have huMuIm :
      (inner ℂ u (carryGammaComplexCauchyReadout mu hmu v)).im =
        inner ℝ u.fst (allBasesCauchyBlock mu hmu v).snd -
          inner ℝ u.snd (allBasesCauchyBlock mu hmu v).fst := by
    simp only [RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_im]
    rfl
  have hLambdaVRe :
      (inner ℂ (carryGammaComplexCauchyReadout lambda hlambda u) v).re =
        inner ℝ (allBasesCauchyBlock lambda hlambda u).fst v.fst +
          inner ℝ (allBasesCauchyBlock lambda hlambda u).snd v.snd := by
    simp only [RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_re]
    rfl
  have hLambdaVIm :
      (inner ℂ (carryGammaComplexCauchyReadout lambda hlambda u) v).im =
        inner ℝ (allBasesCauchyBlock lambda hlambda u).fst v.snd -
          inner ℝ (allBasesCauchyBlock lambda hlambda u).snd v.fst := by
    simp only [RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_im]
    rfl
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.sub_re, Complex.conj_re,
      Complex.sub_im, Complex.conj_im]
    rw [hfgRe, hfgIm, huMuRe, hLambdaVRe]
    linear_combination h11 + h22
  · simp only [Complex.mul_im, Complex.sub_re, Complex.conj_re,
      Complex.sub_im, Complex.conj_im]
    rw [hfgRe, hfgIm, huMuIm, hLambdaVIm]
    linear_combination h12 - h21

/-! ## Source-varying positive boundary kernel -/

/-- Oriented two-source boundary readout.  The source may depend on the
spectral parameter; the two resulting vectors nevertheless live in the same
global camera Hilbert space. -/
def carryGammaPolarizedBoundaryReadout
    (source : ℂ → CarryGammaComplexCamera)
    (lambda mu : ℂ) (hlambda : lambda.im ≠ 0) (hmu : mu.im ≠ 0) : ℂ :=
  inner ℂ
      (carryGammaComplexCauchyReadout lambda hlambda (source lambda))
      (source mu) -
    inner ℂ (source lambda)
      (carryGammaComplexCauchyReadout mu hmu (source mu))

/-- The complete source-varying boundary readout is a positive Hilbert Gram
multiplied by the spectral separation.  No equality between the two sources,
coordinate projection, or scalar cancellation is used. -/
theorem carryGammaPolarizedBoundaryReadout_eq_inner
    (source : ℂ → CarryGammaComplexCamera)
    (lambda mu : ℂ) (hlambda : lambda.im ≠ 0) (hmu : mu.im ≠ 0) :
    carryGammaPolarizedBoundaryReadout source lambda mu hlambda hmu =
      (mu - conj lambda) *
        inner ℂ
          (carryGammaComplexState lambda hlambda (source lambda))
          (carryGammaComplexState mu hmu (source mu)) := by
  have hgreen := carryGammaComplex_twoParameter_greenIdentity
    lambda mu hlambda hmu (source lambda) (source mu)
  unfold carryGammaPolarizedBoundaryReadout
  calc
    inner ℂ
          (carryGammaComplexCauchyReadout lambda hlambda (source lambda))
          (source mu) -
        inner ℂ (source lambda)
          (carryGammaComplexCauchyReadout mu hmu (source mu)) =
      -((conj lambda - mu) *
        inner ℂ
          (carryGammaComplexState lambda hlambda (source lambda))
          (carryGammaComplexState mu hmu (source mu))) := by
        rw [hgreen]
        ring
    _ = _ := by ring

/-- On the diagonal the oriented boundary readout is exactly the spectral
jump times the squared norm of the full two-quadrature gamma state. -/
theorem carryGammaPolarizedBoundaryReadout_diagonal_eq_norm_sq
    (source : ℂ → CarryGammaComplexCamera)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    carryGammaPolarizedBoundaryReadout source lambda lambda hlambda hlambda =
      (lambda - conj lambda) *
        ((‖carryGammaComplexState lambda hlambda (source lambda)‖ : ℝ) : ℂ) ^ 2 := by
  rw [carryGammaPolarizedBoundaryReadout_eq_inner]
  simp [inner_self_eq_norm_sq_to_K]

/-- Once the nonzero spectral separation is exposed, identifying any scalar
kernel with the gamma Gram is equivalent to identifying its numerator with
the complete boundary readout.  This is an equivalence, not a new
scalarization hypothesis. -/
theorem carryGammaComplex_inner_eq_kernel_iff_boundaryReadout_eq
    (source : ℂ → CarryGammaComplexCamera)
    (kernel : ℂ → ℂ → ℂ)
    (lambda mu : ℂ) (hlambda : lambda.im ≠ 0) (hmu : mu.im ≠ 0)
    (hseparation : mu - conj lambda ≠ 0) :
    inner ℂ
        (carryGammaComplexState lambda hlambda (source lambda))
        (carryGammaComplexState mu hmu (source mu)) =
        kernel lambda mu ↔
      carryGammaPolarizedBoundaryReadout source lambda mu hlambda hmu =
        (mu - conj lambda) * kernel lambda mu := by
  rw [carryGammaPolarizedBoundaryReadout_eq_inner]
  constructor
  · intro h
    rw [h]
  · intro h
    exact mul_left_cancel₀ hseparation h

/-- Fixed-source anti-Weyl scalar response.  The minus sign is the canonical
rotation from the anti-Herglotz Cauchy convention to a positive kernel. -/
def carryGammaAntiWeylResponse
    (source : CarryGammaComplexCamera)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) : ℂ :=
  -inner ℂ source (carryGammaComplexCauchyReadout lambda hlambda source)

/-- Division-free positive-kernel identity for one unchanged source.  The
same two-quadrature gamma state occurs on both sides, so positivity is not
obtained by scalar cancellation or by deleting a channel. -/
theorem carryGammaAntiWeylResponse_twoParameter_eq_inner
    (source : CarryGammaComplexCamera)
    (lambda mu : ℂ) (hlambda : lambda.im ≠ 0) (hmu : mu.im ≠ 0) :
    carryGammaAntiWeylResponse source mu hmu -
        conj (carryGammaAntiWeylResponse source lambda hlambda) =
      (mu - conj lambda) *
        inner ℂ
          (carryGammaComplexState lambda hlambda source)
          (carryGammaComplexState mu hmu source) := by
  have hgreen := carryGammaComplex_twoParameter_greenIdentity
    lambda mu hlambda hmu source source
  unfold carryGammaAntiWeylResponse
  rw [map_neg, inner_conj_symm]
  linear_combination hgreen

/-- The diagonal anti-Weyl boundary difference is the nonnegative gamma
energy multiplied by the spectral jump. -/
theorem carryGammaAntiWeylResponse_diagonal_eq_norm_sq
    (source : CarryGammaComplexCamera)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    carryGammaAntiWeylResponse source lambda hlambda -
        conj
          (carryGammaAntiWeylResponse source lambda hlambda) =
      (lambda - conj lambda) *
        ((‖carryGammaComplexState lambda hlambda source‖ : ℝ) : ℂ) ^ 2 := by
  rw [carryGammaAntiWeylResponse_twoParameter_eq_inner]
  simp [inner_self_eq_norm_sq_to_K]

end

end CarrySelfAdjointOperator
