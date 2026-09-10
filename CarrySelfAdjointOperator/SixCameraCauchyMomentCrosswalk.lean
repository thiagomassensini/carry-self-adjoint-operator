import CarrySelfAdjointOperator.SixCameraCenteredGlobalHaloDecision
import NativeCarrySpectralWeyl.Infinite.WeylInverse
import NativeCarrySpectralWeyl.Infinite.ComplexifiedCauchy
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# Six-camera compression of the all-bases Cauchy family

This module records the typed finite-coordinate compression that is available
in the current pin.  The six-camera coordinates are first whitened with the
existing sixCameraGram inverse square root, embedded in the completed
CameraHilbert, and then put into the realified camera complexification used
by allBasesCauchyBlock.

The resulting Cauchy object is a literal compression by an adjoint; it is not
an independently invented six-by-six moment model.  The global Weyl inverse
remains the densely defined LinearPMap from Infinite/WeylInverse.lean.
Consequently this file proves the exact compression and scalar resolvent
identities, while recording the missing finite-moment/asymptotic bridge rather
than asserting a false inverse-of-compression identity.
-/

open scoped BigOperators ENNReal MeasureTheory RealInnerProductSpace Matrix
  MatrixOrder ComplexConjugate
open Set MeasureTheory Filter

noncomputable section

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera

set_option autoImplicit false

/-! ## The whitened six-camera coordinate inclusion -/

/-- Extension-by-zero of six labelled camera coordinates to the finitely
supported all-camera coefficient space. -/
def sixCameraCauchyCameraFinsuppMap :
    (Fin 6 → ℝ) →ₗ[ℝ] CameraFinsupp where
  toFun c := ∑ i : Fin 6,
    Finsupp.single (atlasSixCameraIndex i) (c i)
  map_add' c d := by
    classical
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finsupp.single_add]
  map_smul' a c := by
    classical
    simp only [Pi.smul_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change Finsupp.single (atlasSixCameraIndex i) (a * c i) =
      a • Finsupp.single (atlasSixCameraIndex i) (c i)
    simp [smul_eq_mul]

@[simp] theorem sixCameraCauchyCameraFinsuppMap_apply (c : Fin 6 → ℝ) :
    sixCameraCauchyCameraFinsuppMap c = ∑ i : Fin 6,
      Finsupp.single (atlasSixCameraIndex i) (c i) := by
  rfl

/-- The raw six-camera synthesis into the completed all-camera Hilbert space. -/
def sixCameraCauchyCameraHilbertSynthesisLinear :
    (Fin 6 → ℝ) →ₗ[ℝ] CameraHilbert :=
  cameraEmbedding.toLinearMap.comp sixCameraCauchyCameraFinsuppMap

@[simp] theorem sixCameraCauchyCameraHilbertSynthesisLinear_apply
    (c : Fin 6 → ℝ) :
    sixCameraCauchyCameraHilbertSynthesisLinear c =
      atlasSixCameraHilbertEmbedding c := by
  classical
  change cameraEmbedding (∑ i : Fin 6,
      Finsupp.single (atlasSixCameraIndex i) (c i)) =
    atlasSixCameraHilbertEmbedding c
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show Finsupp.single (atlasSixCameraIndex i) (c i) =
      c i • Finsupp.single (atlasSixCameraIndex i) 1 by
    ext j
    by_cases h : atlasSixCameraIndex i = j <;> simp [h]]
  rw [map_smul, cameraVector]

/-- The whitened six-camera synthesis into the completed CameraHilbert. -/
def sixCameraCauchyWhitenedHilbertSynthesisLinear :
    (Fin 6 → ℝ) →ₗ[ℝ] CameraHilbert :=
  sixCameraCauchyCameraHilbertSynthesisLinear.comp
    (Matrix.mulVecLin (positiveInverseSqrt sixCameraGram))

@[simp] theorem sixCameraCauchyWhitenedHilbertSynthesisLinear_apply
    (c : Fin 6 → ℝ) :
    sixCameraCauchyWhitenedHilbertSynthesisLinear c =
      sixCameraWhitenedCameraHilbertEmbedding c := by
  rw [sixCameraCauchyWhitenedHilbertSynthesisLinear,
    LinearMap.comp_apply,
    sixCameraCauchyCameraHilbertSynthesisLinear_apply]
  rfl

/-- The same synthesis with the finite coordinate space equipped with its
canonical Euclidean inner product. -/
def sixCameraCauchyWhitenedHilbertSynthesisLinearE :
    EuclideanSpace ℝ (Fin 6) →ₗ[ℝ] CameraHilbert where
  toFun c := sixCameraCauchyWhitenedHilbertSynthesisLinear c.ofLp
  map_add' c d := by
    rw [show (c + d).ofLp = c.ofLp + d.ofLp by rfl]
    rw [map_add]
  map_smul' a c := by
    rw [show (a • c).ofLp = a • c.ofLp by rfl]
    change sixCameraCauchyWhitenedHilbertSynthesisLinear (a • c.ofLp) =
      a • sixCameraCauchyWhitenedHilbertSynthesisLinear c.ofLp
    exact sixCameraCauchyWhitenedHilbertSynthesisLinear.map_smul a c.ofLp

/-- Continuous version of the whitened six-camera synthesis. -/
def sixCameraCauchyWhitenedHilbertSynthesisContinuous :
    EuclideanSpace ℝ (Fin 6) →L[ℝ] CameraHilbert :=
  LinearMap.toContinuousLinearMap sixCameraCauchyWhitenedHilbertSynthesisLinearE

@[simp] theorem sixCameraCauchyWhitenedHilbertSynthesisContinuous_apply
    (c : EuclideanSpace ℝ (Fin 6)) :
    sixCameraCauchyWhitenedHilbertSynthesisContinuous c =
      sixCameraWhitenedCameraHilbertEmbedding c.ofLp := by
  change sixCameraCauchyWhitenedHilbertSynthesisLinear c.ofLp = _
  exact sixCameraCauchyWhitenedHilbertSynthesisLinear_apply c.ofLp

/-- The whitened six-camera inclusion is an isometry for the standard finite
Euclidean inner product. -/
theorem sixCameraCauchyWhitenedHilbertSynthesisContinuous_inner
    (u v : EuclideanSpace ℝ (Fin 6)) :
    inner ℝ (sixCameraCauchyWhitenedHilbertSynthesisContinuous u)
        (sixCameraCauchyWhitenedHilbertSynthesisContinuous v) =
      inner ℝ u v := by
  calc
    inner ℝ (sixCameraCauchyWhitenedHilbertSynthesisContinuous u)
        (sixCameraCauchyWhitenedHilbertSynthesisContinuous v) =
      inner ℝ (naimarkIsometry
          (sixCameraCauchyWhitenedHilbertSynthesisContinuous u))
        (naimarkIsometry
          (sixCameraCauchyWhitenedHilbertSynthesisContinuous v)) := by
      rw [naimarkIsometry_inner]
    _ = inner ℝ (sixCameraWhitenedNaimarkSynthesis u.ofLp)
        (sixCameraWhitenedNaimarkSynthesis v.ofLp) := by
      rw [sixCameraCauchyWhitenedHilbertSynthesisContinuous_apply,
        sixCameraCauchyWhitenedHilbertSynthesisContinuous_apply,
        naimarkIsometry_sixCameraWhitenedCameraHilbertEmbedding,
        naimarkIsometry_sixCameraWhitenedCameraHilbertEmbedding]
    _ = inner ℝ u v := by
      rw [sixCameraWhitenedNaimarkSynthesis_inner]
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [star_trivial]
      exact dotProduct_comm _ _

/-- The all-bases Naimark realization of the whitened finite synthesis is the
existing six-camera Naimark synthesis. -/
theorem naimarkIsometry_sixCameraCauchyWhitenedHilbertSynthesis
    (c : EuclideanSpace ℝ (Fin 6)) :
    naimarkIsometry
        (sixCameraCauchyWhitenedHilbertSynthesisContinuous c) =
      sixCameraWhitenedNaimarkSynthesis c.ofLp := by
  rw [sixCameraCauchyWhitenedHilbertSynthesisContinuous_apply]
  exact naimarkIsometry_sixCameraWhitenedCameraHilbertEmbedding c.ofLp

/-! ## Realification and literal Cauchy compression -/

/-- Put a real six-camera vector in the first coordinate of the canonical
realified complexification.  The second coordinate is exactly zero. -/
def sixCameraCauchyRealifiedEmbedding :
    EuclideanSpace ℝ (Fin 6) →L[ℝ] RealifiedCameraComplexification :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ CameraHilbert CameraHilbert).symm.toContinuousLinearMap ∘L
    (sixCameraCauchyWhitenedHilbertSynthesisContinuous.prod
      (0 : EuclideanSpace ℝ (Fin 6) →L[ℝ] CameraHilbert))

@[simp] theorem sixCameraCauchyRealifiedEmbedding_toPair
    (c : EuclideanSpace ℝ (Fin 6)) :
    (WithLp.prodContinuousLinearEquiv 2 ℝ CameraHilbert CameraHilbert)
        (sixCameraCauchyRealifiedEmbedding c) =
      (sixCameraWhitenedCameraHilbertEmbedding c.ofLp,
        (0 : CameraHilbert)) := by
  simp [sixCameraCauchyRealifiedEmbedding, ContinuousLinearMap.comp_apply]

/-- The literal six-camera compression of the full realified Cauchy block.
It is defined by the embedding and its Hilbert adjoint. -/
def sixCameraRealifiedCauchyCompression (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    EuclideanSpace ℝ (Fin 6) →L[ℝ] EuclideanSpace ℝ (Fin 6) :=
  sixCameraCauchyRealifiedEmbedding.adjoint ∘L
    (allBasesCauchyBlock lambda hlambda ∘L
      sixCameraCauchyRealifiedEmbedding)

/-- Exact pairing formula for the compressed realified Cauchy block. -/
theorem sixCameraRealifiedCauchyCompression_inner (lambda : ℂ)
    (hlambda : lambda.im ≠ 0)
    (u v : EuclideanSpace ℝ (Fin 6)) :
    inner ℝ u (sixCameraRealifiedCauchyCompression lambda hlambda v) =
      inner ℝ (sixCameraCauchyRealifiedEmbedding u)
        (allBasesCauchyBlock lambda hlambda
          (sixCameraCauchyRealifiedEmbedding v)) := by
  rw [sixCameraRealifiedCauchyCompression, ContinuousLinearMap.comp_apply]
  exact sixCameraCauchyRealifiedEmbedding.adjoint_inner_right u
    (allBasesCauchyBlock lambda hlambda
      (sixCameraCauchyRealifiedEmbedding v))

/-- The real component of the compressed Cauchy family, still defined by
literal compression of the existing global real component. -/
def sixCameraCauchyRealPartCompression (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    EuclideanSpace ℝ (Fin 6) →L[ℝ] EuclideanSpace ℝ (Fin 6) :=
  sixCameraCauchyWhitenedHilbertSynthesisContinuous.adjoint ∘L
    (allBasesCauchyRealPart lambda hlambda ∘L
      sixCameraCauchyWhitenedHilbertSynthesisContinuous)

/-- The real-component compression has the expected all-bases resolvent
pairing. -/
theorem sixCameraCauchyRealPartCompression_inner (lambda : ℂ)
    (hlambda : lambda.im ≠ 0)
    (u v : EuclideanSpace ℝ (Fin 6)) :
    inner ℝ u (sixCameraCauchyRealPartCompression lambda hlambda v) =
      inner ℝ (naimarkIsometry
          (sixCameraCauchyWhitenedHilbertSynthesisContinuous u))
        (logarithmicResolventRealOperator lambda hlambda
          (naimarkIsometry
            (sixCameraCauchyWhitenedHilbertSynthesisContinuous v))) := by
  rw [sixCameraCauchyRealPartCompression,
    ContinuousLinearMap.comp_apply]
  calc
    inner ℝ u
        (sixCameraCauchyWhitenedHilbertSynthesisContinuous.adjoint
          (allBasesCauchyRealPart lambda hlambda
            (sixCameraCauchyWhitenedHilbertSynthesisContinuous v))) =
        inner ℝ (sixCameraCauchyWhitenedHilbertSynthesisContinuous u)
          (allBasesCauchyRealPart lambda hlambda
            (sixCameraCauchyWhitenedHilbertSynthesisContinuous v)) := by
      exact sixCameraCauchyWhitenedHilbertSynthesisContinuous.adjoint_inner_right
        u (allBasesCauchyRealPart lambda hlambda
          (sixCameraCauchyWhitenedHilbertSynthesisContinuous v))
    _ = inner ℝ (naimarkIsometry
          (sixCameraCauchyWhitenedHilbertSynthesisContinuous u))
        (logarithmicResolventRealOperator lambda hlambda
          (naimarkIsometry
            (sixCameraCauchyWhitenedHilbertSynthesisContinuous v))) := by
      exact inner_allBasesCauchyRealPart lambda hlambda
        (sixCameraCauchyWhitenedHilbertSynthesisContinuous u)
        (sixCameraCauchyWhitenedHilbertSynthesisContinuous v)

/-- The imaginary component has the analogous literal compression formula. -/
def sixCameraCauchyImaginaryPartCompression (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    EuclideanSpace ℝ (Fin 6) →L[ℝ] EuclideanSpace ℝ (Fin 6) :=
  sixCameraCauchyWhitenedHilbertSynthesisContinuous.adjoint ∘L
    (allBasesCauchyImaginaryPart lambda hlambda ∘L
      sixCameraCauchyWhitenedHilbertSynthesisContinuous)

/-- The imaginary-component compression has the expected all-bases resolvent
pairing. -/
theorem sixCameraCauchyImaginaryPartCompression_inner (lambda : ℂ)
    (hlambda : lambda.im ≠ 0)
    (u v : EuclideanSpace ℝ (Fin 6)) :
    inner ℝ u (sixCameraCauchyImaginaryPartCompression lambda hlambda v) =
      inner ℝ (naimarkIsometry
          (sixCameraCauchyWhitenedHilbertSynthesisContinuous u))
        (logarithmicResolventImaginaryOperator lambda hlambda
          (naimarkIsometry
            (sixCameraCauchyWhitenedHilbertSynthesisContinuous v))) := by
  rw [sixCameraCauchyImaginaryPartCompression,
    ContinuousLinearMap.comp_apply]
  calc
    inner ℝ u
        (sixCameraCauchyWhitenedHilbertSynthesisContinuous.adjoint
          (allBasesCauchyImaginaryPart lambda hlambda
            (sixCameraCauchyWhitenedHilbertSynthesisContinuous v))) =
        inner ℝ (sixCameraCauchyWhitenedHilbertSynthesisContinuous u)
          (allBasesCauchyImaginaryPart lambda hlambda
            (sixCameraCauchyWhitenedHilbertSynthesisContinuous v)) := by
      exact sixCameraCauchyWhitenedHilbertSynthesisContinuous.adjoint_inner_right
        u (allBasesCauchyImaginaryPart lambda hlambda
          (sixCameraCauchyWhitenedHilbertSynthesisContinuous v))
    _ = inner ℝ (naimarkIsometry
          (sixCameraCauchyWhitenedHilbertSynthesisContinuous u))
        (logarithmicResolventImaginaryOperator lambda hlambda
          (naimarkIsometry
            (sixCameraCauchyWhitenedHilbertSynthesisContinuous v))) := by
      exact inner_allBasesCauchyImaginaryPart lambda hlambda
        (sixCameraCauchyWhitenedHilbertSynthesisContinuous u)
        (sixCameraCauchyWhitenedHilbertSynthesisContinuous v)

/-! ## Exact scalar remainder identity -/

/-- A third-order resolvent identity with an exact, unsummed remainder.
The hypotheses are kept explicit so that no inverse is silently cancelled. -/
theorem scalar_resolvent_third_order {lambda : ℂ} {y : ℝ}
    (hlambda : lambda ≠ 0)
    (hsub : lambda - (y : ℂ) ≠ 0) :
    (lambda - (y : ℂ))⁻¹ =
      lambda⁻¹ + lambda⁻¹ * lambda⁻¹ * (y : ℂ) +
        lambda⁻¹ * lambda⁻¹ * (y : ℂ)^2 *
          (lambda - (y : ℂ))⁻¹ := by
  field_simp
  ring

/-- The same exact identity under the Cauchy off-real-axis hypothesis. -/
theorem scalar_resolvent_third_order_of_offReal {lambda : ℂ} {y : ℝ}
    (hlambda : lambda.im ≠ 0) :
    (lambda - (y : ℂ))⁻¹ =
      lambda⁻¹ + lambda⁻¹ * lambda⁻¹ * (y : ℂ) +
        lambda⁻¹ * lambda⁻¹ * (y : ℂ)^2 *
          (lambda - (y : ℂ))⁻¹ := by
  have hsub : lambda - (y : ℂ) ≠ 0 := by
    intro hz
    have hi : lambda.im = 0 := by
      have hz' := congrArg Complex.im hz
      simpa using hz'
    exact hlambda hi
  apply scalar_resolvent_third_order
  · intro hzero
    apply hlambda
    rw [hzero]
    rfl
  · exact hsub

/-- The exact scalar identity at the logarithmic coordinate used by the
global Cauchy block. -/
theorem scalar_logarithmicCoordinate_resolvent_third_order_of_offReal
    {lambda : ℂ} (hlambda : lambda.im ≠ 0) (x : ℝ) :
    (lambda - (logarithmicCoordinate x : ℂ))⁻¹ =
      lambda⁻¹ + lambda⁻¹ * lambda⁻¹ *
          (logarithmicCoordinate x : ℂ) +
        lambda⁻¹ * lambda⁻¹ * (logarithmicCoordinate x : ℂ)^2 *
          (lambda - (logarithmicCoordinate x : ℂ))⁻¹ := by
  simpa using
    (scalar_resolvent_third_order_of_offReal (lambda := lambda)
      (y := logarithmicCoordinate x) hlambda)

/-! ## The partial Weyl boundary is intentionally exposed, not inverted. -/

/-- The global Weyl inverse remains defined on the range of the global Cauchy
block; this convenience theorem keeps that domain visible at the finite
crosswalk boundary. -/
theorem sixCameraCauchy_globalWeyl_domain (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    (allBasesWeylInverse lambda hlambda).domain =
      LinearMap.range
        (allBasesCauchyBlock lambda hlambda :
          RealifiedCameraComplexification →ₗ[ℝ]
            RealifiedCameraComplexification) :=
  allBasesWeylInverse_domain lambda hlambda

end CarrySelfAdjointOperator
