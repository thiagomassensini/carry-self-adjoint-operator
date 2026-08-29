import CarrySelfAdjointOperator.CompletedC3CompressedLogarithmicOperator

/-!
# Completed limit form of the intrinsic compressed C3 source

The finite compressed sources need not converge to the separately packed
six-camera source.  This module instead takes their own structural limit.
Formal symmetry moves the unbounded compressed logarithmic operator onto a
fixed domain test, leaving only the already-proved strong convergence of the
TFVD state.  Consequently the finite sources converge against every vector of
the exact logarithmic domain, and every permanent camera coordinate has a
canonical cutoff limit.

The logarithmic domain is dense.  A Bessel bound for the resulting linear form
is therefore equivalent, by continuous extension and Riesz representation, to
the existence of a unique intrinsic Hilbert source.  No complementary Naimark
channel is set to zero, and no six-camera target is imposed.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace LinearPMap lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- Distributional limit of the compressed source on the exact logarithmic
domain. -/
def canonicalCompletedC3CompressedSourceLimitForm
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re)
    (test : realifiedCompressedLogarithmicMultiplication.domain) : Real :=
  inner Real (test : RealifiedCameraComplexification)
      (realifiedCompressedScalar z
        (completedC3SymplecticCameraState (operatorHeightParameter z) hs)) -
    inner Real (realifiedCompressedLogarithmicMultiplication test)
      (completedC3SymplecticCameraState (operatorHeightParameter z) hs)

/-- The limiting source readout is a real-linear functional on the exact
compressed logarithmic domain. -/
def canonicalCompletedC3CompressedSourceLimitLinearMap
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re) :
    realifiedCompressedLogarithmicMultiplication.domain →ₗ[Real] Real where
  toFun := canonicalCompletedC3CompressedSourceLimitForm z hs
  map_add' x y := by
    unfold canonicalCompletedC3CompressedSourceLimitForm
    rw [Submodule.coe_add, inner_add_left, LinearPMap.map_add, inner_add_left]
    ring
  map_smul' r x := by
    unfold canonicalCompletedC3CompressedSourceLimitForm
    rw [Submodule.coe_smul, real_inner_smul_left, LinearPMap.map_smul,
      real_inner_smul_left]
    simp only [RingHom.id_apply, smul_eq_mul]
    ring

theorem canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_inner_tendsto
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re)
    (test : realifiedCompressedLogarithmicMultiplication.domain) :
    Filter.Tendsto
      (fun cutoff : Nat =>
        inner Real (test : RealifiedCameraComplexification)
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z))
      Filter.atTop
      (nhds (canonicalCompletedC3CompressedSourceLimitForm z hs test)) := by
  have hstate :=
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector_tendsto
      hbase z hs
  have hscalar : Filter.Tendsto
      (fun cutoff : Nat =>
        realifiedCompressedScalar z
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
            hbase cutoff z : RealifiedCameraComplexification))
      Filter.atTop
      (nhds (realifiedCompressedScalar z
        (completedC3SymplecticCameraState (operatorHeightParameter z) hs))) :=
    (realifiedCompressedScalar z).continuous.continuousAt.tendsto.comp hstate
  have hfirst : Filter.Tendsto
      (fun cutoff : Nat =>
        inner Real (test : RealifiedCameraComplexification)
          (realifiedCompressedScalar z
            (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
              hbase cutoff z : RealifiedCameraComplexification)))
      Filter.atTop
      (nhds (inner Real (test : RealifiedCameraComplexification)
        (realifiedCompressedScalar z
          (completedC3SymplecticCameraState (operatorHeightParameter z) hs)))) :=
    tendsto_const_nhds.inner hscalar
  have hsecond :=
    (tendsto_const_nhds.inner hstate : Filter.Tendsto
      (fun cutoff : Nat =>
        inner Real (realifiedCompressedLogarithmicMultiplication test)
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
            hbase cutoff z : RealifiedCameraComplexification))
      Filter.atTop
      (nhds (inner Real (realifiedCompressedLogarithmicMultiplication test)
        (completedC3SymplecticCameraState (operatorHeightParameter z) hs))))
  have hsub := hfirst.sub hsecond
  exact hsub.congr'
    (Filter.Eventually.of_forall fun cutoff => by
      dsimp only
      rw [canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_eq_defect]
      unfold realifiedCompressedLogarithmicDefectSource
      rw [inner_sub_right]
      rw [← realifiedCompressedLogarithmicMultiplication_isFormalAdjoint
        test
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
          hbase cutoff z)])

/-- First-channel permanent camera coordinate as an exact domain test. -/
def realifiedCompressedLogarithmicBasisFst (n : Nat) :
    realifiedCompressedLogarithmicMultiplication.domain :=
  ⟨WithLp.toLp 2 (completedC3OrthonormalCameraVector n, 0), by
    constructor
    · simpa only [realifiedNaimarkPort_fst, WithLp.toLp_fst] using
        naimarkIsometry_completedC3OrthonormalCameraVector_mem_domain n
    · simp [realifiedNaimarkPort_snd]⟩

/-- Second-channel permanent camera coordinate as an exact domain test. -/
def realifiedCompressedLogarithmicBasisSnd (n : Nat) :
    realifiedCompressedLogarithmicMultiplication.domain :=
  ⟨WithLp.toLp 2 (0, completedC3OrthonormalCameraVector n), by
    constructor
    · simp [realifiedNaimarkPort_fst]
    · simpa only [realifiedNaimarkPort_snd, WithLp.toLp_snd] using
        naimarkIsometry_completedC3OrthonormalCameraVector_mem_domain n⟩

/-- Finite camera cores, packed in the realified carrier. -/
def realifiedCameraCorePairEmbedding
    (u : CameraFinsupp × CameraFinsupp) :
    RealifiedCameraComplexification :=
  WithLp.toLp 2 (cameraEmbedding u.1, cameraEmbedding u.2)

theorem realifiedCameraCorePairEmbedding_denseRange :
    DenseRange realifiedCameraCorePairEmbedding := by
  have hprod : DenseRange
      (Prod.map (cameraEmbedding : CameraFinsupp → CameraHilbert)
        (cameraEmbedding : CameraFinsupp → CameraHilbert)) :=
    cameraEmbedding_denseRange.prodMap cameraEmbedding_denseRange
  have hlp : DenseRange
      (WithLp.toLp 2 : CameraHilbert × CameraHilbert →
      RealifiedCameraComplexification) :=
    (WithLp.toLp_surjective 2).denseRange
  have heq : realifiedCameraCorePairEmbedding =
      (WithLp.toLp 2 : CameraHilbert × CameraHilbert →
        RealifiedCameraComplexification) ∘
        Prod.map (cameraEmbedding : CameraFinsupp → CameraHilbert)
          (cameraEmbedding : CameraFinsupp → CameraHilbert) := by
    funext u
    rfl
  rw [heq]
  exact hlp.comp hprod (WithLp.prod_continuous_toLp 2 _ _)

theorem realifiedCameraCorePairEmbedding_mem_compressedDomain
    (u : CameraFinsupp × CameraFinsupp) :
    realifiedCameraCorePairEmbedding u ∈
      realifiedCompressedLogarithmicMultiplication.domain := by
  constructor
  · rw [realifiedNaimarkPort_fst]
    change naimarkIsometry (cameraEmbedding u.1) ∈
      logarithmicMultiplication.domain
    rw [naimarkIsometry_cameraEmbedding, logarithmicMultiplication_domain]
    exact naimarkCoreMap_mem_logarithmicMultiplicationDomain u.1
  · rw [realifiedNaimarkPort_snd]
    change naimarkIsometry (cameraEmbedding u.2) ∈
      logarithmicMultiplication.domain
    rw [naimarkIsometry_cameraEmbedding, logarithmicMultiplication_domain]
    exact naimarkCoreMap_mem_logarithmicMultiplicationDomain u.2

/-- The compressed logarithmic domain is dense in the intrinsic camera
carrier. -/
theorem realifiedCompressedLogarithmicMultiplication_denseDomain :
    Dense (realifiedCompressedLogarithmicMultiplication.domain :
      Set RealifiedCameraComplexification) := by
  apply Dense.mono
    (show Set.range realifiedCameraCorePairEmbedding ⊆
      (realifiedCompressedLogarithmicMultiplication.domain :
        Set RealifiedCameraComplexification) by
      rintro x ⟨u, rfl⟩
      exact realifiedCameraCorePairEmbedding_mem_compressedDomain u)
  exact realifiedCameraCorePairEmbedding_denseRange

/-- Exact boundedness gate for promoting the distributional source form to a
vector of the intrinsic camera Hilbert space. -/
def CanonicalCompletedC3CompressedSourceFormBounded
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re) : Prop :=
  ∃ C : Real, ∀ test : realifiedCompressedLogarithmicMultiplication.domain,
    ‖canonicalCompletedC3CompressedSourceLimitForm z hs test‖ ≤
      C * ‖(test : RealifiedCameraComplexification)‖

/-- A camera vector realizes the completed compressed source form on the exact
operator domain. -/
def IsCanonicalCompletedC3CompressedHilbertSource
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re)
    (source : RealifiedCameraComplexification) : Prop :=
  ∀ test : realifiedCompressedLogarithmicMultiplication.domain,
    inner Real (test : RealifiedCameraComplexification) source =
      canonicalCompletedC3CompressedSourceLimitForm z hs test

/-- Continuous extension of a bounded compressed source form from the dense
operator domain. -/
def canonicalCompletedC3CompressedSourceFunctional
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs) :
    RealifiedCameraComplexification →L[Real] Real :=
  let C := Classical.choose hbound
  let hC := Classical.choose_spec hbound
  (canonicalCompletedC3CompressedSourceLimitLinearMap z hs).mkContinuous C hC
    |>.extend
      (Submodule.subtypeL
        realifiedCompressedLogarithmicMultiplication.domain)

/-- Riesz vector representing the bounded completed compressed source form. -/
def canonicalCompletedC3CompressedHilbertSource
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs) :
    RealifiedCameraComplexification :=
  (InnerProductSpace.toDual Real RealifiedCameraComplexification).symm
    (canonicalCompletedC3CompressedSourceFunctional z hs hbound)

theorem canonicalCompletedC3CompressedHilbertSource_realizes
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs) :
    IsCanonicalCompletedC3CompressedHilbertSource z hs
      (canonicalCompletedC3CompressedHilbertSource z hs hbound) := by
  intro test
  rw [real_inner_comm]
  unfold canonicalCompletedC3CompressedHilbertSource
  rw [InnerProductSpace.toDual_symm_apply]
  let C : Real := Classical.choose hbound
  let hC := Classical.choose_spec hbound
  change
    (((canonicalCompletedC3CompressedSourceLimitLinearMap z hs).mkContinuous C hC)
      |>.extend (Submodule.subtypeL
        realifiedCompressedLogarithmicMultiplication.domain))
        ((Submodule.subtypeL
          realifiedCompressedLogarithmicMultiplication.domain) test) = _
  rw [ContinuousLinearMap.extend_eq
    _ realifiedCompressedLogarithmicMultiplication_denseDomain.denseRange_val
    isometry_subtype_coe.isUniformInducing]
  rfl

/-- A Hilbert realization supplies the exact Bessel bound for the source form. -/
theorem canonicalCompletedC3CompressedSourceFormBounded_of_realizes
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re)
    {source : RealifiedCameraComplexification}
    (hsource : IsCanonicalCompletedC3CompressedHilbertSource z hs source) :
    CanonicalCompletedC3CompressedSourceFormBounded z hs := by
  refine ⟨‖source‖, ?_⟩
  intro test
  rw [← hsource test]
  simpa [mul_comm] using
    (norm_inner_le_norm (𝕜 := Real)
      (test : RealifiedCameraComplexification) source)

/-- Exact Riesz/Bessel equivalence for the completed compressed source. -/
theorem canonicalCompletedC3CompressedSourceFormBounded_iff_hilbertSource :
    CanonicalCompletedC3CompressedSourceFormBounded z hs ↔
      ∃ source : RealifiedCameraComplexification,
        IsCanonicalCompletedC3CompressedHilbertSource z hs source := by
  constructor
  · intro hbound
    exact ⟨canonicalCompletedC3CompressedHilbertSource z hs hbound,
      canonicalCompletedC3CompressedHilbertSource_realizes z hs hbound⟩
  · rintro ⟨source, hsource⟩
    exact canonicalCompletedC3CompressedSourceFormBounded_of_realizes
      z hs hsource

/-- Density makes the Hilbert realization of the source form unique. -/
theorem IsCanonicalCompletedC3CompressedHilbertSource.unique
    {z : Complex} {hs : 0 < (operatorHeightParameter z).re}
    {source target : RealifiedCameraComplexification}
    (hsource : IsCanonicalCompletedC3CompressedHilbertSource z hs source)
    (htarget : IsCanonicalCompletedC3CompressedHilbertSource z hs target) :
    source = target := by
  have hall (u : RealifiedCameraComplexification) :
      inner Real u (source - target) = 0 := by
    refine
      realifiedCompressedLogarithmicMultiplication_denseDomain.denseRange_val.induction_on
        u ?_ ?_
    · exact isClosed_eq
        (continuous_id.inner (continuous_const.sub continuous_const))
        continuous_const
    · intro test
      rw [inner_sub_right, hsource test, htarget test]
      ring
  have hself := hall (source - target)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)

/-- Any strong cutoff limit realizes the already-constructed distributional
source form. -/
theorem isCanonicalCompletedC3CompressedHilbertSource_of_tendsto
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re)
    (source : RealifiedCameraComplexification)
    (hsource : Filter.Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      Filter.atTop (nhds source)) :
    IsCanonicalCompletedC3CompressedHilbertSource z hs source := by
  intro test
  have hread : Filter.Tendsto
      (fun cutoff : Nat =>
        inner Real (test : RealifiedCameraComplexification)
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z))
      Filter.atTop
      (nhds (inner Real (test : RealifiedCameraComplexification) source)) :=
    tendsto_const_nhds.inner hsource
  have hform :=
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_inner_tendsto
      hbase z hs test
  exact tendsto_nhds_unique hread hform

/-- Whenever strong convergence is established, its limit is forced to be the
Riesz vector of the completed source form. -/
theorem canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_limit_eq_hilbertSource
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs)
    (source : RealifiedCameraComplexification)
    (hsource : Filter.Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      Filter.atTop (nhds source)) :
    source = canonicalCompletedC3CompressedHilbertSource z hs hbound := by
  exact
    (isCanonicalCompletedC3CompressedHilbertSource_of_tendsto
      hbase z hs source hsource).unique
      (canonicalCompletedC3CompressedHilbertSource_realizes z hs hbound)

/-- Strong convergence of the intrinsic compressed sources is exactly their
Cauchy property in the complete camera Hilbert carrier. -/
theorem exists_canonicalCompletedC3FiniteCompressedSource_limit_iff_cauchy
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) :
    (∃ source : RealifiedCameraComplexification,
      Filter.Tendsto
        (fun cutoff : Nat =>
          canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z)
        Filter.atTop (nhds source)) ↔
      CauchySeq
        (fun cutoff : Nat =>
          canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z) := by
  constructor
  · rintro ⟨source, hsource⟩
    exact hsource.cauchySeq
  · intro hcauchy
    exact cauchySeq_tendsto_of_complete hcauchy

/-- The remaining strong-limit gate may equivalently be checked on the
compressed logarithmic images.  The scalar part is already convergent. -/
theorem canonicalCompletedC3FiniteCompressedSource_cauchy_iff_logarithmicImage_cauchy
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re) :
    CauchySeq
        (fun cutoff : Nat =>
          canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z) ↔
      CauchySeq
        (fun cutoff : Nat =>
          realifiedCompressedLogarithmicMultiplication
            (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
              hbase cutoff z)) := by
  have hstate :=
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector_tendsto
      hbase z hs
  have hscalar : Filter.Tendsto
      (fun cutoff : Nat =>
        realifiedCompressedScalar z
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
            hbase cutoff z : RealifiedCameraComplexification))
      Filter.atTop
      (nhds (realifiedCompressedScalar z
        (completedC3SymplecticCameraState (operatorHeightParameter z) hs))) :=
    (realifiedCompressedScalar z).continuous.continuousAt.tendsto.comp hstate
  constructor
  · intro hsource
    have hcauchy := hscalar.cauchySeq.add hsource.neg
    have heq :
        (fun cutoff : Nat =>
          realifiedCompressedLogarithmicMultiplication
            (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
              hbase cutoff z)) =
          (fun cutoff : Nat =>
            realifiedCompressedScalar z
              (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
                hbase cutoff z : RealifiedCameraComplexification)) +
            -(fun cutoff : Nat =>
              canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
                hbase cutoff z) := by
      funext cutoff
      rw [Pi.add_apply, Pi.neg_apply, ← sub_eq_add_neg]
      exact
        canonicalCompletedC3CausalResponseBoundaryFinite_compressedLogarithmic_eq_scalar_sub_source
          hbase cutoff z
    rw [heq]
    exact hcauchy
  · intro himage
    have hcauchy := hscalar.cauchySeq.add himage.neg
    have heq :
        (fun cutoff : Nat =>
          canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z) =
          (fun cutoff : Nat =>
            realifiedCompressedScalar z
              (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
                hbase cutoff z : RealifiedCameraComplexification)) +
            -(fun cutoff : Nat =>
              realifiedCompressedLogarithmicMultiplication
                (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
                  hbase cutoff z)) := by
      funext cutoff
      rw [Pi.add_apply, Pi.neg_apply, ← sub_eq_add_neg]
      exact
        (canonicalCompletedC3CausalResponseBoundaryFinite_scalar_sub_compressedLogarithmic_eq_source
          hbase cutoff z).symm
    rw [heq]
    exact hcauchy

/-- A Cauchy proof constructs both the Bessel bound and the canonical Riesz
source, and the finite compressed sources converge strongly to that vector. -/
theorem exists_canonicalCompletedC3CompressedHilbertSource_tendsto_of_cauchy
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re)
    (hcauchy : CauchySeq
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)) :
    ∃ hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs,
      Filter.Tendsto
        (fun cutoff : Nat =>
          canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z)
        Filter.atTop
        (nhds (canonicalCompletedC3CompressedHilbertSource z hs hbound)) := by
  rcases cauchySeq_tendsto_of_complete hcauchy with ⟨source, hsource⟩
  have hrealizes :=
    isCanonicalCompletedC3CompressedHilbertSource_of_tendsto
      hbase z hs source hsource
  let hbound :=
    canonicalCompletedC3CompressedSourceFormBounded_of_realizes
      z hs hrealizes
  refine ⟨hbound, ?_⟩
  have heq : source =
      canonicalCompletedC3CompressedHilbertSource z hs hbound :=
    hrealizes.unique
      (canonicalCompletedC3CompressedHilbertSource_realizes z hs hbound)
  simpa [heq] using hsource

/-- Every first-channel source coordinate has an unconditional cutoff limit. -/
theorem canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_fstCoordinate_tendsto
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re) (n : Nat) :
    Filter.Tendsto
      (fun cutoff : Nat =>
        inner Real (completedC3OrthonormalCameraVector n)
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z).fst)
      Filter.atTop
      (nhds (canonicalCompletedC3CompressedSourceLimitForm z hs
        (realifiedCompressedLogarithmicBasisFst n))) := by
  simpa [realifiedCompressedLogarithmicBasisFst, WithLp.prod_inner_apply] using
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_inner_tendsto
      hbase z hs (realifiedCompressedLogarithmicBasisFst n)

/-- Every second-channel source coordinate has an unconditional cutoff limit. -/
theorem canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_sndCoordinate_tendsto
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re) (n : Nat) :
    Filter.Tendsto
      (fun cutoff : Nat =>
        inner Real (completedC3OrthonormalCameraVector n)
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z).snd)
      Filter.atTop
      (nhds (canonicalCompletedC3CompressedSourceLimitForm z hs
        (realifiedCompressedLogarithmicBasisSnd n))) := by
  simpa [realifiedCompressedLogarithmicBasisSnd, WithLp.prod_inner_apply] using
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_inner_tendsto
      hbase z hs (realifiedCompressedLogarithmicBasisSnd n)

end

end CarrySelfAdjointOperator
