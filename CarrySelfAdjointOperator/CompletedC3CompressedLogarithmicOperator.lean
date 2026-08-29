import CarrySelfAdjointOperator.CompletedC3NaimarkLeakObstruction

/-!
# Compressed logarithmic operator on the completed C3 camera carrier

The ambient logarithmic multiplier does not preserve the Naimark camera
range.  This module therefore keeps its complementary leak channel and defines
the intrinsic compression `A* Y A` on the exact pullback domain.

Every finite causal TFVD state belongs to that domain and satisfies an exact
compressed defect equation.  The compression is formally symmetric.  A
concrete camera-3 row is computed without Gram or spectral hypotheses: it has
eigenvalue `log 3`, and yields two cutoff-independent necessary coordinates
for any proposed vector limit of the compressed C3 sources.  At the central
height these coordinates also prove that the compressed sources cannot
converge to the separately packed canonical six-camera source.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace LinearPMap lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- Camera vectors whose Naimark realization belongs coordinatewise to the
maximal logarithmic domain. -/
def realifiedCompressedLogarithmicDomain :
    Submodule Real RealifiedCameraComplexification where
  carrier := {u |
    (realifiedNaimarkPort u).fst ∈ logarithmicMultiplication.domain ∧
      (realifiedNaimarkPort u).snd ∈ logarithmicMultiplication.domain}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    constructor
    · simpa using logarithmicMultiplication.domain.add_mem hx.1 hy.1
    · simpa using logarithmicMultiplication.domain.add_mem hx.2 hy.2
  smul_mem' := by
    intro c x hx
    constructor
    · simpa using logarithmicMultiplication.domain.smul_mem c hx.1
    · simpa using logarithmicMultiplication.domain.smul_mem c hx.2

theorem mem_realifiedCompressedLogarithmicDomain_iff
    (u : RealifiedCameraComplexification) :
    u ∈ realifiedCompressedLogarithmicDomain ↔
      (realifiedNaimarkPort u).fst ∈ logarithmicMultiplication.domain ∧
        (realifiedNaimarkPort u).snd ∈ logarithmicMultiplication.domain :=
  Iff.rfl

/-- Lift of a compressed camera-domain vector to the ambient maximal domain. -/
def realifiedCompressedLogarithmicDomainLift :
    realifiedCompressedLogarithmicDomain →ₗ[Real]
      RealifiedLogarithmicDomain where
  toFun u :=
    (⟨(realifiedNaimarkPort (u : RealifiedCameraComplexification)).fst,
        (mem_realifiedCompressedLogarithmicDomain_iff _).mp u.property |>.1⟩,
      ⟨(realifiedNaimarkPort (u : RealifiedCameraComplexification)).snd,
        (mem_realifiedCompressedLogarithmicDomain_iff _).mp u.property |>.2⟩)
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change (realifiedNaimarkPort ((x : RealifiedCameraComplexification) + y)).fst =
        (realifiedNaimarkPort (x : RealifiedCameraComplexification)).fst +
          (realifiedNaimarkPort (y : RealifiedCameraComplexification)).fst
      simp
    · apply Subtype.ext
      change (realifiedNaimarkPort ((x : RealifiedCameraComplexification) + y)).snd =
        (realifiedNaimarkPort (x : RealifiedCameraComplexification)).snd +
          (realifiedNaimarkPort (y : RealifiedCameraComplexification)).snd
      simp
  map_smul' c x := by
    apply Prod.ext
    · apply Subtype.ext
      change (realifiedNaimarkPort
          (c • (x : RealifiedCameraComplexification))).fst =
        c • (realifiedNaimarkPort (x : RealifiedCameraComplexification)).fst
      simp
    · apply Subtype.ext
      change (realifiedNaimarkPort
          (c • (x : RealifiedCameraComplexification))).snd =
        c • (realifiedNaimarkPort (x : RealifiedCameraComplexification)).snd
      simp

@[simp] theorem realifiedCompressedLogarithmicDomainLift_embedding
    (u : realifiedCompressedLogarithmicDomain) :
    realifiedLogarithmicDomainEmbedding
        (realifiedCompressedLogarithmicDomainLift u) =
      realifiedNaimarkPort (u : RealifiedCameraComplexification) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;> rfl

/-- Compression `A* Y A` of the ambient logarithmic multiplier to the
intrinsic all-camera Hilbert carrier. -/
def realifiedCompressedLogarithmicMultiplication :
    RealifiedCameraComplexification →ₗ.[Real]
      RealifiedCameraComplexification where
  domain := realifiedCompressedLogarithmicDomain
  toFun := realifiedNaimarkAdjoint.toLinearMap.comp
    (realifiedLogarithmicMultiplication.comp
      realifiedCompressedLogarithmicDomainLift)

@[simp] theorem realifiedCompressedLogarithmicMultiplication_apply
    (u : realifiedCompressedLogarithmicDomain) :
    realifiedCompressedLogarithmicMultiplication u =
      realifiedNaimarkAdjoint
        (realifiedLogarithmicMultiplication
          (realifiedCompressedLogarithmicDomainLift u)) :=
  rfl

/-- The finite causal response/boundary packing belongs to the compressed
maximal domain. -/
theorem canonicalCompletedC3CausalResponseBoundaryFiniteCameraState_mem_domain
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z : Complex) :
    finiteC3SymplecticCameraPacking
        (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
        (canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff
          (operatorHeightParameter z)) ∈
      realifiedCompressedLogarithmicDomain := by
  let M := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
  let x := canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff
    (operatorHeightParameter z)
  have hembed := finiteC3SymplecticNaimarkDomainVector_embedding M x
  constructor
  · change (realifiedNaimarkPort (finiteC3SymplecticCameraPacking M x)).fst ∈ _
    rw [show realifiedNaimarkPort (finiteC3SymplecticCameraPacking M x) =
      finiteC3SymplecticNaimarkRealization M x by rfl, ← hembed]
    exact (finiteC3SymplecticNaimarkDomainVector M x).1.property
  · change (realifiedNaimarkPort (finiteC3SymplecticCameraPacking M x)).snd ∈ _
    rw [show realifiedNaimarkPort (finiteC3SymplecticCameraPacking M x) =
      finiteC3SymplecticNaimarkRealization M x by rfl, ← hembed]
    exact (finiteC3SymplecticNaimarkDomainVector M x).2.property

/-- Finite TFVD camera vector bundled in the compressed logarithmic domain. -/
def canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z : Complex) :
    realifiedCompressedLogarithmicDomain :=
  ⟨finiteC3SymplecticCameraPacking
      (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
      (canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff
        (operatorHeightParameter z)),
    canonicalCompletedC3CausalResponseBoundaryFiniteCameraState_mem_domain
      hbase cutoff z⟩

theorem canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector_lift
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z : Complex) :
    realifiedCompressedLogarithmicDomainLift
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
          hbase cutoff z) =
      canonicalCompletedC3CausalResponseBoundaryDomainVector
        hbase cutoff (operatorHeightParameter z) := by
  have hambient :
      realifiedLogarithmicDomainEmbedding
          (realifiedCompressedLogarithmicDomainLift
            (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
              hbase cutoff z)) =
        realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3CausalResponseBoundaryDomainVector
            hbase cutoff (operatorHeightParameter z)) := by
    rw [realifiedCompressedLogarithmicDomainLift_embedding]
    let M := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
    let x := canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff
      (operatorHeightParameter z)
    change realifiedNaimarkPort (finiteC3SymplecticCameraPacking M x) =
      realifiedLogarithmicDomainEmbedding
        (finiteC3SymplecticNaimarkDomainVector M x)
    rw [finiteC3SymplecticNaimarkDomainVector_embedding]
    rfl
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg WithLp.fst hambient
  · apply Subtype.ext
    exact congrArg WithLp.snd hambient

/-- Complex scalar multiplication transported to the intrinsic camera
complexification through the canonical Naimark port/readout. -/
def realifiedCompressedScalar (z : Complex) :
    RealifiedCameraComplexification →L[Real]
      RealifiedCameraComplexification :=
  realifiedNaimarkAdjoint ∘L
    (realifiedNaimarkScalar z ∘L realifiedNaimarkPort)

/-- Exact finite compressed resolvent equation.  The complementary Naimark
channel is absent from this equation because it is retained separately in the
orthogonal energy ledger, not set equal to zero. -/
theorem canonicalCompletedC3CausalResponseBoundaryFinite_compressedDefectEquation
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z : Complex) :
    realifiedCompressedScalar z
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
          hbase cutoff z : RealifiedCameraComplexification) =
      realifiedCompressedLogarithmicMultiplication
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
            hbase cutoff z) +
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z := by
  unfold realifiedCompressedScalar
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
    canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource
    realifiedLambdaMinusLogarithmicMultiplication
  simp only [ContinuousLinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
    realifiedCompressedLogarithmicMultiplication_apply]
  rw [← realifiedCompressedLogarithmicDomainLift_embedding]
  rw [canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector_lift]
  simp only [map_sub]
  abel

theorem canonicalCompletedC3CausalResponseBoundaryFinite_scalar_sub_compressedLogarithmic_eq_source
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z : Complex) :
    realifiedCompressedScalar z
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
            hbase cutoff z : RealifiedCameraComplexification) -
        realifiedCompressedLogarithmicMultiplication
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
            hbase cutoff z) =
      canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
        hbase cutoff z := by
  rw [canonicalCompletedC3CausalResponseBoundaryFinite_compressedDefectEquation]
  abel

theorem canonicalCompletedC3CausalResponseBoundaryFinite_compressedLogarithmic_eq_scalar_sub_source
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z : Complex) :
    realifiedCompressedLogarithmicMultiplication
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
            hbase cutoff z) =
      realifiedCompressedScalar z
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
            hbase cutoff z : RealifiedCameraComplexification) -
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z := by
  rw [canonicalCompletedC3CausalResponseBoundaryFinite_compressedDefectEquation]
  abel

/-- The finite compressed camera states converge to the intrinsic camera state
whose Naimark promotion is the completed TFVD vector. -/
theorem canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector_tendsto
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re) :
    Filter.Tendsto
      (fun cutoff : Nat =>
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
          hbase cutoff z : RealifiedCameraComplexification))
      Filter.atTop
      (nhds (completedC3SymplecticCameraState
        (operatorHeightParameter z) hs)) := by
  have hlimit :=
    (finiteC3GenuineSymplecticCameraPacking_tendsto hs).comp
      (finiteCameraWindow_add_one_tendsto_atTop hbase)
  exact hlimit.congr'
    (Filter.Eventually.of_forall fun cutoff => by
      symm
      change
        finiteC3SymplecticCameraPacking
            (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
            (canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff
              (operatorHeightParameter z)) =
          finiteC3SymplecticCameraPacking
            (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
            (finiteC3GenuineBracketGreenBoundaryPair
              (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
              (operatorHeightParameter z))
      rw [canonicalCompletedC3CausalResponseBoundaryTfvdPort_eq_genuine])

/-- The logarithmic image forced by the compressed limit equation. -/
def canonicalCompletedC3CausalResponseBoundaryExpectedCompressedLogarithmicImage
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re) :
    RealifiedCameraComplexification :=
  realifiedCompressedScalar z
      (completedC3SymplecticCameraState (operatorHeightParameter z) hs) -
    canonicalCompletedC3SixCameraSource z

/-- After the already-proved camera-state convergence, convergence of the
compressed logarithmic image is equivalent exactly to convergence of the
compressed source.  No assertion about the complementary Naimark energy enters. -/
theorem canonicalCompletedC3CausalResponseBoundary_compressedLogarithmicImage_tendsto_iff_source
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re) :
    Filter.Tendsto
        (fun cutoff : Nat =>
          realifiedCompressedLogarithmicMultiplication
            (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
              hbase cutoff z))
        Filter.atTop
        (nhds
          (canonicalCompletedC3CausalResponseBoundaryExpectedCompressedLogarithmicImage
            z hs)) ↔
      Filter.Tendsto
        (fun cutoff : Nat =>
          canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z)
        Filter.atTop
        (nhds (canonicalCompletedC3SixCameraSource z)) := by
  have hscalar : Filter.Tendsto
      (fun cutoff : Nat =>
        realifiedCompressedScalar z
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
            hbase cutoff z : RealifiedCameraComplexification))
      Filter.atTop
      (nhds (realifiedCompressedScalar z
        (completedC3SymplecticCameraState (operatorHeightParameter z) hs))) :=
    (realifiedCompressedScalar z).continuous.continuousAt.tendsto.comp
      (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector_tendsto
        hbase z hs)
  constructor
  · intro himage
    have hsource := hscalar.sub himage
    simpa [canonicalCompletedC3CausalResponseBoundaryExpectedCompressedLogarithmicImage]
      using hsource.congr'
        (Filter.Eventually.of_forall fun cutoff => by
          exact
            canonicalCompletedC3CausalResponseBoundaryFinite_scalar_sub_compressedLogarithmic_eq_source
              hbase cutoff z)
  · intro hsource
    have himage := hscalar.sub hsource
    simpa [canonicalCompletedC3CausalResponseBoundaryExpectedCompressedLogarithmicImage]
      using himage.congr'
        (Filter.Eventually.of_forall fun cutoff => by
          exact
            (canonicalCompletedC3CausalResponseBoundaryFinite_compressedLogarithmic_eq_scalar_sub_source
              hbase cutoff z).symm)

theorem inner_realifiedNaimarkAdjoint_eq_inner_realifiedNaimarkPort
    (x : RealifiedNaimarkComplexification)
    (u : RealifiedCameraComplexification) :
    inner Real (realifiedNaimarkAdjoint x) u =
      inner Real x (realifiedNaimarkPort u) := by
  calc
    inner Real (realifiedNaimarkAdjoint x) u =
        inner Real u (realifiedNaimarkAdjoint x) := real_inner_comm _ _
    _ = inner Real (realifiedNaimarkPort u) x :=
      (inner_realifiedNaimarkPort_eq_inner_realifiedNaimarkAdjoint u x).symm
    _ = inner Real x (realifiedNaimarkPort u) := real_inner_comm _ _

/-- Compression by the Naimark isometry preserves formal symmetry of the
maximal logarithmic multiplier. -/
theorem realifiedCompressedLogarithmicMultiplication_isFormalAdjoint :
    realifiedCompressedLogarithmicMultiplication.IsFormalAdjoint
      realifiedCompressedLogarithmicMultiplication := by
  intro x y
  change
    inner Real
        (realifiedNaimarkAdjoint
          (realifiedLogarithmicMultiplication
            (realifiedCompressedLogarithmicDomainLift x)))
        (y : RealifiedCameraComplexification) =
      inner Real (x : RealifiedCameraComplexification)
        (realifiedNaimarkAdjoint
          (realifiedLogarithmicMultiplication
            (realifiedCompressedLogarithmicDomainLift y)))
  rw [inner_realifiedNaimarkAdjoint_eq_inner_realifiedNaimarkPort,
    ← inner_realifiedNaimarkPort_eq_inner_realifiedNaimarkAdjoint]
  rw [← realifiedCompressedLogarithmicDomainLift_embedding,
    ← realifiedCompressedLogarithmicDomainLift_embedding]
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change
    inner Real
          (logarithmicMultiplication
            (realifiedCompressedLogarithmicDomainLift x).1)
          ((realifiedCompressedLogarithmicDomainLift y).1 : NaimarkSpace) +
        inner Real
          (logarithmicMultiplication
            (realifiedCompressedLogarithmicDomainLift x).2)
          ((realifiedCompressedLogarithmicDomainLift y).2 : NaimarkSpace) =
      inner Real
          ((realifiedCompressedLogarithmicDomainLift x).1 : NaimarkSpace)
          (logarithmicMultiplication
            (realifiedCompressedLogarithmicDomainLift y).1) +
        inner Real
          ((realifiedCompressedLogarithmicDomainLift x).2 : NaimarkSpace)
          (logarithmicMultiplication
            (realifiedCompressedLogarithmicDomainLift y).2)
  rw [logarithmicMultiplication_isFormalAdjoint,
    logarithmicMultiplication_isFormalAdjoint]

/-! ## A concrete row of the compressed logarithmic operator -/

/-- The first permanent imaginary coordinate is a genuine logarithmic
eigen-readout of the compressed operator.  The complementary centered
Naimark vector does not disappear; it is orthogonal to the camera range and
therefore does not enter this compressed row. -/
theorem inner_completedC3OrthonormalCameraVector_one_compressedLogarithmic
    (u : CameraHilbert)
    (hu : naimarkIsometry u ∈ logarithmicMultiplication.domain) :
    inner Real (completedC3OrthonormalCameraVector 1)
        (naimarkAdjoint
          (logarithmicMultiplication ⟨naimarkIsometry u, hu⟩)) =
      Real.log 3 *
        inner Real (completedC3OrthonormalCameraVector 1) u := by
  rw [completedC3OrthonormalCameraVector_one]
  simp only [real_inner_smul_left]
  rw [naimarkAdjoint]
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [show completedC3RawCameraVector 1 =
      cameraVector minimalSlopeCamera by rfl]
  change
    (Real.sqrt 6)⁻¹ *
        inner Real (naimarkIsometry (cameraVector minimalSlopeCamera))
          (logarithmicMultiplication ⟨naimarkIsometry u, hu⟩) =
      Real.log 3 *
        ((Real.sqrt 6)⁻¹ *
          inner Real (cameraVector minimalSlopeCamera) u)
  rw [naimarkIsometry_cameraVector]
  have hformal := logarithmicMultiplication_isFormalAdjoint
    (⟨naimarkCameraVector minimalSlopeCamera,
      naimarkCameraVector_mem_logarithmicMultiplicationDomain
        minimalSlopeCamera⟩ : logarithmicMultiplication.domain)
    (⟨naimarkIsometry u, hu⟩ : logarithmicMultiplication.domain)
  rw [← hformal]
  have hdecompose :
      logarithmicMultiplication
          (⟨naimarkCameraVector minimalSlopeCamera,
            naimarkCameraVector_mem_logarithmicMultiplicationDomain
              minimalSlopeCamera⟩ : logarithmicMultiplication.domain) =
        centeredNaimarkCameraVector minimalSlopeCamera +
          Real.log 3 • naimarkCameraVector minimalSlopeCamera := by
    unfold centeredNaimarkCameraVector
    rw [minimalSlopeCamera_slope]
    norm_num
  rw [hdecompose, inner_add_left,
    inner_centeredMinimalSlopeCamera_naimarkIsometry,
    real_inner_smul_left]
  change
    (Real.sqrt 6)⁻¹ *
        (0 + Real.log 3 *
          inner Real (naimarkCameraVector minimalSlopeCamera)
            (naimarkIsometry u)) =
      Real.log 3 *
        ((Real.sqrt 6)⁻¹ *
          inner Real (cameraVector minimalSlopeCamera) u)
  rw [← naimarkIsometry_cameraVector, naimarkIsometry_inner]
  ring

@[simp] theorem realifiedCompressedScalar_fst
    (z : Complex) (u : RealifiedCameraComplexification) :
    (realifiedCompressedScalar z u).fst =
      z.re • u.fst - z.im • u.snd := by
  unfold realifiedCompressedScalar
  simp only [ContinuousLinearMap.comp_apply, realifiedNaimarkAdjoint_fst]
  rw [realifiedNaimarkScalar_fst, realifiedNaimarkPort_fst,
    realifiedNaimarkPort_snd, map_sub, map_smul, map_smul]
  change
    z.re • (naimarkAdjoint ∘L naimarkIsometry.toContinuousLinearMap) u.fst -
      z.im • (naimarkAdjoint ∘L naimarkIsometry.toContinuousLinearMap) u.snd = _
  rw [naimarkAdjoint_comp_naimarkIsometry]
  rfl

@[simp] theorem realifiedCompressedScalar_snd
    (z : Complex) (u : RealifiedCameraComplexification) :
    (realifiedCompressedScalar z u).snd =
      z.im • u.fst + z.re • u.snd := by
  unfold realifiedCompressedScalar
  simp only [ContinuousLinearMap.comp_apply, realifiedNaimarkAdjoint_snd]
  rw [realifiedNaimarkScalar_snd, realifiedNaimarkPort_fst,
    realifiedNaimarkPort_snd, map_add, map_smul, map_smul]
  change
    z.im • (naimarkAdjoint ∘L naimarkIsometry.toContinuousLinearMap) u.fst +
      z.re • (naimarkAdjoint ∘L naimarkIsometry.toContinuousLinearMap) u.snd = _
  rw [naimarkAdjoint_comp_naimarkIsometry]
  rfl

theorem inner_completedC3OrthonormalCameraVector_one_compressedLogarithmic_fst
    (u : realifiedCompressedLogarithmicDomain) :
    inner Real (completedC3OrthonormalCameraVector 1)
        (realifiedCompressedLogarithmicMultiplication u).fst =
      Real.log 3 *
        inner Real (completedC3OrthonormalCameraVector 1)
          (u : RealifiedCameraComplexification).fst := by
  rw [realifiedCompressedLogarithmicMultiplication_apply,
    realifiedNaimarkAdjoint_fst,
    realifiedLogarithmicMultiplication_fst]
  have huFst :
      naimarkIsometry (u : RealifiedCameraComplexification).fst ∈
        logarithmicMultiplication.domain := by
    simpa only [realifiedNaimarkPort_fst] using
      ((mem_realifiedCompressedLogarithmicDomain_iff _).mp u.property).1
  have hliftFst :
      (realifiedCompressedLogarithmicDomainLift u).1 =
        (⟨naimarkIsometry (u : RealifiedCameraComplexification).fst, huFst⟩ :
          logarithmicMultiplication.domain) := by
    apply Subtype.ext
    exact realifiedNaimarkPort_fst (u : RealifiedCameraComplexification)
  rw [hliftFst]
  exact inner_completedC3OrthonormalCameraVector_one_compressedLogarithmic
    (u : RealifiedCameraComplexification).fst
    huFst

theorem inner_completedC3OrthonormalCameraVector_one_compressedLogarithmic_snd
    (u : realifiedCompressedLogarithmicDomain) :
    inner Real (completedC3OrthonormalCameraVector 1)
        (realifiedCompressedLogarithmicMultiplication u).snd =
      Real.log 3 *
        inner Real (completedC3OrthonormalCameraVector 1)
          (u : RealifiedCameraComplexification).snd := by
  rw [realifiedCompressedLogarithmicMultiplication_apply,
    realifiedNaimarkAdjoint_snd,
    realifiedLogarithmicMultiplication_snd]
  have huSnd :
      naimarkIsometry (u : RealifiedCameraComplexification).snd ∈
        logarithmicMultiplication.domain := by
    simpa only [realifiedNaimarkPort_snd] using
      ((mem_realifiedCompressedLogarithmicDomain_iff _).mp u.property).2
  have hliftSnd :
      (realifiedCompressedLogarithmicDomainLift u).2 =
        (⟨naimarkIsometry (u : RealifiedCameraComplexification).snd, huSnd⟩ :
          logarithmicMultiplication.domain) := by
    apply Subtype.ext
    exact realifiedNaimarkPort_snd (u : RealifiedCameraComplexification)
  rw [hliftSnd]
  exact inner_completedC3OrthonormalCameraVector_one_compressedLogarithmic
    (u : RealifiedCameraComplexification).snd
    huSnd

/-- Intrinsic logarithmic defect of a camera-domain vector. -/
def realifiedCompressedLogarithmicDefectSource
    (z : Complex) (u : realifiedCompressedLogarithmicDomain) :
    RealifiedCameraComplexification :=
  realifiedCompressedScalar z
      (u : RealifiedCameraComplexification) -
    realifiedCompressedLogarithmicMultiplication u

/-- Exact first-coordinate formula for the first realified channel of the
compressed defect. -/
theorem inner_completedC3OrthonormalCameraVector_one_compressedDefect_fst
    (z : Complex) (u : realifiedCompressedLogarithmicDomain) :
    inner Real (completedC3OrthonormalCameraVector 1)
        (realifiedCompressedLogarithmicDefectSource z u).fst =
      (z.re - Real.log 3) *
          inner Real (completedC3OrthonormalCameraVector 1)
            (u : RealifiedCameraComplexification).fst -
        z.im *
          inner Real (completedC3OrthonormalCameraVector 1)
            (u : RealifiedCameraComplexification).snd := by
  unfold realifiedCompressedLogarithmicDefectSource
  rw [WithLp.sub_fst, realifiedCompressedScalar_fst, inner_sub_right,
    inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    inner_completedC3OrthonormalCameraVector_one_compressedLogarithmic_fst]
  ring

/-- Exact first-coordinate formula for the second realified channel of the
compressed defect. -/
theorem inner_completedC3OrthonormalCameraVector_one_compressedDefect_snd
    (z : Complex) (u : realifiedCompressedLogarithmicDomain) :
    inner Real (completedC3OrthonormalCameraVector 1)
        (realifiedCompressedLogarithmicDefectSource z u).snd =
      z.im *
          inner Real (completedC3OrthonormalCameraVector 1)
            (u : RealifiedCameraComplexification).fst +
        (z.re - Real.log 3) *
          inner Real (completedC3OrthonormalCameraVector 1)
            (u : RealifiedCameraComplexification).snd := by
  unfold realifiedCompressedLogarithmicDefectSource
  rw [WithLp.sub_snd, realifiedCompressedScalar_snd, inner_sub_right,
    inner_add_right, real_inner_smul_right, real_inner_smul_right,
    inner_completedC3OrthonormalCameraVector_one_compressedLogarithmic_snd]
  ring

/-- The finite causal TFVD source is literally the intrinsic compressed
logarithmic defect; the ambient complementary energy is retained separately. -/
theorem canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_eq_defect
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z : Complex) :
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
        hbase cutoff z =
      realifiedCompressedLogarithmicDefectSource z
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
          hbase cutoff z) := by
  exact
    (canonicalCompletedC3CausalResponseBoundaryFinite_scalar_sub_compressedLogarithmic_eq_source
      hbase cutoff z).symm

theorem inner_completedC3OrthonormalCameraVector_one_finiteCompressedState_fst
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z : Complex) :
    inner Real (completedC3OrthonormalCameraVector 1)
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
          hbase cutoff z : RealifiedCameraComplexification).fst =
      -completedC3RadialRealCoefficient (operatorHeightParameter z) *
        (positiveDirichletGradient (operatorHeightParameter z) 0).im := by
  let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
  change
    inner Real (completedC3OrthonormalCameraVector 1)
        (finiteC3SymplecticCameraPacking N
          (canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff
            (operatorHeightParameter z))).fst = _
  rw [canonicalCompletedC3CausalResponseBoundaryTfvdPort_eq_genuine]
  rw [finiteC3SymplecticCameraPacking_apply, WithLp.toLp_fst,
    finiteC3GenuineFirstLegCamera_eq_radial_completedPrefix,
    inner_neg_right, real_inner_smul_right,
    completedC3LegCameraState,
    inner_completedC3OrthonormalCameraVector_one_globalLeg,
    canonicalCompletedC3DirichletGradientPrefixState_apply]
  have hN : 0 < N := by
    dsimp [N]
    omega
  simp [hN]

theorem inner_completedC3OrthonormalCameraVector_one_finiteCompressedState_snd
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z : Complex) :
    inner Real (completedC3OrthonormalCameraVector 1)
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
          hbase cutoff z : RealifiedCameraComplexification).snd =
      (positiveDirichletGradient (operatorHeightParameter z) 0).im := by
  let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
  change
    inner Real (completedC3OrthonormalCameraVector 1)
        (finiteC3SymplecticCameraPacking N
          (canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff
            (operatorHeightParameter z))).snd = _
  rw [canonicalCompletedC3CausalResponseBoundaryTfvdPort_eq_genuine]
  rw [finiteC3SymplecticCameraPacking_apply, WithLp.toLp_snd,
    finiteC3GenuineSecondLegCamera_eq_completedPrefix]
  change
    inner Real (completedC3OrthonormalCameraVector 1)
        (completedC3LegCameraState
          (canonicalCompletedC3DirichletGradientPrefixState
            (operatorHeightParameter z) N)) = _
  rw [completedC3LegCameraState,
    inner_completedC3OrthonormalCameraVector_one_globalLeg,
    canonicalCompletedC3DirichletGradientPrefixState_apply]
  have hN : 0 < N := by
    dsimp [N]
    omega
  simp [hN]

/-- The first compressed source coordinate is already cutoff independent. -/
theorem inner_completedC3OrthonormalCameraVector_one_finiteCompressedSource_fst
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z : Complex) :
    inner Real (completedC3OrthonormalCameraVector 1)
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z).fst =
      -((z.re - Real.log 3) *
          completedC3RadialRealCoefficient (operatorHeightParameter z) +
        z.im) *
        (positiveDirichletGradient (operatorHeightParameter z) 0).im := by
  rw [canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_eq_defect,
    inner_completedC3OrthonormalCameraVector_one_compressedDefect_fst,
    inner_completedC3OrthonormalCameraVector_one_finiteCompressedState_fst,
    inner_completedC3OrthonormalCameraVector_one_finiteCompressedState_snd]
  ring

/-- The second compressed source coordinate is already cutoff independent. -/
theorem inner_completedC3OrthonormalCameraVector_one_finiteCompressedSource_snd
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z : Complex) :
    inner Real (completedC3OrthonormalCameraVector 1)
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z).snd =
      (z.re - Real.log 3 -
          z.im * completedC3RadialRealCoefficient (operatorHeightParameter z)) *
        (positiveDirichletGradient (operatorHeightParameter z) 0).im := by
  rw [canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_eq_defect,
    inner_completedC3OrthonormalCameraVector_one_compressedDefect_snd,
    inner_completedC3OrthonormalCameraVector_one_finiteCompressedState_fst,
    inner_completedC3OrthonormalCameraVector_one_finiteCompressedState_snd]
  ring

/-- Any proposed vector limit of the compressed sources must realize the two
explicit cutoff-independent camera-3 coordinates.  This is a necessary
vector condition, not a scalar energy or Gram assumption. -/
theorem finiteCompressedSource_tendsto_necessary_cameraThreeCoordinates
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (target : RealifiedCameraComplexification)
    (hsource : Filter.Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      Filter.atTop (nhds target)) :
    inner Real (completedC3OrthonormalCameraVector 1) target.fst =
        -((z.re - Real.log 3) *
            completedC3RadialRealCoefficient (operatorHeightParameter z) +
          z.im) *
          (positiveDirichletGradient (operatorHeightParameter z) 0).im ∧
      inner Real (completedC3OrthonormalCameraVector 1) target.snd =
        (z.re - Real.log 3 -
            z.im * completedC3RadialRealCoefficient (operatorHeightParameter z)) *
          (positiveDirichletGradient (operatorHeightParameter z) 0).im := by
  let fstTarget : Real :=
    -((z.re - Real.log 3) *
        completedC3RadialRealCoefficient (operatorHeightParameter z) + z.im) *
      (positiveDirichletGradient (operatorHeightParameter z) 0).im
  let sndTarget : Real :=
    (z.re - Real.log 3 -
        z.im * completedC3RadialRealCoefficient (operatorHeightParameter z)) *
      (positiveDirichletGradient (operatorHeightParameter z) 0).im
  have hreadFst : Filter.Tendsto
      (fun cutoff : Nat =>
        inner Real (completedC3OrthonormalCameraVector 1)
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z).fst)
      Filter.atTop
      (nhds (inner Real (completedC3OrthonormalCameraVector 1) target.fst)) := by
    exact
      ((continuous_const.inner
        (WithLp.continuous_fst (p := 2)
          (α := CameraHilbert) (β := CameraHilbert))).tendsto target).comp hsource
  have hreadSnd : Filter.Tendsto
      (fun cutoff : Nat =>
        inner Real (completedC3OrthonormalCameraVector 1)
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z).snd)
      Filter.atTop
      (nhds (inner Real (completedC3OrthonormalCameraVector 1) target.snd)) := by
    exact
      ((continuous_const.inner
        (WithLp.continuous_snd (p := 2)
          (α := CameraHilbert) (β := CameraHilbert))).tendsto target).comp hsource
  have hconstFst : Filter.Tendsto
      (fun _ : Nat => fstTarget) Filter.atTop (nhds fstTarget) :=
    tendsto_const_nhds
  have hconstSnd : Filter.Tendsto
      (fun _ : Nat => sndTarget) Filter.atTop (nhds sndTarget) :=
    tendsto_const_nhds
  have hformulaFst : Filter.Tendsto
      (fun cutoff : Nat =>
        inner Real (completedC3OrthonormalCameraVector 1)
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z).fst)
      Filter.atTop (nhds fstTarget) :=
    hconstFst.congr'
      (Filter.Eventually.of_forall fun cutoff => by
        symm
        exact
          inner_completedC3OrthonormalCameraVector_one_finiteCompressedSource_fst
            hbase cutoff z)
  have hformulaSnd : Filter.Tendsto
      (fun cutoff : Nat =>
        inner Real (completedC3OrthonormalCameraVector 1)
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z).snd)
      Filter.atTop (nhds sndTarget) :=
    hconstSnd.congr'
      (Filter.Eventually.of_forall fun cutoff => by
        symm
        exact
          inner_completedC3OrthonormalCameraVector_one_finiteCompressedSource_snd
            hbase cutoff z)
  constructor
  · change inner Real (completedC3OrthonormalCameraVector 1) target.fst = fstTarget
    exact tendsto_nhds_unique hreadFst hformulaFst
  · change inner Real (completedC3OrthonormalCameraVector 1) target.snd = sndTarget
    exact tendsto_nhds_unique hreadSnd hformulaSnd

/-! ## Exact comparison with the six-camera source readout -/

theorem gramKernel_minimalSlopeCamera_firstC3CameraIndex
    (i : Fin 3) :
    gramKernel minimalSlopeCamera (firstC3CameraIndex i) =
      if i = 1 then 6 else 0 := by
  fin_cases i <;>
    norm_num [gramKernel, periodicMeanKernel, periodicProductMean,
      periodicProductSum, pairPeriod, minimalSlopeCamera,
      completedC3RealCameraIndex, firstC3CameraIndex, cameraLabel,
      cameraSlope, profile, c2Profile, oddProfile, evenProfile,
      dvdIndicator, Finset.sum_range_succ]

theorem gramKernel_minimalSlopeCamera_secondC3CameraIndex
    (i : Fin 3) :
    gramKernel minimalSlopeCamera (secondC3CameraIndex i) =
      if i = 1 then 6 else 0 := by
  fin_cases i <;>
    norm_num [gramKernel, periodicMeanKernel, periodicProductMean,
      periodicProductSum, pairPeriod, minimalSlopeCamera,
      completedC3RealCameraIndex, secondC3CameraIndex, cameraLabel,
      cameraSlope, profile, c2Profile, oddProfile, evenProfile,
      dvdIndicator, Finset.sum_range_succ]

theorem inner_completedC3OrthonormalCameraVector_one_canonicalC3SixCameraSourceMap_fst
    (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3) :
    inner Real (completedC3OrthonormalCameraVector 1)
        (canonicalC3SixCameraSourceMap x).fst =
      Real.sqrt 6 * ((x.1 (1 : Fin 3)).re + (x.2 (1 : Fin 3)).re) := by
  rw [completedC3OrthonormalCameraVector_one]
  unfold canonicalC3SixCameraSourceMap
  rw [WithLp.toLp_fst]
  simp only [real_inner_smul_left]
  change
    (Real.sqrt 6)⁻¹ *
      inner Real (cameraVector minimalSlopeCamera)
        (cameraEmbedding (canonicalC3RealCameraFinsupp x)) = _
  unfold canonicalC3RealCameraFinsupp
  rw [map_add, map_sum, map_sum, inner_add_right]
  simp only [inner_sum]
  simp [cameraVector, gramForm_single_single,
    gramKernel_minimalSlopeCamera_firstC3CameraIndex,
    gramKernel_minimalSlopeCamera_secondC3CameraIndex]
  have hsqrt : Real.sqrt 6 ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 6)]

theorem inner_completedC3OrthonormalCameraVector_one_canonicalC3SixCameraSourceMap_snd
    (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3) :
    inner Real (completedC3OrthonormalCameraVector 1)
        (canonicalC3SixCameraSourceMap x).snd =
      Real.sqrt 6 * ((x.1 (1 : Fin 3)).im + (x.2 (1 : Fin 3)).im) := by
  rw [completedC3OrthonormalCameraVector_one]
  unfold canonicalC3SixCameraSourceMap
  rw [WithLp.toLp_snd]
  simp only [real_inner_smul_left]
  change
    (Real.sqrt 6)⁻¹ *
      inner Real (cameraVector minimalSlopeCamera)
        (cameraEmbedding (canonicalC3ImagCameraFinsupp x)) = _
  unfold canonicalC3ImagCameraFinsupp
  rw [map_add, map_sum, map_sum, inner_add_right]
  simp only [inner_sum]
  simp [cameraVector, gramForm_single_single,
    gramKernel_minimalSlopeCamera_firstC3CameraIndex,
    gramKernel_minimalSlopeCamera_secondC3CameraIndex]
  have hsqrt : Real.sqrt 6 ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 6)]

theorem inner_completedC3OrthonormalCameraVector_one_canonicalCompletedC3SixCameraSource_fst
    (z : Complex) :
    inner Real (completedC3OrthonormalCameraVector 1)
        (canonicalCompletedC3SixCameraSource z).fst =
      Real.sqrt 6 *
        (((canonicalCompletedOperatorC3State z).1 (1 : Fin 3)).re +
          ((canonicalCompletedOperatorC3State z).2 (1 : Fin 3)).re) := by
  exact
    inner_completedC3OrthonormalCameraVector_one_canonicalC3SixCameraSourceMap_fst
      (canonicalCompletedOperatorC3State z)

theorem inner_completedC3OrthonormalCameraVector_one_canonicalCompletedC3SixCameraSource_snd
    (z : Complex) :
    inner Real (completedC3OrthonormalCameraVector 1)
        (canonicalCompletedC3SixCameraSource z).snd =
      Real.sqrt 6 *
        (((canonicalCompletedOperatorC3State z).1 (1 : Fin 3)).im +
          ((canonicalCompletedOperatorC3State z).2 (1 : Fin 3)).im) := by
  exact
    inner_completedC3OrthonormalCameraVector_one_canonicalC3SixCameraSourceMap_snd
      (canonicalCompletedOperatorC3State z)

/-- Convergence to the canonical six-camera source forces two explicit
coordinate identities. -/
theorem finiteCompressedSource_tendsto_canonical_necessary_cameraThreeIdentities
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex)
    (hsource : Filter.Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      Filter.atTop (nhds (canonicalCompletedC3SixCameraSource z))) :
    Real.sqrt 6 *
          (((canonicalCompletedOperatorC3State z).1 (1 : Fin 3)).re +
            ((canonicalCompletedOperatorC3State z).2 (1 : Fin 3)).re) =
        -((z.re - Real.log 3) *
            completedC3RadialRealCoefficient (operatorHeightParameter z) +
          z.im) *
          (positiveDirichletGradient (operatorHeightParameter z) 0).im ∧
      Real.sqrt 6 *
          (((canonicalCompletedOperatorC3State z).1 (1 : Fin 3)).im +
            ((canonicalCompletedOperatorC3State z).2 (1 : Fin 3)).im) =
        (z.re - Real.log 3 -
            z.im * completedC3RadialRealCoefficient (operatorHeightParameter z)) *
          (positiveDirichletGradient (operatorHeightParameter z) 0).im := by
  have hnecessary :=
    finiteCompressedSource_tendsto_necessary_cameraThreeCoordinates
      hbase z (canonicalCompletedC3SixCameraSource z) hsource
  constructor
  · rw [← inner_completedC3OrthonormalCameraVector_one_canonicalCompletedC3SixCameraSource_fst]
    exact hnecessary.1
  · rw [← inner_completedC3OrthonormalCameraVector_one_canonicalCompletedC3SixCameraSource_snd]
    exact hnecessary.2

theorem canonicalCompletedOperatorC3State_eq_greenBoundaryPair (z : Complex) :
    canonicalCompletedOperatorC3State z =
      finiteC3GenuineBracketGreenBoundaryPair 3
        (operatorHeightParameter z) := by
  unfold canonicalCompletedOperatorC3State
  exact canonicalEnrichedC3SourcePort_eq_greenBoundaryPair _

theorem inner_completedC3OrthonormalCameraVector_one_canonicalCompletedC3SixCameraSource_fst_eq_gradient
    (z : Complex) :
    inner Real (completedC3OrthonormalCameraVector 1)
        (canonicalCompletedC3SixCameraSource z).fst =
      Real.sqrt 6 *
        ((completedC3RadialRealCoefficient (operatorHeightParameter z) + 1) *
          (positiveDirichletGradient (operatorHeightParameter z) 1).re) := by
  rw [inner_completedC3OrthonormalCameraVector_one_canonicalCompletedC3SixCameraSource_fst,
    canonicalCompletedOperatorC3State_eq_greenBoundaryPair,
    finiteC3GenuineBracketGreenBoundaryPair_fst_eq_radial_mul_completedPrefix,
    finiteC3GenuineBracketGreenBoundaryPair_snd_eq_completedPrefix,
    canonicalCompletedC3DirichletGradientPrefixState_apply]
  norm_num
  unfold completedC3RadialRealCoefficient
  ring

theorem dirichletTerm_half_eq_realRpow (n : Nat) :
    dirichletTerm (1 / 2 : Complex) (n : Int) =
      (((n : Real) ^ (-(1 / 2 : Real)) : Real) : Complex) := by
  unfold dirichletTerm
  norm_num
  convert (Complex.ofReal_cpow (Nat.cast_nonneg n)
    (-(1 / 2 : Real))).symm using 1
  all_goals norm_num

theorem natDirichletTerm_half_eq_realRpow (n : Nat) :
    natDirichletTerm (1 / 2 : Complex) n =
      (((n : Real) ^ (-(1 / 2 : Real)) : Real) : Complex) := by
  exact dirichletTerm_half_eq_realRpow n

theorem positiveDirichletGradient_half_im (n : Nat) :
    (positiveDirichletGradient (1 / 2 : Complex) n).im = 0 := by
  unfold positiveDirichletGradient
  rw [natDirichletTerm_half_eq_realRpow,
    natDirichletTerm_half_eq_realRpow]
  simp

theorem positiveDirichletGradient_half_one_re_ne_zero :
    (positiveDirichletGradient (1 / 2 : Complex) 1).re ≠ 0 := by
  have hs : (1 / 2 : Complex) ∈ genuineCriticalStrip := by
    constructor <;> norm_num
  have hedge := finiteReflectedGradientEdge_re_pos hs 1
  have hne : positiveDirichletGradient (1 / 2 : Complex) 1 ≠ 0 := by
    intro hzero
    unfold finiteReflectedGradientEdge at hedge
    rw [hzero] at hedge
    simp at hedge
  intro hre
  apply hne
  apply Complex.ext
  · exact hre
  · exact positiveDirichletGradient_half_im 1

theorem completedC3RadialRealCoefficient_operatorHeightParameter_zero :
    completedC3RadialRealCoefficient (operatorHeightParameter 0) = 1 := by
  norm_num [completedC3RadialRealCoefficient, operatorHeightParameter,
    criticalDisplacement]

theorem inner_completedC3OrthonormalCameraVector_one_canonicalCompletedC3SixCameraSource_zero_fst_ne_zero :
    inner Real (completedC3OrthonormalCameraVector 1)
        (canonicalCompletedC3SixCameraSource 0).fst ≠ 0 := by
  rw [inner_completedC3OrthonormalCameraVector_one_canonicalCompletedC3SixCameraSource_fst_eq_gradient,
    completedC3RadialRealCoefficient_operatorHeightParameter_zero]
  norm_num [operatorHeightParameter]
  exact positiveDirichletGradient_half_one_re_ne_zero

theorem canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_zero_fst_readout
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) :
    inner Real (completedC3OrthonormalCameraVector 1)
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff 0).fst = 0 := by
  rw [inner_completedC3OrthonormalCameraVector_one_finiteCompressedSource_fst]
  norm_num [operatorHeightParameter]
  rw [positiveDirichletGradient_half_im]
  simp

/-- The compressed all-cutoff sources cannot converge to the separately
packed canonical six-camera source, already at the central height. -/
theorem canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_not_tendsto_canonical_at_zero
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) :
    ¬ Filter.Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff 0)
      Filter.atTop (nhds (canonicalCompletedC3SixCameraSource 0)) := by
  intro hsource
  have hnecessary :=
    finiteCompressedSource_tendsto_necessary_cameraThreeCoordinates
      hbase 0 (canonicalCompletedC3SixCameraSource 0) hsource
  apply
    inner_completedC3OrthonormalCameraVector_one_canonicalCompletedC3SixCameraSource_zero_fst_ne_zero
  rw [hnecessary.1]
  norm_num [operatorHeightParameter]
  rw [positiveDirichletGradient_half_im]
  simp

end

end CarrySelfAdjointOperator
