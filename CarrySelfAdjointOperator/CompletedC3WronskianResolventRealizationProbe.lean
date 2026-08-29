import CarrySelfAdjointOperator.CompletedTfvdGreenAllOrderIntertwining
import CarrySelfAdjointOperator.CanonicalCompletedC3TfvdResolventDomain
import CarrySelfAdjointOperator.CompletedC3DirichletGradientBracketSource
import Mathlib.Tactic

/-!
# Independent TFVD domain realization probe

The completed TFVD ledger has an ambient Naimark realization independently
of the logarithmic resolvent.  Because its six camera coordinates have finite
support, that realization belongs coordinatewise to the maximal logarithmic
domain.  This file constructs that domain point and checks, before invoking
resolvent uniqueness, whether it is the required response state.

The calculation distinguishes the TFVD source realization from a TFVD
Wronskian response realization.  No Wronskian equality, zero hypothesis, or
new defect equation is assumed.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- The real finite-support Naimark coordinate of the canonical TFVD port. -/
def canonicalCompletedC3TfvdNaimarkSourceRealCoordinate (z : ℂ) :
    NaimarkSpace :=
  naimarkCoreMap
    (c3RealCameraFinsupp
      (canonicalCompletedTfvdGreenPortState (operatorHeightParameter z)))

/-- The imaginary finite-support Naimark coordinate of the canonical TFVD
port. -/
def canonicalCompletedC3TfvdNaimarkSourceImagCoordinate (z : ℂ) :
    NaimarkSpace :=
  naimarkCoreMap
    (c3ImagCameraFinsupp
      (canonicalCompletedTfvdGreenPortState (operatorHeightParameter z)))

theorem canonicalCompletedC3TfvdNaimarkSourceRealCoordinate_mem_domain
    (z : ℂ) :
    canonicalCompletedC3TfvdNaimarkSourceRealCoordinate z ∈
      logarithmicMultiplication.domain := by
  rw [logarithmicMultiplication_domain]
  exact naimarkCoreMap_mem_logarithmicMultiplicationDomain _

theorem canonicalCompletedC3TfvdNaimarkSourceImagCoordinate_mem_domain
    (z : ℂ) :
    canonicalCompletedC3TfvdNaimarkSourceImagCoordinate z ∈
      logarithmicMultiplication.domain := by
  rw [logarithmicMultiplication_domain]
  exact naimarkCoreMap_mem_logarithmicMultiplicationDomain _

/-- Independent maximal-domain lift of the existing TFVD Naimark source.
Unlike `canonicalCompletedC3TfvdResolventDomainVector`, this definition does
not apply a resolvent. -/
def canonicalCompletedC3TfvdNaimarkSourceDomainVector
    (z : ℂ) : RealifiedLogarithmicDomain :=
  (⟨canonicalCompletedC3TfvdNaimarkSourceRealCoordinate z,
      canonicalCompletedC3TfvdNaimarkSourceRealCoordinate_mem_domain z⟩,
    ⟨canonicalCompletedC3TfvdNaimarkSourceImagCoordinate z,
      canonicalCompletedC3TfvdNaimarkSourceImagCoordinate_mem_domain z⟩)

/-- Forgetting the domain witnesses gives exactly the existing TFVD Naimark
state. -/
theorem canonicalCompletedC3TfvdNaimarkSourceDomainVector_embedding
    (z : ℂ) :
    realifiedLogarithmicDomainEmbedding
        (canonicalCompletedC3TfvdNaimarkSourceDomainVector z) =
      canonicalCompletedTfvdGreenNaimarkState
        (operatorHeightParameter z) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change
      canonicalCompletedC3TfvdNaimarkSourceRealCoordinate z =
        (canonicalCompletedTfvdGreenNaimarkState
          (operatorHeightParameter z)).fst
    simp only [canonicalCompletedC3TfvdNaimarkSourceRealCoordinate,
      canonicalCompletedTfvdGreenNaimarkState,
      c3SixCameraNaimarkRealization, ContinuousLinearMap.comp_apply,
      realifiedNaimarkPort_fst, c3SixCameraPacking_apply,
      WithLp.toLp_fst]
    rw [naimarkIsometry_cameraEmbedding]
    rfl
  · change
      canonicalCompletedC3TfvdNaimarkSourceImagCoordinate z =
        (canonicalCompletedTfvdGreenNaimarkState
          (operatorHeightParameter z)).snd
    simp only [canonicalCompletedC3TfvdNaimarkSourceImagCoordinate,
      canonicalCompletedTfvdGreenNaimarkState,
      c3SixCameraNaimarkRealization, ContinuousLinearMap.comp_apply,
      realifiedNaimarkPort_snd, c3SixCameraPacking_apply,
      WithLp.toLp_snd]
    rw [naimarkIsometry_cameraEmbedding]
    rfl

/-- The independent lift is the Naimark port of the canonical C3 source. -/
theorem canonicalCompletedC3TfvdNaimarkSourceDomainVector_embedding_eq_port
    (z : ℂ) :
    realifiedLogarithmicDomainEmbedding
        (canonicalCompletedC3TfvdNaimarkSourceDomainVector z) =
      realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z) := by
  rw [canonicalCompletedC3TfvdNaimarkSourceDomainVector_embedding]
  change
    realifiedNaimarkPort
        (canonicalCompletedTfvdGreenCameraState
          (operatorHeightParameter z)) =
      realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z)
  congr 1
  rw [canonicalCompletedC3SixCameraSource_eq_completedTfvdGreenCameraState]
  rfl

/-- Compressing the source-domain lift returns the same canonical camera
source.  This is source reconstruction, not a resolvent boundary response. -/
theorem realifiedNaimarkAdjoint_canonicalCompletedC3TfvdNaimarkSourceDomainVector
    (z : ℂ) :
    realifiedNaimarkAdjoint
        (realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3TfvdNaimarkSourceDomainVector z)) =
      canonicalCompletedC3SixCameraSource z := by
  rw [canonicalCompletedC3TfvdNaimarkSourceDomainVector_embedding_eq_port]
  change
    (realifiedNaimarkAdjoint ∘L realifiedNaimarkPort)
        (canonicalCompletedC3SixCameraSource z) =
      canonicalCompletedC3SixCameraSource z
  rw [NativeCarryC3Crosswalk.realifiedNaimarkAdjoint_comp_realifiedNaimarkPort]
  rfl

/-- Consequently the candidate boundary readout of the raw TFVD Naimark
source is identically zero.  Both terms are the same source pairing. -/
theorem canonicalCompletedC3TfvdNaimarkSourceDomainVector_boundaryReadout_eq_zero
    (z w : ℂ) :
    canonicalCompletedC3CandidateResolventBoundaryReadout z w
        (canonicalCompletedC3TfvdNaimarkSourceDomainVector z)
        (canonicalCompletedC3TfvdNaimarkSourceDomainVector w) = 0 := by
  unfold canonicalCompletedC3CandidateResolventBoundaryReadout
  rw [realifiedNaimarkAdjoint_canonicalCompletedC3TfvdNaimarkSourceDomainVector,
    realifiedNaimarkAdjoint_canonicalCompletedC3TfvdNaimarkSourceDomainVector]
  exact sub_self _

/-- The boundary readout of the actual Gamma domain vector is the positive
Gamma boundary.  This specialization uses only the universal vector-defect
factorization. -/
theorem canonicalCompletedC3CandidateResolventBoundaryReadout_gamma_eq
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3CandidateResolventBoundaryReadout z w
        (carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z))
        (carryGammaIntoDomain w hw (canonicalCompletedC3SixCameraSource w)) =
      canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw := by
  symm
  apply sub_eq_zero.mp
  rw [canonicalCompletedC3GammaBoundary_sub_candidate_eq_universalDefectReadout]
  have hdefect :
      canonicalCompletedC3UniversalResolventDefect z w hz hw
          (carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z))
          (carryGammaIntoDomain w hw (canonicalCompletedC3SixCameraSource w)) =
        0 := by
    simp [canonicalCompletedC3UniversalResolventDefect]
  rw [hdefect, canonicalCompletedC3UniversalResolventDefectReadout_zero]

/-- The direct TFVD Naimark source lift cannot satisfy the canonical
resolvent equation.  If it did, resolvent uniqueness would identify it with
Gamma, contradicting its zero diagonal boundary and strict Gamma
nondegeneracy. -/
theorem canonicalCompletedC3TfvdNaimarkSourceDomainVector_not_defectEquation
    {z : ℂ} (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hz : z.im ≠ 0) :
    ¬(realifiedNaimarkScalar z
          (realifiedLogarithmicDomainEmbedding
            (canonicalCompletedC3TfvdNaimarkSourceDomainVector z)) =
        realifiedLogarithmicMultiplication
            (canonicalCompletedC3TfvdNaimarkSourceDomainVector z) +
          realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z)) := by
  intro hequation
  have hstate :
      canonicalCompletedC3TfvdNaimarkSourceDomainVector z =
        carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z) :=
    carryGammaIntoDomain_unique z hz
      (canonicalCompletedC3SixCameraSource z)
      (canonicalCompletedC3TfvdNaimarkSourceDomainVector z) hequation
  have hsourceZero :=
    canonicalCompletedC3TfvdNaimarkSourceDomainVector_boundaryReadout_eq_zero
      z z
  rw [hstate] at hsourceZero
  have hgammaBoundary :=
    canonicalCompletedC3CandidateResolventBoundaryReadout_gamma_eq z z hz hz
  apply canonicalCompletedC3PolarizedGammaBoundaryReadout_diagonal_ne_zero
    hzStrip hz
  exact hgammaBoundary.symm.trans hsourceZero

/-- The source actually generated by applying `z-Y` to the direct TFVD
Naimark lift. -/
def canonicalCompletedC3TfvdNaimarkInducedDefectSource
    (z : ℂ) : RealifiedNaimarkComplexification :=
  realifiedLambdaMinusLogarithmicMultiplication z
    (canonicalCompletedC3TfvdNaimarkSourceDomainVector z)

/-- The independent TFVD source lift satisfies a defect equation exactly for
its induced source. -/
theorem canonicalCompletedC3TfvdNaimarkSourceDomainVector_inducedDefectEquation
    (z : ℂ) :
    realifiedNaimarkScalar z
        (realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3TfvdNaimarkSourceDomainVector z)) =
      realifiedLogarithmicMultiplication
          (canonicalCompletedC3TfvdNaimarkSourceDomainVector z) +
        canonicalCompletedC3TfvdNaimarkInducedDefectSource z := by
  unfold canonicalCompletedC3TfvdNaimarkInducedDefectSource
    realifiedLambdaMinusLogarithmicMultiplication
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_coe]
  abel

/-- Exact first noncommuting square: throughout the off-axis open strip, the
source induced by the direct TFVD Naimark lift is not the canonical C3 source
appearing in the logarithmic resolvent equation. -/
theorem canonicalCompletedC3TfvdNaimarkInducedDefectSource_ne_canonical
    {z : ℂ} (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hz : z.im ≠ 0) :
    canonicalCompletedC3TfvdNaimarkInducedDefectSource z ≠
      realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z) := by
  intro hsource
  apply canonicalCompletedC3TfvdNaimarkSourceDomainVector_not_defectEquation
    hzStrip hz
  rw [canonicalCompletedC3TfvdNaimarkSourceDomainVector_inducedDefectEquation,
    hsource]

/-! ## Finite all-cutoff response/boundary domain lifts -/

/-- Every permanent Gram--Schmidt camera vector still comes from a finite
camera core.  Gram--Schmidt changes coordinates but does not leave the span
of the finitely many literal cameras used at that stage. -/
theorem completedC3OrthonormalCameraVector_mem_cameraEmbeddingRange
    (n : ℕ) :
    completedC3OrthonormalCameraVector n ∈
      LinearMap.range cameraEmbedding.toLinearMap := by
  unfold completedC3OrthonormalCameraVector
  apply Submodule.smul_mem
  have hspan := InnerProductSpace.gramSchmidt_mem_span
    ℝ completedC3RawCameraVector (le_refl n)
  apply (show
      Submodule.span ℝ (completedC3RawCameraVector '' Set.Iic n) ≤
        LinearMap.range cameraEmbedding.toLinearMap by
    rw [Submodule.span_le]
    rintro x ⟨i, hi, rfl⟩
    refine ⟨Finsupp.single (completedC3RealCameraIndex i) 1, ?_⟩
    simp [completedC3RawCameraVector, cameraVector])
  exact hspan

/-- A chosen finite camera coefficient vector realizing the permanent
orthonormal coordinate. -/
def completedC3OrthonormalCameraCore (n : ℕ) : CameraFinsupp :=
  Classical.choose
    (completedC3OrthonormalCameraVector_mem_cameraEmbeddingRange n)

@[simp] theorem cameraEmbedding_completedC3OrthonormalCameraCore
    (n : ℕ) :
    cameraEmbedding (completedC3OrthonormalCameraCore n) =
      completedC3OrthonormalCameraVector n :=
  Classical.choose_spec
    (completedC3OrthonormalCameraVector_mem_cameraEmbeddingRange n)

/-- The Naimark image of every permanent all-cutoff coordinate belongs to
the maximal logarithmic domain. -/
theorem naimarkIsometry_completedC3OrthonormalCameraVector_mem_domain
    (n : ℕ) :
    naimarkIsometry (completedC3OrthonormalCameraVector n) ∈
      logarithmicMultiplication.domain := by
  rw [← cameraEmbedding_completedC3OrthonormalCameraCore,
    naimarkIsometry_cameraEmbedding]
  rw [logarithmicMultiplication_domain]
  exact naimarkCoreMap_mem_logarithmicMultiplicationDomain _

/-- Finite camera-core synthesis using the chosen representatives of the
permanent orthonormal camera coordinates. -/
def finiteC3CameraCoreCoordinateState (M : ℕ)
    (x : EuclideanSpace ℝ (FiniteC3RealCoordinate M)) : CameraFinsupp :=
  ∑ j : FiniteC3RealCoordinate M,
    x j • completedC3OrthonormalCameraCore (finiteC3RealCoordinateNat j)

/-- Camera completion of the finite core synthesis is exactly the permanent
all-cutoff camera-coordinate synthesis. -/
theorem cameraEmbedding_finiteC3CameraCoreCoordinateState
    (M : ℕ) (x : EuclideanSpace ℝ (FiniteC3RealCoordinate M)) :
    cameraEmbedding (finiteC3CameraCoreCoordinateState M x) =
      finiteC3CameraCoordinateLinearMap M x := by
  unfold finiteC3CameraCoreCoordinateState finiteC3CameraCoordinateLinearMap
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, cameraEmbedding_completedC3OrthonormalCameraCore]

/-- Finite camera core of one complex TFVD leg. -/
def finiteC3LegCameraCore (M : ℕ)
    (x : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M) : CameraFinsupp :=
  finiteC3CameraCoreCoordinateState M
    (finiteC3LegRealCoordinateIsometry M x)

/-- The chosen finite leg core realizes the existing all-cutoff leg
isometry exactly. -/
theorem cameraEmbedding_finiteC3LegCameraCore
    (M : ℕ)
    (x : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M) :
    cameraEmbedding (finiteC3LegCameraCore M x) =
      finiteC3LegCameraIsometry M x := by
  rw [finiteC3LegCameraCore,
    cameraEmbedding_finiteC3CameraCoreCoordinateState]
  rfl

/-- The finite all-cutoff symplectic TFVD state, bundled with coordinatewise
membership in the maximal logarithmic domain. -/
def finiteC3SymplecticNaimarkDomainVector (M : ℕ)
    (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    RealifiedLogarithmicDomain :=
  (⟨naimarkCoreMap (-finiteC3LegCameraCore M x.1),
      by
        rw [logarithmicMultiplication_domain]
        exact naimarkCoreMap_mem_logarithmicMultiplicationDomain _⟩,
    ⟨naimarkCoreMap (finiteC3LegCameraCore M x.2),
      by
        rw [logarithmicMultiplication_domain]
        exact naimarkCoreMap_mem_logarithmicMultiplicationDomain _⟩)

/-- Forgetting the finite domain witnesses gives exactly the existing
all-cutoff symplectic Naimark realization. -/
theorem finiteC3SymplecticNaimarkDomainVector_embedding
    (M : ℕ) (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    realifiedLogarithmicDomainEmbedding
        (finiteC3SymplecticNaimarkDomainVector M x) =
      finiteC3SymplecticNaimarkRealization M x := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change
      (realifiedLogarithmicDomainEmbedding
        (finiteC3SymplecticNaimarkDomainVector M x)).fst =
        (finiteC3SymplecticNaimarkRealization M x).fst
    rw [realifiedLogarithmicDomainEmbedding_fst]
    change naimarkCoreMap (-finiteC3LegCameraCore M x.1) = _
    rw [show finiteC3SymplecticNaimarkRealization M x =
        realifiedNaimarkPort (finiteC3SymplecticCameraPacking M x) by rfl,
      realifiedNaimarkPort_fst, finiteC3SymplecticCameraPacking_apply,
      WithLp.toLp_fst]
    rw [map_neg, ← cameraEmbedding_finiteC3LegCameraCore,
      map_neg, naimarkIsometry_cameraEmbedding]
    rfl
  · change
      (realifiedLogarithmicDomainEmbedding
        (finiteC3SymplecticNaimarkDomainVector M x)).snd =
        (finiteC3SymplecticNaimarkRealization M x).snd
    rw [realifiedLogarithmicDomainEmbedding_snd]
    change naimarkCoreMap (finiteC3LegCameraCore M x.2) = _
    rw [show finiteC3SymplecticNaimarkRealization M x =
        realifiedNaimarkPort (finiteC3SymplecticCameraPacking M x) by rfl,
      realifiedNaimarkPort_snd, finiteC3SymplecticCameraPacking_apply,
      WithLp.toLp_snd]
    change naimarkCoreMap (finiteC3LegCameraCore M x.2) =
      naimarkIsometry (finiteC3LegCameraIsometry M x.2)
    rw [← cameraEmbedding_finiteC3LegCameraCore,
      naimarkIsometry_cameraEmbedding]
    rfl

/-- The finite two-leg port reconstructed from the separated causal Green
response and its exact boundary return. -/
def canonicalCompletedC3CausalResponseBoundaryTfvdPort
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (s : ℂ) :
    NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier
      (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1) :=
  let state :=
    canonicalCompletedC3DirichletGradientBracketGreenResponse base cutoff s +
      canonicalCompletedC3DirichletGradientPrefixBoundaryReturn
        hbase cutoff s
  (WithLp.toLp 2 (fun i =>
      (completedC3RadialRealCoefficient s : ℂ) * state i.val),
    WithLp.toLp 2 (fun i => state i.val))

/-- Causal response plus boundary return is exactly the finite Genuine/TFVD
port, before Naimark promotion or a scalar boundary readout. -/
theorem canonicalCompletedC3CausalResponseBoundaryTfvdPort_eq_genuine
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (s : ℂ) :
    canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff s =
      NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
        (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1) s := by
  let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
  have hsum :
      canonicalCompletedC3DirichletGradientBracketGreenResponse base cutoff s +
          canonicalCompletedC3DirichletGradientPrefixBoundaryReturn
            hbase cutoff s =
        canonicalCompletedC3DirichletGradientPrefixState s N := by
    exact canonicalCompletedC3DirichletGradient_greenResponse_add_boundary_eq_prefix
      hbase s
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    funext i
    change
      (completedC3RadialRealCoefficient s : ℂ) *
          (canonicalCompletedC3DirichletGradientBracketGreenResponse
              base cutoff s +
            canonicalCompletedC3DirichletGradientPrefixBoundaryReturn
              hbase cutoff s) i.val = _
    rw [hsum]
    exact (finiteC3GenuineBracketGreenBoundaryPair_fst_eq_radial_mul_completedPrefix
      N s i).symm
  · apply WithLp.ofLp_injective 2
    funext i
    change
      (canonicalCompletedC3DirichletGradientBracketGreenResponse
            base cutoff s +
          canonicalCompletedC3DirichletGradientPrefixBoundaryReturn
            hbase cutoff s) i.val = _
    rw [hsum]
    exact (finiteC3GenuineBracketGreenBoundaryPair_snd_eq_completedPrefix
      N s i).symm

/-- Canonical maximal-domain lift of the finite causal response/boundary
TFVD port. -/
def canonicalCompletedC3CausalResponseBoundaryDomainVector
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (s : ℂ) : RealifiedLogarithmicDomain :=
  finiteC3SymplecticNaimarkDomainVector
    (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
    (canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff s)

/-- Forgetting its graph-domain witnesses yields exactly the finite
Genuine/TFVD symplectic Naimark state. -/
theorem canonicalCompletedC3CausalResponseBoundaryDomainVector_embedding
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (s : ℂ) :
    realifiedLogarithmicDomainEmbedding
        (canonicalCompletedC3CausalResponseBoundaryDomainVector
          hbase cutoff s) =
      finiteC3SymplecticNaimarkRealization
        (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
          (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
          s) := by
  rw [canonicalCompletedC3CausalResponseBoundaryDomainVector,
    finiteC3SymplecticNaimarkDomainVector_embedding,
    canonicalCompletedC3CausalResponseBoundaryTfvdPort_eq_genuine]

/-- The finite domain vectors converge after forgetting graph-domain
witnesses to the already constructed completed all-cutoff TFVD state. -/
theorem canonicalCompletedC3CausalResponseBoundaryDomainVector_embedding_tendsto
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun cutoff : ℕ =>
        realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3CausalResponseBoundaryDomainVector
            hbase cutoff s))
      Filter.atTop
      (nhds (completedC3SymplecticNaimarkState s hs)) := by
  have hlimit :=
    (finiteC3GenuineSymplecticNaimarkRealization_tendsto hs).comp
      (finiteCameraWindow_add_one_tendsto_atTop hbase)
  exact hlimit.congr'
    (Filter.Eventually.of_forall fun cutoff =>
      (canonicalCompletedC3CausalResponseBoundaryDomainVector_embedding
        hbase cutoff s).symm)

/-- Coordinatewise closed-graph passage for the realified logarithmic
operator.  Ambient convergence alone is insufficient; convergence of the
two logarithmic images is the exact additional datum needed to obtain a
maximal-domain limit. -/
theorem exists_realifiedLogarithmicDomain_limit_of_graph_tendsto
    (u : ℕ → RealifiedLogarithmicDomain)
    (limit image : RealifiedNaimarkComplexification)
    (hembedding : Filter.Tendsto
      (fun n => realifiedLogarithmicDomainEmbedding (u n))
      Filter.atTop (nhds limit))
    (himage : Filter.Tendsto
      (fun n => realifiedLogarithmicMultiplication (u n))
      Filter.atTop (nhds image)) :
    ∃ uLimit : RealifiedLogarithmicDomain,
      realifiedLogarithmicDomainEmbedding uLimit = limit ∧
        realifiedLogarithmicMultiplication uLimit = image := by
  have hembeddingFst : Filter.Tendsto
      (fun n => ((u n).1 : NaimarkSpace))
      Filter.atTop (nhds limit.fst) := by
    have h := ((WithLp.continuous_fst (p := 2)
      (α := NaimarkSpace) (β := NaimarkSpace)).tendsto limit).comp hembedding
    exact h.congr' (Filter.Eventually.of_forall fun n =>
      realifiedLogarithmicDomainEmbedding_fst (u n))
  have hembeddingSnd : Filter.Tendsto
      (fun n => ((u n).2 : NaimarkSpace))
      Filter.atTop (nhds limit.snd) := by
    have h := ((WithLp.continuous_snd (p := 2)
      (α := NaimarkSpace) (β := NaimarkSpace)).tendsto limit).comp hembedding
    exact h.congr' (Filter.Eventually.of_forall fun n =>
      realifiedLogarithmicDomainEmbedding_snd (u n))
  have himageFst : Filter.Tendsto
      (fun n => logarithmicMultiplication (u n).1)
      Filter.atTop (nhds image.fst) := by
    have h := ((WithLp.continuous_fst (p := 2)
      (α := NaimarkSpace) (β := NaimarkSpace)).tendsto image).comp himage
    exact h.congr' (Filter.Eventually.of_forall fun n =>
      realifiedLogarithmicMultiplication_fst (u n))
  have himageSnd : Filter.Tendsto
      (fun n => logarithmicMultiplication (u n).2)
      Filter.atTop (nhds image.snd) := by
    have h := ((WithLp.continuous_snd (p := 2)
      (α := NaimarkSpace) (β := NaimarkSpace)).tendsto image).comp himage
    exact h.congr' (Filter.Eventually.of_forall fun n =>
      realifiedLogarithmicMultiplication_snd (u n))
  have hgraphFst :
      (limit.fst, image.fst) ∈ logarithmicMultiplication.graph :=
    logarithmicMultiplication_isClosed.mem_of_tendsto
      (hembeddingFst.prodMk_nhds himageFst)
      (Filter.Eventually.of_forall fun n =>
        logarithmicMultiplication.mem_graph (u n).1)
  have hgraphSnd :
      (limit.snd, image.snd) ∈ logarithmicMultiplication.graph :=
    logarithmicMultiplication_isClosed.mem_of_tendsto
      (hembeddingSnd.prodMk_nhds himageSnd)
      (Filter.Eventually.of_forall fun n =>
        logarithmicMultiplication.mem_graph (u n).2)
  rcases (LinearPMap.mem_graph_iff logarithmicMultiplication).mp hgraphFst with
    ⟨uFst, huFst, hmulFst⟩
  rcases (LinearPMap.mem_graph_iff logarithmicMultiplication).mp hgraphSnd with
    ⟨uSnd, huSnd, hmulSnd⟩
  refine ⟨(uFst, uSnd), ?_, ?_⟩
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact huFst
    · exact huSnd
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact hmulFst
    · exact hmulSnd

/-- Specialization of the closed-graph passage to the canonical finite
causal response/boundary TFVD vectors.  It isolates convergence of their
logarithmic images as the only remaining datum needed to lift the completed
all-cutoff state to the maximal logarithmic domain. -/
theorem exists_canonicalCompletedC3CausalResponseBoundaryDomainLimit
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    {s : ℂ} (hs : 0 < s.re)
    (image : RealifiedNaimarkComplexification)
    (himage : Filter.Tendsto
      (fun cutoff : ℕ =>
        realifiedLogarithmicMultiplication
          (canonicalCompletedC3CausalResponseBoundaryDomainVector
            hbase cutoff s))
      Filter.atTop (nhds image)) :
    ∃ uLimit : RealifiedLogarithmicDomain,
      realifiedLogarithmicDomainEmbedding uLimit =
          completedC3SymplecticNaimarkState s hs ∧
        realifiedLogarithmicMultiplication uLimit = image := by
  exact exists_realifiedLogarithmicDomain_limit_of_graph_tendsto
    (fun cutoff : ℕ =>
      canonicalCompletedC3CausalResponseBoundaryDomainVector
        hbase cutoff s)
    (completedC3SymplecticNaimarkState s hs)
    image
    (canonicalCompletedC3CausalResponseBoundaryDomainVector_embedding_tendsto
      hbase hs)
    himage

/-- The logarithmic image forced by the canonical C3 resolvent equation at
the completed all-cutoff TFVD state.  This is a target for convergence, not
an independently postulated response state. -/
def canonicalCompletedC3CausalResponseBoundaryExpectedLogarithmicImage
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    RealifiedNaimarkComplexification :=
  realifiedNaimarkScalar z
      (completedC3SymplecticNaimarkState
        (operatorHeightParameter z) hs) -
    realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z)

/-- Source induced at one cutoff by applying the concrete logarithmic defect
operator `z - Y` to the finite causal response/boundary TFVD vector. -/
def canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (z : ℂ) : RealifiedNaimarkComplexification :=
  realifiedLambdaMinusLogarithmicMultiplication z
    (canonicalCompletedC3CausalResponseBoundaryDomainVector
      hbase cutoff (operatorHeightParameter z))

/-- Canonical camera compression of the finite logarithmic defect source. -/
def canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (z : ℂ) : RealifiedCameraComplexification :=
  realifiedNaimarkAdjoint
    (canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource
      hbase cutoff z)

/-- Component of the finite logarithmic defect source not reconstructed by
the canonical camera readout. -/
def canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (z : ℂ) : RealifiedNaimarkComplexification :=
  canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource
      hbase cutoff z -
    realifiedNaimarkPort
      (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
        hbase cutoff z)

/-- Exact decomposition of every finite induced source into its canonical
camera reconstruction and the remaining ambient component. -/
theorem canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource_eq_port_add_leak
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (z : ℂ) :
    canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource
        hbase cutoff z =
      realifiedNaimarkPort
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z) +
        canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
          hbase cutoff z := by
  unfold canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
  abel

/-- The leak is invisible to the canonical camera readout.  Hence it is the
genuine complementary Naimark channel left after coherent reconstruction. -/
theorem realifiedNaimarkAdjoint_canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (z : ℂ) :
    realifiedNaimarkAdjoint
        (canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
          hbase cutoff z) = 0 := by
  rw [canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak,
    map_sub]
  change
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z -
        (realifiedNaimarkAdjoint ∘L realifiedNaimarkPort)
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z) =
      0
  rw [NativeCarryC3Crosswalk.realifiedNaimarkAdjoint_comp_realifiedNaimarkPort]
  simp

/-- Exact carrier/no-leak decomposition of the finite source convergence.
The first limit is intrinsic camera reconstruction.  The second is the
ambient Naimark component invisible to that readout. -/
theorem canonicalCompletedC3CausalResponseBoundary_inducedSource_tendsto_iff_compressed_and_noLeak
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) :
    Filter.Tendsto
        (fun cutoff : ℕ =>
          canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource
            hbase cutoff z)
        Filter.atTop
        (nhds (realifiedNaimarkPort
          (canonicalCompletedC3SixCameraSource z))) ↔
      Filter.Tendsto
          (fun cutoff : ℕ =>
            canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
              hbase cutoff z)
          Filter.atTop
          (nhds (canonicalCompletedC3SixCameraSource z)) ∧
        Filter.Tendsto
          (fun cutoff : ℕ =>
            canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
              hbase cutoff z)
          Filter.atTop (nhds 0) := by
  constructor
  · intro hsource
    have hcompressed :=
      realifiedNaimarkAdjoint.continuous.continuousAt.tendsto.comp hsource
    have hadjoint :
        realifiedNaimarkAdjoint
            (realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z)) =
          canonicalCompletedC3SixCameraSource z := by
      change
        (realifiedNaimarkAdjoint ∘L realifiedNaimarkPort)
            (canonicalCompletedC3SixCameraSource z) =
          canonicalCompletedC3SixCameraSource z
      rw [NativeCarryC3Crosswalk.realifiedNaimarkAdjoint_comp_realifiedNaimarkPort]
      rfl
    rw [hadjoint] at hcompressed
    have hported :=
      realifiedNaimarkPort.continuous.continuousAt.tendsto.comp hcompressed
    have hleak := hsource.sub hported
    refine ⟨hcompressed, ?_⟩
    simpa [canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak,
      canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource]
      using hleak
  · rintro ⟨hcompressed, hleak⟩
    have hported :=
      realifiedNaimarkPort.continuous.continuousAt.tendsto.comp hcompressed
    have hsource := hported.add hleak
    simpa [canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak,
      canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource]
      using hsource

/-- The remaining graph convergence is exactly the geometric assertion that
the finite logarithmic defect sources converge to the canonical C3 source.
This equivalence uses only the already-proved ambient convergence and the
linear identity `(z - Y)u = zu - Yu`. -/
theorem canonicalCompletedC3CausalResponseBoundary_logarithmicImage_tendsto_iff_inducedSource
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    Filter.Tendsto
        (fun cutoff : ℕ =>
          realifiedLogarithmicMultiplication
            (canonicalCompletedC3CausalResponseBoundaryDomainVector
              hbase cutoff (operatorHeightParameter z)))
        Filter.atTop
        (nhds
          (canonicalCompletedC3CausalResponseBoundaryExpectedLogarithmicImage
            z hs)) ↔
      Filter.Tendsto
        (fun cutoff : ℕ =>
          canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource
            hbase cutoff z)
        Filter.atTop
        (nhds (realifiedNaimarkPort
          (canonicalCompletedC3SixCameraSource z))) := by
  have hscalar : Filter.Tendsto
      (fun cutoff : ℕ =>
        realifiedNaimarkScalar z
          (realifiedLogarithmicDomainEmbedding
            (canonicalCompletedC3CausalResponseBoundaryDomainVector
              hbase cutoff (operatorHeightParameter z))))
      Filter.atTop
      (nhds (realifiedNaimarkScalar z
        (completedC3SymplecticNaimarkState
          (operatorHeightParameter z) hs))) :=
    (realifiedNaimarkScalar z).continuous.continuousAt.tendsto.comp
      (canonicalCompletedC3CausalResponseBoundaryDomainVector_embedding_tendsto
        hbase hs)
  constructor
  · intro himage
    have hsource := hscalar.sub himage
    have htarget :
        realifiedNaimarkScalar z
              (completedC3SymplecticNaimarkState
                (operatorHeightParameter z) hs) -
            canonicalCompletedC3CausalResponseBoundaryExpectedLogarithmicImage
              z hs =
          realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z) := by
      unfold canonicalCompletedC3CausalResponseBoundaryExpectedLogarithmicImage
      abel
    rw [htarget] at hsource
    exact hsource.congr'
      (Filter.Eventually.of_forall fun cutoff => by
        unfold canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource
          realifiedLambdaMinusLogarithmicMultiplication
        simp only [LinearMap.sub_apply, LinearMap.coe_comp,
          Function.comp_apply, ContinuousLinearMap.coe_coe])
  · intro hsource
    have himage := hscalar.sub hsource
    have htarget :
        realifiedNaimarkScalar z
              (completedC3SymplecticNaimarkState
                (operatorHeightParameter z) hs) -
            realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z) =
          canonicalCompletedC3CausalResponseBoundaryExpectedLogarithmicImage
            z hs := by
      rfl
    rw [htarget] at himage
    exact himage.congr'
      (Filter.Eventually.of_forall fun cutoff => by
        unfold canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource
          realifiedLambdaMinusLogarithmicMultiplication
        simp only [LinearMap.sub_apply, LinearMap.coe_comp,
          Function.comp_apply, ContinuousLinearMap.coe_coe]
        abel)

/-- A graph-limit proof for the finite causal response/boundary vectors
produces a completed maximal-domain vector satisfying the canonical C3
resolvent equation.  Thus no scalar Wronskian equality is required for this
vector realization; the precise remaining gate is the displayed `Tendsto`
of logarithmic images. -/
theorem exists_canonicalCompletedC3CausalResponseBoundaryResolventCandidate_of_graphTendsto
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re)
    (himage : Filter.Tendsto
      (fun cutoff : ℕ =>
        realifiedLogarithmicMultiplication
          (canonicalCompletedC3CausalResponseBoundaryDomainVector
            hbase cutoff (operatorHeightParameter z)))
      Filter.atTop
      (nhds
        (canonicalCompletedC3CausalResponseBoundaryExpectedLogarithmicImage
          z hs))) :
    ∃ candidate : RealifiedLogarithmicDomain,
      realifiedLogarithmicDomainEmbedding candidate =
          completedC3SymplecticNaimarkState
            (operatorHeightParameter z) hs ∧
        realifiedNaimarkScalar z
            (realifiedLogarithmicDomainEmbedding candidate) =
          realifiedLogarithmicMultiplication candidate +
            realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z) := by
  rcases exists_canonicalCompletedC3CausalResponseBoundaryDomainLimit
      hbase hs
      (canonicalCompletedC3CausalResponseBoundaryExpectedLogarithmicImage
        z hs)
      himage with
    ⟨candidate, hembedding, hlogarithmic⟩
  refine ⟨candidate, hembedding, ?_⟩
  rw [hembedding, hlogarithmic]
  unfold canonicalCompletedC3CausalResponseBoundaryExpectedLogarithmicImage
  abel

/-- Direct geometric consumer for the completed resolvent candidate.  The
only inputs are convergence of the compressed source to the canonical C3
source and disappearance of the complementary Naimark channel. -/
theorem exists_canonicalCompletedC3CausalResponseBoundaryResolventCandidate_of_compressedSource_and_noLeak
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re)
    (hcompressed : Filter.Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      Filter.atTop (nhds (canonicalCompletedC3SixCameraSource z)))
    (hnoLeak : Filter.Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
          hbase cutoff z)
      Filter.atTop (nhds 0)) :
    ∃ candidate : RealifiedLogarithmicDomain,
      realifiedLogarithmicDomainEmbedding candidate =
          completedC3SymplecticNaimarkState
            (operatorHeightParameter z) hs ∧
        realifiedNaimarkScalar z
            (realifiedLogarithmicDomainEmbedding candidate) =
          realifiedLogarithmicMultiplication candidate +
            realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z) := by
  apply
    exists_canonicalCompletedC3CausalResponseBoundaryResolventCandidate_of_graphTendsto
      hbase z hs
  rw [canonicalCompletedC3CausalResponseBoundary_logarithmicImage_tendsto_iff_inducedSource
    hbase z hs,
    canonicalCompletedC3CausalResponseBoundary_inducedSource_tendsto_iff_compressed_and_noLeak
      hbase z]
  exact ⟨hcompressed, hnoLeak⟩

end

end CarrySelfAdjointOperator
