import CarrySelfAdjointOperator.CompletedC3CompressedGammaGramCorrection
import Mathlib.Tactic

/-!
# Canonical coisometric Naimark block

The all-bases Naimark port is an isometry and its adjoint is the canonical
camera readout.  This module packages the part of that geometry which is
lost by compression alone.  Every ambient vector is sent to the pair

`(camera readout, orthogonal escape)`

and is reconstructed exactly from those two channels.  The resulting block
is an isometry.  Thus no ambient direction is discarded, including the
nonzero leak already exhibited by the C3 obstruction witness.
-/

open scoped InnerProductSpace lp

namespace CarrySelfAdjointOperator

open Filter
open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-! ## The port projection is the orthogonal projection -/

/-- The complementary component of the canonical Naimark-port projection. -/
def canonicalCompletedC3AmbientPortEscape :
    RealifiedNaimarkComplexification →L[ℝ]
      RealifiedNaimarkComplexification :=
  (1 : RealifiedNaimarkComplexification →L[ℝ]
      RealifiedNaimarkComplexification) -
    canonicalCompletedC3AmbientPortProjection

@[simp] theorem canonicalCompletedC3AmbientPortEscape_apply
    (x : RealifiedNaimarkComplexification) :
    canonicalCompletedC3AmbientPortEscape x =
      x - canonicalCompletedC3AmbientPortProjection x := by
  rfl

/-- The range of `U U*` is exactly the promoted camera range. -/
theorem canonicalCompletedC3AmbientPortProjection_range :
    canonicalCompletedC3AmbientPortProjection.range =
      realifiedNaimarkPort.range := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨realifiedNaimarkAdjoint x, rfl⟩
  · rintro y ⟨u, rfl⟩
    exact ⟨realifiedNaimarkPort u,
      canonicalCompletedC3AmbientPortProjection_realifiedNaimarkPort u⟩

/-- `U U*` is symmetric in the ambient real Hilbert structure. -/
theorem canonicalCompletedC3AmbientPortProjection_isSymmetric :
    canonicalCompletedC3AmbientPortProjection.toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ
      (realifiedNaimarkPort (realifiedNaimarkAdjoint x)) y =
    inner ℝ x
      (realifiedNaimarkPort (realifiedNaimarkAdjoint y))
  rw [inner_realifiedNaimarkPort_eq_inner_realifiedNaimarkAdjoint,
    inner_realifiedNaimarkAdjoint_eq_inner_realifiedNaimarkPort]

/-- `U U*` is a genuine star projection, not only an algebraic idempotent. -/
theorem canonicalCompletedC3AmbientPortProjection_isStarProjection :
    IsStarProjection canonicalCompletedC3AmbientPortProjection := by
  rw [ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]
  refine ⟨?_, canonicalCompletedC3AmbientPortProjection_isSymmetric⟩
  change canonicalCompletedC3AmbientPortProjection.toLinearMap ∘ₗ
      canonicalCompletedC3AmbientPortProjection.toLinearMap =
    canonicalCompletedC3AmbientPortProjection.toLinearMap
  apply LinearMap.ext
  exact canonicalCompletedC3AmbientPortProjection_idempotent

/-- Canonical orthogonal-projection spelling of the Naimark coisometry. -/
theorem canonicalCompletedC3AmbientPortProjection_eq_starProjection_range :
    ∃ (_ : canonicalCompletedC3AmbientPortProjection.range.HasOrthogonalProjection),
      canonicalCompletedC3AmbientPortProjection =
        canonicalCompletedC3AmbientPortProjection.range.starProjection := by
  exact isStarProjection_iff_eq_starProjection_range.mp
    canonicalCompletedC3AmbientPortProjection_isStarProjection

/-! ## Lossless port-plus-escape block -/

/-- Hilbert direct sum retaining both the intrinsic camera readout and the
ambient component invisible to that readout. -/
abbrev CanonicalCompletedC3NaimarkPortEscapeCarrier :=
  WithLp 2
    (RealifiedCameraComplexification × RealifiedNaimarkComplexification)

/-- Canonical lossless readout `x ↦ (U* x, x - U U* x)`. -/
def canonicalCompletedC3NaimarkPortEscapeReadout :
    RealifiedNaimarkComplexification →L[ℝ]
      CanonicalCompletedC3NaimarkPortEscapeCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ
      RealifiedCameraComplexification
      RealifiedNaimarkComplexification).symm.toContinuousLinearMap ∘L
    realifiedNaimarkAdjoint.prod canonicalCompletedC3AmbientPortEscape

@[simp] theorem canonicalCompletedC3NaimarkPortEscapeReadout_fst
    (x : RealifiedNaimarkComplexification) :
    (canonicalCompletedC3NaimarkPortEscapeReadout x).fst =
      realifiedNaimarkAdjoint x := by
  rfl

@[simp] theorem canonicalCompletedC3NaimarkPortEscapeReadout_snd
    (x : RealifiedNaimarkComplexification) :
    (canonicalCompletedC3NaimarkPortEscapeReadout x).snd =
      x - canonicalCompletedC3AmbientPortProjection x := by
  rfl

/-- Synthesis of an intrinsic camera channel and an ambient escape channel. -/
def canonicalCompletedC3NaimarkPortEscapeSynthesis :
    CanonicalCompletedC3NaimarkPortEscapeCarrier →L[ℝ]
      RealifiedNaimarkComplexification :=
  (realifiedNaimarkPort.coprod
      (1 : RealifiedNaimarkComplexification →L[ℝ]
        RealifiedNaimarkComplexification)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ
      RealifiedCameraComplexification
      RealifiedNaimarkComplexification).toContinuousLinearMap

@[simp] theorem canonicalCompletedC3NaimarkPortEscapeSynthesis_apply
    (x : CanonicalCompletedC3NaimarkPortEscapeCarrier) :
    canonicalCompletedC3NaimarkPortEscapeSynthesis x =
      realifiedNaimarkPort x.fst + x.snd := by
  rfl

/-- Synthesis after the enlarged readout reconstructs every ambient vector. -/
theorem canonicalCompletedC3NaimarkPortEscapeSynthesis_comp_readout :
    canonicalCompletedC3NaimarkPortEscapeSynthesis ∘L
        canonicalCompletedC3NaimarkPortEscapeReadout = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change realifiedNaimarkPort (realifiedNaimarkAdjoint x) +
      (x - canonicalCompletedC3AmbientPortProjection x) = x
  change canonicalCompletedC3AmbientPortProjection x +
      (x - canonicalCompletedC3AmbientPortProjection x) = x
  abel

/-- The enlarged readout is injective by its explicit left inverse. -/
theorem canonicalCompletedC3NaimarkPortEscapeReadout_injective :
    Function.Injective canonicalCompletedC3NaimarkPortEscapeReadout := by
  intro x y hxy
  have h := congrArg canonicalCompletedC3NaimarkPortEscapeSynthesis hxy
  simpa only [← ContinuousLinearMap.comp_apply,
    canonicalCompletedC3NaimarkPortEscapeSynthesis_comp_readout,
    one_apply_eq_self] using h

/-! ## Exact orthogonal energy conservation -/

/-- The promoted camera component is orthogonal to the retained escape. -/
theorem inner_canonicalCompletedC3AmbientPortProjection_escape_eq_zero
    (x : RealifiedNaimarkComplexification) :
    inner ℝ (canonicalCompletedC3AmbientPortProjection x)
      (canonicalCompletedC3AmbientPortEscape x) = 0 := by
  change inner ℝ
      (realifiedNaimarkPort (realifiedNaimarkAdjoint x))
      (x - canonicalCompletedC3AmbientPortProjection x) = 0
  rw [inner_realifiedNaimarkPort_eq_inner_realifiedNaimarkAdjoint,
    realifiedNaimarkAdjoint_sub_canonicalCompletedC3AmbientPortProjection]
  simp

/-- Coordinatewise realification preserves the norm of the Naimark port. -/
theorem norm_realifiedNaimarkPort
    (u : RealifiedCameraComplexification) :
    ‖realifiedNaimarkPort u‖ = ‖u‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2]
  simp only [realifiedNaimarkPort_fst, realifiedNaimarkPort_snd,
    naimarkIsometry.norm_map]

/-- Projection energy is exactly the energy visible to the camera readout. -/
theorem norm_canonicalCompletedC3AmbientPortProjection
    (x : RealifiedNaimarkComplexification) :
    ‖canonicalCompletedC3AmbientPortProjection x‖ =
      ‖realifiedNaimarkAdjoint x‖ := by
  change ‖realifiedNaimarkPort (realifiedNaimarkAdjoint x)‖ = _
  exact norm_realifiedNaimarkPort _

/-- Every ambient energy splits exactly into camera and escape energies. -/
theorem canonicalCompletedC3AmbientPortEscape_pythagoras
    (x : RealifiedNaimarkComplexification) :
    ‖x‖ ^ 2 =
      ‖realifiedNaimarkAdjoint x‖ ^ 2 +
        ‖canonicalCompletedC3AmbientPortEscape x‖ ^ 2 := by
  have hdecomp :
      x = canonicalCompletedC3AmbientPortProjection x +
        canonicalCompletedC3AmbientPortEscape x := by
    simp [canonicalCompletedC3AmbientPortEscape]
  calc
    ‖x‖ ^ 2 =
        ‖canonicalCompletedC3AmbientPortProjection x +
          canonicalCompletedC3AmbientPortEscape x‖ ^ 2 := by rw [← hdecomp]
    _ = ‖canonicalCompletedC3AmbientPortProjection x‖ ^ 2 +
          ‖canonicalCompletedC3AmbientPortEscape x‖ ^ 2 := by
      rw [norm_add_sq_real,
        inner_canonicalCompletedC3AmbientPortProjection_escape_eq_zero]
      ring
    _ = ‖realifiedNaimarkAdjoint x‖ ^ 2 +
          ‖canonicalCompletedC3AmbientPortEscape x‖ ^ 2 := by
      rw [norm_canonicalCompletedC3AmbientPortProjection]

/-- The enlarged readout preserves squared norm exactly. -/
theorem canonicalCompletedC3NaimarkPortEscapeReadout_norm_sq
    (x : RealifiedNaimarkComplexification) :
    ‖canonicalCompletedC3NaimarkPortEscapeReadout x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [canonicalCompletedC3NaimarkPortEscapeReadout_fst,
    canonicalCompletedC3NaimarkPortEscapeReadout_snd,
    ← canonicalCompletedC3AmbientPortEscape_apply]
  exact (canonicalCompletedC3AmbientPortEscape_pythagoras x).symm

/-- The lossless coisometric block bundled as a linear isometry. -/
def canonicalCompletedC3NaimarkPortEscapeIsometry :
    RealifiedNaimarkComplexification →ₗᵢ[ℝ]
      CanonicalCompletedC3NaimarkPortEscapeCarrier where
  toLinearMap := canonicalCompletedC3NaimarkPortEscapeReadout.toLinearMap
  norm_map' x := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    exact canonicalCompletedC3NaimarkPortEscapeReadout_norm_sq x

@[simp] theorem canonicalCompletedC3NaimarkPortEscapeIsometry_apply
    (x : RealifiedNaimarkComplexification) :
    canonicalCompletedC3NaimarkPortEscapeIsometry x =
      canonicalCompletedC3NaimarkPortEscapeReadout x :=
  rfl

/-! ## Canonical component limits of the completed C3 source -/

/-- Intrinsic component of the completed ambient induced source.  It is
defined by the canonical coisometric readout, so no separate bounded-form
realization is needed to state its existence. -/
def canonicalCompletedC3CoisometricCompressedSourceLimit
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    RealifiedCameraComplexification :=
  realifiedNaimarkAdjoint
    (canonicalCompletedC3AmbientInducedSourceLimit z hs)

/-- Ambient component of the same source which is invisible to every camera
readout. -/
def canonicalCompletedC3CoisometricNaimarkLeakLimit
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    RealifiedNaimarkComplexification :=
  canonicalCompletedC3AmbientPortEscape
    (canonicalCompletedC3AmbientInducedSourceLimit z hs)

/-- At a finite cutoff, the enlarged readout is exactly the already-defined
compressed source together with its retained Naimark leak. -/
theorem canonicalCompletedC3NaimarkPortEscapeReadout_finiteInducedSource
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (z : ℂ) :
    canonicalCompletedC3NaimarkPortEscapeReadout
        (canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource
          hbase cutoff z) =
      WithLp.toLp 2
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z,
          canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
            hbase cutoff z) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · rfl

/-- The finite compressed sources converge without a separate boundedness
hypothesis: continuity of the coisometric readout supplies the limit. -/
theorem canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_tendsto_coisometric
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CoisometricCompressedSourceLimit z hs)) := by
  unfold canonicalCompletedC3CoisometricCompressedSourceLimit
  exact realifiedNaimarkAdjoint.continuous.continuousAt.tendsto.comp
    (canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource_tendsto_ambientLimit
      hbase z hs)

/-- The coisometric component is the intrinsic Hilbert realization of the
completed compressed source form. -/
theorem canonicalCompletedC3CoisometricCompressedSourceLimit_realizes
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    IsCanonicalCompletedC3CompressedHilbertSource z hs
      (canonicalCompletedC3CoisometricCompressedSourceLimit z hs) := by
  let hbase : FiniteNativeCarryOperator.Camera.IsSupported 3 := by
    norm_num [FiniteNativeCarryOperator.Camera.IsSupported]
  exact isCanonicalCompletedC3CompressedHilbertSource_of_tendsto
    hbase z hs
    (canonicalCompletedC3CoisometricCompressedSourceLimit z hs)
    (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_tendsto_coisometric
      hbase z hs)

/-- Coisometric completion supplies the previously abstract Bessel bound
without an additional source hypothesis. -/
theorem canonicalCompletedC3CoisometricCompressedSourceFormBounded
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    CanonicalCompletedC3CompressedSourceFormBounded z hs := by
  exact canonicalCompletedC3CompressedSourceFormBounded_of_realizes z hs
    (canonicalCompletedC3CoisometricCompressedSourceLimit_realizes z hs)

/-- The Riesz construction instantiated by the coisometric bound is exactly
the component obtained by applying the canonical Naimark adjoint. -/
theorem canonicalCompletedC3CompressedHilbertSource_coisometric_eq
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3CompressedHilbertSource z hs
        (canonicalCompletedC3CoisometricCompressedSourceFormBounded z hs) =
      canonicalCompletedC3CoisometricCompressedSourceLimit z hs := by
  exact
    (canonicalCompletedC3CompressedHilbertSource_realizes z hs
      (canonicalCompletedC3CoisometricCompressedSourceFormBounded z hs)).unique
      (canonicalCompletedC3CoisometricCompressedSourceLimit_realizes z hs)

/-- Division-free compressed resolvent equation with the source written
directly as the coisometric component of the ambient completed source. -/
theorem canonicalCompletedC3CoisometricCompressedSourceLimit_eq_scalar_sub_image
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3CoisometricCompressedSourceLimit z hs =
      realifiedCompressedScalar z
          (completedC3SymplecticCameraState (operatorHeightParameter z) hs) -
        completedC3CompressedLogarithmicImageLimit
          (operatorHeightParameter z) := by
  have hsource :=
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_tendsto_coisometric
      hbase z hs
  rw [← canonicalCompletedC3CompressedHilbertSource_coisometric_eq z hs] at hsource
  have h := canonicalCompletedC3CompressedHilbertSource_eq_scalar_sub_image
    hbase z hs
      (canonicalCompletedC3CoisometricCompressedSourceFormBounded z hs)
      hsource
  rw [canonicalCompletedC3CompressedHilbertSource_coisometric_eq z hs] at h
  exact h

/-- Canonical closed compressed resolvent realization with no existential
boundedness witness in its statement. -/
theorem exists_canonicalCompletedC3CoisometricCompressedResolventCandidate
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    ∃ candidate : realifiedCompressedLogarithmicMultiplication.closure.domain,
      (candidate : RealifiedCameraComplexification) =
          completedC3SymplecticCameraState (operatorHeightParameter z) hs ∧
        realifiedCompressedScalar z
            (candidate : RealifiedCameraComplexification) =
          realifiedCompressedLogarithmicMultiplication.closure candidate +
            canonicalCompletedC3CoisometricCompressedSourceLimit z hs := by
  rcases exists_completedC3CompressedLogarithmicClosureCandidate
      hbase z hs with ⟨candidate, hcandidate, himage⟩
  refine ⟨candidate, hcandidate, ?_⟩
  rw [himage,
    canonicalCompletedC3CoisometricCompressedSourceLimit_eq_scalar_sub_image
      hbase z hs,
    hcandidate]
  abel

/-- The complementary finite sources converge at the same time, with no
claim that their limit vanishes. -/
theorem canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak_tendsto_coisometric
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CoisometricNaimarkLeakLimit z hs)) := by
  unfold canonicalCompletedC3CoisometricNaimarkLeakLimit
  exact canonicalCompletedC3AmbientPortEscape.continuous.continuousAt.tendsto.comp
    (canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource_tendsto_ambientLimit
      hbase z hs)

/-- Joint cutoff completion occurs in the lossless port-plus-escape carrier. -/
theorem canonicalCompletedC3FinitePortEscapeSource_tendsto
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    Tendsto
      (fun cutoff : ℕ =>
        WithLp.toLp 2
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
              hbase cutoff z,
            canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
              hbase cutoff z))
      atTop
      (nhds (canonicalCompletedC3NaimarkPortEscapeReadout
        (canonicalCompletedC3AmbientInducedSourceLimit z hs))) := by
  have h :=
    canonicalCompletedC3NaimarkPortEscapeReadout.continuous.continuousAt.tendsto.comp
      (canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource_tendsto_ambientLimit
        hbase z hs)
  exact h.congr' (Eventually.of_forall fun cutoff =>
    canonicalCompletedC3NaimarkPortEscapeReadout_finiteInducedSource
      hbase cutoff z)

/-- The completed source is reconstructed exactly from its two canonical
component limits. -/
theorem canonicalCompletedC3AmbientInducedSourceLimit_eq_coisometricPort_add_leak
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3AmbientInducedSourceLimit z hs =
      realifiedNaimarkPort
          (canonicalCompletedC3CoisometricCompressedSourceLimit z hs) +
        canonicalCompletedC3CoisometricNaimarkLeakLimit z hs := by
  unfold canonicalCompletedC3CoisometricCompressedSourceLimit
    canonicalCompletedC3CoisometricNaimarkLeakLimit
  change canonicalCompletedC3AmbientInducedSourceLimit z hs =
    canonicalCompletedC3AmbientPortProjection
        (canonicalCompletedC3AmbientInducedSourceLimit z hs) +
      canonicalCompletedC3AmbientPortEscape
        (canonicalCompletedC3AmbientInducedSourceLimit z hs)
  simp [canonicalCompletedC3AmbientPortEscape]

/-- The canonical completed leak remains invisible to the camera readout. -/
theorem realifiedNaimarkAdjoint_canonicalCompletedC3CoisometricNaimarkLeakLimit
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    realifiedNaimarkAdjoint
        (canonicalCompletedC3CoisometricNaimarkLeakLimit z hs) = 0 := by
  unfold canonicalCompletedC3CoisometricNaimarkLeakLimit
  exact realifiedNaimarkAdjoint_sub_canonicalCompletedC3AmbientPortProjection _

/-- Exact completed energy conservation for the induced source. -/
theorem canonicalCompletedC3AmbientInducedSourceLimit_norm_sq_coisometric
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    ‖canonicalCompletedC3AmbientInducedSourceLimit z hs‖ ^ 2 =
      ‖canonicalCompletedC3CoisometricCompressedSourceLimit z hs‖ ^ 2 +
        ‖canonicalCompletedC3CoisometricNaimarkLeakLimit z hs‖ ^ 2 := by
  exact canonicalCompletedC3AmbientPortEscape_pythagoras
    (canonicalCompletedC3AmbientInducedSourceLimit z hs)

/-- Whenever the older Riesz-named compressed source is supplied, uniqueness
of the strong limit identifies it with the canonical coisometric limit. -/
theorem canonicalCompletedC3CompressedHilbertSource_eq_coisometricLimit
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs)
    (hsource : Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource z hs hbound))) :
    canonicalCompletedC3CompressedHilbertSource z hs hbound =
      canonicalCompletedC3CoisometricCompressedSourceLimit z hs := by
  exact tendsto_nhds_unique hsource
    (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_tendsto_coisometric
      hbase z hs)

/-- Under the same naming interface, the older ambient leak is exactly the
canonical complementary projection. -/
theorem canonicalCompletedC3AmbientNaimarkLeakLimit_eq_coisometricLimit
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs)
    (hsource : Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource z hs hbound))) :
    canonicalCompletedC3AmbientNaimarkLeakLimit z hs hbound =
      canonicalCompletedC3CoisometricNaimarkLeakLimit z hs := by
  exact tendsto_nhds_unique
    (canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak_tendsto_ambientLimit
      hbase z hs hbound hsource)
    (canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak_tendsto_coisometric
      hbase z hs)

/-! ## The escape channel is genuinely present -/

/-- The established geometric witness survives the canonical completion:
the second component of the lossless block is genuinely nonzero. -/
theorem canonicalCompletedC3CoisometricNaimarkLeakLimit_ne_zero_at_witness
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) :
    canonicalCompletedC3CoisometricNaimarkLeakLimit
        noLeakWitnessHeight
        (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num) ≠ 0 := by
  rcases exists_canonicalCompletedC3AmbientNaimarkLeakLimit_ne_zero_at_witness
      hbase with ⟨hbound, hsource, hne⟩
  rw [canonicalCompletedC3AmbientNaimarkLeakLimit_eq_coisometricLimit
    hbase noLeakWitnessHeight
      (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num)
      hbound hsource] at hne
  exact hne

/-- Consequently the ambient Naimark projection is not the identity.  The
coisometric readout is exact, but compression alone is not lossless. -/
theorem canonicalCompletedC3AmbientPortProjection_ne_one
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) :
    canonicalCompletedC3AmbientPortProjection ≠ 1 := by
  intro hprojection
  have hleak :=
    canonicalCompletedC3CoisometricNaimarkLeakLimit_ne_zero_at_witness hbase
  apply hleak
  unfold canonicalCompletedC3CoisometricNaimarkLeakLimit
    canonicalCompletedC3AmbientPortEscape
  rw [hprojection]
  simp

end

end CarrySelfAdjointOperator
