import CarrySelfAdjointOperator.CompletedC3CompressedSourceTailControl
import Mathlib.Tactic

/-!
# Ambient all-order source tail control

The intrinsic compressed source retains the camera projection of the
logarithmic defect.  The complementary Naimark channel is generally nonzero,
so the ambient resolvent realization must instead control the full vectors
`Y u_M` before taking `(z - Y) u_M`.

The logarithmic graph bound established for every permanent camera coordinate
already applies before compression.  This file uses that bound to construct
the full ambient logarithmic series, proves strong convergence of the finite
images and induced sources, and identifies the completed TFVD Naimark state as
the ambient resolvent response to that full source.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace LinearPMap lp
  Topology

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-! ## Ambient logarithmic synthesis -/

/-- Full ambient logarithmic image of one permanent camera coordinate. -/
def completedC3AmbientLogarithmicCoordinateImage (n : ℕ) : NaimarkSpace :=
  logarithmicNaimarkCoreLinearMap (completedC3OrthonormalCameraCore n)

/-- The ambient image has the same logarithmic graph bound used for the
compressed coordinate image. -/
theorem norm_completedC3AmbientLogarithmicCoordinateImage_le (n : ℕ) :
    ‖completedC3AmbientLogarithmicCoordinateImage n‖ ≤
      ‖commonInitialLogarithmicLp‖ + (1 + Real.log (n + 4)) := by
  exact norm_logarithmicNaimarkCore_completedC3OrthonormalCameraCore_le n

/-- Logarithmic multiplication of a finite C3 leg is the exact synthesis of
the ambient coordinate images. -/
theorem logarithmicNaimarkCore_finiteC3LegCameraCore
    (M : ℕ) (x : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M) :
    logarithmicNaimarkCoreLinearMap (finiteC3LegCameraCore M x) =
      ∑ j : FiniteC3RealCoordinate M,
        ![(x j.1).re, (x j.1).im] j.2 •
          completedC3AmbientLogarithmicCoordinateImage
            (finiteC3RealCoordinateNat j) := by
  unfold finiteC3LegCameraCore finiteC3CameraCoreCoordinateState
    completedC3AmbientLogarithmicCoordinateImage
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  rfl

/-- One ambient logarithmic term with both real quadratures retained. -/
def completedC3AmbientLogarithmicLegTerm (s : ℂ) (n : ℕ) : NaimarkSpace :=
  (positiveDirichletGradient s n).re •
      completedC3AmbientLogarithmicCoordinateImage (2 * n) +
    (positiveDirichletGradient s n).im •
      completedC3AmbientLogarithmicCoordinateImage (2 * n + 1)

/-- Finite prefix of the full ambient logarithmic leg. -/
def completedC3AmbientLogarithmicLegPrefix (s : ℂ) (N : ℕ) : NaimarkSpace :=
  ∑ n ∈ Finset.range N, completedC3AmbientLogarithmicLegTerm s n

theorem logarithmicNaimarkCore_genuineSecondLeg_eq_ambientPrefix
    (N : ℕ) (s : ℂ) :
    logarithmicNaimarkCoreLinearMap
        (finiteC3LegCameraCore N
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
            N s).2) =
      completedC3AmbientLogarithmicLegPrefix s N := by
  rw [logarithmicNaimarkCore_finiteC3LegCameraCore]
  rw [Fintype.sum_prod_type]
  unfold completedC3AmbientLogarithmicLegPrefix
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  have hnlt : n < N := Finset.mem_range.mp hn
  simp only [hnlt, dif_pos]
  rw [Fin.sum_univ_two]
  simp only [finiteC3RealCoordinateNat]
  simp [completedC3AmbientLogarithmicLegTerm,
    NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair_snd_apply]

/-! ## Absolute summability -/

theorem norm_completedC3AmbientLogarithmicCoordinateImage_even_le (n : ℕ) :
    ‖completedC3AmbientLogarithmicCoordinateImage (2 * n)‖ ≤
      completedC3CompressedLogarithmicCoordinateWeight n := by
  calc
    _ ≤ ‖commonInitialLogarithmicLp‖ +
        (1 + Real.log (2 * n + 4)) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        norm_completedC3AmbientLogarithmicCoordinateImage_le (2 * n)
    _ ≤ ‖commonInitialLogarithmicLp‖ +
        (1 + Real.log (2 * n + 5)) := by
      have hlog : Real.log (2 * (n : ℝ) + 4) ≤
          Real.log (2 * (n : ℝ) + 5) := by
        apply Real.log_le_log
        · positivity
        · norm_num
      exact add_le_add (le_refl _) (add_le_add (le_refl _) hlog)
    _ = completedC3CompressedLogarithmicCoordinateWeight n := rfl

theorem norm_completedC3AmbientLogarithmicCoordinateImage_odd_le (n : ℕ) :
    ‖completedC3AmbientLogarithmicCoordinateImage (2 * n + 1)‖ ≤
      completedC3CompressedLogarithmicCoordinateWeight n := by
  have h :=
    norm_completedC3AmbientLogarithmicCoordinateImage_le (2 * n + 1)
  unfold completedC3CompressedLogarithmicCoordinateWeight
  convert h using 1
  all_goals push_cast
  all_goals ring_nf

theorem norm_completedC3AmbientLogarithmicLegTerm_le
    (s : ℂ) (n : ℕ) :
    ‖completedC3AmbientLogarithmicLegTerm s n‖ ≤
      2 * completedC3CompressedLogarithmicCoordinateWeight n *
        ‖positiveDirichletGradient s n‖ := by
  unfold completedC3AmbientLogarithmicLegTerm
  calc
    _ ≤
        ‖(positiveDirichletGradient s n).re •
          completedC3AmbientLogarithmicCoordinateImage (2 * n)‖ +
        ‖(positiveDirichletGradient s n).im •
          completedC3AmbientLogarithmicCoordinateImage (2 * n + 1)‖ :=
      norm_add_le _ _
    _ = |(positiveDirichletGradient s n).re| *
          ‖completedC3AmbientLogarithmicCoordinateImage (2 * n)‖ +
        |(positiveDirichletGradient s n).im| *
          ‖completedC3AmbientLogarithmicCoordinateImage (2 * n + 1)‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖positiveDirichletGradient s n‖ *
          completedC3CompressedLogarithmicCoordinateWeight n +
        ‖positiveDirichletGradient s n‖ *
          completedC3CompressedLogarithmicCoordinateWeight n := by
      exact add_le_add
        (mul_le_mul (Complex.abs_re_le_norm _)
          (norm_completedC3AmbientLogarithmicCoordinateImage_even_le n)
          (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (Complex.abs_im_le_norm _)
          (norm_completedC3AmbientLogarithmicCoordinateImage_odd_le n)
          (norm_nonneg _) (norm_nonneg _))
    _ = 2 * completedC3CompressedLogarithmicCoordinateWeight n *
        ‖positiveDirichletGradient s n‖ := by ring

/-- The full ambient logarithmic leg is absolutely summable throughout the
open right half-plane. -/
theorem summable_completedC3AmbientLogarithmicLegTerm
    {s : ℂ} (hs : 0 < s.re) :
    Summable (completedC3AmbientLogarithmicLegTerm s) := by
  have hbase : Summable
      (fun n : ℕ => (n : ℝ) ^ (-s.re / 2 - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift : Summable
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-s.re / 2 - 1)) := by
    have h := hbase.comp_injective
      (show Function.Injective (fun n : ℕ => n + 1) by
        intro a b hab
        exact Nat.add_right_cancel hab)
    change Summable
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-s.re / 2 - 1)) at h
    exact h
  let C : ℝ := 2 *
    ((‖commonInitialLogarithmicLp‖ + 1 +
      (5 : ℝ) ^ (s.re / 2) / (s.re / 2)) * ‖s‖)
  have hmajorant := hshift.mul_left C
  exact hmajorant.of_norm_bounded fun n => by
    calc
      ‖completedC3AmbientLogarithmicLegTerm s n‖ ≤
          2 * completedC3CompressedLogarithmicCoordinateWeight n *
            ‖positiveDirichletGradient s n‖ :=
        norm_completedC3AmbientLogarithmicLegTerm_le s n
      _ = 2 *
          (completedC3CompressedLogarithmicCoordinateWeight n *
            ‖positiveDirichletGradient s n‖) := by ring
      _ ≤ 2 *
          (((‖commonInitialLogarithmicLp‖ + 1 +
              (5 : ℝ) ^ (s.re / 2) / (s.re / 2)) * ‖s‖) *
            (((n + 1 : ℕ) : ℝ) ^ (-s.re / 2 - 1))) := by
        exact mul_le_mul_of_nonneg_left
          (completedC3CompressedLogarithmicCoordinateWeight_mul_gradient_le
            hs n) (by norm_num)
      _ = C * (((n + 1 : ℕ) : ℝ) ^ (-s.re / 2 - 1)) := by
        dsimp [C]
        ring

theorem completedC3AmbientLogarithmicLegPrefix_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (completedC3AmbientLogarithmicLegPrefix s) atTop
      (nhds (∑' n : ℕ, completedC3AmbientLogarithmicLegTerm s n)) := by
  exact (summable_completedC3AmbientLogarithmicLegTerm hs).tendsto_sum_tsum_nat

/-! ## Full graph and source limits -/

def completedC3AmbientLogarithmicLegLimit (s : ℂ) : NaimarkSpace :=
  ∑' n : ℕ, completedC3AmbientLogarithmicLegTerm s n

def completedC3AmbientLogarithmicImageLimit
    (s : ℂ) : RealifiedNaimarkComplexification :=
  WithLp.toLp 2
    (-(completedC3RadialRealCoefficient s •
        completedC3AmbientLogarithmicLegLimit s),
      completedC3AmbientLogarithmicLegLimit s)

theorem canonicalCompletedC3FiniteAmbientLogarithmicImage_snd_eq_prefix
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (z : ℂ) :
    (realifiedLogarithmicMultiplication
      (canonicalCompletedC3CausalResponseBoundaryDomainVector hbase cutoff
        (operatorHeightParameter z))).snd =
      completedC3AmbientLogarithmicLegPrefix
        (operatorHeightParameter z)
        (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1) := by
  let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
  rw [realifiedLogarithmicMultiplication_snd]
  change
    logarithmicNaimarkCoreLinearMap
      (finiteC3LegCameraCore N
        (canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff
          (operatorHeightParameter z)).2) = _
  rw [canonicalCompletedC3CausalResponseBoundaryTfvdPort_eq_genuine]
  exact logarithmicNaimarkCore_genuineSecondLeg_eq_ambientPrefix
    N (operatorHeightParameter z)

theorem canonicalCompletedC3FiniteAmbientLogarithmicImage_fst_eq_prefix
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (z : ℂ) :
    (realifiedLogarithmicMultiplication
      (canonicalCompletedC3CausalResponseBoundaryDomainVector hbase cutoff
        (operatorHeightParameter z))).fst =
      -(completedC3RadialRealCoefficient (operatorHeightParameter z) •
        completedC3AmbientLogarithmicLegPrefix
          (operatorHeightParameter z)
          (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)) := by
  let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
  rw [realifiedLogarithmicMultiplication_fst]
  change
    logarithmicNaimarkCoreLinearMap
      (-finiteC3LegCameraCore N
        (canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff
          (operatorHeightParameter z)).1) = _
  rw [canonicalCompletedC3CausalResponseBoundaryTfvdPort_eq_genuine,
    finiteC3LegCameraCore_genuineFirst_eq_radial_smul_second,
    map_neg, map_smul,
    logarithmicNaimarkCore_genuineSecondLeg_eq_ambientPrefix]

/-- The full, uncompressed logarithmic images converge strongly; the
complementary Naimark channel is retained in this limit. -/
theorem canonicalCompletedC3FiniteAmbientLogarithmicImage_tendsto
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    Tendsto
      (fun cutoff : ℕ =>
        realifiedLogarithmicMultiplication
          (canonicalCompletedC3CausalResponseBoundaryDomainVector hbase cutoff
            (operatorHeightParameter z)))
      atTop
      (nhds (completedC3AmbientLogarithmicImageLimit
        (operatorHeightParameter z))) := by
  let s := operatorHeightParameter z
  let L := completedC3AmbientLogarithmicLegLimit s
  have hleg : Tendsto
      (fun cutoff : ℕ =>
        completedC3AmbientLogarithmicLegPrefix s
          (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1))
      atTop (nhds L) := by
    exact (completedC3AmbientLogarithmicLegPrefix_tendsto hs).comp
      (finiteCameraWindow_add_one_tendsto_atTop hbase)
  have hfirst : Tendsto
      (fun cutoff : ℕ =>
        -(completedC3RadialRealCoefficient s •
          completedC3AmbientLogarithmicLegPrefix s
            (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)))
      atTop
      (nhds (-(completedC3RadialRealCoefficient s • L))) :=
    (hleg.const_smul (completedC3RadialRealCoefficient s)).neg
  have hpair := hfirst.prodMk_nhds hleg
  have hlp :=
    (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp hpair
  unfold completedC3AmbientLogarithmicImageLimit
  change Tendsto _ atTop
    (nhds (WithLp.toLp 2
      (-(completedC3RadialRealCoefficient s • L), L)))
  exact hlp.congr' (Eventually.of_forall fun cutoff => by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change
        -(completedC3RadialRealCoefficient (operatorHeightParameter z) •
            completedC3AmbientLogarithmicLegPrefix
              (operatorHeightParameter z)
              (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)) =
          (realifiedLogarithmicMultiplication
            (canonicalCompletedC3CausalResponseBoundaryDomainVector hbase cutoff
              (operatorHeightParameter z))).fst
      exact
        (canonicalCompletedC3FiniteAmbientLogarithmicImage_fst_eq_prefix
          hbase cutoff z).symm
    · change
        completedC3AmbientLogarithmicLegPrefix
            (operatorHeightParameter z)
            (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1) =
          (realifiedLogarithmicMultiplication
            (canonicalCompletedC3CausalResponseBoundaryDomainVector hbase cutoff
              (operatorHeightParameter z))).snd
      exact
        (canonicalCompletedC3FiniteAmbientLogarithmicImage_snd_eq_prefix
          hbase cutoff z).symm)

/-- Full ambient limit of the induced sources `(z - Y) u_M`. -/
def canonicalCompletedC3AmbientInducedSourceLimit
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    RealifiedNaimarkComplexification :=
  realifiedNaimarkScalar z
      (completedC3SymplecticNaimarkState (operatorHeightParameter z) hs) -
    completedC3AmbientLogarithmicImageLimit (operatorHeightParameter z)

theorem canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource_tendsto_ambientLimit
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3AmbientInducedSourceLimit z hs)) := by
  have hstate :=
    canonicalCompletedC3CausalResponseBoundaryDomainVector_embedding_tendsto
      hbase hs
  have hscalar :=
    (realifiedNaimarkScalar z).continuous.continuousAt.tendsto.comp hstate
  have himage :=
    canonicalCompletedC3FiniteAmbientLogarithmicImage_tendsto hbase z hs
  exact (hscalar.sub himage).congr'
    (Eventually.of_forall fun cutoff => by
      rfl)

/-- Completed complementary Naimark source after the intrinsic camera source
has been reconstructed. -/
def canonicalCompletedC3AmbientNaimarkLeakLimit
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs) :
    RealifiedNaimarkComplexification :=
  canonicalCompletedC3AmbientInducedSourceLimit z hs -
    realifiedNaimarkPort
      (canonicalCompletedC3CompressedHilbertSource z hs hbound)

/-- The finite complementary channels converge strongly to their own ambient
limit; they are retained rather than set equal to zero. -/
theorem canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak_tendsto_ambientLimit
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs)
    (hsource : Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource z hs hbound))) :
    Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3AmbientNaimarkLeakLimit z hs hbound)) := by
  have hambient :=
    canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource_tendsto_ambientLimit
      hbase z hs
  have hported :=
    realifiedNaimarkPort.continuous.continuousAt.tendsto.comp hsource
  simpa [canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak,
    canonicalCompletedC3AmbientNaimarkLeakLimit] using
      hambient.sub hported

/-- Exact completed source decomposition into the intrinsic compressed source
and its nonprojected ambient complement. -/
theorem canonicalCompletedC3AmbientInducedSourceLimit_eq_port_add_leak
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs) :
    canonicalCompletedC3AmbientInducedSourceLimit z hs =
      realifiedNaimarkPort
          (canonicalCompletedC3CompressedHilbertSource z hs hbound) +
        canonicalCompletedC3AmbientNaimarkLeakLimit z hs hbound := by
  unfold canonicalCompletedC3AmbientNaimarkLeakLimit
  abel

/-- At the existing obstruction witness, the completed complementary source
is genuinely nonzero.  Its finite coordinates nevertheless converge strongly
by the ambient tail estimate above. -/
theorem exists_canonicalCompletedC3AmbientNaimarkLeakLimit_ne_zero_at_witness
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) :
    ∃ hbound : CanonicalCompletedC3CompressedSourceFormBounded
        noLeakWitnessHeight
        (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num),
      Tendsto
        (fun cutoff : ℕ =>
          canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff noLeakWitnessHeight)
        atTop
        (nhds (canonicalCompletedC3CompressedHilbertSource
          noLeakWitnessHeight
          (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num)
          hbound)) ∧
      canonicalCompletedC3AmbientNaimarkLeakLimit
          noLeakWitnessHeight
          (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num)
          hbound ≠ 0 := by
  let hs : 0 < (operatorHeightParameter noLeakWitnessHeight).re := by
    rw [operatorHeightParameter_noLeakWitnessHeight_re]
    norm_num
  rcases exists_canonicalCompletedC3CompressedHilbertSource_tendsto
      hbase noLeakWitnessHeight hs with ⟨hbound, hsource⟩
  refine ⟨hbound, hsource, ?_⟩
  intro hzero
  have hleak :=
    canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak_tendsto_ambientLimit
      hbase noLeakWitnessHeight hs hbound hsource
  rw [hzero] at hleak
  exact
    (canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak_not_tendsto_zero
      hbase) hleak

/-- The completed TFVD state belongs to the full maximal logarithmic domain
and has the ambient induced source above. -/
theorem exists_canonicalCompletedC3AmbientResolventCandidate
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    ∃ candidate : RealifiedLogarithmicDomain,
      realifiedLogarithmicDomainEmbedding candidate =
          completedC3SymplecticNaimarkState (operatorHeightParameter z) hs ∧
        realifiedLambdaMinusLogarithmicMultiplication z candidate =
          canonicalCompletedC3AmbientInducedSourceLimit z hs := by
  rcases exists_realifiedLogarithmicDomain_limit_of_graph_tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryDomainVector hbase cutoff
          (operatorHeightParameter z))
      (completedC3SymplecticNaimarkState (operatorHeightParameter z) hs)
      (completedC3AmbientLogarithmicImageLimit (operatorHeightParameter z))
      (canonicalCompletedC3CausalResponseBoundaryDomainVector_embedding_tendsto
        hbase hs)
      (canonicalCompletedC3FiniteAmbientLogarithmicImage_tendsto
        hbase z hs) with
    ⟨candidate, hembedding, himage⟩
  refine ⟨candidate, hembedding, ?_⟩
  unfold realifiedLambdaMinusLogarithmicMultiplication
    canonicalCompletedC3AmbientInducedSourceLimit
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_coe]
  rw [hembedding, himage]

/-- Resolvent uniqueness identifies the completed TFVD domain vector with the
ambient logarithmic resolvent of its full induced source. -/
theorem exists_canonicalCompletedC3AmbientResolventResponse
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re) :
    ∃ candidate : RealifiedLogarithmicDomain,
      realifiedLogarithmicDomainEmbedding candidate =
          completedC3SymplecticNaimarkState (operatorHeightParameter z) hs ∧
        candidate = logarithmicResolventIntoDomain z hz
          (canonicalCompletedC3AmbientInducedSourceLimit z hs) := by
  rcases exists_canonicalCompletedC3AmbientResolventCandidate hbase z hs with
    ⟨candidate, hembedding, hsource⟩
  refine ⟨candidate, hembedding, ?_⟩
  apply realifiedLambdaMinusLogarithmicMultiplication_injective z hz
  rw [hsource]
  change canonicalCompletedC3AmbientInducedSourceLimit z hs =
    realifiedLambdaMinusLogarithmicMultiplication z
      (logarithmicResolventDomainElement z hz
        (canonicalCompletedC3AmbientInducedSourceLimit z hs))
  have hresolvent := realified_logarithmic_resolvent_equation z hz
    (canonicalCompletedC3AmbientInducedSourceLimit z hs)
  unfold realifiedLambdaMinusLogarithmicMultiplication
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_coe]
  rw [realifiedLogarithmicDomainEmbedding_resolventDomainElement]
  rw [hresolvent]
  abel

end

end CarrySelfAdjointOperator
