import CarrySelfAdjointOperator.CompletedC3FullWronskianOperatorCarrier
import CarrySelfAdjointOperator.CompletedC3AmbientBoundaryReadout
import CarrySelfAdjointOperator.CanonicalCompletedC3TfvdResolventDomain
import Mathlib.Tactic

/-!
# Completed TFVD trace versus logarithmic resolvent response

The completed enriched one-point state already stores both the all-cutoff
Naimark limit and the four scalar boundary traces.  This module identifies
its direct coordinate with the ambient logarithmic resolvent response and
compares that response with the canonical C3/Gamma resolvent response.

The comparison is made at the source level.  Off the real axis the two
responses agree exactly when their two ambient defect sources agree.  The
existing nonzero-leak witness then tests this condition without introducing a
new scalar sewing premise.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-! ## The two projections of the completed enriched state -/

/-- The direct coordinate of the completed enriched state is the completed
symplectic Naimark vector constructed by the all-cutoff limit. -/
@[simp] theorem canonicalCompletedC3CompletedOnePointState_direct
    (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    (canonicalCompletedC3CompletedOnePointState z hzStrip).direct =
      completedC3SymplecticNaimarkState
        (operatorHeightParameter z) hzStrip.1 :=
  rfl

/-- Off the real axis, that direct coordinate is the embedding of the
ambient logarithmic resolvent response to the full induced TFVD source. -/
theorem canonicalCompletedC3CompletedOnePointState_direct_eq_ambientResolvent
    (z : ℂ) (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    (canonicalCompletedC3CompletedOnePointState z hzStrip).direct =
      realifiedLogarithmicDomainEmbedding
        (canonicalCompletedC3AmbientResolventDomainVector
          z hz hzStrip.1) := by
  rw [canonicalCompletedC3CompletedOnePointState_direct]
  exact
    (canonicalCompletedC3AmbientResolventDomainVector_embedding
      z hz hzStrip.1).symm

/-- The same completed vector carries the exact scalar trace `(F,-F')`.
This records both projections together without identifying their boundary
forms. -/
theorem canonicalCompletedC3CompletedOnePointState_resolvent_and_trace
    (z : ℂ) (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    ((canonicalCompletedC3CompletedOnePointState z hzStrip).direct =
        realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3AmbientResolventDomainVector
            z hz hzStrip.1)) ∧
      (canonicalCompletedC3OnePointCompletedTraceProjection
          (canonicalCompletedC3CompletedOnePointState z hzStrip) =
        completedScalarBoundaryTraceState
          canonicalCompletedC3RawHeightValue
          canonicalCompletedC3RawHeightCompanion z) := by
  exact
    ⟨canonicalCompletedC3CompletedOnePointState_direct_eq_ambientResolvent
        z hz hzStrip,
      canonicalCompletedC3OnePointCompletedTraceProjection_completed_eq
        hzStrip⟩

/-! ## Ambient response versus canonical C3/Gamma response -/

/-- Equality of the completed ambient response with the canonical C3/Gamma
response is equivalent to equality of their defect sources.  This is the
injective-resolvent form of the missing source-to-response square. -/
theorem canonicalCompletedC3CompletedOnePointState_direct_eq_tfvdResolvent_iff_source
    (z : ℂ) (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    (canonicalCompletedC3CompletedOnePointState z hzStrip).direct =
          realifiedLogarithmicDomainEmbedding
            (canonicalCompletedC3TfvdResolventDomainVector z hz) ↔
      canonicalCompletedC3AmbientInducedSourceLimit z hzStrip.1 =
        realifiedNaimarkPort (canonicalCompletedC3TfvdCameraSource z) := by
  constructor
  · intro hresponse
    have hembedding :
        realifiedLogarithmicDomainEmbedding
            (canonicalCompletedC3AmbientResolventDomainVector
              z hz hzStrip.1) =
          realifiedLogarithmicDomainEmbedding
            (canonicalCompletedC3TfvdResolventDomainVector z hz) :=
      (canonicalCompletedC3CompletedOnePointState_direct_eq_ambientResolvent
        z hz hzStrip).symm.trans hresponse
    have hdomain :
        canonicalCompletedC3AmbientResolventDomainVector z hz hzStrip.1 =
          canonicalCompletedC3TfvdResolventDomainVector z hz := by
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg WithLp.fst hembedding
      · apply Subtype.ext
        exact congrArg WithLp.snd hembedding
    have hsources := congrArg
      (realifiedLambdaMinusLogarithmicMultiplication z) hdomain
    unfold canonicalCompletedC3AmbientResolventDomainVector
      canonicalCompletedC3TfvdResolventDomainVector at hsources
    simpa only [realifiedLambdaMinusLogarithmicMultiplication_apply_resolvent]
      using hsources
  · intro hsources
    rw [canonicalCompletedC3CompletedOnePointState_direct_eq_ambientResolvent
      z hz hzStrip]
    apply congrArg realifiedLogarithmicDomainEmbedding
    unfold canonicalCompletedC3AmbientResolventDomainVector
      canonicalCompletedC3TfvdResolventDomainVector
    rw [hsources]

/-! ## Exact vector correction between the two resolvent responses -/

/-- The full ambient source minus the canonical six-camera TFVD source.
This is a vector in the common Naimark ambient space; no boundary channel is
discarded in its definition. -/
def canonicalCompletedC3AmbientTfvdSourceCorrection
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    RealifiedNaimarkComplexification :=
  canonicalCompletedC3AmbientInducedSourceLimit z hs -
    realifiedNaimarkPort (canonicalCompletedC3TfvdCameraSource z)

/-- The source correction resolved in the same maximal logarithmic domain as
the ambient and canonical TFVD responses. -/
def canonicalCompletedC3AmbientTfvdResolvedCorrection
    (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re) :
    RealifiedLogarithmicDomain :=
  logarithmicResolventIntoDomain z hz
    (canonicalCompletedC3AmbientTfvdSourceCorrection z hs)

/-- Exact domain-valued factorization of the completed ambient response into
the canonical TFVD/Gamma response and the resolved source correction. -/
theorem canonicalCompletedC3AmbientResolventDomainVector_eq_tfvd_add_correction
    (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3AmbientResolventDomainVector z hz hs =
      canonicalCompletedC3TfvdResolventDomainVector z hz +
        canonicalCompletedC3AmbientTfvdResolvedCorrection z hz hs := by
  unfold canonicalCompletedC3AmbientResolventDomainVector
    canonicalCompletedC3TfvdResolventDomainVector
    canonicalCompletedC3AmbientTfvdResolvedCorrection
    canonicalCompletedC3AmbientTfvdSourceCorrection
  rw [← map_add]
  congr 1
  abel

/-- The same factorization in the ambient Hilbert space.  In particular, the
direct completed TFVD coordinate is the Gamma response plus a concrete
resolved vector, rather than an unidentified scalar defect. -/
theorem canonicalCompletedC3CompletedOnePointState_direct_eq_tfvd_add_correction
    (z : ℂ) (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    (canonicalCompletedC3CompletedOnePointState z hzStrip).direct =
      realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3TfvdResolventDomainVector z hz) +
        realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3AmbientTfvdResolvedCorrection
            z hz hzStrip.1) := by
  rw [canonicalCompletedC3CompletedOnePointState_direct_eq_ambientResolvent
    z hz hzStrip,
    canonicalCompletedC3AmbientResolventDomainVector_eq_tfvd_add_correction]
  exact map_add realifiedLogarithmicDomainEmbedding _ _

/-- The resolved correction has exactly the source correction as its defect;
this is the division-free operator equation for the retained channels. -/
theorem canonicalCompletedC3AmbientTfvdResolvedCorrection_defectEquation
    (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re) :
    realifiedNaimarkScalar z
        (realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3AmbientTfvdResolvedCorrection z hz hs)) =
      realifiedLogarithmicMultiplication
          (canonicalCompletedC3AmbientTfvdResolvedCorrection z hz hs) +
        canonicalCompletedC3AmbientTfvdSourceCorrection z hs := by
  simpa [canonicalCompletedC3AmbientTfvdResolvedCorrection] using
    realified_logarithmic_resolvent_equation z hz
      (canonicalCompletedC3AmbientTfvdSourceCorrection z hs)

/-- Resolvent injectivity says that the vector correction vanishes exactly
when its full ambient source correction vanishes. -/
theorem canonicalCompletedC3AmbientTfvdResolvedCorrection_eq_zero_iff_source
    (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3AmbientTfvdResolvedCorrection z hz hs = 0 ↔
      canonicalCompletedC3AmbientTfvdSourceCorrection z hs = 0 := by
  constructor
  · intro hzero
    apply logarithmicResolventIntoDomain_injective z hz
    change logarithmicResolventIntoDomain z hz
        (canonicalCompletedC3AmbientTfvdSourceCorrection z hs) = 0 at hzero
    exact hzero.trans (map_zero (logarithmicResolventIntoDomain z hz)).symm
  · intro hzero
    unfold canonicalCompletedC3AmbientTfvdResolvedCorrection
    rw [hzero]
    exact map_zero (logarithmicResolventIntoDomain z hz)

/-! ## The two retained source channels -/

/-- Intrinsic compressed-port source minus the canonical TFVD camera source.
It is kept in the camera carrier before applying the Naimark port. -/
def canonicalCompletedC3CompressedTfvdPortSourceCorrection
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs) :
    RealifiedCameraComplexification :=
  canonicalCompletedC3CompressedHilbertSource z hs hbound -
    canonicalCompletedC3TfvdCameraSource z

/-- Resolvent response to the compressed-port source correction. -/
def canonicalCompletedC3CompressedTfvdPortResolvedCorrection
    (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs) :
    RealifiedLogarithmicDomain :=
  logarithmicResolventIntoDomain z hz
    (realifiedNaimarkPort
      (canonicalCompletedC3CompressedTfvdPortSourceCorrection
        z hs hbound))

/-- Resolvent response to the complementary ambient Naimark leak. -/
def canonicalCompletedC3AmbientLeakResolvedCorrection
    (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs) :
    RealifiedLogarithmicDomain :=
  logarithmicResolventIntoDomain z hz
    (canonicalCompletedC3AmbientNaimarkLeakLimit z hs hbound)

/-- Exact channelwise source decomposition.  The full correction consists of
the compressed-port discrepancy and the complementary ambient leak. -/
theorem canonicalCompletedC3AmbientTfvdSourceCorrection_eq_port_add_leak
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs) :
    canonicalCompletedC3AmbientTfvdSourceCorrection z hs =
      realifiedNaimarkPort
          (canonicalCompletedC3CompressedTfvdPortSourceCorrection
            z hs hbound) +
        canonicalCompletedC3AmbientNaimarkLeakLimit z hs hbound := by
  unfold canonicalCompletedC3AmbientTfvdSourceCorrection
    canonicalCompletedC3CompressedTfvdPortSourceCorrection
  rw [canonicalCompletedC3AmbientInducedSourceLimit_eq_port_add_leak
      z hs hbound,
    map_sub]
  abel

/-- Linearity of the resolvent preserves the two source channels exactly. -/
theorem canonicalCompletedC3AmbientTfvdResolvedCorrection_eq_port_add_leak
    (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs) :
    canonicalCompletedC3AmbientTfvdResolvedCorrection z hz hs =
      canonicalCompletedC3CompressedTfvdPortResolvedCorrection
          z hz hs hbound +
        canonicalCompletedC3AmbientLeakResolvedCorrection
          z hz hs hbound := by
  unfold canonicalCompletedC3AmbientTfvdResolvedCorrection
    canonicalCompletedC3CompressedTfvdPortResolvedCorrection
    canonicalCompletedC3AmbientLeakResolvedCorrection
  rw [canonicalCompletedC3AmbientTfvdSourceCorrection_eq_port_add_leak,
    map_add]

/-- Resolvent uniqueness replaces the canonical TFVD term by the concrete
Gamma response without changing the correction vector. -/
theorem canonicalCompletedC3AmbientResolventDomainVector_eq_gamma_add_correction
    (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3AmbientResolventDomainVector z hz hs =
      carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z) +
        canonicalCompletedC3AmbientTfvdResolvedCorrection z hz hs := by
  rw [canonicalCompletedC3AmbientResolventDomainVector_eq_tfvd_add_correction,
    canonicalCompletedC3TfvdResolventDomainVector_eq_gamma]

/-- Fully channel-separated ambient Hilbert-space formula: the direct
completed state is the canonical Gamma response, plus the resolved
compressed-port discrepancy, plus the resolved complementary leak. -/
theorem canonicalCompletedC3CompletedOnePointState_direct_eq_gamma_add_port_add_leak
    (z : ℂ) (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hzStrip.1) :
    (canonicalCompletedC3CompletedOnePointState z hzStrip).direct =
      realifiedLogarithmicDomainEmbedding
          (carryGammaIntoDomain z hz
            (canonicalCompletedC3SixCameraSource z)) +
        realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3CompressedTfvdPortResolvedCorrection
            z hz hzStrip.1 hbound) +
        realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3AmbientLeakResolvedCorrection
            z hz hzStrip.1 hbound) := by
  rw [canonicalCompletedC3CompletedOnePointState_direct_eq_ambientResolvent
    z hz hzStrip,
    canonicalCompletedC3AmbientResolventDomainVector_eq_gamma_add_correction
      z hz hzStrip.1,
    canonicalCompletedC3AmbientTfvdResolvedCorrection_eq_port_add_leak
      z hz hzStrip.1 hbound,
    map_add, map_add]
  abel

/-! ## The existing leak witness tests the source equality -/

/-- At the established leak witness, the ambient induced source is not the
Naimark port of the canonical completed C3 source.  Both possible port terms
lie in the Naimark range, whereas the retained complementary source has zero
adjoint compression and is nonzero. -/
theorem exists_canonicalCompletedC3AmbientInducedSourceLimit_ne_tfvdSource_at_witness
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
      canonicalCompletedC3AmbientInducedSourceLimit
          noLeakWitnessHeight
          (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num) ≠
        realifiedNaimarkPort
          (canonicalCompletedC3TfvdCameraSource noLeakWitnessHeight) := by
  let hs : 0 < (operatorHeightParameter noLeakWitnessHeight).re := by
    rw [operatorHeightParameter_noLeakWitnessHeight_re]
    norm_num
  rcases exists_canonicalCompletedC3AmbientNaimarkLeakLimit_ne_zero_at_witness
      hbase with ⟨hbound, hsource, hleak⟩
  refine ⟨hbound, hsource, ?_⟩
  intro hambient
  have hadjointLeak :=
    realifiedNaimarkAdjoint_canonicalCompletedC3AmbientNaimarkLeakLimit
      hbase noLeakWitnessHeight hs hbound hsource
  have hdecomposition :=
    canonicalCompletedC3AmbientInducedSourceLimit_eq_port_add_leak
      noLeakWitnessHeight hs hbound
  have hadjointPort (u : RealifiedCameraComplexification) :
      realifiedNaimarkAdjoint (realifiedNaimarkPort u) = u := by
    change (realifiedNaimarkAdjoint ∘L realifiedNaimarkPort) u = u
    rw [NativeCarryC3Crosswalk.realifiedNaimarkAdjoint_comp_realifiedNaimarkPort]
    rfl
  have hadjoint := congrArg realifiedNaimarkAdjoint hambient
  rw [hdecomposition, map_add, hadjointPort, hadjointLeak, add_zero,
    hadjointPort] at hadjoint
  rw [hambient, hadjoint] at hdecomposition
  have hleakZero :
      canonicalCompletedC3AmbientNaimarkLeakLimit
          noLeakWitnessHeight hs hbound = 0 :=
    by
      apply add_left_cancel
        (a := realifiedNaimarkPort
          (canonicalCompletedC3TfvdCameraSource noLeakWitnessHeight))
      simpa using hdecomposition.symm
  exact hleak hleakZero

/-- The exact resolved correction is genuinely nonzero at the established
source witness.  Injectivity of the off-real-axis resolvent transports the
source mismatch without invoking a Gram or scalar boundary identity. -/
theorem canonicalCompletedC3AmbientTfvdResolvedCorrection_ne_zero_at_witness
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) :
    canonicalCompletedC3AmbientTfvdResolvedCorrection
        noLeakWitnessHeight
        (by rw [noLeakWitnessHeight_im]; norm_num)
        (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num) ≠
      0 := by
  let hz : noLeakWitnessHeight.im ≠ 0 := by
    rw [noLeakWitnessHeight_im]
    norm_num
  let hs : 0 < (operatorHeightParameter noLeakWitnessHeight).re := by
    rw [operatorHeightParameter_noLeakWitnessHeight_re]
    norm_num
  change canonicalCompletedC3AmbientTfvdResolvedCorrection
      noLeakWitnessHeight hz hs ≠ 0
  rcases
      exists_canonicalCompletedC3AmbientInducedSourceLimit_ne_tfvdSource_at_witness
        hbase with ⟨hbound, hsource, hsources⟩
  intro hzero
  have hsourceZero :
      canonicalCompletedC3AmbientTfvdSourceCorrection
          noLeakWitnessHeight hs = 0 :=
    (canonicalCompletedC3AmbientTfvdResolvedCorrection_eq_zero_iff_source
      noLeakWitnessHeight hz hs).mp hzero
  apply hsources
  exact sub_eq_zero.mp hsourceZero

/-- Consequently the direct coordinate of the completed enriched TFVD state
is not the canonical C3/Gamma resolvent response at the same witness. -/
theorem canonicalCompletedC3CompletedOnePointState_direct_ne_tfvdResolvent_at_witness
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) :
    (canonicalCompletedC3CompletedOnePointState
        noLeakWitnessHeight
        (by
          constructor
          · rw [operatorHeightParameter_noLeakWitnessHeight_re]
            norm_num
          · rw [operatorHeightParameter_noLeakWitnessHeight_re]
            norm_num)).direct ≠
      realifiedLogarithmicDomainEmbedding
        (canonicalCompletedC3TfvdResolventDomainVector
          noLeakWitnessHeight
          (by rw [noLeakWitnessHeight_im]; norm_num)) := by
  let hzStrip : operatorHeightParameter noLeakWitnessHeight ∈
      genuineCriticalStrip := by
    constructor
    · rw [operatorHeightParameter_noLeakWitnessHeight_re]
      norm_num
    · rw [operatorHeightParameter_noLeakWitnessHeight_re]
      norm_num
  let hz : noLeakWitnessHeight.im ≠ 0 := by
    rw [noLeakWitnessHeight_im]
    norm_num
  rcases
      exists_canonicalCompletedC3AmbientInducedSourceLimit_ne_tfvdSource_at_witness
        hbase with ⟨hbound, hsource, hsources⟩
  intro hresponse
  exact hsources
    ((canonicalCompletedC3CompletedOnePointState_direct_eq_tfvdResolvent_iff_source
      noLeakWitnessHeight hz hzStrip).mp hresponse)

end

end CarrySelfAdjointOperator
