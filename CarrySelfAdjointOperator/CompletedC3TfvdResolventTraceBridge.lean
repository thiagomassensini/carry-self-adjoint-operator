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
