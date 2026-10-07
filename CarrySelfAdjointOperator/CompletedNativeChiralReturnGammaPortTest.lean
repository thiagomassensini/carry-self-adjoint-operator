import CarrySelfAdjointOperator.CompletedNativeChiralReturnCoisometricSewing

/-!
# The complete induced source versus the upstream Gamma camera port

The source is the already completed TFVD induced source, not the scalar trace.
Its canonical port and orthogonal leak are split before applying the bounded
logarithmic resolvent. Resolvent transport need not preserve their orthogonality.
No new source, metric, normalization, or positivity hypothesis is introduced.
-/
namespace CarrySelfAdjointOperator
open CPFormal.Analytic.Cp NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Boundary
noncomputable section
set_option autoImplicit false

/-- The full induced source belongs to the upstream camera port precisely
when its existing complementary coordinate is zero. -/
theorem canonicalCompletedC3AmbientInducedSource_mem_port_iff_leak_zero
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3AmbientInducedSourceLimit z hs ∈ realifiedNaimarkPort.range ↔
      canonicalCompletedC3CoisometricNaimarkLeakLimit z hs = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    change realifiedNaimarkPort u = _ at hu
    unfold canonicalCompletedC3CoisometricNaimarkLeakLimit
    rw [← hu, canonicalCompletedC3AmbientPortEscape_apply,
      canonicalCompletedC3AmbientPortProjection_realifiedNaimarkPort, sub_self]
  · intro hleak
    refine ⟨canonicalCompletedC3CoisometricCompressedSourceLimit z hs, ?_⟩
    change realifiedNaimarkPort _ = _
    have h := canonicalCompletedC3AmbientInducedSourceLimit_eq_coisometricPort_add_leak z hs
    simpa only [hleak, add_zero] using h.symm

/-- Complete vector response: Gamma of the canonical camera source plus the
resolved leak. Both channels are transported before any pairing is taken. -/
theorem canonicalCompletedC3AmbientResponse_eq_gammaPort_add_resolvedLeak
    (z : ℂ) (hz : z.im ≠ 0) (hs : 0 < (operatorHeightParameter z).re) :
    completedC3SymplecticNaimarkState (operatorHeightParameter z) hs =
      carryGammaSource z hz (canonicalCompletedC3CoisometricCompressedSourceLimit z hs) +
        logarithmicResolventBlock z hz (canonicalCompletedC3CoisometricNaimarkLeakLimit z hs) := by
  rw [← canonicalCompletedC3AmbientResolventDomainVector_embedding z hz hs]
  simp only [canonicalCompletedC3AmbientResolventDomainVector,
    logarithmicResolventIntoDomain_apply,
    realifiedLogarithmicDomainEmbedding_resolventDomainElement]
  rw [canonicalCompletedC3AmbientInducedSourceLimit_eq_coisometricPort_add_leak, map_add]
  rfl

/-- A Gamma response with the same completed vector exists exactly when
the full induced source lies in the port. This quantifies over every camera
source, rather than only the old canonical TFVD source. -/
theorem canonicalCompletedC3AmbientResponse_exists_gamma_iff_leak_zero
    (z : ℂ) (hz : z.im ≠ 0) (hs : 0 < (operatorHeightParameter z).re) :
    (∃ u : RealifiedCameraComplexification,
      carryGammaSource z hz u =
        completedC3SymplecticNaimarkState (operatorHeightParameter z) hs) ↔
      canonicalCompletedC3CoisometricNaimarkLeakLimit z hs = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    apply (canonicalCompletedC3AmbientInducedSource_mem_port_iff_leak_zero z hs).mp
    refine ⟨u, ?_⟩
    apply logarithmicResolventBlock_injective z hz
    change carryGammaSource z hz u = _
    rw [hu, ← canonicalCompletedC3AmbientResolventDomainVector_embedding z hz hs]
    rfl
  · intro hleak
    refine ⟨canonicalCompletedC3CoisometricCompressedSourceLimit z hs, ?_⟩
    have h := canonicalCompletedC3AmbientResponse_eq_gammaPort_add_resolvedLeak z hz hs
    simpa only [hleak, map_zero, add_zero] using h.symm

/-- At the geometric witness, no camera source whatsoever produces the
same completed response via the upstream Gamma map at the same parameter.
This excludes only the port-only realization; the full ambient response
and its retained leak remain available. -/
theorem canonicalCompletedC3AmbientResponse_no_gammaPort_at_witness :
    ¬ ∃ u : RealifiedCameraComplexification,
      carryGammaSource noLeakWitnessHeight
          (by rw [noLeakWitnessHeight_im]; norm_num) u =
        completedC3SymplecticNaimarkState (operatorHeightParameter noLeakWitnessHeight)
          (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num) := by
  rw [canonicalCompletedC3AmbientResponse_exists_gamma_iff_leak_zero]
  exact canonicalCompletedC3CoisometricNaimarkLeakLimit_ne_zero_at_witness
    (base := 3) (by norm_num [FiniteNativeCarryOperator.Camera.IsSupported])

/-- The complete response pairing retains the two ordered port/leak cross
terms. Orthogonality of the source split is not asserted after resolvent
transport, and no term is removed by compression. -/
theorem canonicalCompletedC3AmbientResponse_inner_eq_gammaLeak_fourTerms
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re)
    (ht : 0 < (operatorHeightParameter w).re) :
    let g := fun z hz hs => canonicalCompletedC3GammaNaimarkView
      (carryGammaSource z hz (canonicalCompletedC3CoisometricCompressedSourceLimit z hs))
    let l := fun z hz hs => canonicalCompletedC3GammaNaimarkView
      (logarithmicResolventBlock z hz (canonicalCompletedC3CoisometricNaimarkLeakLimit z hs))
    inner ℂ
        (canonicalCompletedC3GammaNaimarkView
          (completedC3SymplecticNaimarkState (operatorHeightParameter z) hs))
        (canonicalCompletedC3GammaNaimarkView
          (completedC3SymplecticNaimarkState (operatorHeightParameter w) ht)) =
      inner ℂ (g z hz hs) (g w hw ht) + inner ℂ (g z hz hs) (l w hw ht) +
        (inner ℂ (l z hz hs) (g w hw ht) + inner ℂ (l z hz hs) (l w hw ht)) := by
  dsimp only
  rw [canonicalCompletedC3AmbientResponse_eq_gammaPort_add_resolvedLeak z hz hs,
    canonicalCompletedC3AmbientResponse_eq_gammaPort_add_resolvedLeak w hw ht,
    canonicalCompletedC3GammaNaimarkView_add, canonicalCompletedC3GammaNaimarkView_add,
    inner_add_left, inner_add_right, inner_add_right]

end
end CarrySelfAdjointOperator
