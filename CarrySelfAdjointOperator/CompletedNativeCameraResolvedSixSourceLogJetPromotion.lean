import CarrySelfAdjointOperator.CompletedNativeTfvdSixSourceCameraPromotionAudit
import Mathlib.Tactic

/-!
# Camera-resolved logarithmic roles in the completed six-source datum

The multibase camera ledger already resolves the logarithmic Dirichlet channel
at a real native height.  This file makes the same finite-support construction
available at an arbitrary complex parameter and inserts it, role by role, in
the three `logJet` occurrences of the seeded six-source TFVD datum.

It deliberately does *not* invent a camera decomposition of the three
ordinary roles.  The companion obstruction file records why the present
logarithmic factorization channel cannot simply be reused for them: its
initial boundary atom vanishes, while the ordinary source retains that atom.
Thus this is a partial, provenance-preserving promotion, not an illicit
six-role promotion with the ordinary data silently synthesized early.
-/

open scoped BigOperators lp ENNReal NNReal

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-! ## Complex-parameter camera log channel -/

/-- The existing camera log-slope channel, without restricting its parameter
to the native real line. -/
noncomputable def cameraResolvedLogSlopeChannelAt
    (M : ℕ) (s : ℂ) (camera : ℕ) : CarryVerticalL2 :=
  nativeGpreCanonicalVerticalRealization
    (∑ n ∈ Finset.range M,
      Finsupp.single n ((cameraResolvedLogDirichletGradient s n) camera))

/-- Finite external-camera support of the complex log channel. -/
noncomputable def cameraResolvedLogSlopeSupportAt
    (M : ℕ) (s : ℂ) : Finset ℕ := by
  classical
  exact (Finset.range M).biUnion (fun n =>
    (cameraResolvedLogDirichletGradient s n).support)

/-- The complex-parameter prefix with its external camera labels retained. -/
noncomputable def finiteCameraResolvedLogSlopePrefixStateAt
    (M : ℕ) (s : ℂ) : CameraResolvedCarryVertical := by
  classical
  exact ∑ camera ∈ cameraResolvedLogSlopeSupportAt M s,
    Finsupp.single camera (cameraResolvedLogSlopeChannelAt M s camera)

theorem cameraResolvedLogSlopeChannelAt_apply
    (M : ℕ) (s : ℂ) (camera sample : ℕ) :
    cameraResolvedLogSlopeChannelAt M s camera sample =
      ∑ n ∈ Finset.range M,
        if n = sample then
          (cameraResolvedLogDirichletGradient s n) camera
        else 0 := by
  change
    (∑ n ∈ Finset.range M,
      Finsupp.single n ((cameraResolvedLogDirichletGradient s n) camera) :
      ℕ →₀ ℂ) sample = _
  by_cases hsample : sample < M <;>
    simp [Finset.sum_apply, Finsupp.single_apply, hsample]

theorem finiteCameraResolvedLogSlopePrefixStateAt_synthesis_apply
    (M : ℕ) (s : ℂ) :
    cameraChannelSynthesis (finiteCameraResolvedLogSlopePrefixStateAt M s) =
      ∑ camera ∈ cameraResolvedLogSlopeSupportAt M s,
        cameraResolvedLogSlopeChannelAt M s camera := by
  simp [finiteCameraResolvedLogSlopePrefixStateAt, cameraChannelSynthesis]

/-- Exact complex-parameter synthesis of the camera-resolved log channel. -/
theorem finiteCameraResolvedLogSlopePrefixStateAt_synthesis_eq_completedTfvd
    (M : ℕ) (s : ℂ) :
    cameraChannelSynthesis (finiteCameraResolvedLogSlopePrefixStateAt M s) =
      canonicalCompletedC3LogJetPrefixState s M := by
  classical
  have hsupport (n : ℕ) (hn : n < M) :
      (cameraResolvedLogDirichletGradient s n).support ⊆
        cameraResolvedLogSlopeSupportAt M s := by
    intro camera hcamera
    exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr hn, hcamera⟩
  have hsum (n : ℕ) (hn : n < M) :
      (∑ camera ∈ cameraResolvedLogSlopeSupportAt M s,
        (cameraResolvedLogDirichletGradient s n) camera) =
        positiveLogDirichletGradient s n := by
    let g := cameraResolvedLogDirichletGradient s n
    calc
      (∑ camera ∈ cameraResolvedLogSlopeSupportAt M s, g camera) =
          ∑ camera ∈ g.support, g camera := by
        symm
        apply Finset.sum_subset (hsupport n hn)
        intro camera hcamera hnot
        exact Finsupp.notMem_support_iff.mp hnot
      _ = cameraComplexSynthesis g :=
        (cameraComplexSynthesis_apply g).symm
      _ = positiveLogDirichletGradient s n :=
        cameraComplexSynthesis_cameraResolvedLogDirichletGradient s n
  rw [finiteCameraResolvedLogSlopePrefixStateAt_synthesis_apply]
  ext sample
  rw [canonicalCompletedC3LogJetPrefixState_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply,
    cameraResolvedLogSlopeChannelAt_apply]
  rw [Finset.sum_comm]
  by_cases hsample : sample < M
  · simpa [hsample] using hsum sample hsample
  · simp [hsample]

/-- On the native real line the new spelling is definitionally the existing
camera-resolved log prefix. -/
theorem finiteCameraResolvedLogSlopePrefixStateAt_nativeLine
    (M : ℕ) (time : ℝ) :
    finiteCameraResolvedLogSlopePrefixStateAt M (nativeLine time) =
      finiteCameraResolvedLogSlopePrefixState M time :=
  rfl

/-! ## The three retained log-jet roles -/

/-- A camera-resolved TFVD analysis for one logarithmic source parameter. -/
noncomputable def cameraResolvedSeededClockLogJetTfvdAnalysis
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (s : ℂ) :
    ℕ →₀ NativeGpreFiniteTfvdAnalysisCarrier S :=
  cameraChannelTfvdAnalysis q S
    (finiteCameraResolvedLogSlopePrefixStateAt (3 * M) s)

/-- Synthesizing the camera-resolved log analysis gives exactly the established
seeded-clock `logJet` TFVD analysis. -/
theorem cameraResolvedSeededClockLogJetTfvdAnalysis_synthesis_eq_seededClock
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (s : ℂ) :
    cameraChannelAnalysisSynthesis S
        (cameraResolvedSeededClockLogJetTfvdAnalysis M q S s) =
      nativeC3SeededClockLogJetTfvdAnalysis M q S s := by
  unfold cameraResolvedSeededClockLogJetTfvdAnalysis
  rw [cameraChannelAnalysisSynthesis_tfvdAnalysis_commutes,
    finiteCameraResolvedLogSlopePrefixStateAt_synthesis_eq_completedTfvd]
  rfl

/-- The three source parameters of the six-source datum, retaining a
camera-resolved analysis for each of its logarithmic roles. -/
noncomputable def cameraResolvedSeededClockLogJetParameterAnalyses
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ) :
    CanonicalC3SixSourceParameterRole →
      (ℕ →₀ NativeGpreFiniteTfvdAnalysisCarrier S)
  | .z => cameraResolvedSeededClockLogJetTfvdAnalysis M q S z
  | .w => cameraResolvedSeededClockLogJetTfvdAnalysis M q S w
  | .reflectedZ => cameraResolvedSeededClockLogJetTfvdAnalysis M q S
      (reflectedParameter z)

/-- Each synthesized camera family is exactly the corresponding retained
`logJet` source role of the canonical seeded six-source analysis. -/
theorem cameraResolvedSeededClockLogJetParameterAnalyses_synthesis_eq_role
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ)
    (parameter : CanonicalC3SixSourceParameterRole) :
    cameraChannelAnalysisSynthesis S
        (cameraResolvedSeededClockLogJetParameterAnalyses M q S z w parameter) =
      canonicalC3SixSourceRoleAnalysis S
        (nativeC3SeededClockTfvdSixSourceAnalysis M q S z w)
        (parameter, .logJet) := by
  cases parameter <;>
    simp only [cameraResolvedSeededClockLogJetParameterAnalyses,
      canonicalC3SixSourceRoleAnalysis,
      nativeC3SeededClockTfvdSixSourceAnalysis] <;>
    exact cameraResolvedSeededClockLogJetTfvdAnalysis_synthesis_eq_seededClock
      M q S _

end

end CarrySelfAdjointOperator
