import CarrySelfAdjointOperator.CompletedNativeCameraResolvedOrdinaryAffineSeed
import CarrySelfAdjointOperator.CompletedNativeCameraResolvedSixSourceLogJetPromotion
import Mathlib.Tactic

/-!
# Boundary-aware camera resolution of the ordinary C3 gradient channel

The ordinary Dirichlet *value* is not a pure camera sum: its initial value is
the global unit boundary seed.  The factorization ledger nevertheless supplies
a canonical finite camera presentation of the boundary-free value
`positiveDirichletValue s n - 1`.  Taking consecutive differences then gives
an exact camera resolution of `positiveDirichletGradient` without placing the
seed in an arbitrary camera.

The normalization by `log (n + 1)` is used only away from the boundary.  It
is the inverse of the already established factorization synthesis
`cameraLogContributionVectorComplex`; no Parseval or positivity assertion is
made here.
-/

open scoped BigOperators lp ENNReal NNReal

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

noncomputable section
set_option autoImplicit false

/-- A scalar ordinary-value ledger with a separate global boundary coordinate
and a finite external-camera component. -/
structure CameraResolvedOrdinaryValueLedger where
  boundarySeed : ℂ
  cameraValue : CameraLogComplexSpace

/-- Synthesize the value represented by an affine ordinary ledger. -/
def cameraResolvedOrdinaryValueLedgerSynthesis
    (x : CameraResolvedOrdinaryValueLedger) : ℂ :=
  x.boundarySeed + cameraComplexSynthesis x.cameraValue

/-- The finite camera ledger for the part of the ordinary Dirichlet value
which remains after removing the global incoming seed.  The initial atom has
no external camera support. -/
noncomputable def cameraResolvedOrdinaryBoundaryFreeValue
    (s : ℂ) (n : ℕ) : CameraLogComplexSpace :=
  if n = 0 then 0 else
    ((positiveDirichletValue s n - 1) *
        (Real.log ((n + 1 : ℕ) : ℝ) : ℂ)⁻¹) •
      cameraLogContributionVectorComplex (n + 1)

/-- The canonical ordinary ledger at one positive Dirichlet vertex.  Its
boundary coordinate remains global rather than being charged to a camera. -/
noncomputable def canonicalCameraResolvedOrdinaryValueLedger
    (s : ℂ) (n : ℕ) : CameraResolvedOrdinaryValueLedger where
  boundarySeed := canonicalOrdinaryBoundarySeed s
  cameraValue := cameraResolvedOrdinaryBoundaryFreeValue s n

/-- The factorization-normalized camera ledger synthesizes exactly the
ordinary value after subtraction of the global boundary seed. -/
theorem cameraComplexSynthesis_cameraResolvedOrdinaryBoundaryFreeValue
    (s : ℂ) (n : ℕ) :
    cameraComplexSynthesis (cameraResolvedOrdinaryBoundaryFreeValue s n) =
      positiveDirichletValue s n - 1 := by
  by_cases hn : n = 0
  · subst n
    simp [cameraResolvedOrdinaryBoundaryFreeValue,
      positiveDirichletValue_zero_eq_one]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hgt : 1 < n + 1 := by omega
    have hgtReal : (1 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast hgt
    have hlogpos : 0 < Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_pos hgtReal
    have hlogReal : Real.log ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hlogpos
    have hlog : (Real.log ((n + 1 : ℕ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hlogReal
    rw [cameraResolvedOrdinaryBoundaryFreeValue, if_neg hn,
      cameraComplexSynthesis.map_smul,
      cameraComplexSynthesis_cameraLogContributionVectorComplex,
      primeDepthLogLedger_eq_log (Nat.succ_ne_zero n)]
    simp only [smul_eq_mul]
    rw [show n + 1 = n.succ by omega]
    field_simp [hlog]

/-- The affine boundary-plus-camera synthesis is the literal ordinary
Dirichlet value. -/
theorem cameraResolvedOrdinaryValueLedgerSynthesis_canonical
    (s : ℂ) (n : ℕ) :
    cameraResolvedOrdinaryValueLedgerSynthesis
      (canonicalCameraResolvedOrdinaryValueLedger s n) =
      positiveDirichletValue s n := by
  unfold cameraResolvedOrdinaryValueLedgerSynthesis
  change canonicalOrdinaryBoundarySeed s +
      cameraComplexSynthesis (cameraResolvedOrdinaryBoundaryFreeValue s n) =
    positiveDirichletValue s n
  rw [cameraComplexSynthesis_cameraResolvedOrdinaryBoundaryFreeValue,
    canonicalOrdinaryBoundarySeed_eq_one]
  ring

/-- The global boundary coordinate of the canonical ordinary ledger is always
the unit seed. -/
theorem canonicalCameraResolvedOrdinaryValueLedger_boundarySeed_eq_one
    (s : ℂ) (n : ℕ) :
    (canonicalCameraResolvedOrdinaryValueLedger s n).boundarySeed = 1 :=
  canonicalOrdinaryBoundarySeed_eq_one s

/-- Consecutive camera differences resolve the ordinary gradient.  The
boundary seed is not redistributed: it cancels because it is the same global
coordinate at both vertices. -/
noncomputable def cameraResolvedOrdinaryDirichletGradient
    (s : ℂ) (n : ℕ) : CameraLogComplexSpace :=
  cameraResolvedOrdinaryBoundaryFreeValue s (n + 1) -
    cameraResolvedOrdinaryBoundaryFreeValue s n

@[simp] theorem cameraResolvedOrdinaryDirichletGradient_apply
    (s : ℂ) (n camera : ℕ) :
    cameraResolvedOrdinaryDirichletGradient s n camera =
      cameraResolvedOrdinaryBoundaryFreeValue s (n + 1) camera -
        cameraResolvedOrdinaryBoundaryFreeValue s n camera := by
  rfl

/-- Exact external-camera synthesis of the native ordinary gradient. -/
theorem cameraComplexSynthesis_cameraResolvedOrdinaryDirichletGradient
    (s : ℂ) (n : ℕ) :
    cameraComplexSynthesis (cameraResolvedOrdinaryDirichletGradient s n) =
      positiveDirichletGradient s n := by
  rw [cameraResolvedOrdinaryDirichletGradient, map_sub,
    cameraComplexSynthesis_cameraResolvedOrdinaryBoundaryFreeValue,
    cameraComplexSynthesis_cameraResolvedOrdinaryBoundaryFreeValue]
  simp only [positiveDirichletGradient,
    positiveDirichletValue_eq_natDirichletTerm, Nat.add_assoc]
  ring

/-! ## Finite ordinary-gradient prefixes with external camera labels -/

/-- One external camera channel for the ordinary-gradient prefix at an
arbitrary complex parameter. -/
noncomputable def cameraResolvedOrdinarySlopeChannelAt
    (M : ℕ) (s : ℂ) (camera : ℕ) : CarryVerticalL2 :=
  nativeGpreCanonicalVerticalRealization
    (∑ n ∈ Finset.range M,
      Finsupp.single n ((cameraResolvedOrdinaryDirichletGradient s n) camera))

/-- The finite set of external cameras actually present in an ordinary
gradient prefix. -/
noncomputable def cameraResolvedOrdinarySlopeSupportAt
    (M : ℕ) (s : ℂ) : Finset ℕ := by
  classical
  exact (Finset.range M).biUnion (fun n =>
    (cameraResolvedOrdinaryDirichletGradient s n).support)

/-- The ordinary finite prefix with its external camera labels retained. -/
noncomputable def finiteCameraResolvedOrdinarySlopePrefixStateAt
    (M : ℕ) (s : ℂ) : CameraResolvedCarryVertical := by
  classical
  exact ∑ camera ∈ cameraResolvedOrdinarySlopeSupportAt M s,
    Finsupp.single camera (cameraResolvedOrdinarySlopeChannelAt M s camera)

theorem cameraResolvedOrdinarySlopeChannelAt_apply
    (M : ℕ) (s : ℂ) (camera sample : ℕ) :
    cameraResolvedOrdinarySlopeChannelAt M s camera sample =
      ∑ n ∈ Finset.range M,
        if n = sample then
          (cameraResolvedOrdinaryDirichletGradient s n) camera
        else 0 := by
  change
    (∑ n ∈ Finset.range M,
      Finsupp.single n ((cameraResolvedOrdinaryDirichletGradient s n) camera) :
      ℕ →₀ ℂ) sample = _
  by_cases hsample : sample < M <;>
    simp [Finset.sum_apply, Finsupp.single_apply, hsample]

theorem finiteCameraResolvedOrdinarySlopePrefixStateAt_synthesis_apply
    (M : ℕ) (s : ℂ) :
    cameraChannelSynthesis (finiteCameraResolvedOrdinarySlopePrefixStateAt M s) =
      ∑ camera ∈ cameraResolvedOrdinarySlopeSupportAt M s,
        cameraResolvedOrdinarySlopeChannelAt M s camera := by
  simp [finiteCameraResolvedOrdinarySlopePrefixStateAt, cameraChannelSynthesis]

/-- Synthesizing the finite external-camera ordinary channels gives exactly
the established completed ordinary TFVD prefix. -/
theorem finiteCameraResolvedOrdinarySlopePrefixStateAt_synthesis_eq_completedTfvd
    (M : ℕ) (s : ℂ) :
    cameraChannelSynthesis (finiteCameraResolvedOrdinarySlopePrefixStateAt M s) =
      canonicalCompletedC3DirichletGradientPrefixState s M := by
  classical
  have hsupport (n : ℕ) (hn : n < M) :
      (cameraResolvedOrdinaryDirichletGradient s n).support ⊆
        cameraResolvedOrdinarySlopeSupportAt M s := by
    intro camera hcamera
    exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr hn, hcamera⟩
  have hsum (n : ℕ) (hn : n < M) :
      (∑ camera ∈ cameraResolvedOrdinarySlopeSupportAt M s,
        (cameraResolvedOrdinaryDirichletGradient s n) camera) =
        positiveDirichletGradient s n := by
    let g := cameraResolvedOrdinaryDirichletGradient s n
    calc
      (∑ camera ∈ cameraResolvedOrdinarySlopeSupportAt M s, g camera) =
          ∑ camera ∈ g.support, g camera := by
        symm
        apply Finset.sum_subset (hsupport n hn)
        intro camera hcamera hnot
        exact Finsupp.notMem_support_iff.mp hnot
      _ = cameraComplexSynthesis g :=
        (cameraComplexSynthesis_apply g).symm
      _ = positiveDirichletGradient s n :=
        cameraComplexSynthesis_cameraResolvedOrdinaryDirichletGradient s n
  rw [finiteCameraResolvedOrdinarySlopePrefixStateAt_synthesis_apply]
  ext sample
  rw [canonicalCompletedC3DirichletGradientPrefixState_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply,
    cameraResolvedOrdinarySlopeChannelAt_apply]
  rw [Finset.sum_comm]
  by_cases hsample : sample < M
  · simpa [hsample] using hsum sample hsample
  · simp [hsample]

/-! ## Ordinary six-source roles with their boundary ledger retained -/

/-- The external-camera TFVD analysis of one ordinary-gradient source. -/
noncomputable def cameraResolvedSeededClockOrdinaryTfvdAnalysis
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (s : ℂ) :
    ℕ →₀ NativeGpreFiniteTfvdAnalysisCarrier S :=
  cameraChannelTfvdAnalysis q S
    (finiteCameraResolvedOrdinarySlopePrefixStateAt (3 * M) s)

/-- Synthesizing the camera-resolved ordinary-gradient analysis gives the
existing ordinary seeded-clock TFVD analysis. -/
theorem cameraResolvedSeededClockOrdinaryTfvdAnalysis_synthesis_eq_seededClock
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (s : ℂ) :
    cameraChannelAnalysisSynthesis S
        (cameraResolvedSeededClockOrdinaryTfvdAnalysis M q S s) =
      nativeC3SeededClockOrdinaryTfvdAnalysis M q S s := by
  unfold cameraResolvedSeededClockOrdinaryTfvdAnalysis
  rw [cameraChannelAnalysisSynthesis_tfvdAnalysis_commutes,
    finiteCameraResolvedOrdinarySlopePrefixStateAt_synthesis_eq_completedTfvd]
  rfl

/-- One ordinary source role retains its global seed separately from the
external camera family that resolves its gradient prefix. -/
structure CameraResolvedSeededClockOrdinaryRoleAnalysis
    (S : Finset NativeGpreBoundaryContext) where
  boundarySeed : ℂ
  cameraAnalysis : ℕ →₀ NativeGpreFiniteTfvdAnalysisCarrier S

/-- The camera-resolved ordinary role at each of the three six-source
parameter provenances. -/
noncomputable def cameraResolvedSeededClockOrdinaryParameterAnalyses
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ) :
    CanonicalC3SixSourceParameterRole →
      CameraResolvedSeededClockOrdinaryRoleAnalysis S
  | .z => ⟨canonicalOrdinaryBoundarySeed z,
      cameraResolvedSeededClockOrdinaryTfvdAnalysis M q S z⟩
  | .w => ⟨canonicalOrdinaryBoundarySeed w,
      cameraResolvedSeededClockOrdinaryTfvdAnalysis M q S w⟩
  | .reflectedZ => ⟨canonicalOrdinaryBoundarySeed (reflectedParameter z),
      cameraResolvedSeededClockOrdinaryTfvdAnalysis M q S (reflectedParameter z)⟩

/-- The boundary component is the unit incoming seed in each ordinary source
role, including reflected evaluation. -/
theorem cameraResolvedSeededClockOrdinaryParameterAnalyses_boundary_eq_one
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ)
    (parameter : CanonicalC3SixSourceParameterRole) :
    (cameraResolvedSeededClockOrdinaryParameterAnalyses M q S z w parameter).boundarySeed = 1 := by
  cases parameter <;>
    simp [cameraResolvedSeededClockOrdinaryParameterAnalyses,
      canonicalOrdinaryBoundarySeed_eq_one]

/-- The camera component of each affine ordinary role synthesizes to the
corresponding canonical ordinary six-source analysis.  The seed has not been
assigned to a camera; it lives in the companion `boundarySeed` field. -/
theorem cameraResolvedSeededClockOrdinaryParameterAnalyses_synthesis_eq_role
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ)
    (parameter : CanonicalC3SixSourceParameterRole) :
    cameraChannelAnalysisSynthesis S
        (cameraResolvedSeededClockOrdinaryParameterAnalyses
          M q S z w parameter).cameraAnalysis =
      canonicalC3SixSourceRoleAnalysis S
        (nativeC3SeededClockTfvdSixSourceAnalysis M q S z w)
        (parameter, .ordinary) := by
  cases parameter <;>
    simp only [cameraResolvedSeededClockOrdinaryParameterAnalyses,
      canonicalC3SixSourceRoleAnalysis,
      nativeC3SeededClockTfvdSixSourceAnalysis] <;>
    exact cameraResolvedSeededClockOrdinaryTfvdAnalysis_synthesis_eq_seededClock
      M q S _

/-! ## The affine six-source camera ledger -/

/-- A six-source role before external camera synthesis.  The boundary field is
nonzero precisely for ordinary roles; the TFVD analysis itself consumes the
gradient component, so its boundary contribution has already been retained in
the affine value presentation from which that gradient was formed. -/
structure CameraResolvedAffineSixSourceRoleAnalysis
    (S : Finset NativeGpreBoundaryContext) where
  boundarySeed : ℂ
  cameraAnalysis : ℕ →₀ NativeGpreFiniteTfvdAnalysisCarrier S

/-- The complete six-role family with ordinary roles stored as
`boundary ⊕ camera-gradient`, and log-jet roles stored as their already
camera-resolved linear channels.  Source roles and external camera labels
remain distinct types. -/
noncomputable def cameraResolvedSeededClockAffineSixSourceRoleAnalyses
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ) :
    CanonicalC3SixSourceRole → CameraResolvedAffineSixSourceRoleAnalysis S
  | (parameter, .ordinary) =>
      let ordinary := cameraResolvedSeededClockOrdinaryParameterAnalyses
        M q S z w parameter
      ⟨ordinary.boundarySeed, ordinary.cameraAnalysis⟩
  | (parameter, .logJet) =>
      ⟨0, cameraResolvedSeededClockLogJetParameterAnalyses M q S z w parameter⟩

/-- The affine ledger retains the unit boundary coordinate exactly at the
ordinary roles, and zero at the already linear log-jet roles. -/
theorem cameraResolvedSeededClockAffineSixSourceRoleAnalyses_boundarySeed
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ)
    (role : CanonicalC3SixSourceRole) :
    (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
      M q S z w role).boundarySeed =
      if role.2 = .ordinary then 1 else 0 := by
  rcases role with ⟨parameter, channel⟩
  cases parameter <;> cases channel <;>
    simp [cameraResolvedSeededClockAffineSixSourceRoleAnalyses,
      cameraResolvedSeededClockOrdinaryParameterAnalyses,
      canonicalOrdinaryBoundarySeed_eq_one]

/-- Synthesizing the camera part of every affine role gives exactly the
corresponding canonical seeded six-source analysis. -/
theorem cameraResolvedSeededClockAffineSixSourceRoleAnalyses_synthesis_eq_role
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ)
    (role : CanonicalC3SixSourceRole) :
    cameraChannelAnalysisSynthesis S
      (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
        M q S z w role).cameraAnalysis =
      canonicalC3SixSourceRoleAnalysis S
        (nativeC3SeededClockTfvdSixSourceAnalysis M q S z w) role := by
  rcases role with ⟨parameter, channel⟩
  cases parameter <;> cases channel
  · exact cameraResolvedSeededClockOrdinaryParameterAnalyses_synthesis_eq_role
      M q S z w .z
  · exact cameraResolvedSeededClockLogJetParameterAnalyses_synthesis_eq_role
      M q S z w .z
  · exact cameraResolvedSeededClockOrdinaryParameterAnalyses_synthesis_eq_role
      M q S z w .w
  · exact cameraResolvedSeededClockLogJetParameterAnalyses_synthesis_eq_role
      M q S z w .w
  · exact cameraResolvedSeededClockOrdinaryParameterAnalyses_synthesis_eq_role
      M q S z w .reflectedZ
  · exact cameraResolvedSeededClockLogJetParameterAnalyses_synthesis_eq_role
      M q S z w .reflectedZ

/-- Repack the synthesized camera analyses without identifying a source role
with a camera label. -/
noncomputable def cameraResolvedSeededClockAffineSixSourceAnalysisSynthesis
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ) :
    CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S :=
  canonicalC3SixSourceRoleAnalysisData S
    (fun role => cameraChannelAnalysisSynthesis S
      (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
        M q S z w role).cameraAnalysis)

/-- All six affine roles synthesize to the canonical seeded six-source TFVD
analysis.  This is the sought boundary-aware promotion: ordinary data use a
global seed plus camera-gradient channels, while log-jet data use the existing
linear camera channels. -/
theorem cameraResolvedSeededClockAffineSixSourceAnalysis_synthesis_eq_canonical
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ) :
    cameraResolvedSeededClockAffineSixSourceAnalysisSynthesis M q S z w =
      nativeC3SeededClockTfvdSixSourceAnalysis M q S z w := by
  calc
    cameraResolvedSeededClockAffineSixSourceAnalysisSynthesis M q S z w =
        canonicalC3SixSourceRoleAnalysisData S
          (canonicalC3SixSourceRoleAnalysis S
            (nativeC3SeededClockTfvdSixSourceAnalysis M q S z w)) := by
      apply congrArg (canonicalC3SixSourceRoleAnalysisData S)
      funext role
      exact cameraResolvedSeededClockAffineSixSourceRoleAnalyses_synthesis_eq_role
        M q S z w role
    _ = nativeC3SeededClockTfvdSixSourceAnalysis M q S z w :=
      canonicalC3SixSourceRoleAnalysisData_roleAnalysis S _

/-! ## A finite external-camera family of complete six-source analyses -/

/-- The finitely many external camera labels occurring anywhere among the six
affine source roles.  This is an atlas of labels, not an identification of
those labels with the six source roles. -/
noncomputable def cameraResolvedSeededClockAffineSixSourceSupport
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ) :
    Finset ℕ := by
  classical
  exact Finset.univ.biUnion (fun role : CanonicalC3SixSourceRole =>
    (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
      M q S z w role).cameraAnalysis.support)

/-- The complete six-source TFVD analysis carried by one external camera.
All six source roles are retained at this camera label before any Green
pairing. -/
noncomputable def cameraResolvedSeededClockAffineSixSourceCameraAnalysis
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ)
    (camera : ℕ) : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S :=
  canonicalC3SixSourceRoleAnalysisData S
    (fun role =>
      (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
        M q S z w role).cameraAnalysis camera)

/-- Summing one external-camera analysis over its finite support recovers the
complete affine six-source synthesis. -/
theorem cameraResolvedSeededClockAffineSixSourceCameraAnalysis_sum_eq_synthesis
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ) :
    ∑ camera ∈ cameraResolvedSeededClockAffineSixSourceSupport M q S z w,
      cameraResolvedSeededClockAffineSixSourceCameraAnalysis M q S z w camera =
      cameraResolvedSeededClockAffineSixSourceAnalysisSynthesis M q S z w := by
  classical
  have hsupport (role : CanonicalC3SixSourceRole) :
      (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
        M q S z w role).cameraAnalysis.support ⊆
        cameraResolvedSeededClockAffineSixSourceSupport M q S z w := by
    intro camera hcamera
    exact Finset.mem_biUnion.mpr ⟨role, Finset.mem_univ _, hcamera⟩
  have hrole (role : CanonicalC3SixSourceRole) :
      (∑ camera ∈ cameraResolvedSeededClockAffineSixSourceSupport M q S z w,
        (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
          M q S z w role).cameraAnalysis camera) =
        cameraChannelAnalysisSynthesis S
          (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
            M q S z w role).cameraAnalysis := by
    calc
      (∑ camera ∈ cameraResolvedSeededClockAffineSixSourceSupport M q S z w,
        (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
          M q S z w role).cameraAnalysis camera) =
          ∑ camera ∈ (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
            M q S z w role).cameraAnalysis.support,
            (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
              M q S z w role).cameraAnalysis camera := by
        symm
        apply Finset.sum_subset (hsupport role)
        intro camera hcamera hnot
        exact Finsupp.notMem_support_iff.mp hnot
      _ = cameraChannelAnalysisSynthesis S
          (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
            M q S z w role).cameraAnalysis := by
        change
          (∑ camera ∈ (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
            M q S z w role).cameraAnalysis.support,
            (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
              M q S z w role).cameraAnalysis camera) =
            (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
              M q S z w role).cameraAnalysis.sum (fun _ b => b)
        rfl
  have hdata (A : Finset ℕ) :
      (∑ camera ∈ A,
        cameraResolvedSeededClockAffineSixSourceCameraAnalysis M q S z w camera) =
        canonicalC3SixSourceRoleAnalysisData S
          (fun role => ∑ camera ∈ A,
            (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
              M q S z w role).cameraAnalysis camera) := by
    induction A using Finset.induction_on with
    | empty =>
        change (0 : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) = 0
        rfl
    | insert camera A hcamera ih =>
        simp only [Finset.sum_insert hcamera]
        rw [ih]
        rfl
  calc
    (∑ camera ∈ cameraResolvedSeededClockAffineSixSourceSupport M q S z w,
      cameraResolvedSeededClockAffineSixSourceCameraAnalysis M q S z w camera) =
        canonicalC3SixSourceRoleAnalysisData S
          (fun role => ∑ camera ∈
            cameraResolvedSeededClockAffineSixSourceSupport M q S z w,
            (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
              M q S z w role).cameraAnalysis camera) :=
      hdata _
    _ = cameraResolvedSeededClockAffineSixSourceAnalysisSynthesis M q S z w := by
      apply congrArg (canonicalC3SixSourceRoleAnalysisData S)
      funext role
      exact hrole role

/-- The finite camera family synthesizes to the native canonical six-source
analysis, with the ordinary unit seed retained only in the affine provenance
ledger and never placed in a camera coordinate. -/
theorem cameraResolvedSeededClockAffineSixSourceCameraAnalysis_sum_eq_canonical
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ) :
    ∑ camera ∈ cameraResolvedSeededClockAffineSixSourceSupport M q S z w,
      cameraResolvedSeededClockAffineSixSourceCameraAnalysis M q S z w camera =
      nativeC3SeededClockTfvdSixSourceAnalysis M q S z w := by
  rw [cameraResolvedSeededClockAffineSixSourceCameraAnalysis_sum_eq_synthesis,
    cameraResolvedSeededClockAffineSixSourceAnalysis_synthesis_eq_canonical]

end

end CarrySelfAdjointOperator
