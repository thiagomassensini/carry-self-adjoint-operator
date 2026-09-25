import CarrySelfAdjointOperator.CompletedNativeCameraResolvedFixedAtlasPairwise
import CarrySelfAdjointOperator.CompletedNativeCameraResolvedPairwiseAnalyticNoGo

/-!
# Independent-reflected lift of the completed C3 six-source ledger

The physical six-source ledger specializes its `reflectedZ` roles using
`reflectedParameter z`.  On the canonical one-variable response curve this is
anti-holomorphic.  This file moves the reflection boundary to the final
physical section: the `reflectedZ` roles are instead supplied by an independent
coordinate `v`, through `operatorHeightParameter v`.

This is not the pre-existing Hermitian ``polarized'' ledger: the latter still
contains an explicit complex conjugation in one factor.  The construction here
is an independent-reflected source presentation; no complex analyticity is
asserted merely from that name.
-/

open scoped BigOperators lp ENNReal NNReal ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary

noncomputable section
set_option autoImplicit false

/-- The three genuinely independent parameter inputs of the lifted six-source
datum.  The direct `z` and fixed `w` roles use `u` and `0`; only the historical
`reflectedZ` roles use the new independent coordinate `v`. -/
def canonicalC3IndependentReflectedRoleParameter (u v : ℂ) :
    CanonicalC3SixSourceParameterRole → ℂ
  | .z => operatorHeightParameter u
  | .w => operatorHeightParameter 0
  | .reflectedZ => operatorHeightParameter v

/-- The six TFVD analyses before physical reflection is imposed.  In
particular, its two `reflectedZ` roles contain `operatorHeightParameter v`,
not `reflectedParameter (operatorHeightParameter u)`. -/
def nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S :=
  canonicalC3SixSourceRoleAnalysisData S (fun role =>
    match role with
    | (parameter, .ordinary) =>
        nativeC3SeededClockOrdinaryTfvdAnalysis M q S
          (canonicalC3IndependentReflectedRoleParameter u v parameter)
    | (parameter, .logJet) =>
        nativeC3SeededClockLogJetTfvdAnalysis M q S
          (canonicalC3IndependentReflectedRoleParameter u v parameter))

/-- On the physical section, the independent reflected coordinate restores the
established seeded-clock six-source analysis exactly. -/
theorem nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected_physicalSection
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (u : ℂ) :
    nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected M q S u
        ((starRingEnd ℂ) u) =
      nativeC3SeededClockTfvdSixSourceAnalysis M q S
        (operatorHeightParameter u) (operatorHeightParameter 0) := by
  unfold nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected
    canonicalC3SixSourceRoleAnalysisData
    canonicalC3IndependentReflectedRoleParameter
    nativeC3SeededClockTfvdSixSourceAnalysis
  rw [reflectedParameter_operatorHeightParameter_eq_operatorHeightParameter_conj]

/-! ## The same independent coordinate before camera synthesis -/

/-- Camera-resolved TFVD analyses for the six roles of the independent-
reflected datum. Source roles and external camera labels remain distinct. -/
def cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    CanonicalC3SixSourceRole → (ℕ →₀ NativeGpreFiniteTfvdAnalysisCarrier S)
  | (parameter, .ordinary) =>
      cameraResolvedSeededClockOrdinaryTfvdAnalysis M q S
        (canonicalC3IndependentReflectedRoleParameter u v parameter)
  | (parameter, .logJet) =>
      cameraResolvedSeededClockLogJetTfvdAnalysis M q S
        (canonicalC3IndependentReflectedRoleParameter u v parameter)

/-- No camera label is created by the independent reflected coordinate. -/
theorem cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses_support_subset_atlas
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (u v : ℂ)
    (role : CanonicalC3SixSourceRole) :
    (cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses
      M q S u v role).support ⊆ canonicalFiniteCameraAtlas M := by
  rcases role with ⟨parameter, channel⟩
  cases parameter <;> cases channel
  · simpa [cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses,
      canonicalC3IndependentReflectedRoleParameter] using
      cameraResolvedSeededClockOrdinaryTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
        M q S (operatorHeightParameter u)
  · simpa [cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses,
      canonicalC3IndependentReflectedRoleParameter] using
      cameraResolvedSeededClockLogJetTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
        M q S (operatorHeightParameter u)
  · simpa [cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses,
      canonicalC3IndependentReflectedRoleParameter] using
      cameraResolvedSeededClockOrdinaryTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
        M q S (operatorHeightParameter 0)
  · simpa [cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses,
      canonicalC3IndependentReflectedRoleParameter] using
      cameraResolvedSeededClockLogJetTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
        M q S (operatorHeightParameter 0)
  · simpa [cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses,
      canonicalC3IndependentReflectedRoleParameter] using
      cameraResolvedSeededClockOrdinaryTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
        M q S (operatorHeightParameter v)
  · simpa [cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses,
      canonicalC3IndependentReflectedRoleParameter] using
      cameraResolvedSeededClockLogJetTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
        M q S (operatorHeightParameter v)

/-- One external camera carrying all six independent-reflected TFVD roles. -/
def cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (u v : ℂ)
    (camera : ℕ) : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S :=
  canonicalC3SixSourceRoleAnalysisData S (fun role =>
    (cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses
      M q S u v role) camera)

/-- A Finsupp whose support is contained in the fixed material atlas can be
summed over that atlas without changing its camera-channel synthesis. -/
theorem sum_canonicalFiniteCameraAtlas_eq_cameraChannelAnalysisSynthesis
    (M : ℕ) (S : Finset NativeGpreBoundaryContext)
    (f : ℕ →₀ NativeGpreFiniteTfvdAnalysisCarrier S)
    (hfsupport : f.support ⊆ canonicalFiniteCameraAtlas M) :
    (∑ camera ∈ canonicalFiniteCameraAtlas M, f camera) =
      cameraChannelAnalysisSynthesis S f := by
  calc
    (∑ camera ∈ canonicalFiniteCameraAtlas M, f camera) =
        ∑ camera ∈ f.support, f camera := by
      symm
      apply Finset.sum_subset hfsupport
      intro camera _ hnot
      exact Finsupp.notMem_support_iff.mp hnot
    _ = cameraChannelAnalysisSynthesis S f := by
      change (∑ camera ∈ f.support, f camera) = f.sum (fun _ b => b)
      rfl

/-- The fixed-atlas camera sum recovers the independent-reflected six-source
analysis, role by role. -/
theorem cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis_sum_eq_canonical
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    ∑ camera ∈ canonicalFiniteCameraAtlas M,
      cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis
        M q S u v camera =
      nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected M q S u v := by
  have hrole (role : CanonicalC3SixSourceRole) :
      (∑ camera ∈ canonicalFiniteCameraAtlas M,
        (cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses
          M q S u v role) camera) =
        canonicalC3SixSourceRoleAnalysis S
          (nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected M q S u v)
          role := by
    rcases role with ⟨parameter, channel⟩
    cases parameter <;> cases channel
    · simpa [cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses,
        nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected,
        canonicalC3SixSourceRoleAnalysis, canonicalC3SixSourceRoleAnalysisData,
        canonicalC3IndependentReflectedRoleParameter] using
        (sum_canonicalFiniteCameraAtlas_eq_cameraChannelAnalysisSynthesis M S
          (cameraResolvedSeededClockOrdinaryTfvdAnalysis M q S (operatorHeightParameter u))
          (cameraResolvedSeededClockOrdinaryTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
            M q S (operatorHeightParameter u))).trans
          (cameraResolvedSeededClockOrdinaryTfvdAnalysis_synthesis_eq_seededClock M q S
            (operatorHeightParameter u))
    · simpa [cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses,
        nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected,
        canonicalC3SixSourceRoleAnalysis, canonicalC3SixSourceRoleAnalysisData,
        canonicalC3IndependentReflectedRoleParameter] using
        (sum_canonicalFiniteCameraAtlas_eq_cameraChannelAnalysisSynthesis M S
          (cameraResolvedSeededClockLogJetTfvdAnalysis M q S (operatorHeightParameter u))
          (cameraResolvedSeededClockLogJetTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
            M q S (operatorHeightParameter u))).trans
          (cameraResolvedSeededClockLogJetTfvdAnalysis_synthesis_eq_seededClock M q S
            (operatorHeightParameter u))
    · simpa [cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses,
        nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected,
        canonicalC3SixSourceRoleAnalysis, canonicalC3SixSourceRoleAnalysisData,
        canonicalC3IndependentReflectedRoleParameter] using
        (sum_canonicalFiniteCameraAtlas_eq_cameraChannelAnalysisSynthesis M S
          (cameraResolvedSeededClockOrdinaryTfvdAnalysis M q S (operatorHeightParameter 0))
          (cameraResolvedSeededClockOrdinaryTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
            M q S (operatorHeightParameter 0))).trans
          (cameraResolvedSeededClockOrdinaryTfvdAnalysis_synthesis_eq_seededClock M q S
            (operatorHeightParameter 0))
    · simpa [cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses,
        nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected,
        canonicalC3SixSourceRoleAnalysis, canonicalC3SixSourceRoleAnalysisData,
        canonicalC3IndependentReflectedRoleParameter] using
        (sum_canonicalFiniteCameraAtlas_eq_cameraChannelAnalysisSynthesis M S
          (cameraResolvedSeededClockLogJetTfvdAnalysis M q S (operatorHeightParameter 0))
          (cameraResolvedSeededClockLogJetTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
            M q S (operatorHeightParameter 0))).trans
          (cameraResolvedSeededClockLogJetTfvdAnalysis_synthesis_eq_seededClock M q S
            (operatorHeightParameter 0))
    · simpa [cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses,
        nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected,
        canonicalC3SixSourceRoleAnalysis, canonicalC3SixSourceRoleAnalysisData,
        canonicalC3IndependentReflectedRoleParameter] using
        (sum_canonicalFiniteCameraAtlas_eq_cameraChannelAnalysisSynthesis M S
          (cameraResolvedSeededClockOrdinaryTfvdAnalysis M q S (operatorHeightParameter v))
          (cameraResolvedSeededClockOrdinaryTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
            M q S (operatorHeightParameter v))).trans
          (cameraResolvedSeededClockOrdinaryTfvdAnalysis_synthesis_eq_seededClock M q S
            (operatorHeightParameter v))
    · simpa [cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses,
        nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected,
        canonicalC3SixSourceRoleAnalysis, canonicalC3SixSourceRoleAnalysisData,
        canonicalC3IndependentReflectedRoleParameter] using
        (sum_canonicalFiniteCameraAtlas_eq_cameraChannelAnalysisSynthesis M S
          (cameraResolvedSeededClockLogJetTfvdAnalysis M q S (operatorHeightParameter v))
          (cameraResolvedSeededClockLogJetTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
            M q S (operatorHeightParameter v))).trans
          (cameraResolvedSeededClockLogJetTfvdAnalysis_synthesis_eq_seededClock M q S
            (operatorHeightParameter v))
  have hdata :
      (∑ camera ∈ canonicalFiniteCameraAtlas M,
        cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis
          M q S u v camera) =
        canonicalC3SixSourceRoleAnalysisData S (fun role =>
          ∑ camera ∈ canonicalFiniteCameraAtlas M,
            (cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses
              M q S u v role) camera) := by
    induction (canonicalFiniteCameraAtlas M) using Finset.induction_on with
    | empty => rfl
    | insert camera A hcamera ih =>
        simp only [Finset.sum_insert hcamera]
        rw [ih]
        rfl
  calc
    (∑ camera ∈ canonicalFiniteCameraAtlas M,
      cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis
        M q S u v camera) =
        canonicalC3SixSourceRoleAnalysisData S (fun role =>
          ∑ camera ∈ canonicalFiniteCameraAtlas M,
            (cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses
              M q S u v role) camera) := hdata
    _ = canonicalC3SixSourceRoleAnalysisData S
        (canonicalC3SixSourceRoleAnalysis S
          (nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected M q S u v)) := by
      apply congrArg (canonicalC3SixSourceRoleAnalysisData S)
      funext role
      exact hrole role
    _ = nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected M q S u v :=
      canonicalC3SixSourceRoleAnalysisData_roleAnalysis S _

/-- The independent camera family restricts exactly to the established
physical camera family when `v = conj u`. -/
theorem cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis_physicalSection
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (u : ℂ)
    (camera : ℕ) :
    cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis M q S u
        ((starRingEnd ℂ) u) camera =
      cameraResolvedSeededClockAffineSixSourceCameraAnalysis M q S
        (operatorHeightParameter u) (operatorHeightParameter 0) camera := by
  unfold cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis
    cameraResolvedSeededClockAffineSixSourceCameraAnalysis
  apply congrArg (canonicalC3SixSourceRoleAnalysisData S)
  funext role
  rcases role with ⟨parameter, channel⟩
  cases parameter <;> cases channel <;>
    simp only [cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses,
      cameraResolvedSeededClockAffineSixSourceRoleAnalyses,
      cameraResolvedSeededClockOrdinaryParameterAnalyses,
      cameraResolvedSeededClockLogJetParameterAnalyses,
      canonicalC3IndependentReflectedRoleParameter] <;>
    rw [reflectedParameter_operatorHeightParameter_eq_operatorHeightParameter_conj]

/-! ## Reconstruction and ports before physical reflection -/

/-- One camera's reconstructed source for the independent-reflected ledger. -/
def cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) (camera : ℕ) :
    CanonicalC3AllCutoffMixedSourceHilbert :=
  canonicalC3AllCutoffMixedSourceTfvdReconstruction q hq0 hq1 S
    (cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis
      M q S u v camera)

/-- The reconstructed camera source restricts to its already compiled
physical counterpart on `v = conj u`. -/
theorem cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction_physicalSection
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) (camera : ℕ) :
    cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
      M q hq0 hq1 S u ((starRingEnd ℂ) u) camera =
    cameraResolvedSeededClockAffineSixSourceReconstruction M
      (operatorHeightParameter u) (operatorHeightParameter 0)
      q hq0 hq1 S camera := by
  unfold cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
    cameraResolvedSeededClockAffineSixSourceReconstruction
  rw [cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis_physicalSection]

/-- The direct Green port in the lift.  Its height parameter is the fixed
second source coordinate `operatorHeightParameter 0`. -/
def cameraResolvedIndependentReflectedDirectGreenPort
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) (camera : ℕ) :
    FiniteC3GreenPortCarrier (3 * M) :=
  CanonicalC3AllCutoffMixedSourceHilbert.greenPort (3 * M)
    (operatorHeightParameter 0)
    (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
      M q hq0 hq1 S u v camera).wSource

/-- The reflected Green port in the lift receives the independent reflected
height coordinate `operatorHeightParameter v` directly. -/
def cameraResolvedIndependentReflectedReflectedGreenPort
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) (camera : ℕ) :
    FiniteC3GreenPortCarrier (3 * M) :=
  CanonicalC3AllCutoffMixedSourceHilbert.greenPort (3 * M)
    (operatorHeightParameter v)
    (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
      M q hq0 hq1 S u v camera).reflectedZSource

/-- The direct lifted port has the established physical section. -/
theorem cameraResolvedIndependentReflectedDirectGreenPort_physicalSection
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) (camera : ℕ) :
    cameraResolvedIndependentReflectedDirectGreenPort M q hq0 hq1 S
      u ((starRingEnd ℂ) u) camera =
    cameraResolvedDirectGreenPort M (operatorHeightParameter u)
      (operatorHeightParameter 0) q hq0 hq1 S camera := by
  unfold cameraResolvedIndependentReflectedDirectGreenPort
    cameraResolvedDirectGreenPort
    canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort
  rw [cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction_physicalSection]
  rfl

/-- The reflected lifted port has the established physical section; this is
where the final substitution `v = conj u` restores physical reflection. -/
theorem cameraResolvedIndependentReflectedReflectedGreenPort_physicalSection
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) (camera : ℕ) :
    cameraResolvedIndependentReflectedReflectedGreenPort M q hq0 hq1 S
      u ((starRingEnd ℂ) u) camera =
    cameraResolvedReflectedGreenPort M (operatorHeightParameter u)
      (operatorHeightParameter 0) q hq0 hq1 S camera := by
  unfold cameraResolvedIndependentReflectedReflectedGreenPort
    cameraResolvedReflectedGreenPort
    canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort
  rw [cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction_physicalSection,
    reflectedParameter_operatorHeightParameter_eq_operatorHeightParameter_conj]
  rfl

/-- One camera-pair Green contribution before physical reflection is imposed. -/
def canonicalC3CameraResolvedIndependentReflectedGreenKernel
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ)
    (directCamera reflectedCamera : ℕ) : ℂ :=
  greenForm (𝕜 := ℂ)
    (cameraResolvedIndependentReflectedDirectGreenPort M q hq0 hq1 S u v directCamera)
    (cameraResolvedIndependentReflectedReflectedGreenPort M q hq0 hq1 S u v reflectedCamera)

/-- The independent-reflected pair kernel specializes exactly to the existing
physical pair kernel. -/
theorem canonicalC3CameraResolvedIndependentReflectedGreenKernel_physicalSection
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ)
    (directCamera reflectedCamera : ℕ) :
    canonicalC3CameraResolvedIndependentReflectedGreenKernel M q hq0 hq1 S
      u ((starRingEnd ℂ) u) directCamera reflectedCamera =
    canonicalC3CameraResolvedCorrectedGreenKernel M
      (operatorHeightParameter u) (operatorHeightParameter 0)
      q hq0 hq1 S directCamera reflectedCamera := by
  unfold canonicalC3CameraResolvedIndependentReflectedGreenKernel
    canonicalC3CameraResolvedCorrectedGreenKernel
  rw [cameraResolvedIndependentReflectedDirectGreenPort_physicalSection,
    cameraResolvedIndependentReflectedReflectedGreenPort_physicalSection]

/-! ## Fixed-atlas reconstruction and pairwise Green sum -/

/-- The canonical reconstructed source of the independent-reflected ledger. -/
def canonicalC3IndependentReflectedSixSourceReconstruction
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    CanonicalC3AllCutoffMixedSourceHilbert :=
  canonicalC3AllCutoffMixedSourceTfvdReconstruction q hq0 hq1 S
    (nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected M q S u v)

/-- Reconstruction commutes with the fixed finite camera sum in the
independent-reflected ledger. -/
theorem cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction_sum_eq_canonical
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    ∑ camera ∈ canonicalFiniteCameraAtlas M,
      cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
        M q hq0 hq1 S u v camera =
      canonicalC3IndependentReflectedSixSourceReconstruction M q hq0 hq1 S u v := by
  unfold cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
    canonicalC3IndependentReflectedSixSourceReconstruction
  rw [← canonicalC3AllCutoffMixedSourceTfvdReconstruction_finset_sum,
    cameraResolvedSeededClockIndependentReflectedSixSourceCameraAnalysis_sum_eq_canonical]

/-- A finite camera sum survives the `w` source projection and Green-port
extraction. -/
theorem greenPort_wSource_finset_sum
    (N : ℕ) (s : ℂ) {ι : Type*} (A : Finset ι)
    (f : ι → CanonicalC3AllCutoffMixedSourceHilbert) :
    CanonicalC3AllCutoffMixedSourceHilbert.greenPort N s
      (∑ i ∈ A, f i).wSource =
      ∑ i ∈ A,
        CanonicalC3AllCutoffMixedSourceHilbert.greenPort N s (f i).wSource := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      apply Prod.ext <;> ext n <;>
        simp [CanonicalC3AllCutoffMixedSourceHilbert.greenPort,
          CanonicalC3AllCutoffMixedSourceHilbert.wSource]
  | insert a A ha ih =>
      rw [Finset.sum_insert ha,
        canonicalC3AllCutoffMixedSourceHilbert_wSource_add,
        canonicalC3AllCutoffMixedSourceHilbert_greenPort_add,
        ih, Finset.sum_insert ha]

/-- A finite camera sum survives the reflected source projection and Green-port
extraction. -/
theorem greenPort_reflectedZSource_finset_sum
    (N : ℕ) (s : ℂ) {ι : Type*} (A : Finset ι)
    (f : ι → CanonicalC3AllCutoffMixedSourceHilbert) :
    CanonicalC3AllCutoffMixedSourceHilbert.greenPort N s
      (∑ i ∈ A, f i).reflectedZSource =
      ∑ i ∈ A,
        CanonicalC3AllCutoffMixedSourceHilbert.greenPort N s (f i).reflectedZSource := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      apply Prod.ext <;> ext n <;>
        simp [CanonicalC3AllCutoffMixedSourceHilbert.greenPort,
          CanonicalC3AllCutoffMixedSourceHilbert.reflectedZSource]
  | insert a A ha ih =>
      rw [Finset.sum_insert ha,
        canonicalC3AllCutoffMixedSourceHilbert_reflectedZSource_add,
        canonicalC3AllCutoffMixedSourceHilbert_greenPort_add,
        ih, Finset.sum_insert ha]

/-- The canonical direct port before physical reflection. -/
def canonicalC3IndependentReflectedDirectGreenPort
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    FiniteC3GreenPortCarrier (3 * M) :=
  CanonicalC3AllCutoffMixedSourceHilbert.greenPort (3 * M)
    (operatorHeightParameter 0)
    (canonicalC3IndependentReflectedSixSourceReconstruction M q hq0 hq1 S u v).wSource

/-- The canonical reflected port before physical reflection. -/
def canonicalC3IndependentReflectedReflectedGreenPort
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    FiniteC3GreenPortCarrier (3 * M) :=
  CanonicalC3AllCutoffMixedSourceHilbert.greenPort (3 * M)
    (operatorHeightParameter v)
    (canonicalC3IndependentReflectedSixSourceReconstruction M q hq0 hq1 S u v).reflectedZSource

/-- The fixed-atlas sum of direct camera ports is the independent canonical
direct port. -/
theorem cameraResolvedIndependentReflectedDirectGreenPort_sum_eq_canonical
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    ∑ camera ∈ canonicalFiniteCameraAtlas M,
      cameraResolvedIndependentReflectedDirectGreenPort M q hq0 hq1 S u v camera =
      canonicalC3IndependentReflectedDirectGreenPort M q hq0 hq1 S u v := by
  unfold cameraResolvedIndependentReflectedDirectGreenPort
    canonicalC3IndependentReflectedDirectGreenPort
  rw [← greenPort_wSource_finset_sum,
    cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction_sum_eq_canonical]

/-- The fixed-atlas sum of reflected camera ports is the independent canonical
reflected port. -/
theorem cameraResolvedIndependentReflectedReflectedGreenPort_sum_eq_canonical
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    ∑ camera ∈ canonicalFiniteCameraAtlas M,
      cameraResolvedIndependentReflectedReflectedGreenPort M q hq0 hq1 S u v camera =
      canonicalC3IndependentReflectedReflectedGreenPort M q hq0 hq1 S u v := by
  unfold cameraResolvedIndependentReflectedReflectedGreenPort
    canonicalC3IndependentReflectedReflectedGreenPort
  rw [← greenPort_reflectedZSource_finset_sum,
    cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction_sum_eq_canonical]

/-- The independent-reflected corrected Green boundary, before taking the
physical section. -/
def canonicalC3IndependentReflectedCorrectedGreenBoundary
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) : ℂ :=
  greenForm (𝕜 := ℂ)
    (canonicalC3IndependentReflectedDirectGreenPort M q hq0 hq1 S u v)
    (canonicalC3IndependentReflectedReflectedGreenPort M q hq0 hq1 S u v)

/-- The independent-reflected Green boundary is the fixed finite pairwise sum
of its camera kernels. -/
theorem canonicalC3IndependentReflectedCorrectedGreenBoundary_eq_cameraPairwise
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    canonicalC3IndependentReflectedCorrectedGreenBoundary M q hq0 hq1 S u v =
      ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
          canonicalC3CameraResolvedIndependentReflectedGreenKernel M q hq0 hq1 S u v
            directCamera reflectedCamera := by
  unfold canonicalC3IndependentReflectedCorrectedGreenBoundary
    canonicalC3CameraResolvedIndependentReflectedGreenKernel
  rw [← cameraResolvedIndependentReflectedDirectGreenPort_sum_eq_canonical,
    ← cameraResolvedIndependentReflectedReflectedGreenPort_sum_eq_canonical]
  exact greenForm_finset_sum_pairwise
    (canonicalFiniteCameraAtlas M) (canonicalFiniteCameraAtlas M)
    (cameraResolvedIndependentReflectedDirectGreenPort M q hq0 hq1 S u v)
    (cameraResolvedIndependentReflectedReflectedGreenPort M q hq0 hq1 S u v)

/-- Taking `v = conj u` after the independent pairwise construction recovers
the already compiled physical corrected Green boundary. -/
theorem canonicalC3IndependentReflectedCorrectedGreenBoundary_physicalSection
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) :
    canonicalC3IndependentReflectedCorrectedGreenBoundary M q hqpos.le hq1 S
      u ((starRingEnd ℂ) u) =
      canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary M
        (operatorHeightParameter u) (operatorHeightParameter 0)
        q hqpos.le hq1 S
        (nativeC3SeededClockTfvdSixSourceAnalysis M q S
          (operatorHeightParameter u) (operatorHeightParameter 0)) := by
  rw [canonicalC3IndependentReflectedCorrectedGreenBoundary_eq_cameraPairwise]
  calc
    (∑ directCamera ∈ canonicalFiniteCameraAtlas M,
      ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
        canonicalC3CameraResolvedIndependentReflectedGreenKernel M q hqpos.le hq1 S
          u ((starRingEnd ℂ) u) directCamera reflectedCamera) =
        ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
          ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
            canonicalC3CameraResolvedCorrectedGreenKernel M
              (operatorHeightParameter u) (operatorHeightParameter 0)
              q hqpos.le hq1 S directCamera reflectedCamera := by
          apply Finset.sum_congr rfl
          intro directCamera _
          apply Finset.sum_congr rfl
          intro reflectedCamera _
          exact canonicalC3CameraResolvedIndependentReflectedGreenKernel_physicalSection
            M q hqpos.le hq1 S u directCamera reflectedCamera
    _ = canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary M
        (operatorHeightParameter u) (operatorHeightParameter 0)
        q hqpos.le hq1 S
        (nativeC3SeededClockTfvdSixSourceAnalysis M q S
          (operatorHeightParameter u) (operatorHeightParameter 0)) :=
      canonicalC3CameraResolvedCorrectedGreenKernel_fixedAtlas_sum_eq_correctedBoundary
        M (operatorHeightParameter u) (operatorHeightParameter 0) q hqpos hq1 S

/-! ## Full completed readout before the physical section -/

/-- The completed six-source readout with the reflected input held independent
until the final physical section.  Structural provenance, tail completion,
the Hermitian weight and the archimedean chart remain literal separate
channels, exactly as in the physical final readout. -/
def canonicalC3IndependentReflectedSixSourceFinalReadout
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) : ℂ :=
  let data := nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected M q S u v
  let structural := canonicalC3AllCutoffMixedSourceTfvdStructuralReadout M
    (operatorHeightParameter 0) (operatorHeightParameter v) q hq0 hq1 S data
  mixedHermitianWeight nativeXiCompletionFactor u 0 *
      (canonicalC3IndependentReflectedCorrectedGreenBoundary M q hq0 hq1 S u v +
        canonicalC3MixedStructuralScalarReadout structural +
        canonicalC3MixedHeightTailCompletionDefect M u 0) +
    canonicalCompletedC3ArchimedeanChartMixedChannel u 0

/-- The normalized independent-reflected completed response uses exactly the
established central denominator; no denominator is redistributed among
cameras or roles. -/
def canonicalC3IndependentReflectedNormalizedResponse
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) : ℂ :=
  canonicalC3IndependentReflectedSixSourceFinalReadout (M + 1) q hq0 hq1 S u v /
    canonicalC3BracketTfvdSixAnalysisResponseDenominator u

/-- The Green-only summand of the normalized independent-reflected response.
It retains the existing global xi weight and central denominator verbatim. -/
def canonicalC3IndependentReflectedNormalizedCorrectedGreenResponse
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) : ℂ :=
  (mixedHermitianWeight nativeXiCompletionFactor u 0 *
    canonicalC3IndependentReflectedCorrectedGreenBoundary (M + 1) q hq0 hq1 S u v) /
    canonicalC3BracketTfvdSixAnalysisResponseDenominator u

/-- The literal non-Green summand of the independent-reflected response.
No structural, tail, chart, or completion channel is discarded. -/
def canonicalC3IndependentReflectedNonGreenResponse
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) : ℂ :=
  let data := nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected
    (M + 1) q S u v
  let structural := canonicalC3AllCutoffMixedSourceTfvdStructuralReadout (M + 1)
    (operatorHeightParameter 0) (operatorHeightParameter v) q hq0 hq1 S data
  (mixedHermitianWeight nativeXiCompletionFactor u 0 *
      (canonicalC3MixedStructuralScalarReadout structural +
        canonicalC3MixedHeightTailCompletionDefect (M + 1) u 0) +
    canonicalCompletedC3ArchimedeanChartMixedChannel u 0) /
      canonicalC3BracketTfvdSixAnalysisResponseDenominator u

/-- The full independent-reflected normalized response is its pairwise Green
summand plus the explicitly retained non-Green channels. -/
theorem canonicalC3IndependentReflectedNormalizedResponse_eq_green_add_nonGreen
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) :
    canonicalC3IndependentReflectedNormalizedResponse M q hq0 hq1 S u v =
      canonicalC3IndependentReflectedNormalizedCorrectedGreenResponse M q hq0 hq1 S u v +
        canonicalC3IndependentReflectedNonGreenResponse M q hq0 hq1 S u v := by
  unfold canonicalC3IndependentReflectedNormalizedResponse
    canonicalC3IndependentReflectedSixSourceFinalReadout
    canonicalC3IndependentReflectedNormalizedCorrectedGreenResponse
    canonicalC3IndependentReflectedNonGreenResponse
  dsimp only
  ring

/-- The full independent-reflected response has the canonical physical
section.  The final substitution is the only place where `v = conj u` is
made. -/
theorem canonicalC3IndependentReflectedNormalizedResponse_physicalSection
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) :
    canonicalC3IndependentReflectedNormalizedResponse M q hqpos.le hq1 S
      u ((starRingEnd ℂ) u) =
    canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hqpos.le hq1 S u := by
  unfold canonicalC3IndependentReflectedNormalizedResponse
    canonicalC3IndependentReflectedSixSourceFinalReadout
    canonicalC3BracketTfvdSixAnalysisNormalizedResponse
    canonicalC3AllCutoffMixedSourceTfvdFinalReadout
  rw [canonicalC3IndependentReflectedCorrectedGreenBoundary_physicalSection
      (M + 1) q hqpos hq1 S u,
    nativeC3SeededClockTfvdSixSourceAnalysisIndependentReflected_physicalSection,
    reflectedParameter_operatorHeightParameter_eq_operatorHeightParameter_conj,
    nativeC3SeededClockTfvdSixSourceAnalysis_eq_canonical]
  rfl

end

end CarrySelfAdjointOperator
