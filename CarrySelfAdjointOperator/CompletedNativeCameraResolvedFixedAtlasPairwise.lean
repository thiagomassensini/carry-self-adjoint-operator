import CarrySelfAdjointOperator.CompletedNativeCameraResolvedSixSourceGreenPorts
import CarrySelfAdjointOperator.CompletedNativeTfvdSixChannelJet
import Mathlib.Tactic

/-!
# Fixed material atlas for camera-pair Green kernels

The external camera support of a completed six-source analysis is written in
the earlier API as a finite support of parameter-dependent `Finsupp` data.
That is appropriate for a pointwise reconstruction, but it is not a stable
index set through `iteratedDeriv`: a coefficient that vanishes at one
parameter may have a nonzero derivative there.

This file first records the parameter-free *material* atlas.  It is the union
of the factorization supports of the finitely many Dirichlet atoms consumed by
the three-prefix C3 cutoff.  The atlas deliberately has camera labels in
`ℕ`; it makes no claim that the labels are `Nat.Primes` or boundary contexts.

Only the Green boundary is resolved here.  The provenance, off-diagonal,
residual, tail, Hermitian weight, and archimedean-chart terms of the final
readout remain global channels.
-/

open scoped BigOperators lp ENNReal NNReal

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

noncomputable section
set_option autoImplicit false

/-- The finite material camera atlas for a C3 cutoff.  The six source roles
consume gradients through the first `3 * M` samples, hence only the
factorizations of `1, …, 3*M+1` can occur.  In particular this atlas depends
only on `M`, not on analytic parameters, TFVD weight, or boundary contexts. -/
noncomputable def canonicalFiniteCameraAtlas (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (3 * M + 1)).biUnion
    (fun n => (n + 1).factorization.support)

/-- A camera outside the factorization ledger of an atom has zero complex
camera-log contribution at that atom. -/
theorem cameraLogContributionVectorComplex_apply_eq_zero_of_not_mem_factorization_support
    (n camera : ℕ) (hcamera : camera ∉ n.factorization.support) :
    cameraLogContributionVectorComplex n camera = 0 := by
  rw [cameraLogContributionVectorComplex_apply]
  have hzero : n.factorization camera = 0 :=
    Finsupp.notMem_support_iff.mp hcamera
  simp [hzero]

/-- The two material factorization ledgers entering a log-gradient both lie
in the fixed atlas. -/
theorem cameraResolvedLogDirichletGradient_support_subset_canonicalFiniteCameraAtlas
    (M : ℕ) (s : ℂ) {n : ℕ} (hn : n < 3 * M) :
    (cameraResolvedLogDirichletGradient s n).support ⊆
      canonicalFiniteCameraAtlas M := by
  intro camera hcamera
  by_contra hnot
  have hnot₁ : camera ∉ (n + 1).factorization.support := by
    intro hmem
    apply hnot
    change camera ∈ (Finset.range (3 * M + 1)).biUnion
      (fun j => (j + 1).factorization.support)
    apply Finset.mem_biUnion.mpr
    exact ⟨n, Finset.mem_range.mpr (by omega), hmem⟩
  have hnot₂ : camera ∉ (n + 2).factorization.support := by
    intro hmem
    apply hnot
    change camera ∈ (Finset.range (3 * M + 1)).biUnion
      (fun j => (j + 1).factorization.support)
    apply Finset.mem_biUnion.mpr
    exact ⟨n + 1, Finset.mem_range.mpr (by omega), by simpa [Nat.add_assoc] using hmem⟩
  have hval₀ : cameraResolvedLogDirichletValue s n camera = 0 := by
    rw [cameraResolvedLogDirichletValue_apply,
      cameraLogContributionVectorComplex_apply_eq_zero_of_not_mem_factorization_support
        (n + 1) camera hnot₁]
    ring
  have hval₁ : cameraResolvedLogDirichletValue s (n + 1) camera = 0 := by
    rw [cameraResolvedLogDirichletValue_apply,
      cameraLogContributionVectorComplex_apply_eq_zero_of_not_mem_factorization_support
        (n + 2) camera hnot₂]
    ring
  have hzero : cameraResolvedLogDirichletGradient s n camera = 0 := by
    rw [cameraResolvedLogDirichletGradient_apply, hval₁, hval₀]
    ring
  exact (Finsupp.notMem_support_iff.mpr hzero) hcamera

/-- The ordinary boundary-free values entering an ordinary gradient use the
same two material factorization ledgers, so their camera support is also
parameter-free. -/
theorem cameraResolvedOrdinaryDirichletGradient_support_subset_canonicalFiniteCameraAtlas
    (M : ℕ) (s : ℂ) {n : ℕ} (hn : n < 3 * M) :
    (cameraResolvedOrdinaryDirichletGradient s n).support ⊆
      canonicalFiniteCameraAtlas M := by
  intro camera hcamera
  by_contra hnot
  have hnot₁ : camera ∉ (n + 1).factorization.support := by
    intro hmem
    apply hnot
    change camera ∈ (Finset.range (3 * M + 1)).biUnion
      (fun j => (j + 1).factorization.support)
    apply Finset.mem_biUnion.mpr
    exact ⟨n, Finset.mem_range.mpr (by omega), hmem⟩
  have hnot₂ : camera ∉ (n + 2).factorization.support := by
    intro hmem
    apply hnot
    change camera ∈ (Finset.range (3 * M + 1)).biUnion
      (fun j => (j + 1).factorization.support)
    apply Finset.mem_biUnion.mpr
    exact ⟨n + 1, Finset.mem_range.mpr (by omega), by simpa [Nat.add_assoc] using hmem⟩
  have hval₀ : cameraResolvedOrdinaryBoundaryFreeValue s n camera = 0 := by
    by_cases hnzero : n = 0
    · subst n
      simp [cameraResolvedOrdinaryBoundaryFreeValue]
    · rw [cameraResolvedOrdinaryBoundaryFreeValue, if_neg hnzero,
      Finsupp.smul_apply, cameraLogContributionVectorComplex_apply_eq_zero_of_not_mem_factorization_support
        (n + 1) camera hnot₁]
      ring
  have hval₁ : cameraResolvedOrdinaryBoundaryFreeValue s (n + 1) camera = 0 := by
    have hsucc : n + 1 ≠ 0 := by omega
    rw [cameraResolvedOrdinaryBoundaryFreeValue, if_neg hsucc,
      Finsupp.smul_apply, cameraLogContributionVectorComplex_apply_eq_zero_of_not_mem_factorization_support
        (n + 2) camera hnot₂]
    ring
  have hzero : cameraResolvedOrdinaryDirichletGradient s n camera = 0 := by
    rw [cameraResolvedOrdinaryDirichletGradient_apply, hval₁, hval₀]
    ring
  exact (Finsupp.notMem_support_iff.mpr hzero) hcamera

/-- Every camera appearing in a finite log prefix is material, uniformly in
the complex evaluation parameter. -/
theorem cameraResolvedLogSlopeSupportAt_subset_canonicalFiniteCameraAtlas
    (M : ℕ) (s : ℂ) :
    cameraResolvedLogSlopeSupportAt (3 * M) s ⊆ canonicalFiniteCameraAtlas M := by
  intro camera hcamera
  rcases Finset.mem_biUnion.mp hcamera with ⟨n, hn, hcamera⟩
  exact cameraResolvedLogDirichletGradient_support_subset_canonicalFiniteCameraAtlas
    M s (by simpa using Finset.mem_range.mp hn) hcamera

/-- Every camera appearing in a finite ordinary-gradient prefix is material,
uniformly in the complex evaluation parameter. -/
theorem cameraResolvedOrdinarySlopeSupportAt_subset_canonicalFiniteCameraAtlas
    (M : ℕ) (s : ℂ) :
    cameraResolvedOrdinarySlopeSupportAt (3 * M) s ⊆ canonicalFiniteCameraAtlas M := by
  intro camera hcamera
  rcases Finset.mem_biUnion.mp hcamera with ⟨n, hn, hcamera⟩
  exact cameraResolvedOrdinaryDirichletGradient_support_subset_canonicalFiniteCameraAtlas
    M s (by simpa using Finset.mem_range.mp hn) hcamera

/-- The outer `Finsupp` of a finite log prefix introduces no labels beyond
the support used to construct it. -/
theorem finiteCameraResolvedLogSlopePrefixStateAt_support_subset_canonicalFiniteCameraAtlas
    (M : ℕ) (s : ℂ) :
    (finiteCameraResolvedLogSlopePrefixStateAt (3 * M) s).support ⊆
      canonicalFiniteCameraAtlas M := by
  classical
  intro camera hcamera
  rw [finiteCameraResolvedLogSlopePrefixStateAt] at hcamera
  rcases Finsupp.mem_support_finsetSum camera hcamera with
    ⟨sourceCamera, hsourceCamera, hsingle⟩
  have hcameraEq : camera = sourceCamera :=
    (Finsupp.single_apply_ne_zero.mp (Finsupp.mem_support_iff.mp hsingle)).1
  subst camera
  exact cameraResolvedLogSlopeSupportAt_subset_canonicalFiniteCameraAtlas M s hsourceCamera

/-- The outer `Finsupp` of a finite ordinary-gradient prefix likewise carries
only material camera labels. -/
theorem finiteCameraResolvedOrdinarySlopePrefixStateAt_support_subset_canonicalFiniteCameraAtlas
    (M : ℕ) (s : ℂ) :
    (finiteCameraResolvedOrdinarySlopePrefixStateAt (3 * M) s).support ⊆
      canonicalFiniteCameraAtlas M := by
  classical
  intro camera hcamera
  rw [finiteCameraResolvedOrdinarySlopePrefixStateAt] at hcamera
  rcases Finsupp.mem_support_finsetSum camera hcamera with
    ⟨sourceCamera, hsourceCamera, hsingle⟩
  have hcameraEq : camera = sourceCamera :=
    (Finsupp.single_apply_ne_zero.mp (Finsupp.mem_support_iff.mp hsingle)).1
  subst camera
  exact cameraResolvedOrdinarySlopeSupportAt_subset_canonicalFiniteCameraAtlas M s hsourceCamera

/-- Coordinatewise TFVD analysis cannot create a new external camera label. -/
theorem cameraResolvedSeededClockLogJetTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (s : ℂ) :
    (cameraResolvedSeededClockLogJetTfvdAnalysis M q S s).support ⊆
      canonicalFiniteCameraAtlas M := by
  unfold cameraResolvedSeededClockLogJetTfvdAnalysis cameraChannelTfvdAnalysis
  exact Finset.Subset.trans (Finsupp.support_mapRange (hf := map_zero _))
    (finiteCameraResolvedLogSlopePrefixStateAt_support_subset_canonicalFiniteCameraAtlas M s)

/-- Coordinatewise TFVD analysis cannot create a new external camera label in
the ordinary-gradient channel either. -/
theorem cameraResolvedSeededClockOrdinaryTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (s : ℂ) :
    (cameraResolvedSeededClockOrdinaryTfvdAnalysis M q S s).support ⊆
      canonicalFiniteCameraAtlas M := by
  unfold cameraResolvedSeededClockOrdinaryTfvdAnalysis cameraChannelTfvdAnalysis
  exact Finset.Subset.trans (Finsupp.support_mapRange (hf := map_zero _))
    (finiteCameraResolvedOrdinarySlopePrefixStateAt_support_subset_canonicalFiniteCameraAtlas M s)

/-- Each of the six affine source roles has parameter-uniform material camera
support. -/
theorem cameraResolvedSeededClockAffineSixSourceRoleAnalysis_support_subset_canonicalFiniteCameraAtlas
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ)
    (role : CanonicalC3SixSourceRole) :
    (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
      M q S z w role).cameraAnalysis.support ⊆ canonicalFiniteCameraAtlas M := by
  rcases role with ⟨parameter, channel⟩
  cases parameter <;> cases channel
  · simpa [cameraResolvedSeededClockAffineSixSourceRoleAnalyses,
      cameraResolvedSeededClockOrdinaryParameterAnalyses] using
      cameraResolvedSeededClockOrdinaryTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
        M q S z
  · simpa [cameraResolvedSeededClockAffineSixSourceRoleAnalyses,
      cameraResolvedSeededClockLogJetParameterAnalyses] using
      cameraResolvedSeededClockLogJetTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
        M q S z
  · simpa [cameraResolvedSeededClockAffineSixSourceRoleAnalyses,
      cameraResolvedSeededClockOrdinaryParameterAnalyses] using
      cameraResolvedSeededClockOrdinaryTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
        M q S w
  · simpa [cameraResolvedSeededClockAffineSixSourceRoleAnalyses,
      cameraResolvedSeededClockLogJetParameterAnalyses] using
      cameraResolvedSeededClockLogJetTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
        M q S w
  · simpa [cameraResolvedSeededClockAffineSixSourceRoleAnalyses,
      cameraResolvedSeededClockOrdinaryParameterAnalyses] using
      cameraResolvedSeededClockOrdinaryTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
        M q S (reflectedParameter z)
  · simpa [cameraResolvedSeededClockAffineSixSourceRoleAnalyses,
      cameraResolvedSeededClockLogJetParameterAnalyses] using
      cameraResolvedSeededClockLogJetTfvdAnalysis_support_subset_canonicalFiniteCameraAtlas
        M q S (reflectedParameter z)

/-- The parameter-dependent pointwise support is contained in the fixed
material atlas.  This is the stabilization required before differentiating a
camera sum. -/
theorem cameraResolvedSeededClockAffineSixSourceSupport_subset_canonicalFiniteCameraAtlas
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ) :
    cameraResolvedSeededClockAffineSixSourceSupport M q S z w ⊆
      canonicalFiniteCameraAtlas M := by
  intro camera hcamera
  rcases Finset.mem_biUnion.mp hcamera with ⟨role, _, hcamera⟩
  exact cameraResolvedSeededClockAffineSixSourceRoleAnalysis_support_subset_canonicalFiniteCameraAtlas
    M q S z w role hcamera

/-- A camera analysis vanishes outside the pointwise six-role support.  This
is a support statement, not a claim that a camera coefficient remains zero in
a neighborhood of the parameter. -/
theorem cameraResolvedSeededClockAffineSixSourceCameraAnalysis_eq_zero_of_not_mem_support
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (z w : ℂ)
    (camera : ℕ)
    (hcamera : camera ∉ cameraResolvedSeededClockAffineSixSourceSupport M q S z w) :
    cameraResolvedSeededClockAffineSixSourceCameraAnalysis M q S z w camera = 0 := by
  unfold cameraResolvedSeededClockAffineSixSourceCameraAnalysis
  change canonicalC3SixSourceRoleAnalysisData S
      (fun role => (cameraResolvedSeededClockAffineSixSourceRoleAnalyses
        M q S z w role).cameraAnalysis camera) =
      canonicalC3SixSourceRoleAnalysisData S (fun _ => 0)
  apply congrArg (canonicalC3SixSourceRoleAnalysisData S)
  funext role
  apply Finsupp.notMem_support_iff.mp
  intro hrole
  apply hcamera
  exact Finset.mem_biUnion.mpr ⟨role, Finset.mem_univ _, hrole⟩

/-- Outside the pointwise support, the direct port is zero because its whole
six-source analyzed datum is zero. -/
theorem cameraResolvedDirectGreenPort_eq_zero_of_not_mem_support
    (M : ℕ) (z w : ℂ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (camera : ℕ)
    (hcamera : camera ∉ cameraResolvedSeededClockAffineSixSourceSupport M q S z w) :
    cameraResolvedDirectGreenPort M z w q hq0 hq1 S camera = 0 := by
  unfold cameraResolvedDirectGreenPort
  rw [cameraResolvedSeededClockAffineSixSourceCameraAnalysis_eq_zero_of_not_mem_support
    M q S z w camera hcamera]
  exact canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort_zero M z w q hq0 hq1 S

/-- Outside the pointwise support, the reflected port is zero for the same
reason. -/
theorem cameraResolvedReflectedGreenPort_eq_zero_of_not_mem_support
    (M : ℕ) (z w : ℂ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (camera : ℕ)
    (hcamera : camera ∉ cameraResolvedSeededClockAffineSixSourceSupport M q S z w) :
    cameraResolvedReflectedGreenPort M z w q hq0 hq1 S camera = 0 := by
  unfold cameraResolvedReflectedGreenPort
  rw [cameraResolvedSeededClockAffineSixSourceCameraAnalysis_eq_zero_of_not_mem_support
    M q S z w camera hcamera]
  exact canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort_zero M z w q hq0 hq1 S

/-- The direct Green port can be summed over the parameter-independent
material atlas. -/
theorem cameraResolvedDirectGreenPort_fixedAtlas_sum_eq_canonical
    (M : ℕ) (z w : ℂ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∑ camera ∈ canonicalFiniteCameraAtlas M,
      cameraResolvedDirectGreenPort M z w q hqpos.le hq1 S camera =
      canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort M z w q hqpos.le hq1 S
        (nativeC3SeededClockTfvdSixSourceAnalysis M q S z w) := by
  rw [← cameraResolvedDirectGreenPort_sum_eq_canonical M z w q hqpos hq1 S]
  symm
  apply Finset.sum_subset
    (cameraResolvedSeededClockAffineSixSourceSupport_subset_canonicalFiniteCameraAtlas
      M q S z w)
  intro camera _ hcamera
  exact cameraResolvedDirectGreenPort_eq_zero_of_not_mem_support
    M z w q hqpos.le hq1 S camera hcamera

/-- The reflected Green port can likewise be summed over the same fixed
material atlas. -/
theorem cameraResolvedReflectedGreenPort_fixedAtlas_sum_eq_canonical
    (M : ℕ) (z w : ℂ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∑ camera ∈ canonicalFiniteCameraAtlas M,
      cameraResolvedReflectedGreenPort M z w q hqpos.le hq1 S camera =
      canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort M z w q hqpos.le hq1 S
        (nativeC3SeededClockTfvdSixSourceAnalysis M q S z w) := by
  rw [← cameraResolvedReflectedGreenPort_sum_eq_canonical M z w q hqpos hq1 S]
  symm
  apply Finset.sum_subset
    (cameraResolvedSeededClockAffineSixSourceSupport_subset_canonicalFiniteCameraAtlas
      M q S z w)
  intro camera _ hcamera
  exact cameraResolvedReflectedGreenPort_eq_zero_of_not_mem_support
    M z w q hqpos.le hq1 S camera hcamera

/-- Fixed-atlas form of the corrected Green boundary.  The finite outer atlas
is independent of `z` and `w`, which is exactly what makes later
`iteratedDeriv` transport legitimate. -/
theorem canonicalC3CameraResolvedCorrectedGreenKernel_fixedAtlas_sum_eq_correctedBoundary
    (M : ℕ) (z w : ℂ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (∑ directCamera ∈ canonicalFiniteCameraAtlas M,
      ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
        canonicalC3CameraResolvedCorrectedGreenKernel M z w q hqpos.le hq1 S
          directCamera reflectedCamera) =
      canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary M z w q hqpos.le hq1 S
        (nativeC3SeededClockTfvdSixSourceAnalysis M q S z w) := by
  unfold canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary
  rw [← cameraResolvedDirectGreenPort_fixedAtlas_sum_eq_canonical M z w q hqpos hq1 S,
    ← cameraResolvedReflectedGreenPort_fixedAtlas_sum_eq_canonical M z w q hqpos hq1 S]
  exact (greenForm_finset_sum_pairwise
    (canonicalFiniteCameraAtlas M) (canonicalFiniteCameraAtlas M)
    (cameraResolvedDirectGreenPort M z w q hqpos.le hq1 S)
    (cameraResolvedReflectedGreenPort M z w q hqpos.le hq1 S)).symm

/-! ## The actual one-variable response curve -/

/-- The Green boundary along the exact univariate curve used by the canonical
six-analysis jet.  The curve is **not** an invented diagonal: its two
arguments are `operatorHeightParameter u` and the fixed
`operatorHeightParameter 0`, exactly as in
`canonicalC3BracketTfvdSixAnalysisNormalizedResponse`. -/
def canonicalC3CameraResolvedCorrectedGreenBoundaryResponse
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) : ℂ :=
  canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary (M + 1)
    (operatorHeightParameter u) (operatorHeightParameter 0) q hq0 hq1 S
    (nativeC3SeededClockTfvdSixSourceAnalysis (M + 1) q S
      (operatorHeightParameter u) (operatorHeightParameter 0))

/-- One raw camera-pair Green kernel along that same canonical response
curve.  It keeps both camera labels; no diagonalization is made. -/
def canonicalC3CameraResolvedCorrectedGreenResponse
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (directCamera reflectedCamera : ℕ) (u : ℂ) : ℂ :=
  canonicalC3CameraResolvedCorrectedGreenKernel (M + 1)
    (operatorHeightParameter u) (operatorHeightParameter 0) q hq0 hq1 S
    directCamera reflectedCamera

/-- Fixed-atlas functional decomposition of the unnormalized Green boundary
along the precise response curve. -/
theorem canonicalC3CameraResolvedCorrectedGreenBoundaryResponse_eq_cameraPairwise_sum
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) :
    canonicalC3CameraResolvedCorrectedGreenBoundaryResponse M q hqpos.le hq1 S u =
      ∑ directCamera ∈ canonicalFiniteCameraAtlas (M + 1),
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas (M + 1),
          canonicalC3CameraResolvedCorrectedGreenResponse M q hqpos.le hq1 S
            directCamera reflectedCamera u := by
  unfold canonicalC3CameraResolvedCorrectedGreenBoundaryResponse
    canonicalC3CameraResolvedCorrectedGreenResponse
  exact (canonicalC3CameraResolvedCorrectedGreenKernel_fixedAtlas_sum_eq_correctedBoundary
    (M + 1) (operatorHeightParameter u) (operatorHeightParameter 0)
      q hqpos hq1 S).symm

/-- The exact denominator used by the existing normalized six-analysis
response.  Naming it prevents any accidental alteration of the response
curve or its normalization. -/
def canonicalC3BracketTfvdSixAnalysisResponseDenominator (u : ℂ) : ℂ :=
  mixedHermitianWeight canonicalC3ChartFactorHeight u 0 *
    ((2 : ℂ) * completedNativeOperatorCharacteristic u *
      (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0))

/-- The normalized contribution of one camera pair.  The raw pair kernel is
multiplied by the same global weight and divided by the same denominator as
the full response, so it can be subtracted honestly from the full jet. -/
def canonicalC3CameraResolvedNormalizedCorrectedGreenResponse
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (directCamera reflectedCamera : ℕ) (u : ℂ) : ℂ :=
  (mixedHermitianWeight nativeXiCompletionFactor u 0 *
    canonicalC3CameraResolvedCorrectedGreenResponse M q hq0 hq1 S
      directCamera reflectedCamera u) /
    canonicalC3BracketTfvdSixAnalysisResponseDenominator u

/-- The normalized Green-only component of the full six-analysis response. -/
def canonicalC3NormalizedCorrectedGreenResponse
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) : ℂ :=
  (mixedHermitianWeight nativeXiCompletionFactor u 0 *
    canonicalC3CameraResolvedCorrectedGreenBoundaryResponse M q hq0 hq1 S u) /
    canonicalC3BracketTfvdSixAnalysisResponseDenominator u

/-- The fixed atlas also decomposes the normalized Green response. -/
theorem canonicalC3NormalizedCorrectedGreenResponse_eq_cameraPairwise_sum
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) :
    canonicalC3NormalizedCorrectedGreenResponse M q hqpos.le hq1 S u =
      ∑ directCamera ∈ canonicalFiniteCameraAtlas (M + 1),
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas (M + 1),
          canonicalC3CameraResolvedNormalizedCorrectedGreenResponse M q hqpos.le hq1 S
            directCamera reflectedCamera u := by
  unfold canonicalC3NormalizedCorrectedGreenResponse
    canonicalC3CameraResolvedNormalizedCorrectedGreenResponse
  rw [canonicalC3CameraResolvedCorrectedGreenBoundaryResponse_eq_cameraPairwise_sum
    M q hqpos hq1 S u]
  simp only [div_eq_mul_inv]
  rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro directCamera _
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro reflectedCamera _
  ring

/-- The non-Green numerator retained by the completed response: the
structural provenance/off-diagonal/readout-residual scalar, exact tail
completion, and archimedean chart.  The mixed Hermitian weight is deliberately
kept outside the parenthesized structural-plus-tail block exactly as in the
final readout. -/
def canonicalC3CameraResolvedNonGreenResponse
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) : ℂ :=
  let data := nativeC3SeededClockTfvdSixSourceAnalysis (M + 1) q S
    (operatorHeightParameter u) (operatorHeightParameter 0)
  let structural := canonicalC3AllCutoffMixedSourceTfvdStructuralReadout (M + 1)
    (operatorHeightParameter 0)
    (reflectedParameter (operatorHeightParameter u)) q hq0 hq1 S data
  (mixedHermitianWeight nativeXiCompletionFactor u 0 *
      (canonicalC3MixedStructuralScalarReadout structural +
        canonicalC3MixedHeightTailCompletionDefect (M + 1) u 0) +
    canonicalCompletedC3ArchimedeanChartMixedChannel u 0) /
      canonicalC3BracketTfvdSixAnalysisResponseDenominator u

/-- Exact functional split of the completed normalized response.  This
exposes, rather than suppresses, every channel not carried by the pairwise
Green boundary. -/
theorem canonicalC3BracketTfvdSixAnalysisNormalizedResponse_eq_green_add_nonGreen
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) :
    canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hqpos.le hq1 S u =
      canonicalC3NormalizedCorrectedGreenResponse M q hqpos.le hq1 S u +
        canonicalC3CameraResolvedNonGreenResponse M q hqpos.le hq1 S u := by
  unfold canonicalC3BracketTfvdSixAnalysisNormalizedResponse
    canonicalC3NormalizedCorrectedGreenResponse
    canonicalC3CameraResolvedNonGreenResponse
    canonicalC3CameraResolvedCorrectedGreenBoundaryResponse
  rw [canonicalC3AllCutoffMixedSourceTfvdFinalReadout_eq_components]
  rw [nativeC3SeededClockTfvdSixSourceAnalysis_eq_canonical]
  change _ / canonicalC3BracketTfvdSixAnalysisResponseDenominator u = _
  generalize hdenominator : canonicalC3BracketTfvdSixAnalysisResponseDenominator u = denominator
  ring

/-- The all-order coefficient of one *normalized* camera-pair Green response.
The order convention agrees literally with the pre-existing six-analysis jet:
the `(k+1)`-st derivative divided by `(k+1)!`. -/
def canonicalC3CameraResolvedCorrectedGreenJetCoefficient
    (M k : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (directCamera reflectedCamera : ℕ) : ℂ :=
  iteratedDeriv (k + 1)
    (canonicalC3CameraResolvedNormalizedCorrectedGreenResponse
      M q hq0 hq1 S directCamera reflectedCamera) 0 / (k + 1).factorial

/-- The all-order jet of the normalized Green-only response, prior to any
comparison with the full corrected coefficient. -/
def canonicalC3CorrectedGreenJetCoefficient
    (M k : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) : ℂ :=
  iteratedDeriv (k + 1)
    (canonicalC3NormalizedCorrectedGreenResponse M q hq0 hq1 S) 0 /
      (k + 1).factorial

/-- The explicit all-order difference between the full corrected six-analysis
jet and its fixed-atlas Green-only part.  This is a definition of the
residual, not an assertion that it vanishes. -/
def canonicalC3CameraResolvedCorrectedJetResidual
    (M k : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) : ℂ :=
  canonicalC3BracketTfvdSixAnalysisJetCoefficient M k q hq0 hq1 S -
    canonicalC3CorrectedGreenJetCoefficient M k q hq0 hq1 S

/-- Definitional presentation of the full corrected coefficient as its
fixed-atlas Green jet plus the exposed residual. -/
theorem canonicalC3BracketTfvdSixAnalysisJetCoefficient_eq_greenJet_add_residual
    (M k : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3BracketTfvdSixAnalysisJetCoefficient M k q hq0 hq1 S =
      canonicalC3CorrectedGreenJetCoefficient M k q hq0 hq1 S +
        canonicalC3CameraResolvedCorrectedJetResidual M k q hq0 hq1 S := by
  unfold canonicalC3CameraResolvedCorrectedJetResidual
  ring

/-! ## Conditional analytic transport interface -/

/-- Once local differentiability of the already-defined fixed-atlas pair
responses is supplied, `iteratedDeriv` passes through both finite sums.  This
does not add a mathematical hypothesis to the construction: it isolates the
one remaining analytic adapter that must be proved from the finite TFVD/Green
formulae before the all-order pairwise theorem can become unconditional. -/
theorem canonicalC3CorrectedGreenJetCoefficient_eq_cameraPairwise_sum_of_contDiff
    (M k : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (hregular : ∀ directCamera ∈ canonicalFiniteCameraAtlas (M + 1),
      ∀ reflectedCamera ∈ canonicalFiniteCameraAtlas (M + 1),
        ContDiffAt ℂ (k + 1)
          (canonicalC3CameraResolvedNormalizedCorrectedGreenResponse
            M q hqpos.le hq1 S directCamera reflectedCamera) 0) :
    canonicalC3CorrectedGreenJetCoefficient M k q hqpos.le hq1 S =
      ∑ directCamera ∈ canonicalFiniteCameraAtlas (M + 1),
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas (M + 1),
          canonicalC3CameraResolvedCorrectedGreenJetCoefficient M k q hqpos.le hq1 S
            directCamera reflectedCamera := by
  unfold canonicalC3CorrectedGreenJetCoefficient
    canonicalC3CameraResolvedCorrectedGreenJetCoefficient
  have hsum : canonicalC3NormalizedCorrectedGreenResponse M q hqpos.le hq1 S =
      fun u => ∑ directCamera ∈ canonicalFiniteCameraAtlas (M + 1),
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas (M + 1),
          canonicalC3CameraResolvedNormalizedCorrectedGreenResponse
            M q hqpos.le hq1 S directCamera reflectedCamera u := by
    funext u
    exact canonicalC3NormalizedCorrectedGreenResponse_eq_cameraPairwise_sum
      M q hqpos hq1 S u
  rw [hsum]
  rw [iteratedDeriv_fun_sum]
  · simp only [div_eq_mul_inv]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro directCamera hdirectCamera
    rw [iteratedDeriv_fun_sum]
    · rw [Finset.sum_mul]
    · intro reflectedCamera hreflectedCamera
      exact hregular directCamera hdirectCamera reflectedCamera hreflectedCamera
  · intro directCamera hdirectCamera
    exact ContDiffAt.sum fun reflectedCamera hreflectedCamera =>
      hregular directCamera hdirectCamera reflectedCamera hreflectedCamera

/-- The finite camera matrix of normalized Green jets.  Its row and column
indices are external material camera labels in the fixed atlas; no primality
coercion or positivity claim is made here. -/
def canonicalC3CameraResolvedCorrectedGreenJetMatrix
    (M k : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    Matrix (canonicalFiniteCameraAtlas (M + 1))
      (canonicalFiniteCameraAtlas (M + 1)) ℂ :=
  fun directCamera reflectedCamera =>
    canonicalC3CameraResolvedCorrectedGreenJetCoefficient M k q hq0 hq1 S
      directCamera reflectedCamera

/-- The normalized all-order coefficient of the explicitly non-Green
functional remainder. -/
def canonicalC3CameraResolvedNonGreenJetCoefficient
    (M k : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) : ℂ :=
  iteratedDeriv (k + 1)
    (canonicalC3CameraResolvedNonGreenResponse M q hq0 hq1 S) 0 /
      (k + 1).factorial

/-- With the same fixed-atlas pair regularity and the regularity of the
explicit remaining functional, the residual jet is exactly the jet of the
non-Green channels.  The theorem is deliberately conditional: the current
repository has not yet supplied analytic lemmas for the finite TFVD Green
ports, the mixed Hermitian weight, and their normalized denominator. -/
theorem canonicalC3CameraResolvedCorrectedJetResidual_eq_nonGreenJet_of_contDiff
    (M k : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (hregular : ∀ directCamera ∈ canonicalFiniteCameraAtlas (M + 1),
      ∀ reflectedCamera ∈ canonicalFiniteCameraAtlas (M + 1),
        ContDiffAt ℂ (k + 1)
          (canonicalC3CameraResolvedNormalizedCorrectedGreenResponse
            M q hqpos.le hq1 S directCamera reflectedCamera) 0)
    (hremaining : ContDiffAt ℂ (k + 1)
      (canonicalC3CameraResolvedNonGreenResponse M q hqpos.le hq1 S) 0) :
    canonicalC3CameraResolvedCorrectedJetResidual M k q hqpos.le hq1 S =
      canonicalC3CameraResolvedNonGreenJetCoefficient M k q hqpos.le hq1 S := by
  have hgreen : ContDiffAt ℂ (k + 1)
      (canonicalC3NormalizedCorrectedGreenResponse M q hqpos.le hq1 S) 0 := by
    rw [show canonicalC3NormalizedCorrectedGreenResponse M q hqpos.le hq1 S =
        fun u => ∑ directCamera ∈ canonicalFiniteCameraAtlas (M + 1),
          ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas (M + 1),
            canonicalC3CameraResolvedNormalizedCorrectedGreenResponse
              M q hqpos.le hq1 S directCamera reflectedCamera u by
      funext u
      exact canonicalC3NormalizedCorrectedGreenResponse_eq_cameraPairwise_sum
        M q hqpos hq1 S u]
    exact ContDiffAt.sum fun directCamera hdirectCamera =>
      ContDiffAt.sum fun reflectedCamera hreflectedCamera =>
        hregular directCamera hdirectCamera reflectedCamera hreflectedCamera
  have hfull : ContDiffAt ℂ (k + 1)
      (canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hqpos.le hq1 S) 0 := by
    rw [show canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hqpos.le hq1 S =
        canonicalC3NormalizedCorrectedGreenResponse M q hqpos.le hq1 S +
          canonicalC3CameraResolvedNonGreenResponse M q hqpos.le hq1 S by
      funext u
      exact canonicalC3BracketTfvdSixAnalysisNormalizedResponse_eq_green_add_nonGreen
        M q hqpos hq1 S u]
    exact hgreen.add hremaining
  unfold canonicalC3CameraResolvedCorrectedJetResidual
    canonicalC3BracketTfvdSixAnalysisJetCoefficient
    canonicalC3CorrectedGreenJetCoefficient
    canonicalC3CameraResolvedNonGreenJetCoefficient
  rw [show canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hqpos.le hq1 S =
      canonicalC3NormalizedCorrectedGreenResponse M q hqpos.le hq1 S +
        canonicalC3CameraResolvedNonGreenResponse M q hqpos.le hq1 S by
    funext u
    exact canonicalC3BracketTfvdSixAnalysisNormalizedResponse_eq_green_add_nonGreen
      M q hqpos hq1 S u,
    iteratedDeriv_add hgreen hremaining]
  ring



end

end CarrySelfAdjointOperator
