import CarrySelfAdjointOperator.CompletedNativeIndependentReflectedUndressedGreen
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Analytic independent-reflected undressed Green carrier

This file proves analytic regularity for the ordinary reflected source before
it enters the undressed Green carrier.  The proof follows one fixed camera
coordinate through the finite channel map and the continuous TFVD maps.
-/

open scoped BigOperators lp ENNReal NNReal ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open CanonicalC3AllCutoffMixedSourceHilbert

noncomputable section
set_option autoImplicit false

/-! ## Analytic scalar inputs -/

/-- The positive Dirichlet value is analytic after the independent affine
parameter map. -/
theorem positiveDirichletValue_operatorHeight_analyticAt_zero
    (n : ℕ) :
    AnalyticAt ℂ (fun v => positiveDirichletValue (operatorHeightParameter v) n) 0 := by
  have hparameter : AnalyticAt ℂ (fun v => -operatorHeightParameter v) 0 :=
    operatorHeightParameter_analyticAt_zero.neg
  unfold positiveDirichletValue
  exact analyticAt_const.cpow hparameter
    (Complex.natCast_mem_slitPlane.mpr (by omega))

/-- The positive Dirichlet gradient is analytic after the independent affine
parameter map. -/
theorem positiveDirichletGradient_operatorHeight_analyticAt_zero
    (n : ℕ) :
    AnalyticAt ℂ (fun v => positiveDirichletGradient (operatorHeightParameter v) n) 0 := by
  unfold positiveDirichletGradient natDirichletTerm dirichletTerm
  have hparameter : AnalyticAt ℂ (fun v => -operatorHeightParameter v) 0 :=
    operatorHeightParameter_analyticAt_zero.neg
  have hleft : AnalyticAt ℂ
      (fun v => ((n + 2 : ℕ) : ℂ) ^ (-operatorHeightParameter v)) 0 :=
    analyticAt_const.cpow hparameter
      (Complex.natCast_mem_slitPlane.mpr (by omega))
  have hright : AnalyticAt ℂ
      (fun v => ((n + 1 : ℕ) : ℂ) ^ (-operatorHeightParameter v)) 0 :=
    analyticAt_const.cpow hparameter
      (Complex.natCast_mem_slitPlane.mpr (by omega))
  exact hleft.sub hright

/-! ## One fixed external camera -/

/-- One fixed coordinate of the boundary-free ordinary value is analytic. -/
theorem cameraResolvedOrdinaryBoundaryFreeValue_apply_operatorHeight_analyticAt_zero
    (n camera : ℕ) :
    AnalyticAt ℂ
      (fun v =>
        (cameraResolvedOrdinaryBoundaryFreeValue (operatorHeightParameter v) n) camera) 0 := by
  by_cases hn : n = 0
  · subst n
    simpa [cameraResolvedOrdinaryBoundaryFreeValue] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) 0)
  · simp only [cameraResolvedOrdinaryBoundaryFreeValue, if_neg hn,
      Finsupp.smul_apply, smul_eq_mul, cameraLogContributionVectorComplex_apply]
    have hvalue := positiveDirichletValue_operatorHeight_analyticAt_zero n
    have hone : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) 0 := analyticAt_const
    have hlog : AnalyticAt ℂ
        (fun _ : ℂ => (Real.log ((n + 1 : ℕ) : ℝ) : ℂ)⁻¹) 0 :=
      analyticAt_const
    let c : ℂ :=
      (((n + 1).factorization camera : ℝ) : ℂ) *
        ((Real.log (camera : ℝ) : ℝ) : ℂ)
    change AnalyticAt ℂ
      (fun v =>
        (positiveDirichletValue (operatorHeightParameter v) n - 1) *
          (Real.log ((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * c) 0
    exact ((hvalue.sub hone).mul hlog).mul analyticAt_const

/-- One fixed coordinate of the camera-resolved ordinary gradient is
analytic. -/
theorem cameraResolvedOrdinaryDirichletGradient_apply_operatorHeight_analyticAt_zero
    (n camera : ℕ) :
    AnalyticAt ℂ
      (fun v =>
        (cameraResolvedOrdinaryDirichletGradient (operatorHeightParameter v) n) camera) 0 := by
  unfold cameraResolvedOrdinaryDirichletGradient
  exact
    (cameraResolvedOrdinaryBoundaryFreeValue_apply_operatorHeight_analyticAt_zero
      (n + 1) camera).sub
      (cameraResolvedOrdinaryBoundaryFreeValue_apply_operatorHeight_analyticAt_zero n camera)

/-- The fixed camera ordinary slope channel agrees with the finite sum of
continuous coordinate insertions. -/
theorem cameraResolvedOrdinarySlopeChannelAt_eq_finset_single_sum
    (M : ℕ) (s : ℂ) (camera : ℕ) :
    cameraResolvedOrdinarySlopeChannelAt M s camera =
      ∑ n ∈ Finset.range M,
        lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 n
          ((cameraResolvedOrdinaryDirichletGradient s n) camera) := by
  ext sample
  rw [cameraResolvedOrdinarySlopeChannelAt_apply]
  simp only [lp.coeFn_sum, lp.singleContinuousLinearMap_apply,
    lp.coeFn_single, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hns : n = sample <;> simp [hns]

/-- The ordinary slope channel at one external camera is analytic in the
independent reflected coordinate. -/
theorem cameraResolvedOrdinarySlopeChannelAt_operatorHeight_analyticAt_zero
    (M camera : ℕ) :
    AnalyticAt ℂ
      (fun v =>
        cameraResolvedOrdinarySlopeChannelAt M (operatorHeightParameter v) camera) 0 := by
  rw [show (fun v =>
      cameraResolvedOrdinarySlopeChannelAt M (operatorHeightParameter v) camera) =
      fun v => ∑ n ∈ Finset.range M,
        lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 n
          ((cameraResolvedOrdinaryDirichletGradient (operatorHeightParameter v) n) camera) by
        funext v
        exact cameraResolvedOrdinarySlopeChannelAt_eq_finset_single_sum
          M (operatorHeightParameter v) camera]
  have hsingle (n : ℕ) : AnalyticAt ℂ
      (fun v => lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 n
        ((cameraResolvedOrdinaryDirichletGradient (operatorHeightParameter v) n) camera)) 0 := by
    let g : ℂ → ℂ := fun v =>
      (cameraResolvedOrdinaryDirichletGradient (operatorHeightParameter v) n) camera
    have hg : AnalyticAt ℂ g 0 := by
      simpa only [g] using
        cameraResolvedOrdinaryDirichletGradient_apply_operatorHeight_analyticAt_zero n camera
    have hmap : AnalyticAt ℂ
        (fun z : ℂ => lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 n z)
        (g 0) :=
      (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 n).analyticAt (g 0)
    simpa only [g, Function.comp_def] using hmap.comp hg
  induction M with
  | zero =>
      simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : CarryVerticalL2)) 0)
  | succ M ih =>
      have hsum :
          (fun v => ∑ n ∈ Finset.range (M + 1),
            lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 n
              ((cameraResolvedOrdinaryDirichletGradient
                (operatorHeightParameter v) n) camera)) =
          (fun v =>
            (∑ n ∈ Finset.range M,
              lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 n
                ((cameraResolvedOrdinaryDirichletGradient
                  (operatorHeightParameter v) n) camera)) +
            lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 M
              ((cameraResolvedOrdinaryDirichletGradient
                (operatorHeightParameter v) M) camera)) := by
        funext v
        rw [Finset.sum_range_succ]
      rw [hsum]
      exact ih.add (hsingle M)

/-- Evaluating the finite ordinary prefix at a fixed camera recovers that
camera's slope channel, including when the channel vanishes. -/
theorem finiteCameraResolvedOrdinarySlopePrefixStateAt_apply
    (M : ℕ) (s : ℂ) (camera : ℕ) :
    finiteCameraResolvedOrdinarySlopePrefixStateAt M s camera =
      cameraResolvedOrdinarySlopeChannelAt M s camera := by
  classical
  unfold finiteCameraResolvedOrdinarySlopePrefixStateAt
  have hsum :
      (∑ c ∈ cameraResolvedOrdinarySlopeSupportAt M s,
        (Finsupp.single c (cameraResolvedOrdinarySlopeChannelAt M s c) :
          CameraResolvedCarryVertical)) camera =
        if camera ∈ cameraResolvedOrdinarySlopeSupportAt M s then
          cameraResolvedOrdinarySlopeChannelAt M s camera
        else 0 := by
    simp [Finset.sum_apply, Finsupp.single_apply]
  rw [hsum]
  by_cases hcamera : camera ∈ cameraResolvedOrdinarySlopeSupportAt M s
  · simp [hcamera]
  · have hchannel : cameraResolvedOrdinarySlopeChannelAt M s camera = 0 := by
      ext sample
      rw [cameraResolvedOrdinarySlopeChannelAt_apply]
      apply Finset.sum_eq_zero
      intro n hn
      have hnot : camera ∉ (cameraResolvedOrdinaryDirichletGradient s n).support := by
        intro hsupport
        apply hcamera
        exact Finset.mem_biUnion.mpr ⟨n, hn, hsupport⟩
      simp [Finsupp.notMem_support_iff.mp hnot]
    simp [hcamera, hchannel]

/-- One fixed camera coordinate of the external TFVD analysis is the TFVD
analysis of its ordinary slope channel. -/
theorem cameraResolvedSeededClockOrdinaryTfvdAnalysis_apply
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (s : ℂ) (camera : ℕ) :
    cameraResolvedSeededClockOrdinaryTfvdAnalysis M q S s camera =
      nativeGpreFiniteTfvdAnalysis q S
        (cameraResolvedOrdinarySlopeChannelAt (3 * M) s camera) := by
  unfold cameraResolvedSeededClockOrdinaryTfvdAnalysis cameraChannelTfvdAnalysis
  simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
  rw [finiteCameraResolvedOrdinarySlopePrefixStateAt_apply]
  rfl

/-- The fixed-camera ordinary TFVD analysis is analytic after the independent
affine parameter map. -/
theorem cameraResolvedSeededClockOrdinaryTfvdAnalysis_apply_operatorHeight_analyticAt_zero
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (camera : ℕ) :
    AnalyticAt ℂ
      (fun v =>
        cameraResolvedSeededClockOrdinaryTfvdAnalysis M q S
          (operatorHeightParameter v) camera) 0 := by
  rw [show (fun v =>
      cameraResolvedSeededClockOrdinaryTfvdAnalysis M q S
        (operatorHeightParameter v) camera) =
      fun v => nativeGpreFiniteTfvdAnalysis q S
        (cameraResolvedOrdinarySlopeChannelAt
          (3 * M) (operatorHeightParameter v) camera) by
        funext v
        exact cameraResolvedSeededClockOrdinaryTfvdAnalysis_apply
          M q S (operatorHeightParameter v) camera]
  let channel : ℂ → CarryVerticalL2 := fun v =>
    cameraResolvedOrdinarySlopeChannelAt (3 * M) (operatorHeightParameter v) camera
  have hchannel : AnalyticAt ℂ channel 0 := by
    simpa only [channel] using
      cameraResolvedOrdinarySlopeChannelAt_operatorHeight_analyticAt_zero (3 * M) camera
  have hmap : AnalyticAt ℂ
      (fun x : CarryVerticalL2 => nativeGpreFiniteTfvdAnalysis q S x)
      (channel 0) :=
    (nativeGpreFiniteTfvdAnalysis q S).analyticAt (channel 0)
  simpa only [channel, Function.comp_def] using hmap.comp hchannel

/-- The reflected ordinary TFVD datum of one camera, named separately only to
make its analytic path explicit. -/
def cameraResolvedIndependentReflectedOrdinaryTfvdAnalysis
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (v : ℂ) (camera : ℕ) : NativeGpreFiniteTfvdAnalysisCarrier S :=
  cameraResolvedSeededClockOrdinaryTfvdAnalysis M q S
    (operatorHeightParameter v) camera

/-- The `(reflectedZ, ordinary)` role is exactly the named reflected ordinary
TFVD datum. -/
theorem cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses_reflectedZ_ordinary_apply
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (u v : ℂ) (camera : ℕ) :
    (cameraResolvedSeededClockIndependentReflectedSixSourceRoleAnalyses
      M q S u v (.reflectedZ, .ordinary)) camera =
      cameraResolvedIndependentReflectedOrdinaryTfvdAnalysis M q S v camera :=
  rfl

/-- The reflected ordinary TFVD datum is analytic in its independent
coordinate. -/
theorem cameraResolvedIndependentReflectedOrdinaryTfvdAnalysis_analyticAt_zero
    (M : ℕ) (q : ℝ) (S : Finset NativeGpreBoundaryContext) (camera : ℕ) :
    AnalyticAt ℂ
      (fun v =>
        cameraResolvedIndependentReflectedOrdinaryTfvdAnalysis M q S v camera) 0 := by
  exact cameraResolvedSeededClockOrdinaryTfvdAnalysis_apply_operatorHeight_analyticAt_zero
    M q S camera

/-! ## Reconstruction projection -/

/-- The ordinary component of the reconstructed reflected source is supplied
only by the reconstructed `(reflectedZ, ordinary)` TFVD datum. -/
theorem cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction_reflectedZSource_fst_eq
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) (camera : ℕ) :
    (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
      M q hq0 hq1 S u v camera).reflectedZSource.1 =
      nativeGpreFiniteTfvdReconstruction q hq0 hq1 S
        (cameraResolvedIndependentReflectedOrdinaryTfvdAnalysis M q S v camera) := by
  rfl

/-- The reconstructed ordinary reflected source is analytic before it enters
the undressed Green-port extractor. -/
theorem cameraResolvedIndependentReflectedReconstructedOrdinary_analyticAt_zero
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (camera : ℕ) :
    AnalyticAt ℂ
      (fun v =>
        nativeGpreFiniteTfvdReconstruction q hq0 hq1 S
          (cameraResolvedIndependentReflectedOrdinaryTfvdAnalysis M q S v camera)) 0 := by
  let analysis : ℂ → NativeGpreFiniteTfvdAnalysisCarrier S := fun v =>
    cameraResolvedIndependentReflectedOrdinaryTfvdAnalysis M q S v camera
  have hanalysis : AnalyticAt ℂ analysis 0 := by
    simpa only [analysis] using
      cameraResolvedIndependentReflectedOrdinaryTfvdAnalysis_analyticAt_zero M q S camera
  have hmap : AnalyticAt ℂ
      (fun x : NativeGpreFiniteTfvdAnalysisCarrier S =>
        nativeGpreFiniteTfvdReconstruction q hq0 hq1 S x)
      (analysis 0) :=
    (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S).analyticAt (analysis 0)
  simpa only [analysis, Function.comp_def] using hmap.comp hanalysis

/-- The exact analytic capstone for the ordinary component of the
camera-resolved reconstructed reflected source. -/
theorem cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction_reflectedZSource_fst_analyticAt_zero
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) (camera : ℕ) :
    AnalyticAt ℂ
      (fun v =>
        (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
          M q hq0 hq1 S u v camera).reflectedZSource.1) 0 := by
  rw [show (fun v =>
      (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
        M q hq0 hq1 S u v camera).reflectedZSource.1) =
      fun v => nativeGpreFiniteTfvdReconstruction q hq0 hq1 S
        (cameraResolvedIndependentReflectedOrdinaryTfvdAnalysis M q S v camera) by
        funext v
        exact cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction_reflectedZSource_fst_eq
          M q hq0 hq1 S u v camera]
  exact cameraResolvedIndependentReflectedReconstructedOrdinary_analyticAt_zero
    M q hq0 hq1 S camera

/-! ## Undressed Green ports and kernels -/

/-- The reflected undressed Green port is analytic, with no remaining source
hypothesis. -/
theorem cameraResolvedIndependentReflectedUndressedReflectedGreenPort_analyticAt_zero
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) (camera : ℕ) :
    AnalyticAt ℂ
      (fun v => cameraResolvedIndependentReflectedUndressedReflectedGreenPort
        M q hq0 hq1 S u v camera) 0 := by
  apply cameraResolvedIndependentReflectedUndressedReflectedGreenPort_analyticAt_zero_of_reconstructedOrdinary
  exact cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction_reflectedZSource_fst_analyticAt_zero
    M q hq0 hq1 S u camera

/-- The Green form with its first input fixed, bundled as a continuous linear
map in the second input. -/
def greenFormFixedLeft {N : ℕ} (direct : FiniteC3GreenPortCarrier N) :
    FiniteC3GreenPortCarrier N →L[ℂ] ℂ :=
  (innerSL ℂ direct.2).comp
      (ContinuousLinearMap.fst ℂ
        (FiniteC3GreenBoundarySpace N) (FiniteC3GreenBoundarySpace N)) -
    (innerSL ℂ direct.1).comp
      (ContinuousLinearMap.snd ℂ
        (FiniteC3GreenBoundarySpace N) (FiniteC3GreenBoundarySpace N))

@[simp] theorem greenFormFixedLeft_apply
    {N : ℕ} (direct reflected : FiniteC3GreenPortCarrier N) :
    greenFormFixedLeft direct reflected = greenForm direct reflected := by
  simp [greenFormFixedLeft, greenForm, innerSL_apply_apply]

/-- Each pairwise undressed camera Green kernel is analytic in the independent
reflected coordinate. -/
theorem canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel_analyticAt_zero
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ)
    (directCamera reflectedCamera : ℕ) :
    AnalyticAt ℂ
      (fun v => canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
        M q hq0 hq1 S u v directCamera reflectedCamera) 0 := by
  let direct : FiniteC3GreenPortCarrier (3 * M) :=
    cameraResolvedIndependentReflectedUndressedDirectGreenPort
      M q hq0 hq1 S u 0 directCamera
  rw [show (fun v =>
      canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
        M q hq0 hq1 S u v directCamera reflectedCamera) =
      fun v => greenFormFixedLeft direct
        (cameraResolvedIndependentReflectedUndressedReflectedGreenPort
          M q hq0 hq1 S u v reflectedCamera) by
        funext v
        simp only [canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel,
          greenFormFixedLeft_apply]
        have hdirectv :
            cameraResolvedIndependentReflectedUndressedDirectGreenPort
              M q hq0 hq1 S u v directCamera = direct := by
          simpa only [direct] using
            cameraResolvedIndependentReflectedUndressedDirectGreenPort_independent
              M q hq0 hq1 S u v u 0 directCamera
        rw [hdirectv]]
  let reflected : ℂ → FiniteC3GreenPortCarrier (3 * M) := fun v =>
    cameraResolvedIndependentReflectedUndressedReflectedGreenPort
      M q hq0 hq1 S u v reflectedCamera
  have hreflected : AnalyticAt ℂ reflected 0 := by
    simpa only [reflected] using
      cameraResolvedIndependentReflectedUndressedReflectedGreenPort_analyticAt_zero
        M q hq0 hq1 S u reflectedCamera
  have hmap : AnalyticAt ℂ
      (fun x : FiniteC3GreenPortCarrier (3 * M) => greenFormFixedLeft direct x)
      (reflected 0) :=
    (greenFormFixedLeft direct).analyticAt (reflected 0)
  simpa only [reflected, Function.comp_def] using hmap.comp hreflected

/-- The fixed finite pairwise sum of undressed Green kernels is analytic in
the independent reflected coordinate. -/
theorem canonicalC3IndependentReflectedUndressedGreenBoundary_analyticAt_zero
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) :
    AnalyticAt ℂ
      (fun v => canonicalC3IndependentReflectedUndressedGreenBoundary
        M q hq0 hq1 S u v) 0 := by
  rw [show (fun v => canonicalC3IndependentReflectedUndressedGreenBoundary
      M q hq0 hq1 S u v) =
      fun v => ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
          canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
            M q hq0 hq1 S u v directCamera reflectedCamera by
        funext v
        exact canonicalC3IndependentReflectedUndressedGreenBoundary_eq_cameraPairwise
          M q hq0 hq1 S u v]
  have hinner (directCamera : ℕ) : AnalyticAt ℂ
      (fun v => ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
        canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
          M q hq0 hq1 S u v directCamera reflectedCamera) 0 := by
    rw [show (fun v => ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
        canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
          M q hq0 hq1 S u v directCamera reflectedCamera) =
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
          fun v => canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
            M q hq0 hq1 S u v directCamera reflectedCamera by
          funext v
          simp only [Finset.sum_apply]]
    exact Finset.analyticAt_sum (canonicalFiniteCameraAtlas M) (fun reflectedCamera _ =>
      canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel_analyticAt_zero
        M q hq0 hq1 S u directCamera reflectedCamera)
  rw [show (fun v => ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
      ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
        canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
          M q hq0 hq1 S u v directCamera reflectedCamera) =
      ∑ directCamera ∈ canonicalFiniteCameraAtlas M, fun v =>
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
          canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
            M q hq0 hq1 S u v directCamera reflectedCamera by
        funext v
        simp only [Finset.sum_apply]]
  exact Finset.analyticAt_sum (canonicalFiniteCameraAtlas M) (fun directCamera _ =>
    hinner directCamera)

/-! ## Undressed all-order coefficients -/

/-- The `k`-th Taylor coefficient of one undressed camera-pair Green kernel.
Unlike the earlier normalized-response convention, this is the literal
`k`-th derivative divided by `k!`; there is no index shift. -/
def canonicalC3CameraResolvedIndependentReflectedUndressedGreenJetCoefficient
    (M k : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ)
    (directCamera reflectedCamera : ℕ) : ℂ :=
  iteratedDeriv k
    (fun v => canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
      M q hq0 hq1 S u v directCamera reflectedCamera) 0 / (k.factorial : ℂ)

/-- The `k`-th Taylor coefficient of the total undressed Green boundary. -/
def canonicalC3IndependentReflectedUndressedGreenJetCoefficient
    (M k : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) : ℂ :=
  iteratedDeriv k
    (fun v => canonicalC3IndependentReflectedUndressedGreenBoundary
      M q hq0 hq1 S u v) 0 / (k.factorial : ℂ)

/-- All undressed Taylor orders commute with the fixed finite camera-pair
sum. -/
theorem canonicalC3IndependentReflectedUndressedGreenJetCoefficient_eq_cameraPairwise_sum
    (M k : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) :
    canonicalC3IndependentReflectedUndressedGreenJetCoefficient
      M k q hq0 hq1 S u =
      ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
          canonicalC3CameraResolvedIndependentReflectedUndressedGreenJetCoefficient
            M k q hq0 hq1 S u directCamera reflectedCamera := by
  unfold canonicalC3IndependentReflectedUndressedGreenJetCoefficient
    canonicalC3CameraResolvedIndependentReflectedUndressedGreenJetCoefficient
  have hsum :
      (fun v => canonicalC3IndependentReflectedUndressedGreenBoundary
        M q hq0 hq1 S u v) =
      fun v => ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
          canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
            M q hq0 hq1 S u v directCamera reflectedCamera := by
    funext v
    exact canonicalC3IndependentReflectedUndressedGreenBoundary_eq_cameraPairwise
      M q hq0 hq1 S u v
  rw [hsum, iteratedDeriv_fun_sum]
  · simp only [div_eq_mul_inv]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro directCamera hdirectCamera
    rw [iteratedDeriv_fun_sum]
    · rw [Finset.sum_mul]
    · intro reflectedCamera hreflectedCamera
      exact
        (canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel_analyticAt_zero
          M q hq0 hq1 S u directCamera reflectedCamera).contDiffAt
  · intro directCamera hdirectCamera
    exact ContDiffAt.sum fun reflectedCamera hreflectedCamera =>
      (canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel_analyticAt_zero
        M q hq0 hq1 S u directCamera reflectedCamera).contDiffAt

/-- The zeroth undressed pair coefficient is the pairwise kernel value at the
analytic center. -/
theorem canonicalC3CameraResolvedIndependentReflectedUndressedGreenJetCoefficient_zero
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ)
    (directCamera reflectedCamera : ℕ) :
    canonicalC3CameraResolvedIndependentReflectedUndressedGreenJetCoefficient
      M 0 q hq0 hq1 S u directCamera reflectedCamera =
      canonicalC3CameraResolvedIndependentReflectedUndressedGreenKernel
        M q hq0 hq1 S u 0 directCamera reflectedCamera := by
  simp [canonicalC3CameraResolvedIndependentReflectedUndressedGreenJetCoefficient]

/-- The zeroth total undressed coefficient is the total boundary value at the
analytic center. -/
theorem canonicalC3IndependentReflectedUndressedGreenJetCoefficient_zero
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) :
    canonicalC3IndependentReflectedUndressedGreenJetCoefficient
      M 0 q hq0 hq1 S u =
      canonicalC3IndependentReflectedUndressedGreenBoundary M q hq0 hq1 S u 0 := by
  simp [canonicalC3IndependentReflectedUndressedGreenJetCoefficient]

end

end CarrySelfAdjointOperator
