import CarrySelfAdjointOperator.CompletedNativeCameraResolvedOrdinaryGradientPromotion
import CarrySelfAdjointOperator.CompletedNativeCameraResolvedGreenPairwise
import Mathlib.Tactic

/-!
# Camera-resolved reconstructed Green ports for the affine six-source ledger

The ordinary source was affine before its gradient was passed to TFVD.  At
this point all six TFVD analyses are a literal finite camera sum, so the
reconstruction and its two Green-port projections are tested only for their
genuine linearity.  No separate boundary port is introduced.
-/

open scoped BigOperators lp ENNReal NNReal

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Boundary

noncomputable section
set_option autoImplicit false

/-- The six-source reconstruction is additive.  It is implemented
coordinatewise from the continuous linear TFVD reconstruction, rather than
packaged upstream as a single continuous-linear-map wrapper. -/
theorem canonicalC3AllCutoffMixedSourceTfvdReconstruction_add
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (x y : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    canonicalC3AllCutoffMixedSourceTfvdReconstruction q hq0 hq1 S (x + y) =
      canonicalC3AllCutoffMixedSourceTfvdReconstruction q hq0 hq1 S x +
        canonicalC3AllCutoffMixedSourceTfvdReconstruction q hq0 hq1 S y := by
  change WithLp.toLp 2
      (((nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) (x.1.1 + y.1.1),
        (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) (x.1.2 + y.1.2)),
        WithLp.toLp 2
          (((nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) (x.2.1.1 + y.2.1.1),
            (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) (x.2.1.2 + y.2.1.2)),
            ((nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) (x.2.2.1 + y.2.2.1),
              (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) (x.2.2.2 + y.2.2.2)))) =
      WithLp.toLp 2
        (((nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) x.1.1,
          (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) x.1.2),
          WithLp.toLp 2
            (((nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) x.2.1.1,
              (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) x.2.1.2),
              ((nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) x.2.2.1,
                (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) x.2.2.2))) +
        WithLp.toLp 2
          (((nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) y.1.1,
            (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) y.1.2),
            WithLp.toLp 2
              (((nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) y.2.1.1,
                (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) y.2.1.2),
                ((nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) y.2.2.1,
                  (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S) y.2.2.2)))
  simp only [map_add, ← WithLp.toLp_add, Prod.mk_add_mk]

/-- Finite additivity of the coordinatewise six-source reconstruction. -/
theorem canonicalC3AllCutoffMixedSourceTfvdReconstruction_finset_sum
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {ι : Type*} (A : Finset ι)
    (f : ι → CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    canonicalC3AllCutoffMixedSourceTfvdReconstruction q hq0 hq1 S
        (∑ i ∈ A, f i) =
      ∑ i ∈ A,
        canonicalC3AllCutoffMixedSourceTfvdReconstruction q hq0 hq1 S (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      simp [canonicalC3AllCutoffMixedSourceTfvdReconstruction]
  | insert a A ha ih =>
      rw [Finset.sum_insert ha,
        canonicalC3AllCutoffMixedSourceTfvdReconstruction_add,
        ih, Finset.sum_insert ha]

/-- The primitive Green-port projection of one reconstructed C3 state is
additive. -/
theorem canonicalC3AllCutoffMixedSourceHilbert_greenPort_add
    (N : ℕ) (s : ℂ)
    (x y : CanonicalCompletedC3HilbertState) :
    CanonicalC3AllCutoffMixedSourceHilbert.greenPort N s (x + y) =
      CanonicalC3AllCutoffMixedSourceHilbert.greenPort N s x +
        CanonicalC3AllCutoffMixedSourceHilbert.greenPort N s y := by
  apply Prod.ext <;> ext n <;>
    simp [CanonicalC3AllCutoffMixedSourceHilbert.greenPort,
      ← WithLp.toLp_add, mul_add]

/-- The direct (`w`) source projection of the mixed carrier is additive. -/
theorem canonicalC3AllCutoffMixedSourceHilbert_wSource_add
    (x y : CanonicalC3AllCutoffMixedSourceHilbert) :
    CanonicalC3AllCutoffMixedSourceHilbert.wSource (x + y) =
      CanonicalC3AllCutoffMixedSourceHilbert.wSource x +
        CanonicalC3AllCutoffMixedSourceHilbert.wSource y := by
  change (x + y).snd.fst = x.snd.fst + y.snd.fst
  rfl

/-- The reflected-`z` source projection of the mixed carrier is additive. -/
theorem canonicalC3AllCutoffMixedSourceHilbert_reflectedZSource_add
    (x y : CanonicalC3AllCutoffMixedSourceHilbert) :
    CanonicalC3AllCutoffMixedSourceHilbert.reflectedZSource (x + y) =
      CanonicalC3AllCutoffMixedSourceHilbert.reflectedZSource x +
        CanonicalC3AllCutoffMixedSourceHilbert.reflectedZSource y := by
  change (x + y).snd.snd = x.snd.snd + y.snd.snd
  rfl

/-- Direct Green-port extraction is additive on six analyzed sources. -/
theorem canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort_add
    (M : ℕ) (z w : ℂ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (x y : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort M z w q hq0 hq1 S (x + y) =
      canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort M z w q hq0 hq1 S x +
        canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort M z w q hq0 hq1 S y := by
  unfold canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort
  rw [canonicalC3AllCutoffMixedSourceTfvdReconstruction_add,
    canonicalC3AllCutoffMixedSourceHilbert_wSource_add,
    canonicalC3AllCutoffMixedSourceHilbert_greenPort_add]

/-- Reflected Green-port extraction is additive on six analyzed sources. -/
theorem canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort_add
    (M : ℕ) (z w : ℂ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (x y : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort M z w q hq0 hq1 S (x + y) =
      canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort M z w q hq0 hq1 S x +
        canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort M z w q hq0 hq1 S y := by
  unfold canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort
  rw [canonicalC3AllCutoffMixedSourceTfvdReconstruction_add,
    canonicalC3AllCutoffMixedSourceHilbert_reflectedZSource_add,
    canonicalC3AllCutoffMixedSourceHilbert_greenPort_add]

/-- Direct Green-port extraction preserves the zero analyzed datum. -/
theorem canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort_zero
    (M : ℕ) (z w : ℂ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort M z w q hq0 hq1 S 0 = 0 := by
  apply Prod.ext <;> ext n <;>
    simp [canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort,
      canonicalC3AllCutoffMixedSourceTfvdReconstruction,
      CanonicalC3AllCutoffMixedSourceHilbert.wSource,
      CanonicalC3AllCutoffMixedSourceHilbert.greenPort]

/-- Reflected Green-port extraction preserves the zero analyzed datum. -/
theorem canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort_zero
    (M : ℕ) (z w : ℂ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort M z w q hq0 hq1 S 0 = 0 := by
  apply Prod.ext <;> ext n <;>
    simp [canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort,
      canonicalC3AllCutoffMixedSourceTfvdReconstruction,
      CanonicalC3AllCutoffMixedSourceHilbert.reflectedZSource,
      CanonicalC3AllCutoffMixedSourceHilbert.greenPort]

/-- Direct Green-port extraction preserves finite sums of six analyzed
sources. -/
theorem canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort_finset_sum
    (M : ℕ) (z w : ℂ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {ι : Type*} (A : Finset ι)
    (f : ι → CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort M z w q hq0 hq1 S
        (∑ i ∈ A, f i) =
      ∑ i ∈ A,
        canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort M z w q hq0 hq1 S (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      simp [canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort_zero]
  | insert a A ha ih =>
      rw [Finset.sum_insert ha,
        canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort_add,
        ih, Finset.sum_insert ha]

/-- Reflected Green-port extraction preserves finite sums of six analyzed
sources. -/
theorem canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort_finset_sum
    (M : ℕ) (z w : ℂ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {ι : Type*} (A : Finset ι)
    (f : ι → CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort M z w q hq0 hq1 S
        (∑ i ∈ A, f i) =
      ∑ i ∈ A,
        canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort M z w q hq0 hq1 S (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      simp [canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort_zero]
  | insert a A ha ih =>
      rw [Finset.sum_insert ha,
        canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort_add,
        ih, Finset.sum_insert ha]

/-! ## Camera-resolved reconstructed sources and Green ports -/

/-- The lossless mixed source reconstructed from one external camera's full
six-role TFVD analysis. -/
noncomputable def cameraResolvedSeededClockAffineSixSourceReconstruction
    (M : ℕ) (z w : ℂ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (camera : ℕ) :
    CanonicalC3AllCutoffMixedSourceHilbert :=
  canonicalC3AllCutoffMixedSourceTfvdReconstruction q hq0 hq1 S
    (cameraResolvedSeededClockAffineSixSourceCameraAnalysis M q S z w camera)

/-- The canonical reconstructed source is exactly the finite sum of the
camera-resolved reconstructed sources. -/
theorem cameraResolvedSeededClockAffineSixSourceReconstruction_sum_eq_canonical
    (M : ℕ) (z w : ℂ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∑ camera ∈ cameraResolvedSeededClockAffineSixSourceSupport M q S z w,
      cameraResolvedSeededClockAffineSixSourceReconstruction
        M z w q hqpos.le hq1 S camera =
      canonicalC3AllCutoffMixedSourceTfvdReconstruction q hqpos.le hq1 S
        (nativeC3SeededClockTfvdSixSourceAnalysis M q S z w) := by
  change (∑ camera ∈ cameraResolvedSeededClockAffineSixSourceSupport M q S z w,
      canonicalC3AllCutoffMixedSourceTfvdReconstruction q hqpos.le hq1 S
        (cameraResolvedSeededClockAffineSixSourceCameraAnalysis M q S z w camera)) = _
  rw [← canonicalC3AllCutoffMixedSourceTfvdReconstruction_finset_sum
      q hqpos.le hq1 S,
    cameraResolvedSeededClockAffineSixSourceCameraAnalysis_sum_eq_canonical]

/-- The same finite sum is literally the canonical seeded-clock three-prefix
source, by the existing lossless reconstruction theorem. -/
theorem cameraResolvedSeededClockAffineSixSourceReconstruction_sum_eq_prefix
    (M : ℕ) (z w : ℂ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∑ camera ∈ cameraResolvedSeededClockAffineSixSourceSupport M q S z w,
      cameraResolvedSeededClockAffineSixSourceReconstruction
        M z w q hqpos.le hq1 S camera =
      canonicalC3AllCutoffMixedSourcePrefixState M z w := by
  rw [cameraResolvedSeededClockAffineSixSourceReconstruction_sum_eq_canonical
      M z w q hqpos hq1 S,
    canonicalC3AllCutoffMixedSourceTfvdReconstruction_seededClockAnalysis
      M z w q hqpos hq1 S]

/-- Direct Green port retained by one external camera after lossless
reconstruction. -/
noncomputable def cameraResolvedDirectGreenPort
    (M : ℕ) (z w : ℂ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (camera : ℕ) :
    FiniteC3GreenPortCarrier (3 * M) :=
  canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort M z w q hq0 hq1 S
    (cameraResolvedSeededClockAffineSixSourceCameraAnalysis M q S z w camera)

/-- Reflected Green port retained by one external camera after lossless
reconstruction. -/
noncomputable def cameraResolvedReflectedGreenPort
    (M : ℕ) (z w : ℂ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (camera : ℕ) :
    FiniteC3GreenPortCarrier (3 * M) :=
  canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort M z w q hq0 hq1 S
    (cameraResolvedSeededClockAffineSixSourceCameraAnalysis M q S z w camera)

/-- The direct camera port is the ordinary Green-port projection of that
camera's reconstructed mixed source. -/
theorem cameraResolvedDirectGreenPort_eq_reconstruction
    (M : ℕ) (z w : ℂ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (camera : ℕ) :
    cameraResolvedDirectGreenPort M z w q hq0 hq1 S camera =
      CanonicalC3AllCutoffMixedSourceHilbert.greenPort (3 * M) w
        (cameraResolvedSeededClockAffineSixSourceReconstruction
          M z w q hq0 hq1 S camera).wSource := rfl

/-- The reflected camera port is the reflected Green-port projection of that
camera's reconstructed mixed source. -/
theorem cameraResolvedReflectedGreenPort_eq_reconstruction
    (M : ℕ) (z w : ℂ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (camera : ℕ) :
    cameraResolvedReflectedGreenPort M z w q hq0 hq1 S camera =
      CanonicalC3AllCutoffMixedSourceHilbert.greenPort (3 * M)
        (reflectedParameter z)
        (cameraResolvedSeededClockAffineSixSourceReconstruction
          M z w q hq0 hq1 S camera).reflectedZSource := rfl

/-- The canonical direct port is exactly the finite sum of reconstructed
external-camera ports; no new boundary port occurs after gradient TFVD
analysis. -/
theorem cameraResolvedDirectGreenPort_sum_eq_canonical
    (M : ℕ) (z w : ℂ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∑ camera ∈ cameraResolvedSeededClockAffineSixSourceSupport M q S z w,
      cameraResolvedDirectGreenPort M z w q hqpos.le hq1 S camera =
      canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort M z w q hqpos.le hq1 S
        (nativeC3SeededClockTfvdSixSourceAnalysis M q S z w) := by
  change (∑ camera ∈ cameraResolvedSeededClockAffineSixSourceSupport M q S z w,
      canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort M z w q hqpos.le hq1 S
        (cameraResolvedSeededClockAffineSixSourceCameraAnalysis M q S z w camera)) = _
  rw [← canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort_finset_sum,
    cameraResolvedSeededClockAffineSixSourceCameraAnalysis_sum_eq_canonical]

/-- The canonical reflected port is exactly the finite sum of reconstructed
external-camera ports; no new boundary port occurs after gradient TFVD
analysis. -/
theorem cameraResolvedReflectedGreenPort_sum_eq_canonical
    (M : ℕ) (z w : ℂ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∑ camera ∈ cameraResolvedSeededClockAffineSixSourceSupport M q S z w,
      cameraResolvedReflectedGreenPort M z w q hqpos.le hq1 S camera =
      canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort M z w q hqpos.le hq1 S
        (nativeC3SeededClockTfvdSixSourceAnalysis M q S z w) := by
  change (∑ camera ∈ cameraResolvedSeededClockAffineSixSourceSupport M q S z w,
      canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort M z w q hqpos.le hq1 S
        (cameraResolvedSeededClockAffineSixSourceCameraAnalysis M q S z w camera)) = _
  rw [← canonicalC3AllCutoffMixedSourceTfvdReflectedGreenPort_finset_sum,
    cameraResolvedSeededClockAffineSixSourceCameraAnalysis_sum_eq_canonical]

/-! ## The pairwise corrected Green boundary -/

/-- One camera-pair contribution to the corrected Green boundary.  The two
external labels remain independent; no diagonal reduction is built into this
definition. -/
noncomputable def canonicalC3CameraResolvedCorrectedGreenKernel
    (M : ℕ) (z w : ℂ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (directCamera reflectedCamera : ℕ) : ℂ :=
  greenForm (𝕜 := ℂ)
    (cameraResolvedDirectGreenPort M z w q hq0 hq1 S directCamera)
    (cameraResolvedReflectedGreenPort M z w q hq0 hq1 S reflectedCamera)

/-- The corrected six-source Green boundary is precisely the double finite
sum of its camera-pair kernels.  In particular, cross-camera terms are kept
as terms of the theorem rather than discarded by a diagonal convention. -/
theorem canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary_eq_cameraPairwise
    (M : ℕ) (z w : ℂ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary M z w q hqpos.le hq1 S
        (nativeC3SeededClockTfvdSixSourceAnalysis M q S z w) =
      ∑ directCamera ∈ cameraResolvedSeededClockAffineSixSourceSupport M q S z w,
        ∑ reflectedCamera ∈ cameraResolvedSeededClockAffineSixSourceSupport M q S z w,
          canonicalC3CameraResolvedCorrectedGreenKernel M z w q hqpos.le hq1 S
            directCamera reflectedCamera := by
  unfold canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary
  rw [← cameraResolvedDirectGreenPort_sum_eq_canonical M z w q hqpos hq1 S,
    ← cameraResolvedReflectedGreenPort_sum_eq_canonical M z w q hqpos hq1 S]
  exact greenForm_finset_sum_pairwise
    (cameraResolvedSeededClockAffineSixSourceSupport M q S z w)
    (cameraResolvedSeededClockAffineSixSourceSupport M q S z w)
    (cameraResolvedDirectGreenPort M z w q hqpos.le hq1 S)
    (cameraResolvedReflectedGreenPort M z w q hqpos.le hq1 S)

/-- The same pairwise formula written with the individual camera kernel
expanded at each summand. -/
theorem canonicalC3CameraResolvedCorrectedGreenKernel_sum_eq_correctedBoundary
    (M : ℕ) (z w : ℂ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (∑ directCamera ∈ cameraResolvedSeededClockAffineSixSourceSupport M q S z w,
      ∑ reflectedCamera ∈ cameraResolvedSeededClockAffineSixSourceSupport M q S z w,
        canonicalC3CameraResolvedCorrectedGreenKernel M z w q hqpos.le hq1 S
          directCamera reflectedCamera) =
      canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary M z w q hqpos.le hq1 S
        (nativeC3SeededClockTfvdSixSourceAnalysis M q S z w) :=
  (canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary_eq_cameraPairwise
    M z w q hqpos hq1 S).symm

end

end CarrySelfAdjointOperator
