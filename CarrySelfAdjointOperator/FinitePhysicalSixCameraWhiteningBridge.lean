import CarrySelfAdjointOperator.CompletedNativeMultibaseCollectiveReadout
import CarrySelfAdjointOperator.FiniteNativeDepthRawCameraGram
import CarrySelfAdjointOperator.NativeLogEvolution
import NativeCarrySpectralWeyl.Camera.BracketProfileBridge
import Mathlib.Tactic

/-!
# Finite physical six-camera whitening bridge

This module records the part of the finite laboratory realization that is
already represented by the checked library, and keeps distinct the one seam
that is not yet present.

* `finiteCameraMatrix` is the literal complex finite camera matrix;
* `finiteRealSpectralStateVector` is the finite logarithmic orbit with
  critical seed amplitude;
* a left-invertible whitening preserves the kernel of every raw readout;
* the completed native camera characteristic is not the raw finite head: it
  is that head plus its exact whole-center analytic tail.

Consequently, whitening is not the obstruction to comparing a finite
laboratory readout with the canonical completed characteristic.  The missing
comparison is the *additive completion* of the finite orbit readout.  This is
why a nonvanishing scalar gauge alone cannot identify the two finite objects.

No height operator, Jacobi operator, Weyl theorem, positivity certificate, or
limit assertion is constructed here.
-/

open scoped BigOperators Matrix

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Camera.FiniteBridge
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Limits

noncomputable section

/-- Pure linear algebra for Gate A.  Any whitening with a specified left
inverse preserves the zero locus of a camera readout.  This intentionally
does not assume that the entries are real, positive, or obtained from an
inverse square root; those are ways to supply the displayed left inverse. -/
theorem whitened_mulVec_eq_zero_iff_raw_mulVec_eq_zero_of_leftInverse
    {𝕜 output state : Type*} [Field 𝕜]
    [Fintype output] [DecidableEq output] [Fintype state]
    (whitening whiteningInv : Matrix output output 𝕜)
    (raw : Matrix output state 𝕜) (x : state → 𝕜)
    (hleft : whiteningInv * whitening = 1) :
    whitening *ᵥ (raw *ᵥ x) = 0 ↔ raw *ᵥ x = 0 := by
  constructor
  · intro hzero
    have htransport := congrArg (fun y : output → 𝕜 => whiteningInv *ᵥ y) hzero
    rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec,
      Matrix.mulVec_zero] at htransport
    exact htransport
  · intro hzero
    simp [hzero]

/-- The repository's canonical real inverse-square-root whitening supplies
the preceding Gate A hypothesis whenever the finite row Gram is positive
definite.  This is the literal finite statement
`(C Cᵀ)⁻¹/² C x = 0 ↔ C x = 0`; it is independent of the time orbit. -/
theorem finiteCanonicalCameraReadout_mulVec_eq_zero_iff_raw_mulVec_eq_zero
    {camera state : Type*}
    [Fintype camera] [DecidableEq camera] [Fintype state]
    (C : Matrix camera state ℝ)
    (hG : (finiteCameraRowGram C).PosDef) (x : state → ℝ) :
    finiteCanonicalCameraReadout C *ᵥ x = 0 ↔ C *ᵥ x = 0 := by
  rw [finiteCanonicalCameraReadout, ← Matrix.mulVec_mulVec]
  letI := (positiveInverseSqrt_posDef hG).isUnit.invertible
  exact whitened_mulVec_eq_zero_iff_raw_mulVec_eq_zero_of_leftInverse
    (positiveInverseSqrt (finiteCameraRowGram C))
    (positiveInverseSqrt (finiteCameraRowGram C))⁻¹ C x
    (Matrix.inv_mul_of_invertible _)

/-- The literal raw finite camera readout along the already formalized
logarithmic orbit.  This is the direct matrix expression underlying the
laboratory notation `C_N e^{-it L_N} alpha_N`: the state vector is the
unnormalized critical seed orbit, which has the same kernel after multiplication
by any nonzero scalar normalization. -/
def finiteCameraPhysicalRawReadout
    {index : Type*} [Fintype index]
    (cutoff : ℕ) (camera : index → ℕ) (time : ℝ) : index → ℂ :=
  finiteCameraMatrix cutoff camera *ᵥ
    fun n => finiteRealSpectralStateVector
      (finiteFamilyWindow cutoff camera) time n

/-- A physical whitened readout relative to an explicitly supplied complex
whitening matrix.  The repository contains finite Gram and inverse-square-root
objects, but does not presently prove positive definiteness of the literal
finite six-camera row Gram at every cutoff.  Keeping the whitening explicit
therefore records exactly the algebra needed without claiming that missing
finite hypothesis. -/
def finiteCameraPhysicalWhitenedReadout
    {index : Type*} [Fintype index]
    (whitening : Matrix index index ℂ)
    (cutoff : ℕ) (camera : index → ℕ) (time : ℝ) : index → ℂ :=
  whitening *ᵥ finiteCameraPhysicalRawReadout cutoff camera time

/-- Rescaling the physical critical seed by a nonzero complex normalization
does not alter collective blindness.  This is the algebraic bridge from the
unnormalized finite orbit `alpha_N` represented by
`finiteRealSpectralStateVector` to a future unit-normalized `j_N`. -/
theorem smul_finiteCameraPhysicalRawReadout_eq_zero_iff
    {index : Type*} [Fintype index]
    (normalization : ℂ) (hnormalization : normalization ≠ 0)
    (cutoff : ℕ) (camera : index → ℕ) (time : ℝ) :
    normalization • finiteCameraPhysicalRawReadout cutoff camera time = 0 ↔
      finiteCameraPhysicalRawReadout cutoff camera time = 0 := by
  constructor
  · intro hzero
    funext i
    have hcoordinate := congrFun hzero i
    change normalization * finiteCameraPhysicalRawReadout cutoff camera time i = 0 at hcoordinate
    exact (mul_eq_zero.mp hcoordinate).resolve_left hnormalization
  · intro hzero
    simp [hzero]

/-- Gate A specialized to the physical finite orbit: a left-invertible
whitening cannot create or remove collective camera blindness. -/
theorem finiteCameraPhysicalWhitenedReadout_eq_zero_iff_raw_eq_zero
    {index : Type*} [Fintype index] [DecidableEq index]
    (whitening whiteningInv : Matrix index index ℂ)
    (cutoff : ℕ) (camera : index → ℕ) (time : ℝ)
    (hleft : whiteningInv * whitening = 1) :
    finiteCameraPhysicalWhitenedReadout whitening cutoff camera time = 0 ↔
      finiteCameraPhysicalRawReadout cutoff camera time = 0 := by
  exact whitened_mulVec_eq_zero_iff_raw_mulVec_eq_zero_of_leftInverse
    whitening whiteningInv (finiteCameraMatrix cutoff camera)
    (fun n => finiteRealSpectralStateVector
      (finiteFamilyWindow cutoff camera) time n) hleft

/-- The scalar raw finite head for one camera.  This is the exact finite
stencil characteristic already used by the canonical completed ledger.  It
is deliberately named separately from the matrix expression above until the
matrix-orbit/stencil equality is supplied as a theorem. -/
def finiteCameraPhysicalRawHead
    (camera cutoff : ℕ) (time : ℝ) : ℂ :=
  finiteBracketCharacteristic camera cutoff (nativeLine time)

/-- The exact omitted whole-center contribution of a finite camera head. -/
def finiteCameraPhysicalCompletionTail
    (camera cutoff : ℕ) (time : ℝ) : ℂ :=
  ∑' index : ℕ, centerBracketTerm camera (nativeLine time) (index + cutoff)

/-- The completed camera is exactly the physical finite head plus the exact
whole-center completion tail.  This is an identity, not an estimate. -/
theorem finiteCameraPhysicalRawHead_add_completionTail_eq_completed
    (camera cutoff : ℕ) (time : ℝ) :
    finiteCameraPhysicalRawHead camera cutoff time +
        finiteCameraPhysicalCompletionTail camera cutoff time =
      completedNativeCharacteristic camera cutoff (nativeLine time) := by
  rfl

/-- At a canonical native zero, the finite physical head is exactly the
negative of the omitted whole-center tail.  Hence the raw finite head is not
entitled to vanish at a completed zero unless this additional tail cancellation
is proved. -/
theorem finiteCameraPhysicalRawHead_eq_neg_completionTail_of_nativeZero
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) (time : ℝ)
    (hzero : completedNativeOperatorCharacteristic (time : ℂ) = 0) :
    finiteCameraPhysicalRawHead camera cutoff time =
      -finiteCameraPhysicalCompletionTail camera cutoff time := by
  have hcompleted :
      completedNativeCharacteristic camera cutoff (nativeLine time) = 0 :=
    (completedNativeCharacteristic_nativeLine_eq_zero_iff hcamera cutoff time).mpr hzero
  rw [← finiteCameraPhysicalRawHead_add_completionTail_eq_completed] at hcompleted
  exact eq_neg_of_add_eq_zero_left hcompleted

/-- At a native zero, raw-head blindness is equivalent to vanishing of the
completion tail.  This is the precise remaining Gate C condition for an
uncompleted finite laboratory readout. -/
theorem finiteCameraPhysicalRawHead_eq_zero_iff_completionTail_eq_zero_of_nativeZero
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) (time : ℝ)
    (hzero : completedNativeOperatorCharacteristic (time : ℂ) = 0) :
    finiteCameraPhysicalRawHead camera cutoff time = 0 ↔
      finiteCameraPhysicalCompletionTail camera cutoff time = 0 := by
  rw [finiteCameraPhysicalRawHead_eq_neg_completionTail_of_nativeZero
    hcamera time hzero, neg_eq_zero]

/-- The raw finite six-camera head, with one common physical cutoff.  This is
the scalar-stencil candidate to which the six entries of the finite laboratory
matrix readout must still be compared. -/
def finiteSixCameraPhysicalRawHead (cutoff : ℕ) (time : ℝ) : Fin 6 → ℂ :=
  fun i => finiteCameraPhysicalRawHead (sixCamera i) cutoff time

/-- The six completion tails corresponding to one common physical cutoff. -/
def finiteSixCameraPhysicalCompletionTail (cutoff : ℕ) (time : ℝ) : Fin 6 → ℂ :=
  fun i => finiteCameraPhysicalCompletionTail (sixCamera i) cutoff time

/-- The componentwise six-camera completion ledger. -/
theorem finiteSixCameraPhysicalRawHead_add_completionTail_eq_completed
    (cutoff : ℕ) (time : ℝ) :
    finiteSixCameraPhysicalRawHead cutoff time +
        finiteSixCameraPhysicalCompletionTail cutoff time =
      fun i => completedNativeCharacteristic (sixCamera i) cutoff (nativeLine time) := by
  funext i
  exact finiteCameraPhysicalRawHead_add_completionTail_eq_completed
    (sixCamera i) cutoff time

/-- At a canonical zero, every raw six-camera coordinate is the negative of
its exact completion tail.  The theorem makes the finite/completed seam
visible at vector level without assuming a false raw-to-completed equality. -/
theorem finiteSixCameraPhysicalRawHead_eq_neg_completionTail_of_nativeZero
    (cutoff : ℕ) (time : ℝ)
    (hzero : completedNativeOperatorCharacteristic (time : ℂ) = 0) :
    finiteSixCameraPhysicalRawHead cutoff time =
      -finiteSixCameraPhysicalCompletionTail cutoff time := by
  funext i
  exact finiteCameraPhysicalRawHead_eq_neg_completionTail_of_nativeZero
    (two_le_sixCamera i) time hzero

/-- The raw finite six-camera head is collectively blind at a canonical zero
exactly when its omitted whole-center tails vanish collectively. -/
theorem finiteSixCameraPhysicalRawHead_eq_zero_iff_completionTail_eq_zero_of_nativeZero
    (cutoff : ℕ) (time : ℝ)
    (hzero : completedNativeOperatorCharacteristic (time : ℂ) = 0) :
    finiteSixCameraPhysicalRawHead cutoff time = 0 ↔
      finiteSixCameraPhysicalCompletionTail cutoff time = 0 := by
  rw [finiteSixCameraPhysicalRawHead_eq_neg_completionTail_of_nativeZero
    cutoff time hzero, neg_eq_zero]

end

end CarrySelfAdjointOperator
