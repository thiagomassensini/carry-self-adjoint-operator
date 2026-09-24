import CarrySelfAdjointOperator.CompletedNativeMultibaseCollectiveReadout
import CarrySelfAdjointOperator.FiniteNativeDepthRawCameraGram
import CarrySelfAdjointOperator.NativeLogEvolution
import NativeCarrySpectralWeyl.Camera.BracketProfileBridge
import Mathlib.Tactic

/-!
# Finite physical six-camera whitening bridge

This module records the checked finite laboratory realization and its exact
additive completion ledger.

* `finiteCameraMatrix` is the literal complex finite camera matrix;
* `finiteRealSpectralStateVector` is the finite logarithmic orbit with
  critical seed amplitude;
* a left-invertible whitening preserves the kernel of every raw readout;
* the completed native camera characteristic is not the raw finite head: it
  is that head plus its exact whole-center analytic tail; and
* for the historical six-camera package, that tail is added before the
  zero-equivalent completed readout and optional whitening handoff.

Consequently, whitening is not the obstruction to comparing a finite
laboratory readout with the canonical completed characteristic.  The required
comparison is the *additive completion* of the finite orbit readout, now
implemented for the six-camera package.  A nonvanishing scalar gauge alone
would not identify the two finite objects.

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
is deliberately named separately from the matrix expression above; their
exact equality is supplied below by the matrix--stencil theorem. -/
def finiteCameraPhysicalRawHead
    (camera cutoff : ℕ) (time : ℝ) : ℂ :=
  finiteBracketCharacteristic camera cutoff (nativeLine time)

/-- The finite real-spectral coordinate is the positive-index Dirichlet
sample on the native line.  This is the coordinate-level identification used
to expand the literal matrix readout into the finite bracket stencil. -/
theorem realSpectralState_eq_dirichletValue_nativeLine
    (time : ℝ) (n : ℕ) :
    realSpectralState time n =
      dirichletValue (nativeLine time) (n + 1) := by
  unfold realSpectralState positiveDirichletValue dirichletValue
  congr 2
  apply Complex.ext <;>
    simp [nativeLine, criticalLineParameter]

private theorem dirichletValue_nativeLine_zero (time : ℝ) :
    dirichletValue (nativeLine time) 0 = 0 := by
  unfold dirichletValue
  have hnonzero : -nativeLine time ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp [nativeLine] at hre
  simpa only [Nat.cast_zero] using Complex.zero_cpow hnonzero

private theorem sum_range_succ_shift_eq_sum_range
    (f : ℕ → ℂ) (hzero : f 0 = 0) (length : ℕ) :
    (∑ n ∈ Finset.range length, f (n + 1)) =
      ∑ n ∈ Finset.range (length + 1), f n := by
  induction length with
  | zero => simp [hzero]
  | succ length ih =>
      calc
        (∑ n ∈ Finset.range (Nat.succ length), f (n + 1)) =
            (∑ n ∈ Finset.range length, f (n + 1)) + f (length + 1) := by
              rw [Finset.sum_range_succ]
        _ = (∑ n ∈ Finset.range (length + 1), f n) + f (length + 1) := by
              rw [ih]
        _ = ∑ n ∈ Finset.range (Nat.succ length + 1), f n := by
              simpa [Nat.succ_eq_add_one] using
                (Finset.sum_range_succ f (length + 1)).symm

/-- Finite stencil evaluation written as a sum over any camera-complete
positive coordinate window.  This is the scalar matrix--stencil expansion;
the common family window used by `finiteCameraMatrix` is such a window. -/
theorem finiteBracketCharacteristic_nativeLine_eq_sum_finiteCoefficientAt
    {camera cutoff length : ℕ} (hcamera : 2 ≤ camera)
    (hlength : finiteCameraWindow camera cutoff ≤ length) (time : ℝ) :
    finiteBracketCharacteristic camera cutoff (nativeLine time) =
      ∑ n ∈ Finset.range length,
        (finiteCoefficientAt camera cutoff n : ℂ) * realSpectralState time n := by
  rw [← evalDirichletStencil_finiteStencil]
  unfold evalDirichletStencil
  rw [Finsupp.linearCombination_apply]
  let f : ℕ → ℂ := fun n =>
    (finiteCoefficient camera cutoff n : ℂ) * dirichletValue (nativeLine time) n
  have hsupport : (finiteStencil camera cutoff).support ⊆
      Finset.range (length + 1) := by
    intro n hn
    by_contra hnotmem
    have hnle : length + 1 ≤ n := by
      exact Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hnotmem)
    have hwindow : finiteCameraWindow camera cutoff < n := by omega
    have hcoefficient : finiteCoefficient camera cutoff n = 0 :=
      finiteCoefficient_eq_zero_above_complete_horizon hcamera hwindow
    have hstencil : finiteStencil camera cutoff n = 0 := by
      rw [finiteStencil_apply, hcoefficient]
    exact (Finsupp.mem_support_iff.mp hn) hstencil
  rw [Finsupp.sum_of_support_subset (finiteStencil camera cutoff) hsupport
    (fun i coefficient => coefficient • dirichletValue (nativeLine time) i)
    (by intro i hi; simp)]
  have hsum :
      (∑ n ∈ Finset.range (length + 1), f n) =
        ∑ n ∈ Finset.range length, f (n + 1) := by
    symm
    apply sum_range_succ_shift_eq_sum_range
    simp [f, dirichletValue_nativeLine_zero]
  rw [show (∑ x ∈ Finset.range (length + 1),
      (finiteStencil camera cutoff x) • dirichletValue (nativeLine time) x) =
      ∑ x ∈ Finset.range (length + 1), f x by
        apply Finset.sum_congr rfl
        intro x hx
        simp only [f, finiteStencil_apply, zsmul_eq_mul]
    , hsum]
  apply Finset.sum_congr rfl
  intro n hn
  change (finiteCoefficient camera cutoff (n + 1) : ℂ) *
      dirichletValue (nativeLine time) (n + 1) =
    (finiteCoefficient camera cutoff (n + 1) : ℂ) * realSpectralState time n
  rw [realSpectralState_eq_dirichletValue_nativeLine]

/-- Gate A's missing matrix--stencil identity.  The literal finite camera
matrix applied to the finite logarithmic orbit has, in every camera slot, the
finite bracket head for that camera.  No completion tail is used here. -/
theorem finiteCameraPhysicalRawReadout_apply_eq_finiteBracketCharacteristic
    {index : Type*} [Fintype index]
    (cutoff : ℕ) (camera : index → ℕ) (time : ℝ) (i : index)
    (hcamera : 2 ≤ camera i) :
    finiteCameraPhysicalRawReadout cutoff camera time i =
      finiteCameraPhysicalRawHead (camera i) cutoff time := by
  unfold finiteCameraPhysicalRawReadout finiteCameraPhysicalRawHead
  simp only [Matrix.mulVec, dotProduct, finiteCameraMatrix,
    finiteRealSpectralStateVector_apply]
  let length := finiteFamilyWindow cutoff camera
  change (∑ x : Fin length,
      (finiteCoefficientAt (camera i) cutoff x.val : ℂ) *
        realSpectralState time x.val) =
      finiteBracketCharacteristic (camera i) cutoff (nativeLine time)
  calc
    (∑ x : Fin length,
        (finiteCoefficientAt (camera i) cutoff x.val : ℂ) *
          realSpectralState time x.val) =
        ∑ n ∈ Finset.range length,
          (finiteCoefficientAt (camera i) cutoff n : ℂ) * realSpectralState time n :=
      by
        simpa only using (Fin.sum_univ_eq_sum_range
          (fun n : ℕ =>
            (finiteCoefficientAt (camera i) cutoff n : ℂ) *
              realSpectralState time n) length)
    _ = finiteBracketCharacteristic (camera i) cutoff (nativeLine time) :=
      (finiteBracketCharacteristic_nativeLine_eq_sum_finiteCoefficientAt
        hcamera (finiteCameraWindow_le_finiteFamilyWindow cutoff camera i) time).symm

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

/-- The literal matrix readout for the six historical cameras. -/
def finiteSixCameraPhysicalRawReadout (cutoff : ℕ) (time : ℝ) : Fin 6 → ℂ :=
  finiteCameraPhysicalRawReadout cutoff sixCamera time

/-- The finite matrix calculation is exactly the vector of finite bracket
heads, coordinate by coordinate. -/
theorem finiteSixCameraPhysicalRawReadout_eq_rawHead
    (cutoff : ℕ) (time : ℝ) :
    finiteSixCameraPhysicalRawReadout cutoff time =
      finiteSixCameraPhysicalRawHead cutoff time := by
  funext i
  exact finiteCameraPhysicalRawReadout_apply_eq_finiteBracketCharacteristic
    cutoff sixCamera time i (two_le_sixCamera i)

/-- The unnormalized completed camera vector, before removing the individual
nonvanishing camera factors.  It is the literal target of `raw head + tail`. -/
def finiteSixCameraCompletedNativeReadout
    (cutoff : ℕ) (time : ℝ) : Fin 6 → ℂ :=
  fun i => completedNativeCharacteristic (sixCamera i) cutoff (nativeLine time)

/-- The finite physical readout corrected by the already-existing whole-center
tail.  This is the finite object that corresponds to the completed camera
ledger; it is not the raw truncated matrix readout. -/
def finiteSixCameraCompletedPhysicalReadout
    (cutoff : ℕ) (time : ℝ) : Fin 6 → ℂ :=
  finiteSixCameraPhysicalRawReadout cutoff time +
    finiteSixCameraPhysicalCompletionTail cutoff time

/-- Gate B/C: the literal finite matrix readout plus the literal whole-center
tail is exactly the unnormalized completed six-camera vector. -/
theorem finiteSixCameraCompletedPhysicalReadout_eq_completedNativeReadout
    (cutoff : ℕ) (time : ℝ) :
    finiteSixCameraCompletedPhysicalReadout cutoff time =
      finiteSixCameraCompletedNativeReadout cutoff time := by
  rw [finiteSixCameraCompletedPhysicalReadout,
    finiteSixCameraPhysicalRawReadout_eq_rawHead,
    finiteSixCameraPhysicalRawHead_add_completionTail_eq_completed]
  rfl

/-- The completed physical six-camera vector is exactly independent of the
geometric cutoff.  Each cutoff changes the raw finite head and the omitted
whole-center tail, but their physical sum is the same six-coordinate
completed characteristic.  This is an exact stabilization statement, not a
limit assertion. -/
theorem finiteSixCameraCompletedPhysicalReadout_cutoff_independent
    (cutoff₁ cutoff₂ : ℕ) (time : ℝ) :
    finiteSixCameraCompletedPhysicalReadout cutoff₁ time =
      finiteSixCameraCompletedPhysicalReadout cutoff₂ time := by
  rw [finiteSixCameraCompletedPhysicalReadout_eq_completedNativeReadout,
    finiteSixCameraCompletedPhysicalReadout_eq_completedNativeReadout]
  funext i
  apply completedNativeCharacteristic_cutoff_independent (two_le_sixCamera i)
  simp [nativeScalarDomain]
  norm_num

/-- Coordinate form of exact cutoff compensation.  Raising the cutoff moves
precisely the increment of the finite head out of the completion tail, with
opposite sign. -/
theorem finiteCameraPhysicalRawHead_sub_eq_completionTail_sub
    (camera cutoff₁ cutoff₂ : ℕ) (time : ℝ) (hcamera : 2 ≤ camera) :
    finiteCameraPhysicalRawHead camera cutoff₂ time -
        finiteCameraPhysicalRawHead camera cutoff₁ time =
      finiteCameraPhysicalCompletionTail camera cutoff₁ time -
        finiteCameraPhysicalCompletionTail camera cutoff₂ time := by
  have hsum :
      finiteCameraPhysicalRawHead camera cutoff₁ time +
          finiteCameraPhysicalCompletionTail camera cutoff₁ time =
        finiteCameraPhysicalRawHead camera cutoff₂ time +
          finiteCameraPhysicalCompletionTail camera cutoff₂ time := by
    rw [finiteCameraPhysicalRawHead_add_completionTail_eq_completed,
      finiteCameraPhysicalRawHead_add_completionTail_eq_completed]
    apply completedNativeCharacteristic_cutoff_independent hcamera
    simp [nativeScalarDomain]
    norm_num
  calc
    finiteCameraPhysicalRawHead camera cutoff₂ time -
        finiteCameraPhysicalRawHead camera cutoff₁ time =
      (finiteCameraPhysicalRawHead camera cutoff₂ time +
          finiteCameraPhysicalCompletionTail camera cutoff₂ time) -
        (finiteCameraPhysicalRawHead camera cutoff₁ time +
          finiteCameraPhysicalCompletionTail camera cutoff₁ time) +
        (finiteCameraPhysicalCompletionTail camera cutoff₁ time -
          finiteCameraPhysicalCompletionTail camera cutoff₂ time) := by ring
    _ = finiteCameraPhysicalCompletionTail camera cutoff₁ time -
          finiteCameraPhysicalCompletionTail camera cutoff₂ time := by
      rw [hsum]
      ring

/-- The scalar completed ledger is exactly cutoff-independent for every
supported camera.  This is the coordinatewise fact from which the same
statement for any finite supported family follows by extensionality; no new
family-level physical structure is needed. -/
theorem finiteCameraPhysicalRawHead_add_completionTail_cutoff_independent
    (camera cutoff₁ cutoff₂ : ℕ) (time : ℝ) (hcamera : 2 ≤ camera) :
    finiteCameraPhysicalRawHead camera cutoff₁ time +
        finiteCameraPhysicalCompletionTail camera cutoff₁ time =
      finiteCameraPhysicalRawHead camera cutoff₂ time +
        finiteCameraPhysicalCompletionTail camera cutoff₂ time := by
  rw [finiteCameraPhysicalRawHead_add_completionTail_eq_completed,
    finiteCameraPhysicalRawHead_add_completionTail_eq_completed]
  apply completedNativeCharacteristic_cutoff_independent hcamera
  simp [nativeScalarDomain]
  norm_num

/-- Vector form of exact cutoff compensation for the historical six cameras.
The finite head changes with the cutoff, but its increment is exactly the
negative increment of the tail. -/
theorem finiteSixCameraPhysicalRawHead_sub_eq_completionTail_sub
    (cutoff₁ cutoff₂ : ℕ) (time : ℝ) :
    finiteSixCameraPhysicalRawHead cutoff₂ time -
        finiteSixCameraPhysicalRawHead cutoff₁ time =
      finiteSixCameraPhysicalCompletionTail cutoff₁ time -
        finiteSixCameraPhysicalCompletionTail cutoff₂ time := by
  funext i
  exact finiteCameraPhysicalRawHead_sub_eq_completionTail_sub
    (sixCamera i) cutoff₁ cutoff₂ time (two_le_sixCamera i)

/-- A cutoff-free name for the completed physical six-camera readout.  The
seed-only cutoff `0` is used solely as a canonical representative; exact
cutoff independence below proves that this choice carries no physical
content.  This is not a topological `N → ∞` construction. -/
def canonicalCompletedSixCameraPhysicalReadout (time : ℝ) : Fin 6 → ℂ :=
  finiteSixCameraCompletedPhysicalReadout 0 time

/-- Every finite head-plus-tail presentation is literally the canonical
cutoff-free completed physical six-camera readout. -/
theorem finiteSixCameraCompletedPhysicalReadout_eq_canonical
    (cutoff : ℕ) (time : ℝ) :
    finiteSixCameraCompletedPhysicalReadout cutoff time =
      canonicalCompletedSixCameraPhysicalReadout time :=
  finiteSixCameraCompletedPhysicalReadout_cutoff_independent cutoff 0 time

/-- The unnormalized completed six-camera vector has the canonical completed
native zero locus.  Individual factor normalizations are not needed for this
zero-set statement. -/
theorem finiteSixCameraCompletedNativeReadout_eq_zero_iff_nativeZero
    (cutoff : ℕ) (time : ℝ) :
    finiteSixCameraCompletedNativeReadout cutoff time = 0 ↔
      completedNativeOperatorCharacteristic (time : ℂ) = 0 := by
  constructor
  · intro hzero
    have hcoordinate := congrFun hzero (0 : Fin 6)
    change completedNativeCharacteristic (sixCamera (0 : Fin 6)) cutoff
      (nativeLine time) = 0 at hcoordinate
    exact (completedNativeCharacteristic_nativeLine_eq_zero_iff
      (two_le_sixCamera (0 : Fin 6)) cutoff time).mp hcoordinate
  · intro hzero
    funext i
    change completedNativeCharacteristic (sixCamera i) cutoff (nativeLine time) = 0
    exact (completedNativeCharacteristic_nativeLine_eq_zero_iff
      (two_le_sixCamera i) cutoff time).mpr hzero

/-- Gate C: completed physical collective blindness is equivalent to the
canonical native characteristic zero condition. -/
theorem finiteSixCameraCompletedPhysicalReadout_eq_zero_iff_nativeZero
    (cutoff : ℕ) (time : ℝ) :
    finiteSixCameraCompletedPhysicalReadout cutoff time = 0 ↔
      completedNativeOperatorCharacteristic (time : ℂ) = 0 := by
  rw [finiteSixCameraCompletedPhysicalReadout_eq_completedNativeReadout,
    finiteSixCameraCompletedNativeReadout_eq_zero_iff_nativeZero]

/-- The completed physical vector and the previously formalized normalized
completed six-camera collective readout are zero-equivalent.  They are not
claimed equal: each coordinate of the latter has removed a nonvanishing
camera factor and retained the common completion factor. -/
theorem finiteSixCameraCompletedPhysicalReadout_eq_zero_iff_collectiveReadout_eq_zero
    (cutoff : ℕ) (time : ℝ) :
    finiteSixCameraCompletedPhysicalReadout cutoff time = 0 ↔
      completedNativeSixCameraCollectiveReadout (fun _ => cutoff) time = 0 := by
  rw [finiteSixCameraCompletedPhysicalReadout_eq_zero_iff_nativeZero,
    completedNativeSixCameraCollectiveReadout_eq_zero_iff_nativeZero]

/-- The completed physical six-camera vector is a direct handoff to the
pre-existing zero-equivalent height-spectrum bridge. -/
theorem finiteSixCameraCompletedPhysicalReadout_isZeroEquivalent
    (cutoff : ℕ) :
    IsZeroEquivalentCompletedNativeHeightReadout
      (finiteSixCameraCompletedPhysicalReadout cutoff) :=
  fun time => finiteSixCameraCompletedPhysicalReadout_eq_zero_iff_nativeZero cutoff time

/-- The stabilized physical six-camera vector has the canonical completed
native zero locus.  It is a representative of the exact cutoff-independent
head-plus-tail object, not the normalized collective readout. -/
theorem canonicalCompletedSixCameraPhysicalReadout_eq_zero_iff_nativeZero
    (time : ℝ) :
    canonicalCompletedSixCameraPhysicalReadout time = 0 ↔
      completedNativeOperatorCharacteristic (time : ℂ) = 0 := by
  exact finiteSixCameraCompletedPhysicalReadout_eq_zero_iff_nativeZero 0 time

/-- The exact cutoff-free physical readout is ready for the existing
zero-equivalent height-spectrum bridge. -/
theorem canonicalCompletedSixCameraPhysicalReadout_isZeroEquivalent :
    IsZeroEquivalentCompletedNativeHeightReadout
      canonicalCompletedSixCameraPhysicalReadout :=
  fun time => canonicalCompletedSixCameraPhysicalReadout_eq_zero_iff_nativeZero time

/-- Whiten the *completed* physical vector by a supplied complex matrix.  The
matrix is kept explicit: proving that it is the inverse square root of the
literal finite Gram is a separate finite-Gram theorem. -/
def finiteSixCameraCompletedPhysicalWhitenedReadout
    (whitening : Matrix (Fin 6) (Fin 6) ℂ)
    (cutoff : ℕ) (time : ℝ) : Fin 6 → ℂ :=
  whitening *ᵥ finiteSixCameraCompletedPhysicalReadout cutoff time

/-- Gate D, first half: left-invertible whitening preserves the completed
physical collective-blindness condition. -/
theorem finiteSixCameraCompletedPhysicalWhitenedReadout_eq_zero_iff_completed_eq_zero
    (whitening whiteningInv : Matrix (Fin 6) (Fin 6) ℂ)
    (cutoff : ℕ) (time : ℝ)
    (hleft : whiteningInv * whitening = 1) :
    finiteSixCameraCompletedPhysicalWhitenedReadout whitening cutoff time = 0 ↔
      finiteSixCameraCompletedPhysicalReadout cutoff time = 0 := by
  constructor
  · intro hzero
    have htransport := congrArg
      (fun y : Fin 6 → ℂ => whiteningInv *ᵥ y) hzero
    rw [finiteSixCameraCompletedPhysicalWhitenedReadout,
      Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec,
      Matrix.mulVec_zero] at htransport
    exact htransport
  · intro hzero
    simp [finiteSixCameraCompletedPhysicalWhitenedReadout, hzero]

/-- Gate D, completed form: a left-invertibly whitened completed physical
readout has exactly the canonical native zero locus. -/
theorem finiteSixCameraCompletedPhysicalWhitenedReadout_eq_zero_iff_nativeZero
    (whitening whiteningInv : Matrix (Fin 6) (Fin 6) ℂ)
    (cutoff : ℕ) (time : ℝ)
    (hleft : whiteningInv * whitening = 1) :
    finiteSixCameraCompletedPhysicalWhitenedReadout whitening cutoff time = 0 ↔
      completedNativeOperatorCharacteristic (time : ℂ) = 0 := by
  rw [finiteSixCameraCompletedPhysicalWhitenedReadout_eq_zero_iff_completed_eq_zero
    whitening whiteningInv cutoff time hleft,
    finiteSixCameraCompletedPhysicalReadout_eq_zero_iff_nativeZero]

/-- A cutoff-dependent whitening does not need to have cutoff-independent
values.  With its own left inverse, however, its zero locus is exactly that
of the one stabilized unwhitened physical vector. -/
theorem finiteSixCameraCompletedPhysicalWhitenedReadout_eq_zero_iff_canonical_eq_zero
    (whitening whiteningInv : Matrix (Fin 6) (Fin 6) ℂ)
    (cutoff : ℕ) (time : ℝ)
    (hleft : whiteningInv * whitening = 1) :
    finiteSixCameraCompletedPhysicalWhitenedReadout whitening cutoff time = 0 ↔
      canonicalCompletedSixCameraPhysicalReadout time = 0 := by
  rw [finiteSixCameraCompletedPhysicalWhitenedReadout_eq_zero_iff_completed_eq_zero
    whitening whiteningInv cutoff time hleft,
    finiteSixCameraCompletedPhysicalReadout_eq_canonical]

/-- Zero-equivalent spectral handoff for a left-invertibly whitened completed
physical six-camera readout. -/
theorem finiteSixCameraCompletedPhysicalWhitenedReadout_isZeroEquivalent
    (whitening whiteningInv : Matrix (Fin 6) (Fin 6) ℂ)
    (cutoff : ℕ) (hleft : whiteningInv * whitening = 1) :
    IsZeroEquivalentCompletedNativeHeightReadout
      (finiteSixCameraCompletedPhysicalWhitenedReadout whitening cutoff) :=
  fun time => finiteSixCameraCompletedPhysicalWhitenedReadout_eq_zero_iff_nativeZero
    whitening whiteningInv cutoff time hleft

namespace CompletedNativeRealHPCarrierCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {jet : (ℕ ⊕ ℕ) → E}

/-- Completed physical six-camera blindness feeds the already-built signed
height operator without constructing any spectral object anew. -/
theorem finiteSixCameraCompletedPhysicalReadout_zero_hasSignedHeightEigenvalue
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (cutoff : ℕ) {time : ℝ}
    (hzero : finiteSixCameraCompletedPhysicalReadout cutoff time = 0) :
    LinearPMap.HasEigenvalue
      certificate.toReducedMaximalSelfAdjointHeightData.selfAdjointData.complexification
      (time : ℂ) := by
  exact certificate.zeroEquivalentReadout_zero_hasSignedHeightEigenvalue
    (finiteSixCameraCompletedPhysicalReadout_isZeroEquivalent cutoff) hzero

/-- At nonzero height, completed physical six-camera blindness is exactly the
existing reciprocal-square Jacobi point-eigenvalue condition. -/
theorem finiteSixCameraCompletedPhysicalReadout_zero_iff_jacobiEigenvalue_inv_sq
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (cutoff : ℕ) {time : ℝ} (htime : time ≠ 0) :
    finiteSixCameraCompletedPhysicalReadout cutoff time = 0 ↔
      LinearPMap.HasEigenvalue
        certificate.completedJacobiEnergySelfAdjointData.complexification
        ((time : ℂ) ^ 2)⁻¹ := by
  exact certificate.zeroEquivalentReadout_zero_iff_jacobiEigenvalue_inv_sq
    (finiteSixCameraCompletedPhysicalReadout_isZeroEquivalent cutoff) htime

/-- Blindness of the exactly stabilized physical six-camera readout is an
eigenvalue of the pre-existing signed-height operator.  No limit or new
spectral construction occurs in this corollary. -/
theorem canonicalCompletedSixCameraPhysicalReadout_zero_hasSignedHeightEigenvalue
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {time : ℝ}
    (hzero : canonicalCompletedSixCameraPhysicalReadout time = 0) :
    LinearPMap.HasEigenvalue
      certificate.toReducedMaximalSelfAdjointHeightData.selfAdjointData.complexification
      (time : ℂ) := by
  exact certificate.zeroEquivalentReadout_zero_hasSignedHeightEigenvalue
    canonicalCompletedSixCameraPhysicalReadout_isZeroEquivalent hzero

/-- Away from zero height, stabilized physical six-camera blindness is
exactly the existing reciprocal-square Jacobi point-eigenvalue condition. -/
theorem canonicalCompletedSixCameraPhysicalReadout_zero_iff_jacobiEigenvalue_inv_sq
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {time : ℝ} (htime : time ≠ 0) :
    canonicalCompletedSixCameraPhysicalReadout time = 0 ↔
      LinearPMap.HasEigenvalue
        certificate.completedJacobiEnergySelfAdjointData.complexification
        ((time : ℂ) ^ 2)⁻¹ := by
  exact certificate.zeroEquivalentReadout_zero_iff_jacobiEigenvalue_inv_sq
    canonicalCompletedSixCameraPhysicalReadout_isZeroEquivalent htime

/-- Signed-height corollary after any left-invertible whitening of the
completed physical six-camera vector. -/
theorem finiteSixCameraCompletedPhysicalWhitenedReadout_zero_hasSignedHeightEigenvalue
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (whitening whiteningInv : Matrix (Fin 6) (Fin 6) ℂ)
    (cutoff : ℕ) (hleft : whiteningInv * whitening = 1) {time : ℝ}
    (hzero : finiteSixCameraCompletedPhysicalWhitenedReadout whitening cutoff time = 0) :
    LinearPMap.HasEigenvalue
      certificate.toReducedMaximalSelfAdjointHeightData.selfAdjointData.complexification
      (time : ℂ) := by
  exact certificate.zeroEquivalentReadout_zero_hasSignedHeightEigenvalue
    (finiteSixCameraCompletedPhysicalWhitenedReadout_isZeroEquivalent
      whitening whiteningInv cutoff hleft) hzero

/-- At nonzero height, left-invertibly whitened completed physical blindness
is exactly the existing reciprocal-square Jacobi point-eigenvalue condition. -/
theorem finiteSixCameraCompletedPhysicalWhitenedReadout_zero_iff_jacobiEigenvalue_inv_sq
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (whitening whiteningInv : Matrix (Fin 6) (Fin 6) ℂ)
    (cutoff : ℕ) (hleft : whiteningInv * whitening = 1)
    {time : ℝ} (htime : time ≠ 0) :
    finiteSixCameraCompletedPhysicalWhitenedReadout whitening cutoff time = 0 ↔
      LinearPMap.HasEigenvalue
        certificate.completedJacobiEnergySelfAdjointData.complexification
        ((time : ℂ) ^ 2)⁻¹ := by
  exact certificate.zeroEquivalentReadout_zero_iff_jacobiEigenvalue_inv_sq
    (finiteSixCameraCompletedPhysicalWhitenedReadout_isZeroEquivalent
      whitening whiteningInv cutoff hleft) htime

end CompletedNativeRealHPCarrierCertificate

end

end CarrySelfAdjointOperator
