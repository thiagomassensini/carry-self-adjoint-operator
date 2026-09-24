import CarrySelfAdjointOperator.FinitePhysicalSixCameraConcreteWhitening
import Mathlib.Tactic

/-!
# Analytic completed physical six-camera readout

The finite physical laboratory head is a matrix orbit only on the native
real-height line.  Its correct analytic completion is nevertheless already
present coordinatewise: it is the finite bracket head plus the exact
whole-center tail, namely `completedNativeCharacteristic`.

This module packages that analytic, six-coordinate object and its concrete
finite-Gram whitening.  It deliberately makes **no** lossless, Naimark,
Potapov, or finite-state-realization claim for the completion tail.  The
existing Naimark/Green constructions have not been identified with
`centerBracketTerm`; that is a separate architectural seam.
-/

open scoped BigOperators Matrix

namespace CarrySelfAdjointOperator

open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Camera.FiniteBridge
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Limits

noncomputable section

/-- The complex finite stencil head for all six historical cameras.  On the
native line this is the literal finite physical matrix readout, by the
matrix--stencil theorem from the finite physical bridge. -/
def finiteSixCameraPhysicalRawHeadComplex
    (cutoff : ℕ) (z : ℂ) : Fin 6 → ℂ :=
  fun i => finiteBracketCharacteristic (sixCamera i) cutoff z

/-- The exact complex whole-center completion tail for all six historical
cameras.  This is an analytic-series presentation, not a newly postulated
state-space output. -/
def finiteSixCameraPhysicalCompletionTailComplex
    (cutoff : ℕ) (z : ℂ) : Fin 6 → ℂ :=
  fun i => ∑' index : ℕ, centerBracketTerm (sixCamera i) z (index + cutoff)

/-- The complex completed physical camera vector.  The definition is the
already formalized coordinatewise completed characteristic, so it retains the
exact head--tail ledger without identifying the tail with a finite orbit. -/
def finiteSixCameraCompletedPhysicalReadoutComplex
    (cutoff : ℕ) (z : ℂ) : Fin 6 → ℂ :=
  fun i => completedNativeCharacteristic (sixCamera i) cutoff z

/-- The complex completed readout is exactly its finite stencil head plus its
whole-center completion contribution, coordinate by coordinate. -/
theorem finiteSixCameraPhysicalRawHeadComplex_add_completionTailComplex_eq_completed
    (cutoff : ℕ) (z : ℂ) :
    finiteSixCameraPhysicalRawHeadComplex cutoff z +
        finiteSixCameraPhysicalCompletionTailComplex cutoff z =
      finiteSixCameraCompletedPhysicalReadoutComplex cutoff z := by
  funext i
  rfl

/-- Restricting the complex stencil head to the native line gives the real-time
head used by the finite physical matrix--stencil bridge. -/
theorem finiteSixCameraPhysicalRawHeadComplex_nativeLine
    (cutoff : ℕ) (time : ℝ) :
    finiteSixCameraPhysicalRawHeadComplex cutoff (nativeLine time) =
      finiteSixCameraPhysicalRawHead cutoff time := by
  rfl

/-- Restricting the complex tail to the native line gives the existing exact
physical completion-tail vector. -/
theorem finiteSixCameraPhysicalCompletionTailComplex_nativeLine
    (cutoff : ℕ) (time : ℝ) :
    finiteSixCameraPhysicalCompletionTailComplex cutoff (nativeLine time) =
      finiteSixCameraPhysicalCompletionTail cutoff time := by
  rfl

/-- Restricting the complex completed vector to the native line gives the
previously formalized finite physical completed readout. -/
theorem finiteSixCameraCompletedPhysicalReadoutComplex_nativeLine
    (cutoff : ℕ) (time : ℝ) :
    finiteSixCameraCompletedPhysicalReadoutComplex cutoff (nativeLine time) =
      finiteSixCameraCompletedPhysicalReadout cutoff time := by
  rw [finiteSixCameraCompletedPhysicalReadout_eq_completedNativeReadout]
  rfl

/-- The complex completed readout agrees with the common bracket
characteristic in every coordinate on the bracket domain.  Thus the complex
extension is inherited from the existing analytic completion; no continuation
is constructed in this module. -/
theorem finiteSixCameraCompletedPhysicalReadoutComplex_apply_eq_bracketCharacteristic
    (cutoff : ℕ) {z : ℂ} (hz : z ∈ bracketDomain) (i : Fin 6) :
    finiteSixCameraCompletedPhysicalReadoutComplex cutoff z i =
      bracketCharacteristic (sixCamera i) z := by
  exact completedNativeCharacteristic_eq_bracketCharacteristic
    (two_le_sixCamera i) hz

/-- Coordinatewise holomorphy of the complex completed physical readout on
the bracket domain.  The proof transports the existing bracket-characteristic
regularity through the exact head--tail identity; it does not posit a new
analytic continuation. -/
theorem finiteSixCameraCompletedPhysicalReadoutComplex_apply_differentiableOn
    (cutoff : ℕ) (i : Fin 6) :
    DifferentiableOn ℂ
      (fun z => finiteSixCameraCompletedPhysicalReadoutComplex cutoff z i)
      bracketDomain := by
  apply DifferentiableOn.congr
    (bracketCharacteristic_differentiableOn (two_le_sixCamera i))
  intro z hz
  exact finiteSixCameraCompletedPhysicalReadoutComplex_apply_eq_bracketCharacteristic
    cutoff hz i

/-- The concrete finite Gram whitening applied to the analytic completed
camera vector.  It is constant in `z`; it is the complexification of the real
positive inverse square root of the literal finite row Gram. -/
def finitePhysicalSixCameraWhitenedCompletedReadoutComplex
    (cutoff : ℕ) (z : ℂ) : Fin 6 → ℂ :=
  finitePhysicalSixCameraWhitening cutoff *ᵥ
    finiteSixCameraCompletedPhysicalReadoutComplex cutoff z

/-- The analytic whitening decomposes exactly into the whitened finite head
and the whitened completion contribution. -/
def finitePhysicalSixCameraWhitenedRawHeadComplex
    (cutoff : ℕ) (z : ℂ) : Fin 6 → ℂ :=
  finitePhysicalSixCameraWhitening cutoff *ᵥ
    finiteSixCameraPhysicalRawHeadComplex cutoff z

/-- The visible completion contribution after the same constant finite Gram
whitening.  It is an additive transfer contribution, not a multiplicative
gauge. -/
def finitePhysicalSixCameraWhitenedCompletionContributionComplex
    (cutoff : ℕ) (z : ℂ) : Fin 6 → ℂ :=
  finitePhysicalSixCameraWhitening cutoff *ᵥ
    finiteSixCameraPhysicalCompletionTailComplex cutoff z

/-- Exact analytic separation of the interior/head channel from the
completion channel. -/
theorem finitePhysicalSixCameraWhitenedCompletedReadoutComplex_eq_head_add_completion
    (cutoff : ℕ) (z : ℂ) :
    finitePhysicalSixCameraWhitenedCompletedReadoutComplex cutoff z =
      finitePhysicalSixCameraWhitenedRawHeadComplex cutoff z +
        finitePhysicalSixCameraWhitenedCompletionContributionComplex cutoff z := by
  unfold finitePhysicalSixCameraWhitenedCompletedReadoutComplex
    finitePhysicalSixCameraWhitenedRawHeadComplex
    finitePhysicalSixCameraWhitenedCompletionContributionComplex
  rw [← finiteSixCameraPhysicalRawHeadComplex_add_completionTailComplex_eq_completed,
    Matrix.mulVec_add]

/-- On the native line, the complex completed-and-whitened channel is exactly
the concrete physical channel already sent to the signed-height bridge. -/
theorem finitePhysicalSixCameraWhitenedCompletedReadoutComplex_nativeLine
    (cutoff : ℕ) (time : ℝ) :
    finitePhysicalSixCameraWhitenedCompletedReadoutComplex cutoff (nativeLine time) =
      finitePhysicalSixCameraWhitenedCompletedReadout cutoff time := by
  unfold finitePhysicalSixCameraWhitenedCompletedReadoutComplex
    finitePhysicalSixCameraWhitenedCompletedReadout
  rw [finiteSixCameraCompletedPhysicalReadoutComplex_nativeLine,
    finiteSixCameraCompletedPhysicalReadout_eq_canonical]

/-- On the real height line the analytic completed channel retains precisely
the canonical native zero locus.  This theorem uses only the already-proved
concrete whitening left inverse; it does not assert a lossless realization at
non-real `z`. -/
theorem finitePhysicalSixCameraWhitenedCompletedReadoutComplex_nativeLine_eq_zero_iff_nativeZero
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (time : ℝ) :
    finitePhysicalSixCameraWhitenedCompletedReadoutComplex cutoff (nativeLine time) = 0 ↔
      completedNativeOperatorCharacteristic (time : ℂ) = 0 := by
  rw [finitePhysicalSixCameraWhitenedCompletedReadoutComplex_nativeLine,
    finitePhysicalSixCameraWhitenedCompletedReadout_eq_zero_iff_nativeZero
      cutoff hcutoff time]

/-- Root-free real-axis secular of the concrete completed whitened channel.
It is defined from the actual visible channel, rather than from an unproved
Potapov active block. -/
def finitePhysicalSixCameraWhitenedCompletedRootFreeSecular
    (cutoff : ℕ) (time : ℝ) : ℝ :=
  4 * ∑ i, Complex.normSq
    (finitePhysicalSixCameraWhitenedCompletedReadout cutoff time i)

/-- The root-free visible-channel secular vanishes exactly at collective
completed physical blindness. -/
theorem finitePhysicalSixCameraWhitenedCompletedRootFreeSecular_eq_zero_iff
    (cutoff : ℕ) (time : ℝ) :
    finitePhysicalSixCameraWhitenedCompletedRootFreeSecular cutoff time = 0 ↔
      finitePhysicalSixCameraWhitenedCompletedReadout cutoff time = 0 := by
  constructor
  · intro hsecular
    have hsum :
        ∑ i, Complex.normSq
          (finitePhysicalSixCameraWhitenedCompletedReadout cutoff time i) = 0 := by
      exact (mul_eq_zero.mp hsecular).resolve_left (by norm_num)
    funext i
    apply Complex.normSq_eq_zero.mp
    have hterms : ∀ j ∈ (Finset.univ : Finset (Fin 6)),
        Complex.normSq
          (finitePhysicalSixCameraWhitenedCompletedReadout cutoff time j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Complex.normSq_nonneg _)).mp hsum
    exact hterms i (by simp)
  · intro hblind
    simp only [finitePhysicalSixCameraWhitenedCompletedRootFreeSecular, hblind,
      Pi.zero_apply, Complex.normSq_zero, Finset.sum_const_zero, mul_zero]

/-- For every admissible finite cutoff, the concrete root-free secular of the
completed physical visible channel has the canonical native zero set. -/
theorem finitePhysicalSixCameraWhitenedCompletedRootFreeSecular_eq_zero_iff_nativeZero
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (time : ℝ) :
    finitePhysicalSixCameraWhitenedCompletedRootFreeSecular cutoff time = 0 ↔
      completedNativeOperatorCharacteristic (time : ℂ) = 0 := by
  rw [finitePhysicalSixCameraWhitenedCompletedRootFreeSecular_eq_zero_iff,
    finitePhysicalSixCameraWhitenedCompletedReadout_eq_zero_iff_nativeZero cutoff hcutoff]

/-- The root-free physical completed-channel secular is ready for the
existing zero-equivalent spectral handoff.  This is not a claim that it is a
round-trip or Potapov determinant; proving such an identification requires a
conservative realization of the analytic completion channel. -/
theorem finitePhysicalSixCameraWhitenedCompletedRootFreeSecular_isZeroEquivalent
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :
    IsZeroEquivalentCompletedNativeHeightReadout
      (finitePhysicalSixCameraWhitenedCompletedRootFreeSecular cutoff) :=
  fun time =>
    finitePhysicalSixCameraWhitenedCompletedRootFreeSecular_eq_zero_iff_nativeZero
      cutoff hcutoff time

namespace CompletedNativeRealHPCarrierCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {jet : (ℕ ⊕ ℕ) → E}

/-- The root-free secular of the actual completed physical visible channel
uses the existing signed-height bridge without introducing a new operator or
a Potapov realization. -/
theorem finitePhysicalSixCameraWhitenedCompletedRootFreeSecular_zero_hasSignedHeightEigenvalue
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) {time : ℝ}
    (hzero : finitePhysicalSixCameraWhitenedCompletedRootFreeSecular cutoff time = 0) :
    LinearPMap.HasEigenvalue
      certificate.toReducedMaximalSelfAdjointHeightData.selfAdjointData.complexification
      (time : ℂ) := by
  exact certificate.zeroEquivalentReadout_zero_hasSignedHeightEigenvalue
    (finitePhysicalSixCameraWhitenedCompletedRootFreeSecular_isZeroEquivalent
      cutoff hcutoff)
    hzero

/-- Away from zero height, the physical root-free secular has the same
reciprocal-square Jacobi eigenvalue event as the completed visible channel. -/
theorem finitePhysicalSixCameraWhitenedCompletedRootFreeSecular_zero_iff_jacobiEigenvalue_inv_sq
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) {time : ℝ} (htime : time ≠ 0) :
    finitePhysicalSixCameraWhitenedCompletedRootFreeSecular cutoff time = 0 ↔
      LinearPMap.HasEigenvalue
        certificate.completedJacobiEnergySelfAdjointData.complexification
        ((time : ℂ) ^ 2)⁻¹ := by
  exact certificate.zeroEquivalentReadout_zero_iff_jacobiEigenvalue_inv_sq
    (finitePhysicalSixCameraWhitenedCompletedRootFreeSecular_isZeroEquivalent
      cutoff hcutoff)
    htime

end CompletedNativeRealHPCarrierCertificate

end

end CarrySelfAdjointOperator
