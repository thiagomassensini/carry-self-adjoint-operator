import CarrySelfAdjointOperator.FinitePhysicalSixCameraWhiteningBridge
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! Concrete algebraic whitening for the literal finite physical six-camera matrix. -/

open scoped Matrix

namespace CarrySelfAdjointOperator

open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Camera.FiniteBridge
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Limits

noncomputable section

/-- Literal real row Gram `C_N^R (C_N^R)^T`. -/
def finitePhysicalSixCameraRowGram (cutoff : ℕ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  finiteCameraRowGram (finiteLiteralSixCameraMatrix cutoff)

/-- Entrywise identification with the already formalized literal finite
camera overlap sum. -/
theorem finitePhysicalSixCameraRowGram_apply_eq_literalFiniteCameraGram
    (cutoff : ℕ) (i j : Fin 6) :
    finitePhysicalSixCameraRowGram cutoff i j =
      literalFiniteCameraGram cutoff (sixCamera i) (sixCamera j) :=
  finiteLiteralSixCameraMatrix_rowGram_apply_eq_literalFiniteCameraGram cutoff i j

/-- Six leading coordinates are available precisely from cutoff one onward. -/
def finitePhysicalSixCameraLeadingColumn
    (cutoff : ℕ) (_hcutoff : 1 ≤ cutoff) :
    Fin 6 → Fin (finiteFamilyWindow cutoff sixCamera) := fun j =>
  ⟨j.val, by
    have hwindow :=
      finiteCameraWindow_le_finiteFamilyWindow cutoff sixCamera (5 : Fin 6)
    norm_num [sixCamera,
      finiteCameraWindow_of_ne_two (by norm_num : 7 ≠ 2)] at hwindow
    omega⟩

/-- Fixed leading minor witnessing literal row independence. -/
def finitePhysicalSixCameraLeadingMinor
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) : Matrix (Fin 6) (Fin 6) ℝ :=
  (finiteLiteralSixCameraMatrix cutoff).submatrix id
    (finitePhysicalSixCameraLeadingColumn cutoff hcutoff)

/-- Exact integer minor for the exceptional cutoff one. -/
def finitePhysicalSixCameraFirstCutoffMinor : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j => finiteCoefficient (sixCamera i) 1 (j.val + 1)

/-- Stable periodic-profile minor for every cutoff at least two. -/
def finitePhysicalSixCameraProfileMinor : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j => profile (sixCamera i) (j.val + 1)

set_option maxRecDepth 100000 in
theorem finitePhysicalSixCameraFirstCutoffMinor_det :
    finitePhysicalSixCameraFirstCutoffMinor.det = 880 := by
  decide

set_option maxRecDepth 100000 in
theorem finitePhysicalSixCameraProfileMinor_det :
    finitePhysicalSixCameraProfileMinor.det = 960 := by
  decide

theorem finitePhysicalSixCameraLeadingMinor_one :
    finitePhysicalSixCameraLeadingMinor 1 (by norm_num) =
      finitePhysicalSixCameraFirstCutoffMinor.map (fun z : ℤ => (z : ℝ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [finitePhysicalSixCameraLeadingMinor,
      finitePhysicalSixCameraLeadingColumn, finiteLiteralSixCameraMatrix,
      finiteLiteralCameraMatrix, finiteCoefficientAt,
      finitePhysicalSixCameraFirstCutoffMinor]

theorem finitePhysicalSixCameraLeadingMinor_eq_profile
    (cutoff : ℕ) (hcutoff : 2 ≤ cutoff) :
    finitePhysicalSixCameraLeadingMinor cutoff (by omega) =
      finitePhysicalSixCameraProfileMinor.map (fun z : ℤ => (z : ℝ)) := by
  ext i j
  change finiteCoefficientAt (sixCamera i) cutoff j.val =
    (profile (sixCamera i) (j.val + 1) : ℤ)
  apply finiteCoefficientAt_eq_profile_of_lt_core
  · fin_cases i <;> norm_num [sixCamera]
  · have hslope : 3 ≤ cameraSlope (sixCamera i) := by
      fin_cases i <;> norm_num [sixCamera, cameraSlope]
    calc
      j.val < 6 := j.isLt
      _ = 3 * 2 := by norm_num
      _ ≤ cameraSlope (sixCamera i) * cutoff := Nat.mul_le_mul hslope hcutoff

/-- Exact nonsingularity witness. It has just two cutoff-uniform cases. -/
theorem finitePhysicalSixCameraLeadingMinor_det_ne_zero
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :
    (finitePhysicalSixCameraLeadingMinor cutoff hcutoff).det ≠ 0 := by
  by_cases hfirst : cutoff = 1
  · subst cutoff
    rw [finitePhysicalSixCameraLeadingMinor_one, ← Int.cast_det,
      finitePhysicalSixCameraFirstCutoffMinor_det]
    norm_num
  · have hstable : 2 ≤ cutoff := by omega
    rw [show finitePhysicalSixCameraLeadingMinor cutoff hcutoff =
      finitePhysicalSixCameraLeadingMinor cutoff (by omega) by rfl,
      finitePhysicalSixCameraLeadingMinor_eq_profile cutoff hstable,
      ← Int.cast_det, finitePhysicalSixCameraProfileMinor_det]
    norm_num

theorem finitePhysicalSixCameraLeadingMinor_vecMul_apply
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (u : Fin 6 → ℝ) (j : Fin 6) :
    (finitePhysicalSixCameraLeadingMinor cutoff hcutoff).vecMul u j =
      (finiteLiteralSixCameraMatrix cutoff).vecMul u
        (finitePhysicalSixCameraLeadingColumn cutoff hcutoff j) :=
  rfl

/-- Full row rank of the actual literal finite six-camera matrix. -/
theorem finiteLiteralSixCameraMatrix_vecMul_injective
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :
    Function.Injective (finiteLiteralSixCameraMatrix cutoff).vecMul := by
  intro u v huv
  have hminor :
      (finitePhysicalSixCameraLeadingMinor cutoff hcutoff).vecMul u =
        (finitePhysicalSixCameraLeadingMinor cutoff hcutoff).vecMul v := by
    funext j
    rw [finitePhysicalSixCameraLeadingMinor_vecMul_apply,
      finitePhysicalSixCameraLeadingMinor_vecMul_apply]
    exact congrFun huv _
  have hunit : IsUnit (finitePhysicalSixCameraLeadingMinor cutoff hcutoff) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr
        (finitePhysicalSixCameraLeadingMinor_det_ne_zero cutoff hcutoff))
  exact Matrix.vecMul_injective_of_isUnit hunit hminor

/-- Positive definiteness of the literal finite row Gram follows from full row rank. -/
theorem finitePhysicalSixCameraRowGram_posDef
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :
    (finitePhysicalSixCameraRowGram cutoff).PosDef := by
  unfold finitePhysicalSixCameraRowGram finiteCameraRowGram
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.mul_conjTranspose_self
      (finiteLiteralSixCameraMatrix cutoff)
      (finiteLiteralSixCameraMatrix_vecMul_injective cutoff hcutoff)

/-- The real positive inverse square root of the literal finite row Gram. -/
def finitePhysicalSixCameraRealWhitening (cutoff : ℕ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  positiveInverseSqrt (finitePhysicalSixCameraRowGram cutoff)

/-- The algebraic inverse used only to certify the concrete whitening's
left-invertibility. -/
def finitePhysicalSixCameraRealWhiteningInverse (cutoff : ℕ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  (finitePhysicalSixCameraRealWhitening cutoff)⁻¹

/-- The concrete real inverse square root whitens the literal finite row
Gram exactly. -/
theorem finitePhysicalSixCameraRealWhitening_whitens
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :
    finitePhysicalSixCameraRealWhitening cutoff *
        finitePhysicalSixCameraRowGram cutoff *
        finitePhysicalSixCameraRealWhitening cutoff = 1 := by
  unfold finitePhysicalSixCameraRealWhitening
  exact positiveInverseSqrt_whitens
    (finitePhysicalSixCameraRowGram_posDef cutoff hcutoff)

/-- The real literal whitening is invertible as soon as the six literal
camera rows are available. -/
theorem finitePhysicalSixCameraRealWhiteningInverse_mul
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :
    finitePhysicalSixCameraRealWhiteningInverse cutoff *
        finitePhysicalSixCameraRealWhitening cutoff = 1 := by
  unfold finitePhysicalSixCameraRealWhiteningInverse
    finitePhysicalSixCameraRealWhitening
  letI := (positiveInverseSqrt_posDef
    (finitePhysicalSixCameraRowGram_posDef cutoff hcutoff)).isUnit.invertible
  exact Matrix.inv_mul_of_invertible _

/-- The complex finite literal camera matrix is the entrywise realification
of the actual literal real matrix, not the periodic six-camera Gram. -/
theorem complexify_finiteLiteralSixCameraMatrix
    (cutoff : ℕ) :
    (finiteLiteralSixCameraMatrix cutoff).map Complex.ofReal =
      finiteCameraMatrix cutoff sixCamera :=
  rfl

/-- The complex row Gram of the literal finite six-camera matrix is exactly
the complexification of its real row Gram. -/
theorem complexify_finitePhysicalSixCameraRowGram
    (cutoff : ℕ) :
    (finitePhysicalSixCameraRowGram cutoff).map Complex.ofReal =
      finiteCameraMatrix cutoff sixCamera *
        (finiteCameraMatrix cutoff sixCamera)ᴴ := by
  ext i j
  simp [finitePhysicalSixCameraRowGram, finiteCameraRowGram,
    finiteLiteralSixCameraMatrix, finiteLiteralCameraMatrix,
    finiteCameraMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.conj_ofReal]

/-- Concrete complex whitening used by the finite physical readout.  It is
the complexification of the real positive inverse square root of the
literal finite row Gram. -/
def finitePhysicalSixCameraWhitening (cutoff : ℕ) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  (finitePhysicalSixCameraRealWhitening cutoff).map Complex.ofReal

/-- Complexification of the inverse certifying left-invertibility of the
concrete physical whitening. -/
def finitePhysicalSixCameraWhiteningInverse (cutoff : ℕ) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  (finitePhysicalSixCameraRealWhiteningInverse cutoff).map Complex.ofReal

/-- The literal finite complex whitening has an internally constructed left
inverse.  No whitening hypothesis is left for the physical handoff. -/
theorem finitePhysicalSixCameraWhiteningInverse_mul
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :
    finitePhysicalSixCameraWhiteningInverse cutoff *
        finitePhysicalSixCameraWhitening cutoff = 1 := by
  unfold finitePhysicalSixCameraWhiteningInverse finitePhysicalSixCameraWhitening
  change (finitePhysicalSixCameraRealWhiteningInverse cutoff).map Complex.ofRealHom *
      (finitePhysicalSixCameraRealWhitening cutoff).map Complex.ofRealHom = 1
  rw [← Matrix.map_mul,
    finitePhysicalSixCameraRealWhiteningInverse_mul cutoff hcutoff]
  exact Matrix.map_one _ (map_zero Complex.ofRealHom) (map_one Complex.ofRealHom)

/-- Whiten the exactly stabilized completed physical six-camera vector by
the concrete finite literal Gram whitening. -/
def finitePhysicalSixCameraWhitenedCompletedReadout
    (cutoff : ℕ) (time : ℝ) : Fin 6 → ℂ :=
  finitePhysicalSixCameraWhitening cutoff *ᵥ
    canonicalCompletedSixCameraPhysicalReadout time

/-- In laboratory notation, the concrete whitened completed readout is the
finite literal whitening applied to the raw matrix orbit plus its exact
completion tail. -/
theorem finitePhysicalSixCameraWhitenedCompletedReadout_eq_whitening_mulVec_raw_add_tail
    (cutoff : ℕ) (time : ℝ) :
    finitePhysicalSixCameraWhitenedCompletedReadout cutoff time =
    finitePhysicalSixCameraWhitening cutoff *ᵥ
        (finiteSixCameraPhysicalRawReadout cutoff time +
          finiteSixCameraPhysicalCompletionTail cutoff time) := by
  unfold finitePhysicalSixCameraWhitenedCompletedReadout
  rw [← finiteSixCameraCompletedPhysicalReadout_eq_canonical cutoff time]
  rfl

/-- Concrete finite physical whitening preserves precisely the canonical
native zero locus, with no externally supplied left-inverse hypothesis. -/
theorem finitePhysicalSixCameraWhitenedCompletedReadout_eq_zero_iff_nativeZero
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (time : ℝ) :
    finitePhysicalSixCameraWhitenedCompletedReadout cutoff time = 0 ↔
      completedNativeOperatorCharacteristic (time : ℂ) = 0 := by
  change finiteSixCameraCompletedPhysicalWhitenedReadout
      (finitePhysicalSixCameraWhitening cutoff) 0 time = 0 ↔ _
  exact finiteSixCameraCompletedPhysicalWhitenedReadout_eq_zero_iff_nativeZero
    (finitePhysicalSixCameraWhitening cutoff)
    (finitePhysicalSixCameraWhiteningInverse cutoff) 0 time
    (finitePhysicalSixCameraWhiteningInverse_mul cutoff hcutoff)

/-- The concrete literal finite whitening is a direct zero-equivalent
handoff to the pre-existing signed-height spectrum bridge. -/
theorem finitePhysicalSixCameraWhitenedCompletedReadout_isZeroEquivalent
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :
    IsZeroEquivalentCompletedNativeHeightReadout
      (finitePhysicalSixCameraWhitenedCompletedReadout cutoff) :=
  fun time => finitePhysicalSixCameraWhitenedCompletedReadout_eq_zero_iff_nativeZero
    cutoff hcutoff time

namespace CompletedNativeRealHPCarrierCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {jet : (ℕ ⊕ ℕ) → E}

/-- Blindness of the concretely whitened finite physical readout is an
eigenvalue of the already constructed signed-height operator. -/
theorem finitePhysicalSixCameraWhitenedCompletedReadout_zero_hasSignedHeightEigenvalue
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) {time : ℝ}
    (hzero : finitePhysicalSixCameraWhitenedCompletedReadout cutoff time = 0) :
    LinearPMap.HasEigenvalue
      certificate.toReducedMaximalSelfAdjointHeightData.selfAdjointData.complexification
      (time : ℂ) := by
  exact certificate.zeroEquivalentReadout_zero_hasSignedHeightEigenvalue
    (finitePhysicalSixCameraWhitenedCompletedReadout_isZeroEquivalent cutoff hcutoff)
    hzero

/-- Away from zero height, concrete whitened physical blindness is exactly
the existing reciprocal-square Jacobi point-eigenvalue condition. -/
theorem finitePhysicalSixCameraWhitenedCompletedReadout_zero_iff_jacobiEigenvalue_inv_sq
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (cutoff : ℕ) (hcutoff : 1 ≤ cutoff) {time : ℝ} (htime : time ≠ 0) :
    finitePhysicalSixCameraWhitenedCompletedReadout cutoff time = 0 ↔
      LinearPMap.HasEigenvalue
        certificate.completedJacobiEnergySelfAdjointData.complexification
        ((time : ℂ) ^ 2)⁻¹ := by
  exact certificate.zeroEquivalentReadout_zero_iff_jacobiEigenvalue_inv_sq
    (finitePhysicalSixCameraWhitenedCompletedReadout_isZeroEquivalent cutoff hcutoff)
    htime

end CompletedNativeRealHPCarrierCertificate

end

end CarrySelfAdjointOperator
