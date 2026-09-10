import CarrySelfAdjointOperator.FiniteNativeDepthRawCameraGram
import CarrySelfAdjointOperator.FiniteCanonicalCameraReadout
import NativeCarrySpectralWeyl.Infinite.CameraCompletion
import NativeCarrySpectralWeyl.Infinite.Naimark
import NativeCarrySpectralWeyl.Finite.Gram
import NativeCarrySpectralWeyl.Camera.Geometry
import NativeCarrySpectralWeyl.Camera.BracketSeries
import NativeCarrySpectralWeyl.Camera.HigherDerivativeTail
import Mathlib.Tactic

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

/-!
# Atlas Energy six-camera Hilbert asymptotic crosswalk

The historical Atlas Energy repository contains an exact empirical-to-
Spectral-Weyl crosswalk for its six cameras.  That repository is deliberately
not added as a dependency here: the finite and limiting Spectral-Weyl APIs
already pin the camera geometry used by the crosswalk.

This file records the current-side semantic identification and derives the
raw six-camera embedding into the intrinsic camera Hilbert space.  It keeps
three objects distinct: the unnormalised finite row Gram, its cutoff-normalised
version, and the limiting six-camera Gram.  The whitened embedding is defined
from the normalised finite Gram.  Its exact pairing formula is proved, while
the asymptotic isometry is reduced explicitly to continuity of the positive
inverse square root, which is not an available theorem in the current pin.
-/

open scoped BigOperators Matrix RealInnerProductSpace
open Filter

namespace CarrySelfAdjointOperator

open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Limits
open FiniteNativeCarryOperator.Camera

noncomputable section

/-- The six historical labels in their Spectral-Weyl camera indexing. -/
def atlasSixCameraIndex (i : Fin 6) : CameraIndex :=
  ⟨sixCamera i, by
    fin_cases i <;> norm_num [sixCamera]⟩

@[simp] theorem atlasSixCameraIndex_val (i : Fin 6) :
    (atlasSixCameraIndex i : ℕ) = sixCamera i := rfl

/-- Distinct historical labels give distinct supported camera indices. -/
theorem atlasSixCameraIndex_injective :
    Function.Injective atlasSixCameraIndex := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Subtype.val hij
  simpa [sixCamera] using hval

/-- Radius sets recorded by the historical six-camera package. -/
def atlasSixCameraHistoricalRadii : Fin 6 → Finset ℕ :=
  ![({1} : Finset ℕ), {1}, {1, 2}, {1, 2}, {1, 2, 3}, {1, 2, 3}]

/-- Historical empirical periods, which are the spectral slopes here. -/
def atlasSixCameraHistoricalPeriod : Fin 6 → ℕ :=
  ![4, 3, 4, 5, 6, 7]

/-- The historical period list is exactly the Spectral-Weyl slope list. -/
theorem atlasSixCameraHistoricalPeriod_eq_cameraSlope (i : Fin 6) :
    atlasSixCameraHistoricalPeriod i = cameraSlope (sixCamera i) := by
  fin_cases i <;>
    norm_num [atlasSixCameraHistoricalPeriod, sixCamera, cameraSlope]

/-- The historical radius list is exactly the current radius-set API. -/
theorem atlasSixCamera_radiusSet_eq_historical (i : Fin 6) :
    radiusSet (sixCamera i) = atlasSixCameraHistoricalRadii i := by
  fin_cases i <;>
    norm_num [atlasSixCameraHistoricalRadii, sixCamera, radiusSet, halfRange] <;>
    decide

/-- Aligned historical centers agree with the current camera centers. -/
theorem atlasSixCamera_alignedCenter_eq_historical
    (i : Fin 6) (index : ℕ) :
    alignedCenter (sixCamera i) index =
      atlasSixCameraHistoricalPeriod i * (index + 1) := by
  rw [alignedCenter_eq_cameraSlope_mul,
    atlasSixCameraHistoricalPeriod_eq_cameraSlope]

/-- Every member of the historical package is a supported Spectral-Weyl
camera. -/
theorem atlasSixCamera_supported (i : Fin 6) :
    IsSupported (sixCamera i) := by
  change 2 ≤ sixCamera i
  fin_cases i <;> norm_num [sixCamera]

/-- The finite six-camera characteristic has the pinned all-order limit. -/
theorem atlasSixCamera_finiteCharacteristic_tendsto
    (i : Fin 6) {s : ℂ} (hs : -1 < s.re) :
    Tendsto
      (fun cutoff : ℕ =>
        finiteBracketCharacteristic (sixCamera i) cutoff s)
      atTop (nhds (bracketCharacteristic (sixCamera i) s)) := by
  exact finiteBracketCharacteristic_tendsto
    (atlasSixCamera_supported i) hs

/-- The all-order derivative tail bound applies to each historical camera. -/
theorem atlasSixCamera_iteratedDeriv_tail_le
    (i : Fin 6) (cutoff order : ℕ)
    (hcutoff : Real.exp 2 ≤ (cutoff : ℝ)) (time : ℝ) :
    ‖iteratedDeriv order
          (bracketCharacteristic (sixCamera i))
          (nativeLine time) -
        iteratedDeriv order
          (finiteBracketCharacteristic (sixCamera i) cutoff)
          (nativeLine time)‖ ≤
      (order.factorial *
          higherDerivativeCircleConstant (sixCamera i) time) *
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) *
          (Real.log (cutoff : ℝ)) ^ order := by
  exact iteratedDeriv_bracketCharacteristic_nativeLine_tail_le
    (camera := sixCamera i) (cutoff := cutoff) (order := order)
    (atlasSixCamera_supported i) hcutoff time

/-- Unnormalised finite row Gram of the literal six-camera matrix. -/
def atlasRawFiniteSixCameraRowGram (cutoff : ℕ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  finiteCameraRowGram (finiteLiteralSixCameraMatrix cutoff)

/-- Entrywise identification with the literal finite camera Gram. -/
theorem atlasRawFiniteSixCameraRowGram_apply
    (cutoff : ℕ) (i j : Fin 6) :
    atlasRawFiniteSixCameraRowGram cutoff i j =
      literalFiniteCameraGram cutoff (sixCamera i) (sixCamera j) := by
  simpa [atlasRawFiniteSixCameraRowGram] using
    (finiteLiteralSixCameraMatrix_rowGram_apply_eq_literalFiniteCameraGram
      cutoff i j)

/-- The normalised finite Gram, with the camera cutoff kept explicit. -/
def atlasNormalizedFiniteSixCameraRowGram (cutoff : ℕ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  (cutoff : ℝ)⁻¹ • atlasRawFiniteSixCameraRowGram cutoff

/-- The normalised finite Gram converges to the limiting six-camera Gram. -/
theorem atlasNormalizedFiniteSixCameraRowGram_tendsto :
    Tendsto atlasNormalizedFiniteSixCameraRowGram
      atTop (nhds sixCameraGram) := by
  change Tendsto
      (fun cutoff : ℕ =>
        (cutoff : ℝ)⁻¹ • finiteCameraRowGram
          (finiteLiteralSixCameraMatrix cutoff))
      atTop (nhds sixCameraGram)
  exact tendsto_normalizedFiniteLiteralSixCameraRowGram

/-- The raw six-camera coefficient embedding into the intrinsic camera
Hilbert space. -/
def atlasSixCameraHilbertEmbedding (c : Fin 6 → ℝ) : CameraHilbert :=
  ∑ i : Fin 6, c i • cameraVector (atlasSixCameraIndex i)

/-- Entrywise equality between the finite six-camera Gram and the intrinsic
all-bases kernel. -/
theorem atlasSixCameraGram_entry_eq_gramKernel (i j : Fin 6) :
    sixCameraGram i j =
      gramKernel (atlasSixCameraIndex i) (atlasSixCameraIndex j) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [atlasSixCameraIndex, sixCamera, sixCameraGram,
      sixCameraGramRat, gramKernel, periodicMeanKernel,
      periodicProductMean, periodicProductSum, pairPeriod,
      cameraLabel, cameraSlope, profile, c2Profile, oddProfile,
      evenProfile, dvdIndicator, Finset.sum_range_succ]

/-- The raw embedding has the exact limiting Gram pairing. -/
theorem atlasSixCameraHilbertEmbedding_inner
    (c d : Fin 6 → ℝ) :
    inner ℝ (atlasSixCameraHilbertEmbedding c)
      (atlasSixCameraHilbertEmbedding d) =
      c ⬝ᵥ (sixCameraGram *ᵥ d) := by
  classical
  simp only [atlasSixCameraHilbertEmbedding, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, inner_cameraVector]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← atlasSixCameraGram_entry_eq_gramKernel i j]
  ring

/-- A single external coordinate has overlap prescribed by one Gram entry. -/
def atlasSixCameraCoordinate (i : Fin 6) (x : ℝ) : Fin 6 → ℝ :=
  fun j => if j = i then x else 0

theorem atlasSixCameraHilbertEmbedding_coordinate_inner
    (i j : Fin 6) (x y : ℝ) :
    inner ℝ
        (atlasSixCameraHilbertEmbedding
          (atlasSixCameraCoordinate i x))
        (atlasSixCameraHilbertEmbedding
          (atlasSixCameraCoordinate j y)) =
      sixCameraGram i j * (x * y) := by
  rw [atlasSixCameraHilbertEmbedding_inner]
  simp [atlasSixCameraCoordinate, Matrix.mulVec, dotProduct]
  ring

/-- A concrete nonzero off-diagonal overlap of the raw six-camera axes. -/
theorem atlasSixCamera_raw_overlap_2_4 :
    sixCameraGram (0 : Fin 6) (2 : Fin 6) = 10 := by
  rw [← sixCameraGram_eq]
  rw [periodicGramMatrix_apply]
  norm_num [sixCamera, cameraSlope, periodicProductMean, periodicProductSum,
    profile, c2Profile, oddProfile, evenProfile, dvdIndicator,
    Finset.sum_range_succ]

/-- The finite whitening candidate A_M^(-1/2). -/
def atlasSixCameraWhiteningMatrix (cutoff : ℕ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  positiveInverseSqrt (atlasNormalizedFiniteSixCameraRowGram cutoff)

/-- The whitened coefficient embedding investigated in this module. -/
def atlasSixCameraWhitenedHilbertEmbedding
    (cutoff : ℕ) (c : Fin 6 → ℝ) : CameraHilbert :=
  atlasSixCameraHilbertEmbedding
    (atlasSixCameraWhiteningMatrix cutoff *ᵥ c)

/-- Exact pairing formula for the whitened embedding. -/
theorem atlasSixCameraWhitenedHilbertEmbedding_inner
    (cutoff : ℕ) (c d : Fin 6 → ℝ) :
    inner ℝ
        (atlasSixCameraWhitenedHilbertEmbedding cutoff c)
        (atlasSixCameraWhitenedHilbertEmbedding cutoff d) =
      c ⬝ᵥ
        (((atlasSixCameraWhiteningMatrix cutoff)ᵀ *
          sixCameraGram *
          atlasSixCameraWhiteningMatrix cutoff) *ᵥ d) := by
  change inner ℝ
      (atlasSixCameraHilbertEmbedding
        (atlasSixCameraWhiteningMatrix cutoff *ᵥ c))
      (atlasSixCameraHilbertEmbedding
        (atlasSixCameraWhiteningMatrix cutoff *ᵥ d)) =
    c ⬝ᵥ
      (((atlasSixCameraWhiteningMatrix cutoff)ᵀ *
        sixCameraGram *
        atlasSixCameraWhiteningMatrix cutoff) *ᵥ d)
  rw [atlasSixCameraHilbertEmbedding_inner]
  rw [dotProduct_comm]
  rw [← Matrix.dotProduct_transpose_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- If the finite inverse square roots converge to the limiting inverse square
root, the whitened embedding is asymptotically isometric.  The hypothesis is
left explicit because the current pin has no continuity theorem for the
positive inverse square root on finite matrix spaces. -/
theorem atlasSixCameraWhitenedHilbertEmbedding_inner_tendsto_of_inverseSqrt_tendsto
    (hW :
      Tendsto atlasSixCameraWhiteningMatrix
        atTop (nhds (positiveInverseSqrt sixCameraGram)))
    (c d : Fin 6 → ℝ) :
    Tendsto
      (fun cutoff : ℕ =>
        inner ℝ
          (atlasSixCameraWhitenedHilbertEmbedding cutoff c)
          (atlasSixCameraWhitenedHilbertEmbedding cutoff d))
      atTop (nhds (c ⬝ᵥ d)) := by
  have hcont :
      Continuous
        (fun W : Matrix (Fin 6) (Fin 6) ℝ =>
          Wᵀ * sixCameraGram * W) := by
    fun_prop
  have hmat := hcont.continuousAt.tendsto.comp hW
  have hR := positiveInverseSqrt_isHermitian sixCameraGram_posDef
  have hRT :
      (positiveInverseSqrt sixCameraGram)ᵀ =
        positiveInverseSqrt sixCameraGram := by
    ext i j
    simpa only [Matrix.transpose_apply, Matrix.conjTranspose_apply,
      star_trivial] using congr_fun (congr_fun hR.eq i) j
  rw [hRT, positiveInverseSqrt_whitens sixCameraGram_posDef] at hmat
  have hcontPair :
      Continuous
        (fun A : Matrix (Fin 6) (Fin 6) ℝ =>
          c ⬝ᵥ (A *ᵥ d)) := by
    fun_prop
  have hp := hcontPair.continuousAt.tendsto.comp hmat
  have hid : (1 : Matrix (Fin 6) (Fin 6) ℝ) *ᵥ d = d := by
    simp
  rw [hid] at hp
  have hfun :
      (fun cutoff : ℕ =>
        inner ℝ
          (atlasSixCameraWhitenedHilbertEmbedding cutoff c)
          (atlasSixCameraWhitenedHilbertEmbedding cutoff d)) =
      (fun cutoff : ℕ =>
        c ⬝ᵥ
          (((atlasSixCameraWhiteningMatrix cutoff)ᵀ *
            sixCameraGram *
            atlasSixCameraWhiteningMatrix cutoff) *ᵥ d)) := by
    funext cutoff
    exact atlasSixCameraWhitenedHilbertEmbedding_inner cutoff c d
  rw [hfun]
  exact hp

end

end CarrySelfAdjointOperator
