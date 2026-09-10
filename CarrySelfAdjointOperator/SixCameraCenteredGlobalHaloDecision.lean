import CarrySelfAdjointOperator.SixCameraGlobalNaimarkHaloDecomposition
import Mathlib.Tactic

/-!
# Six-camera centered-log global halo decision

This module decides the restriction of the coherent all-camera halo to the
centered-log six-camera synthesis.  It stays in the intrinsic real NaimarkSpace.
-/

open scoped BigOperators ENNReal MeasureTheory RealInnerProductSpace Matrix MatrixOrder
open Set MeasureTheory Filter intervalIntegral

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera

noncomputable section
set_option autoImplicit false

/-- The six selected camera labels have slopes at most seven. -/
lemma sixCamera_slope_le_seven (i : Fin 6) :
    cameraSlope (cameraLabel (atlasSixCameraIndex i)) ≤ 7 := by
  fin_cases i <;> norm_num [atlasSixCameraIndex, sixCamera, cameraLabel, cameraSlope]

/-- A camera with label at least eight has slope at least eight. -/
lemma external_camera_slope_ge_eight {camera : CameraIndex}
    (hcamera : 8 ≤ cameraLabel camera) :
    8 ≤ cameraSlope (cameraLabel camera) := by
  by_cases htwo : cameraLabel camera = 2
  · omega
  · rw [cameraSlope_of_ne_two htwo]
    exact hcamera

/-- Every external camera is orthogonal to the raw centered-log synthesis of
six cameras.  The cancellation is exact: the minimum slope is the selected
slope, so the centered logarithmic factor vanishes. -/
theorem externalCamera_inner_sixCameraCenteredLogNaimarkSynthesis_eq_zero
    {camera : CameraIndex} (hcamera : 8 ≤ cameraLabel camera)
    (c : Fin 6 → ℝ) :
    inner ℝ (naimarkCameraVector camera)
      (sixCameraCenteredLogNaimarkSynthesis c) = 0 := by
  classical
  unfold sixCameraCenteredLogNaimarkSynthesis
  simp only [inner_sum, real_inner_smul_right]
  apply Finset.sum_eq_zero
  intro i hi
  rw [inner_naimarkCameraVector_centeredNaimarkCameraVector]
  have hslope : 8 ≤ cameraSlope (cameraLabel camera) :=
    external_camera_slope_ge_eight hcamera
  have hsel : cameraSlope (cameraLabel (atlasSixCameraIndex i)) ≤ 7 :=
    sixCamera_slope_le_seven i
  have hmin : min (cameraSlope (cameraLabel camera))
      (cameraSlope (cameraLabel (atlasSixCameraIndex i))) =
      cameraSlope (cameraLabel (atlasSixCameraIndex i)) :=
    Nat.min_eq_right (by omega)
  rw [hmin]
  simp

/-- The same orthogonality holds after the six-camera whitening. -/
theorem externalCamera_inner_sixCameraWhitenedCenteredLogNaimarkSynthesis_eq_zero
    {camera : CameraIndex} (hcamera : 8 ≤ cameraLabel camera)
    (c : Fin 6 → ℝ) :
    inner ℝ (naimarkCameraVector camera)
      (sixCameraWhitenedCenteredLogNaimarkSynthesis c) = 0 := by
  unfold sixCameraWhitenedCenteredLogNaimarkSynthesis
  exact externalCamera_inner_sixCameraCenteredLogNaimarkSynthesis_eq_zero
    hcamera _

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

theorem externalCamera_inner_centeredHalo_eq_neg_sixProjection
    {camera : CameraIndex} (hcamera : 8 ≤ cameraLabel camera)
    (c : Fin 6 → ℝ) :
    inner ℝ (naimarkCameraVector camera)
      (sixCameraGlobalCoherentHaloProjection
        (sixCameraWhitenedCenteredLogNaimarkSynthesis c)) =
      - inner ℝ (naimarkCameraVector camera)
        (sixCameraWhitenedNaimarkProjection
          (sixCameraWhitenedCenteredLogNaimarkSynthesis c)) := by
  rw [sixCameraGlobalCoherentHaloProjection_apply, inner_sub_right]
  have hP :
      inner ℝ
          (globalNaimarkCameraProjection
            (sixCameraWhitenedCenteredLogNaimarkSynthesis c))
          (naimarkCameraVector camera) = 0 := by
    rw [globalNaimarkCameraProjection_inner_symm,
      globalNaimarkCameraProjection_fixes_naimarkCameraVector]
    rw [real_inner_comm]
    exact externalCamera_inner_sixCameraWhitenedCenteredLogNaimarkSynthesis_eq_zero
      hcamera c
  have hPzero :
      inner ℝ (naimarkCameraVector camera)
          (globalNaimarkCameraProjection
            (sixCameraWhitenedCenteredLogNaimarkSynthesis c)) = 0 := by
    rw [real_inner_comm]
    exact hP
  rw [hPzero]
  ring

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

theorem sixCameraProjection_centeredLog_eq_returnSynthesis
    (c : Fin 6 → ℝ) :
    sixCameraWhitenedNaimarkProjection
        (sixCameraWhitenedCenteredLogNaimarkSynthesis c) =
      sixCameraWhitenedNaimarkSynthesis
        (sixCameraWhitenedCrossGram *ᵥ c) := by
  rw [sixCameraWhitenedNaimarkProjection,
    sixCameraWhitenedNaimarkAnalysis_apply_centeredLog]

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

def externalCameraWhitenedReadout (camera : CameraIndex)
    (c : Fin 6 → ℝ) : ℝ :=
  inner ℝ (naimarkCameraVector camera)
    (sixCameraWhitenedNaimarkSynthesis c)

theorem externalCameraWhitenedReadout_eq_dotProduct
    (camera : CameraIndex) (c : Fin 6 → ℝ) :
    externalCameraWhitenedReadout camera c =
      (fun i : Fin 6 =>
        gramKernel camera (atlasSixCameraIndex i)) ⬝ᵥ
        (positiveInverseSqrt sixCameraGram *ᵥ c) := by
  unfold externalCameraWhitenedReadout sixCameraWhitenedNaimarkSynthesis
    sixCameraNaimarkSynthesis
  simp only [inner_sum, real_inner_smul_right, inner_naimarkCameraVector]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

theorem externalCameraWhitenedReadout_centeredHalo_eq_neg_returnReadout
    {camera : CameraIndex} (hcamera : 8 ≤ cameraLabel camera)
    (c : Fin 6 → ℝ) :
    inner ℝ (naimarkCameraVector camera)
      (sixCameraGlobalCoherentHaloProjection
        (sixCameraWhitenedCenteredLogNaimarkSynthesis c)) =
      - externalCameraWhitenedReadout camera
        (sixCameraWhitenedCrossGram *ᵥ c) := by
  rw [externalCamera_inner_centeredHalo_eq_neg_sixProjection hcamera c,
    sixCameraProjection_centeredLog_eq_returnSynthesis]
  rfl

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

lemma sixCameraExternalEightGramRow :
    (fun i : Fin 6 =>
      gramKernel sixCameraGlobalHaloWitnessCamera
        (atlasSixCameraIndex i)) =
      ![(8 : ℝ), 0, 16, 0, 8, 0] := by
  funext i
  fin_cases i <;>
    norm_num [sixCameraGlobalHaloWitnessCamera, atlasSixCameraIndex,
      sixCamera, cameraLabel, gramKernel, periodicMeanKernel,
      periodicProductMean, periodicProductSum, pairPeriod, cameraSlope,
      profile, c2Profile, oddProfile, evenProfile, dvdIndicator,
      Finset.sum_range_succ]

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

def sixCameraExternalEightDual : Fin 6 → ℝ :=
  ![(91 / 278 : ℝ), -12 / 139, 155 / 278, 0, 12 / 139, 0]

def sixCameraCenteredGlobalHaloWitness : Fin 6 → ℝ :=
  CFC.sqrt sixCameraGram *ᵥ (Pi.single (4 : Fin 6) 1)

lemma sixCameraExternalEightDual_mul_gram :
    Matrix.vecMul sixCameraExternalEightDual sixCameraGram =
      ![(8 : ℝ), 0, 16, 0, 8, 0] := by
  ext j
  fin_cases j <;>
    norm_num [sixCameraExternalEightDual, Matrix.vecMul, dotProduct,
      sixCameraGram, sixCameraGramRat, Fin.sum_univ_succ]

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

lemma sixCamera_whitening_mul_sqrt_mulVec (v : Fin 6 → ℝ) :
    positiveInverseSqrt sixCameraGram *ᵥ
        (CFC.sqrt sixCameraGram *ᵥ v) = v := by
  have hunit : IsUnit (CFC.sqrt sixCameraGram) :=
    (sixCameraGram_posDef.isStrictlyPositive.sqrt sixCameraGram).isUnit
  letI := hunit.invertible
  have hinv : positiveInverseSqrt sixCameraGram * CFC.sqrt sixCameraGram = 1 := by
    unfold positiveInverseSqrt
    exact Matrix.inv_mul_of_invertible (CFC.sqrt sixCameraGram)
  rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

lemma sixCameraWhitenedCrossGram_mul_centeredGlobalHaloWitness :
    sixCameraWhitenedCrossGram *ᵥ sixCameraCenteredGlobalHaloWitness =
      positiveInverseSqrt sixCameraGram *ᵥ
        ((sixCameraFirstMoment -
            sixCameraGram * cameraLogSlopeDiagonal sixCamera) *ᵥ
          (Pi.single (4 : Fin 6) 1)) := by
  unfold sixCameraCenteredGlobalHaloWitness sixCameraWhitenedCrossGram
  calc
    (positiveInverseSqrt sixCameraGram *
        (sixCameraFirstMoment -
          sixCameraGram * cameraLogSlopeDiagonal sixCamera) *
        positiveInverseSqrt sixCameraGram) *ᵥ
        (CFC.sqrt sixCameraGram *ᵥ (Pi.single (4 : Fin 6) 1)) =
      (positiveInverseSqrt sixCameraGram *
        (sixCameraFirstMoment -
          sixCameraGram * cameraLogSlopeDiagonal sixCamera)) *ᵥ
        (positiveInverseSqrt sixCameraGram *ᵥ
          (CFC.sqrt sixCameraGram *ᵥ (Pi.single (4 : Fin 6) 1))) := by
      exact (Matrix.mulVec_mulVec
        (CFC.sqrt sixCameraGram *ᵥ (Pi.single (4 : Fin 6) 1))
        (positiveInverseSqrt sixCameraGram *
          (sixCameraFirstMoment -
            sixCameraGram * cameraLogSlopeDiagonal sixCamera))
        (positiveInverseSqrt sixCameraGram)).symm
    _ = positiveInverseSqrt sixCameraGram *ᵥ
        ((sixCameraFirstMoment -
            sixCameraGram * cameraLogSlopeDiagonal sixCamera) *ᵥ
          (positiveInverseSqrt sixCameraGram *ᵥ
            (CFC.sqrt sixCameraGram *ᵥ (Pi.single (4 : Fin 6) 1)))) := by
      exact (Matrix.mulVec_mulVec
        (positiveInverseSqrt sixCameraGram *ᵥ
          (CFC.sqrt sixCameraGram *ᵥ (Pi.single (4 : Fin 6) 1)))
        (positiveInverseSqrt sixCameraGram)
        (sixCameraFirstMoment -
          sixCameraGram * cameraLogSlopeDiagonal sixCamera)).symm
    _ = positiveInverseSqrt sixCameraGram *ᵥ
        ((sixCameraFirstMoment -
            sixCameraGram * cameraLogSlopeDiagonal sixCamera) *ᵥ
          (Pi.single (4 : Fin 6) 1)) := by
      rw [sixCamera_whitening_mul_sqrt_mulVec]

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

lemma sixCameraExternalEightDual_dot_inverse_mulVec (z : Fin 6 → ℝ) :
    ![(8 : ℝ), 0, 16, 0, 8, 0] ⬝ᵥ
        (sixCameraGram⁻¹ *ᵥ z) =
      sixCameraExternalEightDual ⬝ᵥ z := by
  rw [← sixCameraExternalEightDual_mul_gram]
  rw [← Matrix.dotProduct_mulVec]
  have hunit : IsUnit sixCameraGram := sixCameraGram_posDef.isUnit
  letI := hunit.invertible
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
    Matrix.one_mulVec]

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

lemma sixCamera_centeredSlopeDefect_e4 :
    (sixCameraFirstMoment -
        sixCameraGram * cameraLogSlopeDiagonal sixCamera) *ᵥ
      (Pi.single (4 : Fin 6) 1) =
      ![(16/3 : ℝ) * (Real.log 4 - Real.log 6),
        6 * (Real.log 3 - Real.log 6),
        (16/3 : ℝ) * (Real.log 4 - Real.log 6), 0, 0, 0] := by
  have hD := sixCameraSlopeDefect_mulVec (Pi.single (4 : Fin 6) 1)
  have hD' :
      (sixCameraGram * cameraLogSlopeDiagonal sixCamera -
          sixCameraFirstMoment) *ᵥ (Pi.single (4 : Fin 6) 1) =
        ![(16/3 : ℝ) * (Real.log 6 - Real.log 4),
          6 * (Real.log 6 - Real.log 3),
          (16/3 : ℝ) * (Real.log 6 - Real.log 4), 0, 0, 0] := by
    simpa using hD
  calc
    (sixCameraFirstMoment -
        sixCameraGram * cameraLogSlopeDiagonal sixCamera) *ᵥ
        (Pi.single (4 : Fin 6) 1) =
        - ((sixCameraGram * cameraLogSlopeDiagonal sixCamera -
          sixCameraFirstMoment) *ᵥ (Pi.single (4 : Fin 6) 1)) := by
            rw [Matrix.sub_mulVec, Matrix.sub_mulVec]
            ext i
            simp only [Pi.neg_apply, Pi.sub_apply]
            ring
    _ = - ![(16/3 : ℝ) * (Real.log 6 - Real.log 4),
          6 * (Real.log 6 - Real.log 3),
          (16/3 : ℝ) * (Real.log 6 - Real.log 4), 0, 0, 0] := by
            rw [hD']
    _ = ![(16/3 : ℝ) * (Real.log 4 - Real.log 6),
        6 * (Real.log 3 - Real.log 6),
        (16/3 : ℝ) * (Real.log 4 - Real.log 6), 0, 0, 0] := by
            ext i
            fin_cases i <;> norm_num <;> ring

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

lemma sixCameraExternalEightDual_dot_centeredSlopeDefect :
    sixCameraExternalEightDual ⬝ᵥ
        ((sixCameraFirstMoment -
            sixCameraGram * cameraLogSlopeDiagonal sixCamera) *ᵥ
          (Pi.single (4 : Fin 6) 1)) =
      (8 / 139 : ℝ) * (91 * Real.log 2 - 82 * Real.log 3) := by
  rw [sixCamera_centeredSlopeDefect_e4]
  norm_num [sixCameraExternalEightDual, dotProduct, Fin.sum_univ_succ]
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [hlog4, hlog6]
  ring

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

lemma sixCameraExternalEightDual_log_combination_ne_zero :
    91 * Real.log 2 - 82 * Real.log 3 ≠ 0 := by
  intro h
  have hlog :
      Real.log ((2 : ℝ) ^ 91) = Real.log ((3 : ℝ) ^ 82) := by
    rw [Real.log_pow, Real.log_pow]
    norm_num
    linarith
  have hpow : (2 : ℝ) ^ 91 = (3 : ℝ) ^ 82 :=
    Real.log_injOn_pos
      (show 0 < (2 : ℝ) ^ 91 by positivity)
      (show 0 < (3 : ℝ) ^ 82 by positivity) hlog
  have hpowNat : (2 : ℕ) ^ 91 = (3 : ℕ) ^ 82 := by
    exact_mod_cast hpow
  norm_num at hpowNat

lemma sixCameraExternalEightDual_dot_centeredSlopeDefect_ne_zero :
    sixCameraExternalEightDual ⬝ᵥ
        ((sixCameraFirstMoment -
            sixCameraGram * cameraLogSlopeDiagonal sixCamera) *ᵥ
          (Pi.single (4 : Fin 6) 1)) ≠ 0 := by
  rw [sixCameraExternalEightDual_dot_centeredSlopeDefect]
  apply mul_ne_zero
  · norm_num
  · exact sixCameraExternalEightDual_log_combination_ne_zero

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

lemma externalCamera8WhitenedReadout_centeredWitness :
    externalCameraWhitenedReadout sixCameraGlobalHaloWitnessCamera
        (sixCameraWhitenedCrossGram *ᵥ sixCameraCenteredGlobalHaloWitness) =
      sixCameraExternalEightDual ⬝ᵥ
        ((sixCameraFirstMoment -
            sixCameraGram * cameraLogSlopeDiagonal sixCamera) *ᵥ
          (Pi.single (4 : Fin 6) 1)) := by
  rw [externalCameraWhitenedReadout_eq_dotProduct,
    sixCameraExternalEightGramRow,
    sixCameraWhitenedCrossGram_mul_centeredGlobalHaloWitness]
  rw [Matrix.mulVec_mulVec]
  rw [positiveInverseSqrt_mul_self sixCameraGram_posDef]
  exact sixCameraExternalEightDual_dot_inverse_mulVec
    ((sixCameraFirstMoment -
        sixCameraGram * cameraLogSlopeDiagonal sixCamera) *ᵥ
      (Pi.single (4 : Fin 6) 1))

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

theorem externalCamera8WhitenedReadout_centeredHalo_witness_ne_zero :
    inner ℝ (naimarkCameraVector sixCameraGlobalHaloWitnessCamera)
      (sixCameraGlobalCoherentHaloProjection
        (sixCameraWhitenedCenteredLogNaimarkSynthesis
          sixCameraCenteredGlobalHaloWitness)) ≠ 0 := by
  rw [externalCameraWhitenedReadout_centeredHalo_eq_neg_returnReadout
    (camera := sixCameraGlobalHaloWitnessCamera)
      (by norm_num [sixCameraGlobalHaloWitnessCamera, cameraLabel])]
  rw [externalCamera8WhitenedReadout_centeredWitness]
  exact neg_ne_zero.mpr sixCameraExternalEightDual_dot_centeredSlopeDefect_ne_zero

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

theorem sixCameraCenteredGlobalHaloProjection_centeredWitness_ne_zero :
    sixCameraGlobalCoherentHaloProjection
        (sixCameraWhitenedCenteredLogNaimarkSynthesis
          sixCameraCenteredGlobalHaloWitness) ≠ 0 := by
  intro hzero
  apply externalCamera8WhitenedReadout_centeredHalo_witness_ne_zero
  rw [hzero, inner_zero_right]

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

theorem externalCamera8WhitenedReadout_cameraReturnCompression_witness :
    externalCameraWhitenedReadout sixCameraGlobalHaloWitnessCamera
        ((cameraReturnCompression sixCameraGram sixCameraFirstMoment
            (cameraLogSlopeDiagonal sixCamera)) *ᵥ
          sixCameraCenteredGlobalHaloWitness) =
      (8 / 139 : ℝ) * (91 * Real.log 2 - 82 * Real.log 3) := by
  rw [← sixCameraWhitenedCrossGram_eq_cameraReturnCompression]
  rw [externalCamera8WhitenedReadout_centeredWitness,
    sixCameraExternalEightDual_dot_centeredSlopeDefect]

theorem externalCamera8WhitenedReadout_cameraReturnCompression_witness_ne_zero :
    externalCameraWhitenedReadout sixCameraGlobalHaloWitnessCamera
        ((cameraReturnCompression sixCameraGram sixCameraFirstMoment
            (cameraLogSlopeDiagonal sixCamera)) *ᵥ
          sixCameraCenteredGlobalHaloWitness) ≠ 0 := by
  rw [externalCamera8WhitenedReadout_cameraReturnCompression_witness]
  apply mul_ne_zero
  · norm_num
  · exact sixCameraExternalEightDual_log_combination_ne_zero

theorem sixCameraGlobalCoherentHaloProjection_centeredLog_not_forall_zero :
    ¬ (∀ c : Fin 6 → ℝ,
      sixCameraGlobalCoherentHaloProjection
          (sixCameraWhitenedCenteredLogNaimarkSynthesis c) = 0) := by
  intro h
  exact sixCameraCenteredGlobalHaloProjection_centeredWitness_ne_zero
    (h sixCameraCenteredGlobalHaloWitness)

theorem sixCameraGlobalCoherentHaloProjection_centeredLog_exists_ne_zero :
    ∃ c : Fin 6 → ℝ,
      sixCameraGlobalCoherentHaloProjection
          (sixCameraWhitenedCenteredLogNaimarkSynthesis c) ≠ 0 :=
  ⟨sixCameraCenteredGlobalHaloWitness,
    sixCameraCenteredGlobalHaloProjection_centeredWitness_ne_zero⟩

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

theorem sixCameraProjection_centeredLog_eq_cameraReturnCompression_synthesis
    (c : Fin 6 → ℝ) :
    sixCameraWhitenedNaimarkProjection
        (sixCameraWhitenedCenteredLogNaimarkSynthesis c) =
      sixCameraWhitenedNaimarkSynthesis
        ((cameraReturnCompression sixCameraGram sixCameraFirstMoment
          (cameraLogSlopeDiagonal sixCamera)) *ᵥ c) := by
  rw [sixCameraProjection_centeredLog_eq_returnSynthesis,
    ← sixCameraWhitenedCrossGram_eq_cameraReturnCompression]

end
end CarrySelfAdjointOperator

