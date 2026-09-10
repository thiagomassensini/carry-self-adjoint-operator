import CarrySelfAdjointOperator.AtlasEnergySixCameraHilbertAsymptoticCrosswalk
import CarrySelfAdjointOperator.CenteredCameraCutoffConvergence
import CarrySelfAdjointOperator.CameraReturnVarianceEnergyBalance
import Mathlib.Tactic
/-!
# Six-camera centered-log Naimark variance crosswalk

This file isolates the exact finite six-camera statement
`D* (I - P) D = sixCameraVariance` in the intrinsic real Naimark space.
Ordinary and centered-log camera vectors are synthesized separately and the
existing positive inverse square root of `sixCameraGram` supplies the
whitening.  The completed all-camera escape remains a distinct typed object;
no identification or new completion is introduced here.
-/

open scoped BigOperators ENNReal MeasureTheory RealInnerProductSpace Matrix MatrixOrder
open Set MeasureTheory Filter intervalIntegral
namespace CarrySelfAdjointOperator
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section
set_option autoImplicit false

 theorem inner_naimarkCameraVector_centeredNaimarkCameraVector (b c : CameraIndex) :
    inner ℝ (naimarkCameraVector b) (centeredNaimarkCameraVector c) =
      gramKernel b c *
        (Real.log (min (cameraSlope (cameraLabel b))
          (cameraSlope (cameraLabel c)) : ℕ) -
          Real.log (cameraSlope (cameraLabel c) : ℕ)) := by
  have hpoint :
      (fun x => inner ℝ (naimarkCameraVector b x)
        (centeredNaimarkCameraVector c x)) =ᵐ[positiveLebesgueMeasure]
      (cameraInterval b ∩ cameraInterval c).indicator
        (fun x => (logarithmicCoordinate x -
          Real.log (cameraSlope (cameraLabel c) : ℝ)) *
          periodicMeanKernel b c) := by
    filter_upwards [naimarkCameraVector_coeFn b,
      centeredNaimarkCameraVector_coeFn c] with x hb hc
    rw [hb, hc]
    by_cases hxb : x ∈ cameraInterval b
    <;> by_cases hxc : x ∈ cameraInterval c
    <;> simp [hxb, hxc, Set.mem_inter_iff, real_inner_smul_right,
      inner_kolmogorovVector]
  have hmeas := (cameraInterval_measurable b).inter (cameraInterval_measurable c)
  have hsubset : cameraInterval b ∩ cameraInterval c ⊆ Ioi 0 :=
    Set.inter_subset_left.trans (cameraInterval_subset_positive b)
  rw [L2.inner_def, integral_congr_ae hpoint, MeasureTheory.integral_indicator hmeas,
    positiveLebesgueMeasure, Measure.restrict_restrict hmeas,
    inter_eq_left.mpr hsubset, MeasureTheory.integral_mul_const]
  have hb : (0 : ℝ) < cameraSlope (cameraLabel b) := by exact_mod_cast cameraSlope_pos b
  have hc : (0 : ℝ) < cameraSlope (cameraLabel c) := by exact_mod_cast cameraSlope_pos c
  simp only [cameraInterval, Ioc_inter_Ioc, max_self]
  let ell : ℝ := min (cameraSlope (cameraLabel b) : ℝ)
    (cameraSlope (cameraLabel c) : ℝ)
  have hell : 0 < ell := by
    dsimp [ell]
    exact lt_min (by exact_mod_cast cameraSlope_pos b)
      (by exact_mod_cast cameraSlope_pos c)
  have hle : ell ≤ cameraSlope (cameraLabel b) := by
    dsimp [ell]
    exact min_le_left _ _
  rw [show min (cameraSlope (cameraLabel b) : ℝ)
      (cameraSlope (cameraLabel c) : ℝ) = ell by rfl]
  rw [← intervalIntegral.integral_of_le hell.le]
  simp only [logarithmicCoordinate]
  rw [intervalIntegral.integral_sub intervalIntegrable_centeredLog_zero
    intervalIntegrable_const, integral_centeredLog_zero hell,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  dsimp [ell]
  have hmin : (min (cameraSlope (cameraLabel b) : ℝ)
      (cameraSlope (cameraLabel c) : ℝ)) =
      ((min (cameraSlope (cameraLabel b))
        (cameraSlope (cameraLabel c)) : ℕ) : ℝ) := by
    exact (Nat.cast_min _ _).symm
  rw [hmin]
  unfold gramKernel
  ring

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera

noncomputable section

 def sixCameraNaimarkSynthesis (c : Fin 6 → ℝ) : NaimarkSpace :=
   ∑ i : Fin 6, c i • naimarkCameraVector (atlasSixCameraIndex i)

 def sixCameraCenteredLogNaimarkSynthesis (c : Fin 6 → ℝ) : NaimarkSpace :=
   ∑ i : Fin 6, c i • centeredNaimarkCameraVector (atlasSixCameraIndex i)

 theorem sixCameraNaimarkSynthesis_inner (c d : Fin 6 → ℝ) :
    inner ℝ (sixCameraNaimarkSynthesis c) (sixCameraNaimarkSynthesis d) =
      c ⬝ᵥ (sixCameraGram *ᵥ d) := by
  classical
  simp only [sixCameraNaimarkSynthesis, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, inner_naimarkCameraVector]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [atlasSixCameraGram_entry_eq_gramKernel]
  ring

 theorem sixCameraCenteredLogNaimarkSynthesis_inner (c d : Fin 6 → ℝ) :
    inner ℝ (sixCameraCenteredLogNaimarkSynthesis c)
      (sixCameraCenteredLogNaimarkSynthesis d) =
      c ⬝ᵥ (sixCameraGram *ᵥ d) := by
  classical
  simp only [sixCameraCenteredLogNaimarkSynthesis, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right,
    inner_centeredNaimarkCameraVector]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [atlasSixCameraGram_entry_eq_gramKernel]
  ring

 theorem sixCameraNaimarkSynthesis_centeredLog_inner_entry
    (i j : Fin 6) :
    inner ℝ (naimarkCameraVector (atlasSixCameraIndex i))
      (centeredNaimarkCameraVector (atlasSixCameraIndex j)) =
      (sixCameraFirstMoment - sixCameraGram * cameraLogSlopeDiagonal sixCamera) i j := by
  rw [inner_naimarkCameraVector_centeredNaimarkCameraVector]
  rw [show (sixCameraFirstMoment - sixCameraGram * cameraLogSlopeDiagonal sixCamera) i j =
      sixCameraGram i j *
        (Real.log (min (cameraSlope (sixCamera i)) (cameraSlope (sixCamera j)) : ℕ) -
          Real.log (cameraSlope (sixCamera j) : ℕ)) by
    rw [← sixCameraFirstMoment_eq, ← sixCameraGram_eq]
    simp only [Matrix.sub_apply, firstMomentMatrix_apply, Matrix.mul_diagonal,
      cameraLogSlopeDiagonal]
    rw [show slopeOverlap sixCamera i j =
        min (cameraSlope (sixCamera i)) (cameraSlope (sixCamera j)) by rfl]
    ring]
  rw [atlasSixCameraGram_entry_eq_gramKernel]
  rfl

 theorem sixCameraNaimarkSynthesis_centeredLog_inner (c d : Fin 6 → ℝ) :
    inner ℝ (sixCameraNaimarkSynthesis c)
      (sixCameraCenteredLogNaimarkSynthesis d) =
      c ⬝ᵥ ((sixCameraFirstMoment -
        sixCameraGram * cameraLogSlopeDiagonal sixCamera) *ᵥ d) := by
  classical
  simp only [sixCameraNaimarkSynthesis, sixCameraCenteredLogNaimarkSynthesis,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [sixCameraNaimarkSynthesis_centeredLog_inner_entry]
  ring

end
end CarrySelfAdjointOperator

namespace CarrySelfAdjointOperator
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
noncomputable section

 def finiteVectorSynthesis (v : Fin 6 → NaimarkSpace) :
      EuclideanSpace ℝ (Fin 6) →ₗ[ℝ] NaimarkSpace where
   toFun c := ∑ i : Fin 6, c.ofLp i • v i
   map_add' c d := by
     simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
   map_smul' a c := by
     change (∑ i : Fin 6, (a * c.ofLp i) • v i) =
       a • ∑ i : Fin 6, c.ofLp i • v i
     calc
       (∑ i : Fin 6, (a * c.ofLp i) • v i) =
           ∑ i : Fin 6, a • (c.ofLp i • v i) := by
         apply Finset.sum_congr rfl
         intro i hi
         rw [smul_smul]
       _ = a • ∑ i : Fin 6, c.ofLp i • v i := by
         symm
         exact Finset.smul_sum

 def sixCameraNaimarkSynthesisLinear :
      EuclideanSpace ℝ (Fin 6) →ₗ[ℝ] NaimarkSpace :=
   finiteVectorSynthesis (fun i => naimarkCameraVector (atlasSixCameraIndex i))

 def sixCameraCenteredLogNaimarkSynthesisLinear :
      EuclideanSpace ℝ (Fin 6) →ₗ[ℝ] NaimarkSpace :=
   finiteVectorSynthesis (fun i => centeredNaimarkCameraVector (atlasSixCameraIndex i))

 theorem sixCameraNaimarkSynthesisLinear_apply (c : EuclideanSpace ℝ (Fin 6)) :
    sixCameraNaimarkSynthesisLinear c = sixCameraNaimarkSynthesis c.ofLp := rfl
 theorem sixCameraCenteredLogNaimarkSynthesisLinear_apply (c : EuclideanSpace ℝ (Fin 6)) :
    sixCameraCenteredLogNaimarkSynthesisLinear c = sixCameraCenteredLogNaimarkSynthesis c.ofLp := rfl

 def sixCameraWhitenedNaimarkSynthesis (c : Fin 6 → ℝ) : NaimarkSpace :=
   sixCameraNaimarkSynthesis (positiveInverseSqrt sixCameraGram *ᵥ c)

 def sixCameraWhitenedCenteredLogNaimarkSynthesis (c : Fin 6 → ℝ) : NaimarkSpace :=
   sixCameraCenteredLogNaimarkSynthesis (positiveInverseSqrt sixCameraGram *ᵥ c)

 theorem sixCameraWhitenedNaimarkSynthesis_inner_matrix (c d : Fin 6 → ℝ) :
    inner ℝ (sixCameraWhitenedNaimarkSynthesis c)
      (sixCameraWhitenedNaimarkSynthesis d) =
      c ⬝ᵥ (((positiveInverseSqrt sixCameraGram)ᵀ *
        sixCameraGram * positiveInverseSqrt sixCameraGram) *ᵥ d) := by
  rw [sixCameraWhitenedNaimarkSynthesis, sixCameraWhitenedNaimarkSynthesis,
    sixCameraNaimarkSynthesis_inner]
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

 theorem sixCameraWhitenedNaimarkSynthesis_inner (c d : Fin 6 → ℝ) :
    inner ℝ (sixCameraWhitenedNaimarkSynthesis c)
      (sixCameraWhitenedNaimarkSynthesis d) = c ⬝ᵥ d := by
  rw [sixCameraWhitenedNaimarkSynthesis_inner_matrix]
  have hR := positiveInverseSqrt_isHermitian sixCameraGram_posDef
  have hRT : (positiveInverseSqrt sixCameraGram)ᵀ =
      positiveInverseSqrt sixCameraGram := by
    ext i j
    simpa only [Matrix.transpose_apply, Matrix.conjTranspose_apply,
      star_trivial] using congr_fun (congr_fun hR.eq i) j
  rw [hRT, positiveInverseSqrt_whitens sixCameraGram_posDef]
  simp

 theorem sixCameraWhitenedCenteredLogNaimarkSynthesis_inner_matrix (c d : Fin 6 → ℝ) :
    inner ℝ (sixCameraWhitenedCenteredLogNaimarkSynthesis c)
      (sixCameraWhitenedCenteredLogNaimarkSynthesis d) =
      c ⬝ᵥ (((positiveInverseSqrt sixCameraGram)ᵀ *
        sixCameraGram * positiveInverseSqrt sixCameraGram) *ᵥ d) := by
  rw [sixCameraWhitenedCenteredLogNaimarkSynthesis,
    sixCameraWhitenedCenteredLogNaimarkSynthesis,
    sixCameraCenteredLogNaimarkSynthesis_inner]
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

 theorem sixCameraWhitenedCenteredLogNaimarkSynthesis_inner (c d : Fin 6 → ℝ) :
    inner ℝ (sixCameraWhitenedCenteredLogNaimarkSynthesis c)
      (sixCameraWhitenedCenteredLogNaimarkSynthesis d) = c ⬝ᵥ d := by
  rw [sixCameraWhitenedCenteredLogNaimarkSynthesis_inner_matrix]
  have hR := positiveInverseSqrt_isHermitian sixCameraGram_posDef
  have hRT : (positiveInverseSqrt sixCameraGram)ᵀ =
      positiveInverseSqrt sixCameraGram := by
    ext i j
    simpa only [Matrix.transpose_apply, Matrix.conjTranspose_apply,
      star_trivial] using congr_fun (congr_fun hR.eq i) j
  rw [hRT, positiveInverseSqrt_whitens sixCameraGram_posDef]
  simp

 def sixCameraWhitenedCrossGram : Matrix (Fin 6) (Fin 6) ℝ :=
   positiveInverseSqrt sixCameraGram *
      (sixCameraFirstMoment - sixCameraGram * cameraLogSlopeDiagonal sixCamera) *
      positiveInverseSqrt sixCameraGram

 theorem sixCameraWhitenedNaimarkSynthesis_centeredLog_inner_matrix
    (c d : Fin 6 → ℝ) :
    inner ℝ (sixCameraWhitenedNaimarkSynthesis c)
      (sixCameraWhitenedCenteredLogNaimarkSynthesis d) =
      c ⬝ᵥ (((positiveInverseSqrt sixCameraGram)ᵀ *
        (sixCameraFirstMoment - sixCameraGram * cameraLogSlopeDiagonal sixCamera) *
        positiveInverseSqrt sixCameraGram) *ᵥ d) := by
  rw [sixCameraWhitenedNaimarkSynthesis,
    sixCameraWhitenedCenteredLogNaimarkSynthesis,
    sixCameraNaimarkSynthesis_centeredLog_inner]
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

 theorem sixCameraWhitenedNaimarkSynthesis_centeredLog_inner
    (c d : Fin 6 → ℝ) :
    inner ℝ (sixCameraWhitenedNaimarkSynthesis c)
      (sixCameraWhitenedCenteredLogNaimarkSynthesis d) =
      c ⬝ᵥ (sixCameraWhitenedCrossGram *ᵥ d) := by
  rw [sixCameraWhitenedNaimarkSynthesis_centeredLog_inner_matrix]
  have hR := positiveInverseSqrt_isHermitian sixCameraGram_posDef
  have hRT : (positiveInverseSqrt sixCameraGram)ᵀ =
      positiveInverseSqrt sixCameraGram := by
    ext i j
    simpa only [Matrix.transpose_apply, Matrix.conjTranspose_apply, star_trivial] using
      congr_fun (congr_fun hR.eq i) j
  rw [hRT]
  rfl

 theorem sixCameraWhitenedCrossGram_eq_cameraReturnCompression :
    sixCameraWhitenedCrossGram =
      cameraReturnCompression sixCameraGram sixCameraFirstMoment
        (cameraLogSlopeDiagonal sixCamera) := by
  rfl


 def sixCameraWhitenedNaimarkAnalysis (x : NaimarkSpace) : Fin 6 → ℝ :=
   fun i =>
     inner ℝ
       (sixCameraWhitenedNaimarkSynthesis (Pi.single i 1)) x

 def sixCameraWhitenedNaimarkProjection (x : NaimarkSpace) : NaimarkSpace :=
   sixCameraWhitenedNaimarkSynthesis
     (sixCameraWhitenedNaimarkAnalysis x)

 def sixCameraWhitenedNaimarkEscape (x : NaimarkSpace) : NaimarkSpace :=
   x - sixCameraWhitenedNaimarkProjection x

 theorem sixCameraWhitenedNaimarkAnalysis_apply_synthesis (c : Fin 6 → ℝ) :
     sixCameraWhitenedNaimarkAnalysis
         (sixCameraWhitenedNaimarkSynthesis c) = c := by
   funext i
   rw [sixCameraWhitenedNaimarkAnalysis]
   rw [sixCameraWhitenedNaimarkSynthesis_inner]
   simp [dotProduct, Pi.single_apply]

 theorem sixCameraWhitenedNaimarkAnalysis_apply_centeredLog (c : Fin 6 → ℝ) :
     sixCameraWhitenedNaimarkAnalysis
         (sixCameraWhitenedCenteredLogNaimarkSynthesis c) =
       sixCameraWhitenedCrossGram *ᵥ c := by
   funext i
   rw [sixCameraWhitenedNaimarkAnalysis]
   rw [sixCameraWhitenedNaimarkSynthesis_centeredLog_inner]
   simp [dotProduct, Pi.single_apply]

 theorem sixCameraWhitenedNaimarkEscape_centeredLog (c : Fin 6 → ℝ) :
     sixCameraWhitenedNaimarkEscape
         (sixCameraWhitenedCenteredLogNaimarkSynthesis c) =
       sixCameraWhitenedCenteredLogNaimarkSynthesis c -
         sixCameraWhitenedNaimarkSynthesis
           (sixCameraWhitenedCrossGram *ᵥ c) := by
   rw [sixCameraWhitenedNaimarkEscape, sixCameraWhitenedNaimarkProjection,
     sixCameraWhitenedNaimarkAnalysis_apply_centeredLog]


 theorem realSixCameraMatrixGramPair (B : Matrix (Fin 6) (Fin 6) ℝ)
    (u v : Fin 6 → ℝ) :
    (B *ᵥ u) ⬝ᵥ (B *ᵥ v) =
      u ⬝ᵥ ((Bᴴ * B) *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec]
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [Matrix.dotProduct_transpose_mulVec]
  rw [dotProduct_comm]


 theorem inner_sub_sub_expansion {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y z w : E) :
    inner ℝ (x - y) (z - w) =
      inner ℝ x z - inner ℝ x w - inner ℝ y z + inner ℝ y w := by
  simp only [inner_sub_left, inner_sub_right]
  ring

 theorem sixCameraWhitenedNaimarkEscape_centeredLog_inner
    (u v : Fin 6 → ℝ) :
    inner ℝ
        (sixCameraWhitenedNaimarkEscape
          (sixCameraWhitenedCenteredLogNaimarkSynthesis u))
        (sixCameraWhitenedNaimarkEscape
          (sixCameraWhitenedCenteredLogNaimarkSynthesis v)) =
      u ⬝ᵥ (sixCameraVariance *ᵥ v) := by
  rw [sixCameraWhitenedNaimarkEscape_centeredLog,
    sixCameraWhitenedNaimarkEscape_centeredLog]
  have hDD :
      inner ℝ (sixCameraWhitenedCenteredLogNaimarkSynthesis u)
        (sixCameraWhitenedCenteredLogNaimarkSynthesis v) =
        u ⬝ᵥ v := by
    exact sixCameraWhitenedCenteredLogNaimarkSynthesis_inner u v |>.trans rfl
  have hUU (a b : Fin 6 → ℝ) :
      inner ℝ (sixCameraWhitenedNaimarkSynthesis a)
        (sixCameraWhitenedNaimarkSynthesis b) = a ⬝ᵥ b := by
    rw [sixCameraWhitenedNaimarkSynthesis_inner_matrix]
    have hR := positiveInverseSqrt_isHermitian sixCameraGram_posDef
    have hRT : (positiveInverseSqrt sixCameraGram)ᵀ =
        positiveInverseSqrt sixCameraGram := by
      ext i j
      simpa only [Matrix.transpose_apply, Matrix.conjTranspose_apply, star_trivial] using
        congr_fun (congr_fun hR.eq i) j
    rw [hRT, positiveInverseSqrt_whitens sixCameraGram_posDef]
    simp
  have hUD (a b : Fin 6 → ℝ) :
      inner ℝ (sixCameraWhitenedNaimarkSynthesis a)
        (sixCameraWhitenedCenteredLogNaimarkSynthesis b) =
        a ⬝ᵥ (sixCameraWhitenedCrossGram *ᵥ b) := by
    exact sixCameraWhitenedNaimarkSynthesis_centeredLog_inner a b
  have hDU (a b : Fin 6 → ℝ) :
      inner ℝ (sixCameraWhitenedCenteredLogNaimarkSynthesis a)
        (sixCameraWhitenedNaimarkSynthesis b) =
        b ⬝ᵥ (sixCameraWhitenedCrossGram *ᵥ a) := by
    rw [real_inner_comm, hUD]
  calc
    inner ℝ
        (sixCameraWhitenedCenteredLogNaimarkSynthesis u -
          sixCameraWhitenedNaimarkSynthesis
            (sixCameraWhitenedCrossGram *ᵥ u))
        (sixCameraWhitenedCenteredLogNaimarkSynthesis v -
          sixCameraWhitenedNaimarkSynthesis
            (sixCameraWhitenedCrossGram *ᵥ v)) =
      inner ℝ (sixCameraWhitenedCenteredLogNaimarkSynthesis u)
          (sixCameraWhitenedCenteredLogNaimarkSynthesis v) -
        inner ℝ (sixCameraWhitenedCenteredLogNaimarkSynthesis u)
          (sixCameraWhitenedNaimarkSynthesis
            (sixCameraWhitenedCrossGram *ᵥ v)) -
        inner ℝ (sixCameraWhitenedNaimarkSynthesis
            (sixCameraWhitenedCrossGram *ᵥ u))
          (sixCameraWhitenedCenteredLogNaimarkSynthesis v) +
        inner ℝ (sixCameraWhitenedNaimarkSynthesis
            (sixCameraWhitenedCrossGram *ᵥ u))
          (sixCameraWhitenedNaimarkSynthesis
            (sixCameraWhitenedCrossGram *ᵥ v)) := by
            exact inner_sub_sub_expansion _ _ _ _
    _ = u ⬝ᵥ v -
        (sixCameraWhitenedCrossGram *ᵥ v) ⬝ᵥ
          (sixCameraWhitenedCrossGram *ᵥ u) -
        (sixCameraWhitenedCrossGram *ᵥ u) ⬝ᵥ
          (sixCameraWhitenedCrossGram *ᵥ v) +
        (sixCameraWhitenedCrossGram *ᵥ u) ⬝ᵥ
          (sixCameraWhitenedCrossGram *ᵥ v) := by
            rw [hDD, hDU, hUD, hUU]
    _ = u ⬝ᵥ v -
        (sixCameraWhitenedCrossGram *ᵥ u) ⬝ᵥ
        (sixCameraWhitenedCrossGram *ᵥ v) := by
            rw [dotProduct_comm
              (sixCameraWhitenedCrossGram *ᵥ v)
              (sixCameraWhitenedCrossGram *ᵥ u)]
            ring
    _ = u ⬝ᵥ v -
        u ⬝ᵥ ((sixCameraWhitenedCrossGramᴴ *
          sixCameraWhitenedCrossGram) *ᵥ v) := by
            rw [realSixCameraMatrixGramPair]
    _ = u ⬝ᵥ (sixCameraVariance *ᵥ v) := by
      have hmat :
          (1 : Matrix (Fin 6) (Fin 6) ℝ) -
              (sixCameraWhitenedCrossGramᴴ * sixCameraWhitenedCrossGram) =
            sixCameraVariance := by
        have hp :
            sixCameraWhitenedCrossGramᴴ * sixCameraWhitenedCrossGram +
                sixCameraVariance =
              (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
          simpa [sixCameraWhitenedCrossGram_eq_cameraReturnCompression] using
            (sixCamera_return_variance_partition)
        calc
          (1 : Matrix (Fin 6) (Fin 6) ℝ) -
                sixCameraWhitenedCrossGramᴴ * sixCameraWhitenedCrossGram =
              (sixCameraWhitenedCrossGramᴴ * sixCameraWhitenedCrossGram +
                sixCameraVariance) -
                sixCameraWhitenedCrossGramᴴ * sixCameraWhitenedCrossGram := by
                  rw [hp]
          _ = sixCameraVariance := by abel
      have hvec :
          v - (sixCameraWhitenedCrossGramᴴ *
            sixCameraWhitenedCrossGram) *ᵥ v =
            sixCameraVariance *ᵥ v := by
        calc
          v - (sixCameraWhitenedCrossGramᴴ *
              sixCameraWhitenedCrossGram) *ᵥ v =
              (1 : Matrix (Fin 6) (Fin 6) ℝ) *ᵥ v -
                (sixCameraWhitenedCrossGramᴴ *
                  sixCameraWhitenedCrossGram) *ᵥ v := by
                    rw [Matrix.one_mulVec]
          _ = ((1 : Matrix (Fin 6) (Fin 6) ℝ) -
                sixCameraWhitenedCrossGramᴴ *
                  sixCameraWhitenedCrossGram) *ᵥ v := by
                    rw [Matrix.sub_mulVec]
          _ = sixCameraVariance *ᵥ v := by rw [hmat]
      rw [← dotProduct_sub u v ((sixCameraWhitenedCrossGramᴴ * sixCameraWhitenedCrossGram) *ᵥ v), hvec]

 theorem sixCameraWhitenedNaimarkProjection_apply_synthesis
    (c : Fin 6 → ℝ) :
    sixCameraWhitenedNaimarkProjection
        (sixCameraWhitenedNaimarkSynthesis c) =
      sixCameraWhitenedNaimarkSynthesis c := by
  rw [sixCameraWhitenedNaimarkProjection,
    sixCameraWhitenedNaimarkAnalysis_apply_synthesis]

 theorem sixCameraWhitenedNaimarkProjection_idempotent
    (x : NaimarkSpace) :
    sixCameraWhitenedNaimarkProjection
        (sixCameraWhitenedNaimarkProjection x) =
      sixCameraWhitenedNaimarkProjection x := by
  rw [sixCameraWhitenedNaimarkProjection, sixCameraWhitenedNaimarkProjection]
  rw [sixCameraWhitenedNaimarkAnalysis_apply_synthesis]

 theorem sixCameraWhitenedNaimarkEscape_apply_synthesis
    (c : Fin 6 → ℝ) :
    sixCameraWhitenedNaimarkEscape
        (sixCameraWhitenedNaimarkSynthesis c) = 0 := by
  rw [sixCameraWhitenedNaimarkEscape, sixCameraWhitenedNaimarkProjection_apply_synthesis]
  exact sub_self _


/-- The reverse mixed pairing is obtained by real symmetry. -/
theorem inner_centeredNaimarkCameraVector_naimarkCameraVector
    (b c : CameraIndex) :
    inner ℝ (centeredNaimarkCameraVector b) (naimarkCameraVector c) =
      gramKernel c b *
        (Real.log (min (cameraSlope (cameraLabel c))
          (cameraSlope (cameraLabel b)) : ℕ) -
          Real.log (cameraSlope (cameraLabel b) : ℕ)) := by
  rw [real_inner_comm, inner_naimarkCameraVector_centeredNaimarkCameraVector]

/-- The squared norm of the finite Naimark escape is the variance quadratic
form. -/
theorem sixCameraWhitenedNaimarkEscape_centeredLog_norm_sq
    (u : Fin 6 → ℝ) :
    ‖sixCameraWhitenedNaimarkEscape
        (sixCameraWhitenedCenteredLogNaimarkSynthesis u)‖ ^ 2 =
      u ⬝ᵥ (sixCameraVariance *ᵥ u) := by
  rw [← real_inner_self_eq_norm_sq]
  exact sixCameraWhitenedNaimarkEscape_centeredLog_inner u u

/-- The positive square-root amplitude has the same quadratic energy. -/
theorem sixCameraWhitenedCenteredLog_variance_sqrt_pair
    (u : Fin 6 → ℝ) :
    (CFC.sqrt sixCameraVariance *ᵥ u) ⬝ᵥ
        (CFC.sqrt sixCameraVariance *ᵥ u) =
      u ⬝ᵥ (sixCameraVariance *ᵥ u) := by
  rw [realSixCameraMatrixGramPair]
  rw [sixCamera_variance_sqrt_gram]

end
end CarrySelfAdjointOperator
