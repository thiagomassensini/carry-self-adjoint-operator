import NativeCarrySpectralWeyl.Finite.Whitening
import Mathlib.Tactic

/-!
# Camera return variance defect

The source logarithmic moments satisfy an exact slope identity. It makes the
complement of the whitened variance a positive square, providing a concrete
return-energy operator for the native camera geometry. These moments use the
camera logarithmic coordinate; no identification with the completed native
height moments is asserted.
-/

open scoped BigOperators Matrix

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Physical logarithmic slopes in the original camera coordinates. -/
def cameraLogSlopeDiagonal {ι : Type*} [DecidableEq ι]
    (camera : ι → ℕ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => Real.log (cameraSlope (camera i)))

/-- The min-slope moment formulas determine the complete second-moment
correction for any finite family of camera profiles. -/
theorem camera_secondMoment_sub_gram_eq_slope_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (period : ℕ) (camera : ι → ℕ) :
    secondCenteredMomentMatrix period camera - periodicGramMatrix period camera =
      cameraLogSlopeDiagonal camera * firstMomentMatrix period camera +
      firstMomentMatrix period camera * cameraLogSlopeDiagonal camera -
      cameraLogSlopeDiagonal camera * periodicGramMatrix period camera *
        cameraLogSlopeDiagonal camera := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, cameraLogSlopeDiagonal,
    Matrix.diagonal_mul, Matrix.mul_diagonal, firstMomentMatrix_apply,
    secondCenteredMomentMatrix_apply, slopeOverlap]
  rcases le_total (cameraSlope (camera i)) (cameraSlope (camera j)) with hij | hji
  · rw [min_eq_left hij]
    ring
  · rw [min_eq_right hji]
    ring

/-- Return compression in whitened camera coordinates. The order `H - G T`
is fixed by the right action of the raw slope operator. -/
def cameraReturnCompression {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H T : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  positiveInverseSqrt G * (H - G * T) * positiveInverseSqrt G

/-- Algebraic factorization before whitening, with the two transposed factors
kept in their correct order. -/
theorem camera_varianceDefect_factorization
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G H J T : Matrix ι ι ℝ} (hG : G.PosDef)
    (hMoment : J - G = T * H + H * T - T * G * T) :
    G - J + H * G⁻¹ * H = (T * G - H) * G⁻¹ * (G * T - H) := by
  letI := hG.isUnit.invertible
  have hGG : G * G⁻¹ = 1 := Matrix.mul_inv_of_invertible G
  have hIG : G⁻¹ * G = 1 := Matrix.inv_mul_of_invertible G
  have hJ : J = G + (T * H + H * T - T * G * T) := by
    rw [← hMoment]
    abel
  rw [hJ]
  calc
    _ = T * G * T - T * H - H * T + H * G⁻¹ * H := by noncomm_ring
    _ = T * (G * G⁻¹) * G * T - T * (G * G⁻¹) * H -
          H * (G⁻¹ * G) * T + H * G⁻¹ * H := by rw [hGG, hIG]; simp
    _ = _ := by noncomm_ring

/-- The missing complement of variance is exactly the square of the return
compression, provided the source moment identity holds. -/
theorem one_sub_varianceOperator_eq_returnCompression_square
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G H J T : Matrix ι ι ℝ} (hG : G.PosDef)
    (hH : H.IsHermitian) (hT : T.IsHermitian)
    (hMoment : J - G = T * H + H * T - T * G * T) :
    1 - varianceOperator G H J =
      (cameraReturnCompression G H T)ᴴ * cameraReturnCompression G H T := by
  have hR := positiveInverseSqrt_isHermitian hG
  have hRR := positiveInverseSqrt_mul_self hG
  rw [varianceOperator_eq_whitened_schur hG]
  rw [← positiveInverseSqrt_whitens hG]
  unfold whitenedMatrix momentSchurComplement cameraReturnCompression
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
    hR.eq, hG.isHermitian.eq, hH.eq, hT.eq]
  have hf := camera_varianceDefect_factorization hG hMoment
  calc
    _ = positiveInverseSqrt G * (G - J + H * G⁻¹ * H) *
          positiveInverseSqrt G := by noncomm_ring
    _ = positiveInverseSqrt G * ((T * G - H) * G⁻¹ * (G * T - H)) *
          positiveInverseSqrt G := by rw [hf]
    _ = positiveInverseSqrt G * ((H - T * G) * G⁻¹ * (H - G * T)) *
          positiveInverseSqrt G := by noncomm_ring
    _ = positiveInverseSqrt G * ((H - T * G) *
          (positiveInverseSqrt G * positiveInverseSqrt G) * (H - G * T)) *
          positiveInverseSqrt G := by rw [hRR]
    _ = _ := by noncomm_ring

/-- The period-derived camera moments satisfy the return-square identity;
positive definiteness is needed only to invert their own Gram. -/
theorem camera_one_sub_variance_eq_return_square
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (period : ℕ) (camera : ι → ℕ)
    (hG : (periodicGramMatrix period camera).PosDef) :
    1 - varianceOperator (periodicGramMatrix period camera)
        (firstMomentMatrix period camera) (secondCenteredMomentMatrix period camera) =
      (cameraReturnCompression (periodicGramMatrix period camera)
        (firstMomentMatrix period camera) (cameraLogSlopeDiagonal camera))ᴴ *
      cameraReturnCompression (periodicGramMatrix period camera)
        (firstMomentMatrix period camera) (cameraLogSlopeDiagonal camera) := by
  apply one_sub_varianceOperator_eq_returnCompression_square hG
    (firstMomentMatrix_isHermitian period camera)
  · exact Matrix.isHermitian_diagonal (fun i => Real.log (cameraSlope (camera i)))
  · exact camera_secondMoment_sub_gram_eq_slope_identity period camera

/-- In the six-camera package, positivity of the complement follows from the
actual period-420 Gram, without a new positivity assumption. -/
theorem sixCamera_one_sub_variance_posSemidef :
    (1 - sixCameraVariance).PosSemidef := by
  have hG : (periodicGramMatrix 420 sixCamera).PosDef := by
    rw [sixCameraGram_eq]
    exact sixCameraGram_posDef
  have h := camera_one_sub_variance_eq_return_square 420 sixCamera hG
  rw [sixCameraGram_eq, sixCameraFirstMoment_eq, sixCameraSecondCenteredMoment_eq] at h
  change (1 - varianceOperator sixCameraGram sixCameraFirstMoment
    sixCameraSecondCenteredMoment).PosSemidef
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The exact mixed return ray in raw camera coordinates, ordered 2 through 7. -/
def sixCameraMixedReturnRay : Fin 6 → ℝ := ![-6, -3, 2, 0, 3, 0]

/-- Its Gram image is supported only at camera 6. Consequently it is
Gram-orthogonal to the other five raw camera axes. -/
theorem sixCameraGram_mul_mixedReturnRay :
    sixCameraGram *ᵥ sixCameraMixedReturnRay = ![0, 0, 0, 0, 278 / 3, 0] := by
  ext i
  fin_cases i <;> norm_num [sixCameraGram, sixCameraGramRat,
    sixCameraMixedReturnRay, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Exact squared length of the mixed ray in its source Gram metric. -/
theorem sixCameraMixedReturnRay_gram_norm_sq :
    sixCameraMixedReturnRay ⬝ᵥ (sixCameraGram *ᵥ sixCameraMixedReturnRay) = 278 := by
  rw [sixCameraGram_mul_mixedReturnRay]
  norm_num [sixCameraMixedReturnRay, dotProduct, Fin.sum_univ_succ]

end
end CarrySelfAdjointOperator
