import CarrySelfAdjointOperator.C3ReturnCompletedTraceChannels
import NativeCarrySpectralWeyl.Finite.StepDensity

/-!
# Intrinsic return and variance energy balance

The camera moment geometry supplies both positive pieces of the identity.
These theorems retain them together and recover the original camera metric.
No target characteristic, response, height moments, or spectral list is used.
-/

open scoped BigOperators Matrix MatrixOrder

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera
open CPFormal.Analytic.Cp

noncomputable section
set_option autoImplicit false

local notation "A₆" => cameraReturnCompression sixCameraGram sixCameraFirstMoment
  (cameraLogSlopeDiagonal sixCamera)
local notation "S₆" => CFC.sqrt sixCameraVariance

/-- Centering each camera by its own logarithmic boundary slope preserves
the complete Gram, including mixed-camera terms. This is the matrix form
of the intrinsic centered logarithmic profile, for every finite atlas. -/
theorem camera_boundaryCentered_momentGram_eq_gram
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (period : ℕ) (camera : ι → ℕ) :
    secondCenteredMomentMatrix period camera -
        firstMomentMatrix period camera * cameraLogSlopeDiagonal camera -
        cameraLogSlopeDiagonal camera * firstMomentMatrix period camera +
        cameraLogSlopeDiagonal camera * periodicGramMatrix period camera *
          cameraLogSlopeDiagonal camera =
      periodicGramMatrix period camera := by
  have h := camera_secondMoment_sub_gram_eq_slope_identity period camera
  calc
    _ = secondCenteredMomentMatrix period camera -
        (cameraLogSlopeDiagonal camera * firstMomentMatrix period camera +
          firstMomentMatrix period camera * cameraLogSlopeDiagonal camera -
          cameraLogSlopeDiagonal camera * periodicGramMatrix period camera *
            cameraLogSlopeDiagonal camera) := by abel
    _ = _ := by rw [← h]; abel

/-- The two positive effects add to the identity in whitened coordinates. -/
theorem sixCamera_return_variance_partition :
    A₆ᴴ * A₆ + sixCameraVariance = 1 := by
  have h := camera_one_sub_variance_eq_return_square
    420 sixCamera (by simpa [sixCameraGram_eq] using sixCameraGram_posDef)
  rw [sixCameraGram_eq, sixCameraFirstMoment_eq,
    sixCameraSecondCenteredMoment_eq] at h
  change 1 - sixCameraVariance = A₆ᴴ * A₆ at h
  rw [← h]
  abel

/-- The positive square root of the existing variance gives its intrinsic
amplitude. No external scalar normalization is selected. -/
theorem sixCamera_variance_sqrt_gram :
    S₆ᴴ * S₆ = sixCameraVariance := by
  have hs : Matrix.IsHermitian S₆ :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg sixCameraVariance)).isHermitian
  rw [hs.eq, ← pow_two]
  exact CFC.sq_sqrt sixCameraVariance sixCameraVariance_posSemidef.nonneg

theorem sixCamera_return_variance_sqrt_partition :
    A₆ᴴ * A₆ + S₆ᴴ * S₆ = 1 := by
  rw [sixCamera_variance_sqrt_gram]
  exact sixCamera_return_variance_partition

/-- Exact reconstruction from the pair of intrinsic amplitudes. -/
theorem sixCamera_return_variance_reconstruction (u : Fin 6 → ℝ) :
    A₆ᴴ *ᵥ (A₆ *ᵥ u) + S₆ᴴ *ᵥ (S₆ *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec,
    sixCamera_return_variance_sqrt_partition, Matrix.one_mulVec]

private theorem real_matrix_gram_pair
    (B : Matrix (Fin 6) (Fin 6) ℝ) (u v : Fin 6 → ℝ) :
    (B *ᵥ u) ⬝ᵥ (B *ᵥ v) = u ⬝ᵥ ((Bᴴ * B) *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

/-- All real cross products survive the two-channel analysis. -/
theorem sixCamera_return_variance_polarization (u v : Fin 6 → ℝ) :
    (A₆ *ᵥ u) ⬝ᵥ (A₆ *ᵥ v) + (S₆ *ᵥ u) ⬝ᵥ (S₆ *ᵥ v) = u ⬝ᵥ v := by
  rw [real_matrix_gram_pair, real_matrix_gram_pair, ← dotProduct_add,
    ← Matrix.add_mulVec, sixCamera_return_variance_sqrt_partition,
    Matrix.one_mulVec]

/-- Parseval energy identity derived from the original camera moments. -/
theorem sixCamera_return_variance_energy (u : Fin 6 → ℝ) :
    (∑ i, (A₆ *ᵥ u) i ^ 2) + (∑ i, (S₆ *ᵥ u) i ^ 2) =
      ∑ i, u i ^ 2 := by
  simpa only [dotProduct, pow_two] using sixCamera_return_variance_polarization u u

/-- No camera direction is lost when the two amplitudes are retained. -/
theorem sixCamera_return_variance_pair_injective :
    Function.Injective (fun u : Fin 6 → ℝ => (A₆ *ᵥ u, S₆ *ᵥ u)) := by
  intro u v h
  have ha := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  dsimp only at ha hs
  rw [← sixCamera_return_variance_reconstruction u,
    ← sixCamera_return_variance_reconstruction v, ha, hs]

/-- A direction invisible to the return defect is fixed by the variance.
This explains why the return-only obstruction does not imply energy loss
in the complete camera geometry. -/
theorem sixCamera_variance_fixes_return_kernel
    (u : Fin 6 → ℝ) (hu : A₆ *ᵥ u = 0) :
    sixCameraVariance *ᵥ u = u := by
  have h := congrArg (fun B : Matrix (Fin 6) (Fin 6) ℝ => B *ᵥ u)
    sixCamera_return_variance_partition
  simpa only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hu,
    Matrix.mulVec_zero, zero_add, Matrix.one_mulVec] using h

/-- The variance amplitude preserves the full energy on a return-blind
direction, even without identifying that amplitude with the vector itself. -/
theorem sixCamera_variance_energy_on_return_kernel
    (u : Fin 6 → ℝ) (hu : A₆ *ᵥ u = 0) :
    (∑ i, (S₆ *ᵥ u) i ^ 2) = ∑ i, u i ^ 2 := by
  have h := sixCamera_return_variance_energy u
  simpa only [hu, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, zero_add] using h

/-- The camera-7 trace pulse from the preceding audit lives in the variance
channel with its full whitened vector preserved by the variance effect. -/
theorem c3LastPulse_variance_fixed (s : ℂ) (a : ℝ) :
    sixCameraVariance *ᵥ
      (CFC.sqrt sixCameraGram *ᵥ
        ![0, 0, (3 : ℝ) ^ (-criticalDisplacement s.re) * a, 0, 0, a]) =
      CFC.sqrt sixCameraGram *ᵥ
        ![0, 0, (3 : ℝ) ^ (-criticalDisplacement s.re) * a, 0, 0, a] := by
  apply sixCamera_variance_fixes_return_kernel
  exact c3LastPulse_returnCompression_zero s a

/-- The same geometry retains the camera-5 initial pulse in the variance
channel. Both legs of the Green port are present. -/
theorem c3InitialPulse_variance_fixed (s : ℂ) (a : ℝ) :
    sixCameraVariance *ᵥ
      (CFC.sqrt sixCameraGram *ᵥ
        ![(3 : ℝ) ^ (-criticalDisplacement s.re) * a, 0, 0, a, 0, 0]) =
      CFC.sqrt sixCameraGram *ᵥ
        ![(3 : ℝ) ^ (-criticalDisplacement s.re) * a, 0, 0, a, 0, 0] := by
  apply sixCamera_variance_fixes_return_kernel
  apply sixCameraReturnCompression_annihilates_cameraSixZero
  simp

/-- In the original coefficient coordinates, the preserved form is exactly
G, including its off-diagonal camera correlations. -/
theorem sixCamera_return_variance_source_gram (c d : Fin 6 → ℝ) :
    (A₆ *ᵥ (CFC.sqrt sixCameraGram *ᵥ c)) ⬝ᵥ
        (A₆ *ᵥ (CFC.sqrt sixCameraGram *ᵥ d)) +
      (S₆ *ᵥ (CFC.sqrt sixCameraGram *ᵥ c)) ⬝ᵥ
        (S₆ *ᵥ (CFC.sqrt sixCameraGram *ᵥ d)) =
      c ⬝ᵥ (sixCameraGram *ᵥ d) := by
  rw [sixCamera_return_variance_polarization, real_matrix_gram_pair]
  have hs : (CFC.sqrt sixCameraGram).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg sixCameraGram)).isHermitian
  rw [hs.eq, ← pow_two, CFC.sq_sqrt sixCameraGram sixCameraGram_posDef.posSemidef.nonneg]


/-- Riesz coordinates of the existing horizontal trace c_7 - c_6.
These are forced by G q = e_7 - e_6, not by a moment target. -/
theorem sixCamera_valueTrace_dual_equation :
    sixCameraGram *ᵥ
      ![(9/139 : ℝ), 9/278, -3/139, 0, -9/278, 1/42] =
      ![0, 0, 0, 0, -1, 1] := by
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      sixCameraGram, sixCameraGramRat]

/-- The dual trace direction is the sum of a mixed-return component and
one universal camera component, with their exact geometric coefficients. -/
theorem sixCamera_valueTrace_dual_decomposition :
    (![(9/139 : ℝ), 9/278, -3/139, 0, -9/278, 1/42] : Fin 6 → ℝ) =
      (-3/278 : ℝ) • sixCameraMixedReturnRay +
        (1/42 : ℝ) • ![0, 0, 0, 0, 0, 1] := by
  ext i
  fin_cases i <;> norm_num [sixCameraMixedReturnRay]

/-- Its squared dual norm is fixed by the same period-derived Gram. -/
theorem sixCamera_valueTrace_dual_norm_sq :
    (![(9/139 : ℝ), 9/278, -3/139, 0, -9/278, 1/42] : Fin 6 → ℝ) ⬝ᵥ
      (sixCameraGram *ᵥ
        ![(9/139 : ℝ), 9/278, -3/139, 0, -9/278, 1/42]) =
      (164/2919 : ℝ) := by
  rw [sixCamera_valueTrace_dual_equation]
  norm_num [dotProduct, Fin.sum_univ_succ]

/-- Pairing against the dual vector reads the trace in the original source
coordinates, including all camera correlations in G. -/
theorem sixCamera_valueTrace_dual_readout (c : Fin 6 → ℝ) :
    (![(9/139 : ℝ), 9/278, -3/139, 0, -9/278, 1/42] : Fin 6 → ℝ) ⬝ᵥ
      (sixCameraGram *ᵥ c) = c 5 - c 4 := by
  have hsym : sixCameraGramᵀ = sixCameraGram := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      sixCameraGram_posDef.isHermitian.eq
  nth_rw 1 [← hsym]
  rw [Matrix.dotProduct_transpose_mulVec, sixCamera_valueTrace_dual_equation]
  simp [dotProduct, Fin.sum_univ_succ]
  ring

private theorem cameras2368_return_cross_means :
    periodicProductMean 24 2 8 = 2 ∧
    periodicProductMean 24 3 6 = 2 ∧
    periodicProductMean 24 3 8 = 0 := by
  norm_num [periodicProductMean, periodicProductSum, profile, c2Profile,
    oddProfile, evenProfile, dvdIndicator, Finset.sum_range_succ]

/-- The original periodic profiles already acquire a second return direction
on the atlas 2,3,6,8. This is a nonzero minor of H - G T, before whitening. -/
theorem cameras2368_returnNumerator_minor :
    let camera : Fin 4 → ℕ := ![2, 3, 6, 8]
    let D := firstMomentMatrix 24 camera -
      periodicGramMatrix 24 camera * cameraLogSlopeDiagonal camera
    D 0 2 * D 1 3 - D 0 3 * D 1 2 = -48 * (Real.log 2) ^ 2 := by
  dsimp only
  have hc2 : (![2, 3, 6, 8] : Fin 4 → ℕ) 2 = 6 := rfl
  have hc3 : (![2, 3, 6, 8] : Fin 4 → ℕ) 3 = 8 := rfl
  have h28 := cameras2368_return_cross_means.1
  have h36 := cameras2368_return_cross_means.2.1
  have h38 := cameras2368_return_cross_means.2.2
  simp only [Matrix.sub_apply, cameraLogSlopeDiagonal, Matrix.mul_diagonal,
    firstMomentMatrix_apply, periodicGramMatrix_apply, slopeOverlap]
  norm_num [hc2, hc3, cameraSlope, h28, h36, h38]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [hlog4, hlog8, hlog6]
  ring
/-- The minor is nonzero without numerical logarithm estimates. -/
theorem cameras2368_returnNumerator_minor_ne_zero :
    let camera : Fin 4 → ℕ := ![2, 3, 6, 8]
    let D := firstMomentMatrix 24 camera -
      periodicGramMatrix 24 camera * cameraLogSlopeDiagonal camera
    D 0 2 * D 1 3 - D 0 3 * D 1 2 ≠ 0 := by
  dsimp only
  rw [cameras2368_returnNumerator_minor]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ (ne_of_gt (Real.log_pos (by norm_num))))

/-- The raw return numerator on this atlas cannot be a single outer product.
This certificate concerns finite camera directions, not the rank of a
spectral orbit or an assertion of unbounded rank over all atlases. -/
theorem cameras2368_returnNumerator_not_rank_one :
    let camera : Fin 4 → ℕ := ![2, 3, 6, 8]
    let D := firstMomentMatrix 24 camera -
      periodicGramMatrix 24 camera * cameraLogSlopeDiagonal camera
    ¬ ∃ u v : Fin 4 → ℝ, D = Matrix.vecMulVec u v := by
  dsimp only
  rintro ⟨u, v, h⟩
  have hm := cameras2368_returnNumerator_minor_ne_zero
  dsimp only at hm
  apply hm
  rw [h]
  simp only [Matrix.vecMulVec_apply]
  ring

end
end CarrySelfAdjointOperator
