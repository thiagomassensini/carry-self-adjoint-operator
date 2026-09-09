import CarrySelfAdjointOperator.NewtonStirlingOperatorIntertwining
import CarrySelfAdjointOperator.FiniteEnrichedCameraState

/-!
# Finite native depth commutator and enriched camera decomposition

This module keeps the finite real matrix layer separate from the complex
Dirichlet readout.  The shift is the truncated shift `S e_j = e_(j-1)`;
the depth multiplier is diagonal in the same basis.  The resulting Ore
identity is exact at every finite size.  The camera decomposition is the
existing Parseval reconstruction, applied to this concrete commutator.
-/

open scoped Matrix

namespace CarrySelfAdjointOperator

open NativeCarryC3Crosswalk

noncomputable section

/-! ## Finite depth matrices -/

/-- Truncated shift: column `j` is sent to row `j-1`. -/
def finiteDepthShift (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i.val + 1 = j.val then 1 else 0

/-- Multiplication by the finite depth coordinate. -/
def finiteDepthIndex (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => (i.val : ℝ))

/-- The weighted first difference in a finite real prefix. -/
def finiteDepthDifference (q : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  q⁻¹ • finiteDepthShift N - 1

/-- Logarithmic depth multiplication on the same finite prefix. -/
def finiteDepthLogMultiplication (p : ℕ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (Real.log (p : ℝ)) • finiteDepthIndex N

/-- The finite real commutator before phase normalization. -/
def finiteNativeDepthCommutator (p : ℕ) (q : ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  finiteDepthDifference q N * finiteDepthLogMultiplication p N -
    finiteDepthLogMultiplication p N * finiteDepthDifference q N

theorem finiteDepthShift_index_commutator (N : ℕ) :
    finiteDepthShift N * finiteDepthIndex N -
        finiteDepthIndex N * finiteDepthShift N =
      finiteDepthShift N := by
  ext i j
  by_cases h : i.val + 1 = j.val
  · have hcast : (j.val : ℝ) = (i.val : ℝ) + 1 := by
      exact_mod_cast h.symm
    simp [h, finiteDepthShift, finiteDepthIndex, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    rw [hcast]
    ring
  · simp [h, finiteDepthShift, finiteDepthIndex, Matrix.mul_diagonal,
      Matrix.diagonal_mul]

theorem finiteDepthDifference_index_commutator
    (N : ℕ) (q : ℝ) :
    finiteDepthDifference q N * finiteDepthIndex N -
        finiteDepthIndex N * finiteDepthDifference q N =
      finiteDepthDifference q N + 1 := by
  unfold finiteDepthDifference
  calc
    (q⁻¹ • finiteDepthShift N - 1) * finiteDepthIndex N -
        finiteDepthIndex N * (q⁻¹ • finiteDepthShift N - 1) =
      q⁻¹ •
        (finiteDepthShift N * finiteDepthIndex N -
          finiteDepthIndex N * finiteDepthShift N) := by
            simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
              Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_sub]
            noncomm_ring
    _ = q⁻¹ • finiteDepthShift N := by
      rw [finiteDepthShift_index_commutator]
    _ = q⁻¹ • finiteDepthShift N - 1 + 1 := by
      simp

theorem finiteDepthDifference_logMultiplication_commutator
    (p N : ℕ) (q : ℝ) :
    finiteDepthDifference q N * finiteDepthLogMultiplication p N -
        finiteDepthLogMultiplication p N * finiteDepthDifference q N =
      (Real.log (p : ℝ)) • (finiteDepthDifference q N + 1) := by
  unfold finiteDepthLogMultiplication
  calc
    finiteDepthDifference q N * ((Real.log (p : ℝ)) • finiteDepthIndex N) -
        (Real.log (p : ℝ)) • finiteDepthIndex N * finiteDepthDifference q N =
      (Real.log (p : ℝ)) •
        (finiteDepthDifference q N * finiteDepthIndex N -
          finiteDepthIndex N * finiteDepthDifference q N) := by
            simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    _ = (Real.log (p : ℝ)) • (finiteDepthDifference q N + 1) := by
      rw [finiteDepthDifference_index_commutator]

theorem finiteNativeDepthCommutator_eq_log_scale
    (p N : ℕ) (q : ℝ) :
    finiteNativeDepthCommutator p q N =
      (Real.log (p : ℝ)) • (finiteDepthDifference q N + 1) := by
  exact finiteDepthDifference_logMultiplication_commutator p N q

/-! ## Visible/blind Parseval splitting -/

variable {camera state : Type*}
  [Fintype camera] [DecidableEq camera]
  [Fintype state] [DecidableEq state]

/-- Visible part of an arbitrary finite operator readout. -/
def finiteVisibleOperatorReadout
    (C : Matrix camera state ℝ) (J : Matrix state state ℝ) :
    Matrix state state ℝ :=
  (finiteCanonicalCameraReadout C)ᵀ *
    (finiteCanonicalCameraReadout C * J)

/-- Blind/provenance part of the same operator readout. -/
def finiteBlindOperatorReadout
    (C : Matrix camera state ℝ) (J : Matrix state state ℝ) :
    Matrix state state ℝ :=
  (finiteCanonicalCameraBlindProjection C)ᵀ *
    (finiteCanonicalCameraBlindProjection C * J)

theorem finiteEnrichedCamera_operator_decomposition
    {C : Matrix camera state ℝ}
    (hG : (finiteCameraRowGram C).PosDef)
    (J : Matrix state state ℝ) :
    finiteVisibleOperatorReadout C J + finiteBlindOperatorReadout C J = J := by
  exact finiteCanonicalEnrichedCamera_reconstruct hG J

theorem finiteNativeDepthCommutator_visible_blind_decomposition
    (p : ℕ) {N : ℕ} {C : Matrix camera (Fin N) ℝ}
    (hG : (finiteCameraRowGram C).PosDef) (q : ℝ) :
    finiteVisibleOperatorReadout C
        (finiteNativeDepthCommutator p q N) +
      finiteBlindOperatorReadout C
        (finiteNativeDepthCommutator p q N) =
      finiteNativeDepthCommutator p q N := by
  exact finiteEnrichedCamera_operator_decomposition hG _

end
end CarrySelfAdjointOperator
