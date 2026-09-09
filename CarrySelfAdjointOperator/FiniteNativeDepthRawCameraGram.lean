import CarrySelfAdjointOperator.FiniteNativeDepthCameraCommutator
import CarrySelfAdjointOperator.ExactCutoffCameraGram

/-!
# Raw finite camera matrix and its exact Gram

The literal coefficient matrix is kept separate from its canonical
whitening.  Its row Gram is the overlap sum already formalized for finite
camera stencils.  The six-camera specialization therefore inherits the exact
normalized convergence to `sixCameraGram` without treating whitening as a
physical readout.
-/

open scoped Matrix

namespace CarrySelfAdjointOperator

open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Limits
open Filter

noncomputable section

/-- Literal real coefficient matrix on the common finite family window. -/
def finiteLiteralCameraMatrix {index : Type*} [Fintype index]
    (cutoff : ℕ) (camera : index → ℕ) :
    Matrix index (Fin (finiteFamilyWindow cutoff camera)) ℝ :=
  fun i n => finiteCoefficientAt (camera i) cutoff n.val

theorem finiteLiteralCameraMatrix_rowGram_apply_eq_literalFiniteCameraGram
    {index : Type*} [Fintype index] {camera : index → ℕ}
    (hcamera : ∀ i, 2 ≤ camera i) (cutoff : ℕ) (i j : index) :
    finiteCameraRowGram (finiteLiteralCameraMatrix cutoff camera) i j =
      literalFiniteCameraGram cutoff (camera i) (camera j) := by
  unfold finiteCameraRowGram finiteLiteralCameraMatrix literalFiniteCameraGram
  rw [Matrix.mul_apply]
  calc
    (∑ x : Fin (finiteFamilyWindow cutoff camera),
        finiteCoefficientAt (camera i) cutoff x.val *
          finiteCoefficientAt (camera j) cutoff x.val) =
      ∑ n ∈ Finset.range (finiteFamilyWindow cutoff camera),
        finiteCoefficientAt (camera i) cutoff n *
          finiteCoefficientAt (camera j) cutoff n := by
            simpa only using Fin.sum_univ_eq_sum_range
              (fun n : ℕ => finiteCoefficientAt (camera i) cutoff n *
                finiteCoefficientAt (camera j) cutoff n)
              (finiteFamilyWindow cutoff camera)
    _ = ∑ n ∈ Finset.range (pairFiniteWindow (camera i) (camera j) cutoff),
        finiteCoefficientAt (camera i) cutoff n *
          finiteCoefficientAt (camera j) cutoff n := by
            have h := sum_finiteFamilyWindow_eq_pairFiniteWindow
              hcamera cutoff (fun _ => (1 : ℂ)) i j
            norm_num at h
            exact_mod_cast h

def finiteLiteralSixCameraMatrix (cutoff : ℕ) :
    Matrix (Fin 6) (Fin (finiteFamilyWindow cutoff sixCamera)) ℝ :=
  finiteLiteralCameraMatrix cutoff sixCamera

theorem finiteLiteralSixCameraMatrix_rowGram_apply_eq_literalFiniteCameraGram
    (cutoff : ℕ) (i j : Fin 6) :
    finiteCameraRowGram (finiteLiteralSixCameraMatrix cutoff) i j =
      literalFiniteCameraGram cutoff (sixCamera i) (sixCamera j) := by
  apply finiteLiteralCameraMatrix_rowGram_apply_eq_literalFiniteCameraGram
  intro i
  fin_cases i <;> norm_num [sixCamera]

theorem tendsto_normalizedFiniteLiteralSixCameraRowGram :
    Tendsto
      (fun cutoff : ℕ =>
        (cutoff : ℝ)⁻¹ • finiteCameraRowGram
          (finiteLiteralSixCameraMatrix cutoff))
      atTop (nhds sixCameraGram) := by
  have h := tendsto_normalizedLiteralSixCameraGram
  apply h.congr'
  filter_upwards [] with cutoff
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [finiteLiteralSixCameraMatrix_rowGram_apply_eq_literalFiniteCameraGram cutoff i j]

end
end CarrySelfAdjointOperator
