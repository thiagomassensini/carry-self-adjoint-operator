import CarrySelfAdjointOperator.NativeGammaMaterialCameraLift
import Mathlib.LinearAlgebra.Matrix.Block

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped Matrix BigOperators
noncomputable section
set_option autoImplicit false

def materialCameraDegreeOrder : Equiv.Perm (Fin 6) := Equiv.swap 0 1

theorem materialCamera_ordered_degrees (C : ℕ) (hC : 1 ≤ C) :
    StrictMono (fun i => materialCameraTopDegree C (materialCameraDegreeOrder i)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    norm_num [materialCameraDegreeOrder, Equiv.swap_apply_def, Fin.ext_iff,
      materialCameraTopDegree] at * <;> omega

def materialCameraTopMinor (C : ℕ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => (materialCameraPolynomial C j).coeff (materialCameraTopDegree C i)

theorem materialCameraLift_maxDegreeMinor (C : ℕ) (hC : 1 ≤ C) :
    (materialCameraTopMinor C).det = 1 := by
  have ht : ((materialCameraTopMinor C).submatrix materialCameraDegreeOrder
      materialCameraDegreeOrder).BlockTriangular id := by
    intro i j hij
    exact materialCamera_coeff_above_top C (materialCameraDegreeOrder j)
      (materialCameraTopDegree C (materialCameraDegreeOrder i))
      (materialCamera_ordered_degrees C hC hij)
  have hd := Matrix.det_of_upperTriangular ht
  rw [Matrix.det_submatrix_equiv_self] at hd
  simpa only [Matrix.submatrix_apply, materialCameraTopMinor,
    materialCamera_top_coefficient C hC, Finset.prod_const_one] using hd

theorem materialCameraTopMinor_isUnit (C : ℕ) (hC : 1 ≤ C) :
    IsUnit (materialCameraTopMinor C).det := by
  rw [materialCameraLift_maxDegreeMinor C hC]
  exact isUnit_one

def materialCameraTopReadout (C : ℕ) (v : Fin (materialCameraWindow C) → ℂ) : Fin 6 → ℂ :=
  fun i => v ⟨materialCameraTopDegree C i, materialCamera_top_lt_window C i⟩

theorem materialCameraTopReadout_lift (C : ℕ) (c : Fin 6 → ℂ) :
    materialCameraTopReadout C (materialCameraLift C c) = materialCameraTopMinor C *ᵥ c := by
  rfl

theorem materialCameraLift_injective (C : ℕ) (hC : 1 ≤ C) :
    Function.Injective (materialCameraLift C) := by
  intro c d hcd
  have he := congrArg (materialCameraTopReadout C) hcd
  rw [materialCameraTopReadout_lift, materialCameraTopReadout_lift] at he
  exact (Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (materialCameraTopMinor_isUnit C hC))) he

def materialCameraDecode (C : ℕ) (v : Fin (materialCameraWindow C) → ℂ) : Fin 6 → ℂ :=
  (materialCameraTopMinor C)⁻¹ *ᵥ materialCameraTopReadout C v

theorem materialCameraDecode_lift (C : ℕ) (hC : 1 ≤ C) (c : Fin 6 → ℂ) :
    materialCameraDecode C (materialCameraLift C c) = c := by
  rw [materialCameraDecode, materialCameraTopReadout_lift, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (materialCameraTopMinor_isUnit C hC), Matrix.one_mulVec]

end
end CarrySelfAdjointOperator.GammaMaterialSewing
