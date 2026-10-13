import CarrySelfAdjointOperator.NativePhysicalMaterialProducer
import CarrySelfAdjointOperator.NativeGammaCameraComplexLinear

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators Matrix
open Polynomial PhysicalSewing NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera.FiniteBridge
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem materialStencilPolynomial_coeff_address (s : FormalStencil) (j : ℕ) :
    (materialStencilPolynomial s).coeff j = (s (j+1) : ℂ) := by
  let L : FormalStencil →ₗ[ℤ] ℂ :=
    { toFun := fun t => (t (j+1) : ℂ)
      map_add' := by intro a b; simp
      map_smul' := by intro a b; simp }
  have he : ((Polynomial.lcoeff ℂ j).restrictScalars ℤ).comp materialStencilPolynomial = L := by
    apply Finsupp.lhom_ext
    intro m c
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, materialStencilPolynomial,
      Finsupp.linearCombination_single, map_smul, Polynomial.lcoeff_apply]
    by_cases hm : m = 0
    · subst m
      simp [L]
    · have hj : m-1 = j ↔ m = j+1 := by omega
      simp [hm, L, Polynomial.coeff_monomial, Finsupp.single_apply, hj]
  exact congrArg (fun f => f s) he

def materialCameraWindow (C : ℕ) : ℕ := 7*C+3

def materialCameraPolynomial (C : ℕ) (i : Fin 6) : ℂ[X] :=
  materialStencilPolynomial (finiteStencil (sixCamera i) C)

/-- Complexification of the six literal stencils, with their original seeds. -/
def materialCameraLift (C : ℕ) : (Fin 6 → ℂ) →ₗ[ℂ] (Fin (materialCameraWindow C) → ℂ) :=
  Matrix.mulVecLin (fun (j : Fin (materialCameraWindow C)) (i : Fin 6) =>
    (materialCameraPolynomial C i).coeff j.val)

theorem materialCameraLift_literal (C : ℕ) (c : Fin 6 → ℂ) (j : Fin (materialCameraWindow C)) :
    materialCameraLift C c j = ∑ i, c i * (finiteCoefficient (sixCamera i) C (j.val+1) : ℂ) := by
  simp only [materialCameraLift, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    materialCameraPolynomial, materialStencilPolynomial_coeff_address, finiteStencil_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

def materialCameraTopDegree (C : ℕ) : Fin 6 → ℕ :=
  ![4*C,3*C,4*C+1,5*C+1,6*C+2,7*C+2]

theorem materialCamera_seed_below_top (C : ℕ) (hC : 1 ≤ C) (i : Fin 6) :
    seedCoefficient (sixCamera i) (materialCameraTopDegree C i+1) = 0 := by
  fin_cases i <;>
    norm_num [sixCamera, materialCameraTopDegree, seedCoefficient,
      FiniteNativeCarryOperator.Camera.radiusSet, FiniteNativeCarryOperator.Camera.halfRange,
      Finset.sum_Icc_succ_top] <;> omega

theorem materialCamera_center_at_top (C : ℕ) (hC : 1 ≤ C) (i : Fin 6) (m : ℕ) (hm : m < C) :
    centerCoefficient (sixCamera i) m (materialCameraTopDegree C i+1) =
      if m = C-1 then 1 else 0 := by
  fin_cases i <;>
    norm_num [sixCamera, materialCameraTopDegree, centerCoefficient, bracketCoefficient,
      FiniteNativeCarryOperator.Camera.radiusSet, FiniteNativeCarryOperator.Camera.halfRange,
      FiniteNativeCarryOperator.Camera.alignedCenter, Finset.sum_Icc_succ_top] <;>
    (try split_ifs) <;> omega

theorem materialCamera_top_coefficient (C : ℕ) (hC : 1 ≤ C) (i : Fin 6) :
    (materialCameraPolynomial C i).coeff (materialCameraTopDegree C i) = 1 := by
  rw [materialCameraPolynomial, materialStencilPolynomial_coeff_address, finiteStencil_apply,
    finiteCoefficient, materialCamera_seed_below_top C hC i]
  simp only [zero_add]
  have hs : (∑ m ∈ Finset.range C,
      centerCoefficient (sixCamera i) m (materialCameraTopDegree C i+1)) = 1 := by
    rw [Finset.sum_congr rfl (fun m hm => materialCamera_center_at_top C hC i m
      (Finset.mem_range.mp hm))]
    simp [show C-1 < C by omega]
  rw [hs]
  norm_num

theorem materialCamera_coeff_above_top (C : ℕ) (i : Fin 6) (j : ℕ)
    (hj : materialCameraTopDegree C i < j) : (materialCameraPolynomial C i).coeff j = 0 := by
  rw [materialCameraPolynomial, materialStencilPolynomial_coeff_address, finiteStencil_apply]
  have hseed : seedCoefficient (sixCamera i) (j+1) = 0 := by
    fin_cases i <;>
      norm_num [sixCamera, materialCameraTopDegree] at hj <;>
      norm_num [sixCamera, seedCoefficient, FiniteNativeCarryOperator.Camera.radiusSet,
        FiniteNativeCarryOperator.Camera.halfRange, Finset.sum_Icc_succ_top] <;>
      omega
  have hcent : ∀ m ∈ Finset.range C, centerCoefficient (sixCamera i) m (j+1) = 0 := by
    intro m hm
    have hmC := Finset.mem_range.mp hm
    fin_cases i <;>
      norm_num [sixCamera, materialCameraTopDegree] at hj <;>
      norm_num [sixCamera, centerCoefficient, bracketCoefficient,
        FiniteNativeCarryOperator.Camera.radiusSet, FiniteNativeCarryOperator.Camera.halfRange,
        FiniteNativeCarryOperator.Camera.alignedCenter, Finset.sum_Icc_succ_top] <;>
      (try split_ifs) <;> omega
  simp [finiteCoefficient, hseed, Finset.sum_eq_zero hcent]

theorem materialCamera_natDegree (C : ℕ) (hC : 1 ≤ C) (i : Fin 6) :
    (materialCameraPolynomial C i).natDegree = materialCameraTopDegree C i := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      (fun j hj => materialCamera_coeff_above_top C i j hj)
  · rw [materialCamera_top_coefficient C hC i]
    exact one_ne_zero

theorem materialCamera_monic (C : ℕ) (hC : 1 ≤ C) (i : Fin 6) :
    (materialCameraPolynomial C i).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, materialCamera_natDegree C hC i]
  exact materialCamera_top_coefficient C hC i

theorem materialCamera_top_lt_window (C : ℕ) (i : Fin 6) :
    materialCameraTopDegree C i < materialCameraWindow C := by
  fin_cases i <;> norm_num [materialCameraTopDegree, materialCameraWindow] <;> omega

theorem materialCamera_window_polynomial (C : ℕ) (i : Fin 6) :
    materialPolynomial (materialCameraWindow C)
      (fun j => (materialCameraPolynomial C i).coeff j.val) = materialCameraPolynomial C i := by
  apply Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
  exact lt_of_le_of_lt (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    (fun j hj => materialCamera_coeff_above_top C i j hj)) (materialCamera_top_lt_window C i)

theorem materialCameraLift_basis (C : ℕ) (i : Fin 6) :
    materialCameraLift C (Pi.single i 1) =
      (fun j => (materialCameraPolynomial C i).coeff j.val) := by
  simp [materialCameraLift]
  rfl

theorem materialCameraLift_zero_cutoff_degenerate :
    materialCameraLift 0 (Pi.single 0 1) = materialCameraLift 0 (Pi.single 1 1) := by
  rw [materialCameraLift_basis, materialCameraLift_basis]
  simp [materialCameraPolynomial, sixCamera, finiteStencil_zero, seedStencil,
    FiniteNativeCarryOperator.Camera.radiusSet, FiniteNativeCarryOperator.Camera.halfRange]

end
end CarrySelfAdjointOperator.GammaMaterialSewing
