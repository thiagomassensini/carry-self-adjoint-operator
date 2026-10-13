import CarrySelfAdjointOperator.NativeGammaMaterialCameraLift

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators
open Polynomial PhysicalSewing NativeCarrySpectralWeyl.Camera.FiniteBridge
noncomputable section
set_option autoImplicit false

theorem materialCameraPolynomial_C2 (C : ℕ) :
    materialCameraPolynomial C 0 = 1 + ∑ m ∈ Finset.range C,
      (X : ℂ[X])^(4*(m+1)-2)*(1-X)^2 := by
  have hs : materialStencilPolynomial (seedStencil 2) = 1 := by
    simpa [seedStencil] using materialStencilPolynomial_atom 0
  have hc (m : ℕ) : materialStencilPolynomial (centerStencil 2 m) =
      (X : ℂ[X])^(4*(m+1)-2)*(1-X)^2 := by
    have he : 4*(m+1) = (4*(m+1)-2)+1+1 := by omega
    change materialStencilPolynomial (centeredBracketStencil (4*(m+1)) 1) = _
    nth_rw 1 [he]
    rw [materialStencilPolynomial_bracket]
    simp
  change materialStencilPolynomial (finiteStencil 2 C) = _
  rw [materialStencilPolynomial_camera, hs]
  simp only [hc]

theorem materialNaturalCameraPolynomial (b C : ℕ) (hb : 3 ≤ b) :
    materialStencilPolynomial (finiteStencil b C) =
      (∑ r ∈ FiniteNativeCarryOperator.Camera.radiusSet b, (X : ℂ[X])^(r-1)) +
      ∑ m ∈ Finset.range C, ∑ r ∈ FiniteNativeCarryOperator.Camera.radiusSet b,
        (X : ℂ[X])^(b*(m+1)-r-1)*(1-X^r)^2 := by
  have hb2 : b ≠ 2 := by omega
  have hr (r : ℕ) (hr : r ∈ FiniteNativeCarryOperator.Camera.radiusSet b) :
      1 ≤ r ∧ r < b := by
    simp only [FiniteNativeCarryOperator.Camera.radiusSet, Finset.mem_Icc,
      FiniteNativeCarryOperator.Camera.halfRange] at hr
    omega
  have hs : materialStencilPolynomial (seedStencil b) =
      ∑ r ∈ FiniteNativeCarryOperator.Camera.radiusSet b, (X : ℂ[X])^(r-1) := by
    rw [seedStencil, if_neg hb2, map_sum]
    apply Finset.sum_congr rfl
    intro r hrr
    have he : r = (r-1)+1 := by have h := hr r hrr; omega
    nth_rw 1 [he]
    rw [materialStencilPolynomial_atom]
  have hc (m : ℕ) : materialStencilPolynomial (centerStencil b m) =
      ∑ r ∈ FiniteNativeCarryOperator.Camera.radiusSet b,
        (X : ℂ[X])^(b*(m+1)-r-1)*(1-X^r)^2 := by
    rw [centerStencil, if_neg hb2, map_sum]
    apply Finset.sum_congr rfl
    intro r hrr
    have hm : b ≤ b*(m+1) := Nat.le_mul_of_pos_right b (by omega)
    have he : b*(m+1) = (b*(m+1)-r-1)+r+1 := by have h := hr r hrr; omega
    simp only [FiniteNativeCarryOperator.Camera.alignedCenter, if_neg hb2]
    nth_rw 1 [he]
    rw [materialStencilPolynomial_bracket]
  rw [materialStencilPolynomial_camera, hs]
  simp only [hc]

theorem materialCameraLift_zero_cutoff_not_injective : ¬Function.Injective (materialCameraLift 0) := by
  intro hi
  have he := hi materialCameraLift_zero_cutoff_degenerate
  have h := congrFun he (0 : Fin 6)
  norm_num [Pi.single_apply, Fin.ext_iff] at h

end
end CarrySelfAdjointOperator.GammaMaterialSewing
