import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Complex.Module

namespace CarrySelfAdjointOperator

open TensorProduct

noncomputable section

/-! ## Generic algebraic core of the post-T0 tower descent

`A` is the provenance/Jordan factor and `T` is the independent prime-power
tower factor.  The lemmas here deliberately know neither the historical J/H
coordinates nor any analytic completion: they express only that a left-factor
map commutes with a right-factor endomorphism and hence that the latter
descends canonically through the corresponding kernel quotient.
-/

variable {A B T : Type*}
variable [AddCommGroup A] [Module ℂ A]
variable [AddCommGroup B] [Module ℂ B]
variable [AddCommGroup T] [Module ℂ T]

/-- `(Q ⊗ id)` commutes with `(id ⊗ N)`. -/
theorem probe_tensor_leftMap_rightMap_commute
    (Q : A →ₗ[ℂ] B) (N : T →ₗ[ℂ] T) :
    (TensorProduct.map Q (LinearMap.id : T →ₗ[ℂ] T)).comp
        (TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) N)
      =
    (TensorProduct.map (LinearMap.id : B →ₗ[ℂ] B) N).comp
        (TensorProduct.map Q (LinearMap.id : T →ₗ[ℂ] T)) := by
  ext a t
  rfl

/-- A right-factor endomorphism preserves the kernel of a left-factor map. -/
theorem probe_tensor_rightMap_preserves_leftMap_ker
    (Q : A →ₗ[ℂ] B) (N : T →ₗ[ℂ] T) :
    LinearMap.ker (TensorProduct.map Q (LinearMap.id : T →ₗ[ℂ] T))
      ≤
    (LinearMap.ker (TensorProduct.map Q (LinearMap.id : T →ₗ[ℂ] T))).comap
      (TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) N) := by
  intro x hx
  have hx0 : TensorProduct.map Q (LinearMap.id : T →ₗ[ℂ] T) x = 0 := hx
  change
    TensorProduct.map Q (LinearMap.id : T →ₗ[ℂ] T)
        (TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) N x) = 0
  calc
    TensorProduct.map Q (LinearMap.id : T →ₗ[ℂ] T)
        (TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) N x) =
      TensorProduct.map (LinearMap.id : B →ₗ[ℂ] B) N
        (TensorProduct.map Q (LinearMap.id : T →ₗ[ℂ] T) x) := by
          exact DFunLike.congr_fun (probe_tensor_leftMap_rightMap_commute Q N) x
    _ = 0 := by rw [hx0, map_zero]

/-- The canonical quotient endomorphism induced by a kernel-stable linear
map.  This uses `Submodule.mapQ`, and therefore never selects a quotient
representative. -/
def probe_inducedEndOfKernelStable
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (Q : V →ₗ[ℂ] W) (N : V →ₗ[ℂ] V)
    (hN : LinearMap.ker Q ≤ (LinearMap.ker Q).comap N) :
    (V ⧸ LinearMap.ker Q) →ₗ[ℂ] (V ⧸ LinearMap.ker Q) :=
  (LinearMap.ker Q).mapQ (LinearMap.ker Q) N hN

theorem probe_inducedEndOfKernelStable_intertwining
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (Q : V →ₗ[ℂ] W) (N : V →ₗ[ℂ] V)
    (hN : LinearMap.ker Q ≤ (LinearMap.ker Q).comap N) :
    (probe_inducedEndOfKernelStable Q N hN).comp
        (LinearMap.ker Q).mkQ =
      (LinearMap.ker Q).mkQ.comp N := by
  exact Submodule.mapQ_mkQ (LinearMap.ker Q) (LinearMap.ker Q) N

theorem probe_inducedEndOfKernelStable_smul_intertwining
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (Q : V →ₗ[ℂ] W) (N : V →ₗ[ℂ] V)
    (hN : LinearMap.ker Q ≤ (LinearMap.ker Q).comap N)
    (a : ℂ) (x : V) :
    (LinearMap.ker Q).mkQ (a • N x) =
      a • probe_inducedEndOfKernelStable Q N hN
        ((LinearMap.ker Q).mkQ x) := by
  rw [LinearMap.map_smul]
  have h :
      probe_inducedEndOfKernelStable Q N hN ((LinearMap.ker Q).mkQ x) =
        (LinearMap.ker Q).mkQ (N x) := by
    simpa [LinearMap.comp_apply] using
      DFunLike.congr_fun
        (probe_inducedEndOfKernelStable_intertwining Q N hN) x
  rw [h]

end

end CarrySelfAdjointOperator
