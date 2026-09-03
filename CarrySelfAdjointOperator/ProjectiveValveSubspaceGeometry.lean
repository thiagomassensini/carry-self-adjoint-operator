import CarrySelfAdjointOperator.ProjectiveValveDirectionSpace
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Subespaços da válvula projetiva

As direções projetivas já identificam retas de curvatura com órbitas
multiplicativas unidimensionais. A geometria pede então a extensão de posto
arbitrário.

Para um subespaço linear `U` de curvaturas formais, definimos o subgrupo das
massas normalizadas cuja curvatura pertence a `U`. A extração de curvatura
transforma produto em soma, logo esse conjunto é fechado por unidade, produto
e inversão.

O mapa

`U ↦ projectiveValveSubspaceMasses U`

reflete exatamente inclusões de subespaços. Em posto um, ele recupera a órbita
escalar já construída, e para uma direção projetiva recupera a órbita associada
à sua reta canônica.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries
open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K] [CharZero K]

/-- Subgrupo das massas normalizadas cuja curvatura pertence ao subespaço
linear `U`. -/
noncomputable def projectiveValveSubspaceMasses
    (U : Submodule K (PowerSeries K)) :
    Subgroup (NormalizedProjectiveMass K) where
  carrier := {A | projectiveValveCurvature A.1 ∈ U}
  one_mem' := by
    change projectiveValveCurvature (1 : PowerSeries K) ∈ U
    rw [projectiveValveCurvature_one]
    exact U.zero_mem
  mul_mem' := by
    intro A B hA hB
    change projectiveValveCurvature ((A * B).1) ∈ U
    rw [NormalizedProjectiveMass.val_mul,
      projectiveValveCurvature_mul A.1 B.1 A.2 B.2]
    exact U.add_mem hA hB
  inv_mem' := by
    intro A hA
    change projectiveValveCurvature ((A⁻¹).1) ∈ U
    rw [NormalizedProjectiveMass.val_inv,
      projectiveValveCurvature_inv A.1 A.2]
    exact U.neg_mem hA

/-- Pertencer ao subgrupo de um subespaço significa exatamente que a
curvatura da massa pertence ao subespaço. -/
@[simp] theorem mem_projectiveValveSubspaceMasses_iff
    (U : Submodule K (PowerSeries K))
    (A : NormalizedProjectiveMass K) :
    A ∈ projectiveValveSubspaceMasses U ↔
      projectiveValveCurvature A.1 ∈ U :=
  Iff.rfl

/-- A massa canônica de toda curvatura de `U` pertence ao subgrupo de `U`. -/
theorem projectiveValveMass_mem_subspaceMasses
    (U : Submodule K (PowerSeries K))
    {D : PowerSeries K}
    (hD : D ∈ U) :
    (⟨projectiveValveMass D,
        projectiveValveMass_constantCoeff D⟩ :
      NormalizedProjectiveMass K) ∈
        projectiveValveSubspaceMasses U := by
  rw [mem_projectiveValveSubspaceMasses_iff,
    projectiveValveCurvature_projectiveValveMass]
  exact hD

/-- Inclusão de subgrupos de massas reflete e preserva exatamente inclusão de
subespaços de curvatura. -/
theorem projectiveValveSubspaceMasses_le_iff
    (U V : Submodule K (PowerSeries K)) :
    projectiveValveSubspaceMasses U ≤
        projectiveValveSubspaceMasses V ↔
      U ≤ V := by
  constructor
  · intro h D hD
    have hMass :
        (⟨projectiveValveMass D,
            projectiveValveMass_constantCoeff D⟩ :
          NormalizedProjectiveMass K) ∈
            projectiveValveSubspaceMasses U :=
      projectiveValveMass_mem_subspaceMasses U hD
    have hMassV := h hMass
    change projectiveValveCurvature (projectiveValveMass D) ∈ V at hMassV
    simpa using hMassV
  · intro h A hA
    change projectiveValveCurvature A.1 ∈ U at hA
    change projectiveValveCurvature A.1 ∈ V
    exact h hA

/-- Subespaços distintos produzem subgrupos de massas distintos. -/
theorem projectiveValveSubspaceMasses_injective :
    Function.Injective
      (projectiveValveSubspaceMasses (K := K)) := by
  intro U V hUV
  apply le_antisymm
  · exact
      (projectiveValveSubspaceMasses_le_iff U V).mp
        (le_of_eq hUV)
  · exact
      (projectiveValveSubspaceMasses_le_iff V U).mp
        (le_of_eq hUV.symm)

/-- O mapa de subespaços de curvatura para subgrupos de massas como uma
imersão de ordens. -/
noncomputable def projectiveValveSubspaceOrderEmbedding :
    Submodule K (PowerSeries K) ↪o
      Subgroup (NormalizedProjectiveMass K) where
  toFun := projectiveValveSubspaceMasses
  inj' := projectiveValveSubspaceMasses_injective (K := K)
  map_rel_iff' := by
    intro U V
    exact projectiveValveSubspaceMasses_le_iff U V

/-- A construção preserva interseções de subespaços. -/
@[simp] theorem projectiveValveSubspaceMasses_inf
    (U V : Submodule K (PowerSeries K)) :
    projectiveValveSubspaceMasses (U ⊓ V) =
      projectiveValveSubspaceMasses U ⊓
        projectiveValveSubspaceMasses V := by
  ext A
  rfl

/-- Em posto um, o subgrupo associado ao span de `D` é exatamente a órbita
escalar gerada por `D`. -/
theorem projectiveValveSubspaceMasses_span_singleton
    (D : PowerSeries K) :
    projectiveValveSubspaceMasses (K ∙ D) =
      projectiveValveOrbit D := by
  ext A
  rw [mem_projectiveValveSubspaceMasses_iff,
    mem_projectiveValveOrbit_iff]
  constructor
  · intro hA
    rcases (Submodule.mem_span_singleton.mp hA) with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    change projectiveValveMass (t • D) = A.1
    rw [ht]
    exact projectiveValveMass_projectiveValveCurvature A.1 A.2
  · rintro ⟨t, rfl⟩
    rw [projectiveValveFlow_curvature]
    exact
      Submodule.smul_mem _ t
        (Submodule.mem_span_singleton_self D)

/-- A órbita de uma direção projetiva é o subgrupo associado à sua reta
unidimensional canônica. -/
theorem projectiveValveDirectionOrbit_eq_subspaceMasses
    (p : ProjectiveValveDirection K) :
    projectiveValveDirectionOrbit p =
      projectiveValveSubspaceMasses p.submodule := by
  induction p using Projectivization.ind with
  | h D hD =>
      rw [projectiveValveDirectionOrbit_mk,
        Projectivization.submodule_mk,
        projectiveValveSubspaceMasses_span_singleton]

end CarrySelfAdjointOperator.ProjectiveValve
