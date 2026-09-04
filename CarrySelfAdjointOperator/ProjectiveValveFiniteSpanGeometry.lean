import CarrySelfAdjointOperator.ProjectiveValveThreeSpaceGeometry
import Mathlib.Data.Fintype.Lattice
import Mathlib.LinearAlgebra.Projectivization.Independence

/-!
# Geometria finita de spans da válvula projetiva

As camadas anteriores constroem manualmente os casos de posto 1, 2, 3 e 4:
órbitas, linhas, planos e espaços projetivos tridimensionais. O padrão já está
claro demais para continuar repetindo arquivos por dimensão.

Este arquivo abstrai a construção para uma família finita arbitrária de
direções projetivas. Para `f : ι → ProjectiveValveDirection K`, definimos o
subespaço gerado pelos representantes canônicos de `f`. Se a família é
projetivamente independente, esse subespaço tem dimensão exatamente
`Fintype.card ι`.

No lado multiplicativo, a associação

`U ↦ projectiveValveSubspaceMasses U`

é empacotada como um `SupBotHom`, portanto preserva automaticamente supremos
finitos. Assim o subgrupo associado ao span finito é exatamente o supremo das
órbitas escalares das direções geradoras e é o menor subgrupo que contém todas
essas órbitas.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries
open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K]

/-- Subespaço linear gerado pelos representantes canônicos de uma família
finita de direções projetivas. -/
noncomputable abbrev projectiveValveFiniteSpanSubspace
    {ι : Type*} [Fintype ι]
    (f : ι → ProjectiveValveDirection K) :
    Submodule K (PowerSeries K) :=
  Submodule.span K (Set.range fun i => (f i).rep)

/-- O span dos representantes é também o supremo das retas canônicas das
direções da família. -/
theorem projectiveValveFiniteSpanSubspace_eq_iSup_submodules
    {ι : Type*} [Fintype ι]
    (f : ι → ProjectiveValveDirection K) :
    projectiveValveFiniteSpanSubspace f =
      ⨆ i, (f i).submodule := by
  unfold projectiveValveFiniteSpanSubspace
  rw [Submodule.span_range_eq_iSup]
  simp only [Projectivization.submodule_eq]

/-- Cada direção geradora pertence ao span projetivo da família. -/
theorem projectiveValveDirection_mem_finiteSpanSubspace
    {ι : Type*} [Fintype ι]
    (f : ι → ProjectiveValveDirection K)
    (i : ι) :
    f i ∈ (projectiveValveFiniteSpanSubspace f).projectivization := by
  rw [Submodule.mem_projectivization_iff_submodule_le,
    projectiveValveFiniteSpanSubspace_eq_iSup_submodules]
  exact le_iSup (fun j => (f j).submodule) i

/-- Uma família projetivamente independente gera um subespaço cuja dimensão
linear é exatamente o número de direções da família. -/
theorem projectiveValveFiniteSpanSubspace_finrank_eq_card
    {ι : Type*} [Fintype ι]
    (f : ι → ProjectiveValveDirection K)
    (hf : Projectivization.Independent f) :
    Module.finrank K (projectiveValveFiniteSpanSubspace f) =
      Fintype.card ι := by
  have hLinearIndependent :
      LinearIndependent K (fun i => (f i).rep) := by
    simpa [Function.comp_def] using
      (Projectivization.independent_iff (f := f)).mp hf
  simpa [projectiveValveFiniteSpanSubspace] using
    (finrank_span_eq_card hLinearIndependent)

/-- Para uma família finita não vazia e independente, o subespaço gerado é o
único subespaço de dimensão `card ι` que contém todas as direções da família. -/
theorem projectiveValveFiniteSpanSubspace_unique
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ProjectiveValveDirection K)
    (hf : Projectivization.Independent f)
    (U : Submodule K (PowerSeries K))
    (hUrank : Module.finrank K U = Fintype.card ι)
    (hU : ∀ i, f i ∈ U.projectivization) :
    U = projectiveValveFiniteSpanSubspace f := by
  have hSpanLe : projectiveValveFiniteSpanSubspace f ≤ U := by
    rw [projectiveValveFiniteSpanSubspace_eq_iSup_submodules]
    refine iSup_le fun i => ?_
    exact
      (Submodule.mem_projectivization_iff_submodule_le U (f i)).mp
        (hU i)
  have hUpos : 0 < Module.finrank K U := by
    rw [hUrank]
    exact Fintype.card_pos
  letI : Module.Finite K U :=
    Module.finite_of_finrank_pos hUpos
  symm
  apply Submodule.eq_of_le_of_finrank_eq hSpanLe
  rw [projectiveValveFiniteSpanSubspace_finrank_eq_card f hf,
    hUrank]

variable [CharZero K]

/-- A correspondência de subespaços de curvatura para subgrupos de massas
como homomorfismo de semirreticulados com fundo. -/
noncomputable def projectiveValveSubspaceSupBotHom :
    SupBotHom
      (Submodule K (PowerSeries K))
      (Subgroup (NormalizedProjectiveMass K)) where
  toFun := projectiveValveSubspaceMasses (K := K)
  map_sup' := projectiveValveSubspaceMasses_sup (K := K)
  map_bot' := projectiveValveSubspaceMasses_bot (K := K)

/-- Aplicar o `SupBotHom` canônico é definicionalmente a mesma coisa que
aplicar `projectiveValveSubspaceMasses`. -/
@[simp] theorem projectiveValveSubspaceSupBotHom_apply
    (U : Submodule K (PowerSeries K)) :
    projectiveValveSubspaceSupBotHom (K := K) U =
      projectiveValveSubspaceMasses U :=
  rfl

/-- A correspondência de subespaços preserva supremos indexados por qualquer
tipo finito. -/
theorem projectiveValveSubspaceMasses_iSup_fintype
    {ι : Type*} [Fintype ι]
    (U : ι → Submodule K (PowerSeries K)) :
    projectiveValveSubspaceMasses (⨆ i, U i) =
      ⨆ i, projectiveValveSubspaceMasses (U i) := by
  have h :=
    map_finset_sup
      (projectiveValveSubspaceSupBotHom (K := K))
      Finset.univ U
  simpa only [Finset.sup_univ_eq_iSup, Function.comp_apply,
    projectiveValveSubspaceSupBotHom_apply] using h

/-- Subgrupo multiplicativo associado ao span finito de uma família de
direções projetivas. -/
noncomputable abbrev projectiveValveFiniteSpan
    {ι : Type*} [Fintype ι]
    (f : ι → ProjectiveValveDirection K) :
    Subgroup (NormalizedProjectiveMass K) :=
  projectiveValveSubspaceMasses
    (projectiveValveFiniteSpanSubspace f)

/-- O subgrupo do span finito é exatamente o supremo das órbitas das direções
geradoras. -/
theorem projectiveValveFiniteSpan_eq_iSup_orbits
    {ι : Type*} [Fintype ι]
    (f : ι → ProjectiveValveDirection K) :
    projectiveValveFiniteSpan f =
      ⨆ i, projectiveValveDirectionOrbit (f i) := by
  unfold projectiveValveFiniteSpan
  rw [projectiveValveFiniteSpanSubspace_eq_iSup_submodules,
    projectiveValveSubspaceMasses_iSup_fintype]
  simp only [projectiveValveDirectionOrbit_eq_subspaceMasses]

/-- Cada órbita geradora está contida no subgrupo do span finito. -/
theorem projectiveValveDirectionOrbit_le_finiteSpan
    {ι : Type*} [Fintype ι]
    (f : ι → ProjectiveValveDirection K)
    (i : ι) :
    projectiveValveDirectionOrbit (f i) ≤
      projectiveValveFiniteSpan f := by
  rw [projectiveValveFiniteSpan_eq_iSup_orbits]
  exact le_iSup (fun j => projectiveValveDirectionOrbit (f j)) i

/-- O span finito é o menor subgrupo que contém todas as órbitas geradoras. -/
theorem projectiveValveFiniteSpan_le_iff
    {ι : Type*} [Fintype ι]
    (f : ι → ProjectiveValveDirection K)
    (H : Subgroup (NormalizedProjectiveMass K)) :
    projectiveValveFiniteSpan f ≤ H ↔
      ∀ i, projectiveValveDirectionOrbit (f i) ≤ H := by
  rw [projectiveValveFiniteSpan_eq_iSup_orbits]
  exact iSup_le_iff

/-- No lado multiplicativo, uma família finita não vazia e independente
identifica unicamente o subgrupo associado a qualquer subespaço da mesma
dimensão que contenha todas as direções da família. -/
theorem projectiveValveSubspaceMasses_eq_finiteSpan_of_finrank_card
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ProjectiveValveDirection K)
    (hf : Projectivization.Independent f)
    (U : Submodule K (PowerSeries K))
    (hUrank : Module.finrank K U = Fintype.card ι)
    (hU : ∀ i, f i ∈ U.projectivization) :
    projectiveValveSubspaceMasses U =
      projectiveValveFiniteSpan f := by
  unfold projectiveValveFiniteSpan
  rw [projectiveValveFiniteSpanSubspace_unique
    f hf U hUrank hU]

end CarrySelfAdjointOperator.ProjectiveValve
