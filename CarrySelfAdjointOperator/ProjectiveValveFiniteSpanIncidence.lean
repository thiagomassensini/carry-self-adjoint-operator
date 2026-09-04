import CarrySelfAdjointOperator.ProjectiveValveFiniteSpanGeometry

/-!
# Incidência e regeneração dos spans finitos da válvula projetiva

A geometria finita já associa a toda família finita de direções projetivas o
subespaço linear gerado pelos seus representantes canônicos e, no lado
multiplicativo, o supremo das órbitas escalares correspondentes.

Este arquivo formaliza a consequência estrutural seguinte. Duas famílias
finitas, não vazias e projetivamente independentes, com a mesma cardinalidade,
geram o mesmo subespaço exatamente quando todos os geradores da segunda
família pertencem ao span da primeira. No lado multiplicativo, a mesma
condição é lida como contenção de todas as órbitas geradoras.

Assim o span finito passa a depender apenas do subespaço projetivo apresentado,
e não da família independente particular escolhida para apresentá-lo.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries
open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K]

/-- A direção `s` pertence ao span projetivo finito da família `f`. -/
noncomputable abbrev projectiveValveDirectionOnFiniteSpan
    {ι : Type*} [Fintype ι]
    (s : ProjectiveValveDirection K)
    (f : ι → ProjectiveValveDirection K) : Prop :=
  s ∈ (projectiveValveFiniteSpanSubspace f).projectivization

/-- Todo gerador pertence ao span finito da própria família. -/
@[simp] theorem projectiveValveDirectionOnFiniteSpan_generator
    {ι : Type*} [Fintype ι]
    (f : ι → ProjectiveValveDirection K)
    (i : ι) :
    projectiveValveDirectionOnFiniteSpan (f i) f :=
  projectiveValveDirection_mem_finiteSpanSubspace f i

/-- **Regeneração finita.**

Duas famílias finitas, não vazias e independentes, de mesma cardinalidade
geram o mesmo subespaço se todos os geradores da segunda pertencem ao span da
primeira. -/
theorem projectiveValveFiniteSpanSubspace_eq_of_family_on_finiteSpan
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (f : ι → ProjectiveValveDirection K)
    (hf : Projectivization.Independent f)
    (g : κ → ProjectiveValveDirection K)
    (hg : Projectivization.Independent g)
    (hcard : Fintype.card ι = Fintype.card κ)
    (hgOn : ∀ j, projectiveValveDirectionOnFiniteSpan (g j) f) :
    projectiveValveFiniteSpanSubspace g =
      projectiveValveFiniteSpanSubspace f := by
  have hUrank :
      Module.finrank K (projectiveValveFiniteSpanSubspace f) =
        Fintype.card κ := by
    rw [projectiveValveFiniteSpanSubspace_finrank_eq_card f hf,
      hcard]
  symm
  exact
    projectiveValveFiniteSpanSubspace_unique
      g hg (projectiveValveFiniteSpanSubspace f) hUrank hgOn

/-- Para duas famílias finitas independentes de mesma cardinalidade, igualdade
dos spans equivale a incidência de toda a segunda família no span da primeira. -/
theorem projectiveValveFiniteSpanSubspace_eq_iff_family_on_finiteSpan
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (f : ι → ProjectiveValveDirection K)
    (hf : Projectivization.Independent f)
    (g : κ → ProjectiveValveDirection K)
    (hg : Projectivization.Independent g)
    (hcard : Fintype.card ι = Fintype.card κ) :
    projectiveValveFiniteSpanSubspace g =
        projectiveValveFiniteSpanSubspace f ↔
      ∀ j, projectiveValveDirectionOnFiniteSpan (g j) f := by
  constructor
  · intro hspans j
    change g j ∈ (projectiveValveFiniteSpanSubspace f).projectivization
    rw [← hspans]
    exact projectiveValveDirection_mem_finiteSpanSubspace g j
  · intro hgOn
    exact
      projectiveValveFiniteSpanSubspace_eq_of_family_on_finiteSpan
        f hf g hg hcard hgOn

variable [CharZero K]

/-- Incidência no span finito e contenção da órbita multiplicativa são a mesma
condição. -/
theorem projectiveValveDirectionOnFiniteSpan_iff_orbit_le
    {ι : Type*} [Fintype ι]
    (s : ProjectiveValveDirection K)
    (f : ι → ProjectiveValveDirection K) :
    projectiveValveDirectionOnFiniteSpan s f ↔
      projectiveValveDirectionOrbit s ≤ projectiveValveFiniteSpan f := by
  unfold projectiveValveDirectionOnFiniteSpan projectiveValveFiniteSpan
  rw [projectiveValveDirectionOrbit_eq_subspaceMasses (K := K) s,
    projectiveValveSubspaceMasses_le_iff,
    Submodule.mem_projectivization_iff_submodule_le]

/-- A regeneração finita transportada para o lado multiplicativo. -/
theorem projectiveValveFiniteSpan_eq_of_family_on_finiteSpan
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (f : ι → ProjectiveValveDirection K)
    (hf : Projectivization.Independent f)
    (g : κ → ProjectiveValveDirection K)
    (hg : Projectivization.Independent g)
    (hcard : Fintype.card ι = Fintype.card κ)
    (hgOn : ∀ j, projectiveValveDirectionOnFiniteSpan (g j) f) :
    projectiveValveFiniteSpan g = projectiveValveFiniteSpan f := by
  unfold projectiveValveFiniteSpan
  rw [projectiveValveFiniteSpanSubspace_eq_of_family_on_finiteSpan
    f hf g hg hcard hgOn]

/-- Para duas famílias finitas independentes de mesma cardinalidade, igualdade
dos subgrupos de span equivale à contenção de todas as órbitas geradoras da
segunda família no span multiplicativo da primeira. -/
theorem projectiveValveFiniteSpan_eq_iff_family_orbits_le
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (f : ι → ProjectiveValveDirection K)
    (hf : Projectivization.Independent f)
    (g : κ → ProjectiveValveDirection K)
    (hg : Projectivization.Independent g)
    (hcard : Fintype.card ι = Fintype.card κ) :
    projectiveValveFiniteSpan g = projectiveValveFiniteSpan f ↔
      ∀ j, projectiveValveDirectionOrbit (g j) ≤
        projectiveValveFiniteSpan f := by
  constructor
  · intro hspans j
    rw [← hspans]
    exact projectiveValveDirectionOrbit_le_finiteSpan g j
  · intro horbits
    apply
      projectiveValveFiniteSpan_eq_of_family_on_finiteSpan
        f hf g hg hcard
    intro j
    exact
      (projectiveValveDirectionOnFiniteSpan_iff_orbit_le
        (K := K) (g j) f).2 (horbits j)

/-- Forma puramente multiplicativa da regeneração: uma família independente
de mesma cardinalidade cujas órbitas estão todas contidas em um span finito
gera exatamente esse mesmo span. -/
theorem projectiveValveFiniteSpan_eq_of_family_orbits_le
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (f : ι → ProjectiveValveDirection K)
    (hf : Projectivization.Independent f)
    (g : κ → ProjectiveValveDirection K)
    (hg : Projectivization.Independent g)
    (hcard : Fintype.card ι = Fintype.card κ)
    (horbits : ∀ j, projectiveValveDirectionOrbit (g j) ≤
      projectiveValveFiniteSpan f) :
    projectiveValveFiniteSpan g = projectiveValveFiniteSpan f :=
  (projectiveValveFiniteSpan_eq_iff_family_orbits_le
    f hf g hg hcard).2 horbits

end CarrySelfAdjointOperator.ProjectiveValve
