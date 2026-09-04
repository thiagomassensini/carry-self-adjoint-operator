import CarrySelfAdjointOperator.ProjectiveValvePlaneIncidence

/-!
# Coplanaridade da válvula projetiva

A geometria de planos já prova que três direções não colineares determinam um
único subespaço de dimensão três e que incidência nesse plano equivale à
contenção da órbita multiplicativa correspondente.

Este arquivo introduz a relação simétrica de coplanaridade para quatro
direções. Quatro pontos são coplanares quando estão contidos em algum
subespaço projetivo de dimensão linear no máximo três. Relativamente a um
trio não colinear `p,q,r`, essa condição equivale exatamente a o quarto ponto
pertencer ao plano canônico gerado pelo trio e, no lado multiplicativo, a sua
órbita estar contida no subgrupo-plano.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries
open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K]

/-- Quatro direções da válvula são coplanares quando algum subespaço
projetivo de dimensão linear no máximo três contém todas elas. -/
noncomputable abbrev projectiveValveCoplanar
    (p q r s : ProjectiveValveDirection K) : Prop :=
  ∃ M : Projectivization.Subspace K (PowerSeries K),
    Module.Finite K M.submodule ∧
      Module.finrank K M.submodule ≤ 3 ∧
        ({p, q, r, s} : Set (ProjectiveValveDirection K)) ⊆ M

/-- Pertencer ao plano determinado por um trio não colinear implica
coplanaridade com esse trio. -/
theorem projectiveValveCoplanar_of_directionOnPlane
    (p q r s : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hnotcol : ¬projectiveValveCollinear p q r)
    (hs : projectiveValveDirectionOnPlane s p q r) :
    projectiveValveCoplanar p q r s := by
  refine
    ⟨(projectiveValvePlaneSubspace p q r).projectivization,
      ?_, ?_, ?_⟩
  · rw [Projectivization.Subspace.submodule.apply_symm_apply]
    exact Module.finite_of_finrank_eq_succ
      (projectiveValvePlaneSubspace_finrank_eq_three
        p q r hpq hnotcol)
  · rw [Projectivization.Subspace.submodule.apply_symm_apply,
      projectiveValvePlaneSubspace_finrank_eq_three
        p q r hpq hnotcol]
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hxp | hx
    · subst x
      exact projectiveValveDirection_mem_planeSubspace_left p q r
    · rcases hx with hxq | hx
      · subst x
        exact projectiveValveDirection_mem_planeSubspace_middle p q r
      · rcases hx with hxr | hxs
        · subst x
          exact projectiveValveDirection_mem_planeSubspace_right p q r
        · subst x
          exact hs

/-- Relativamente a um trio não colinear, toda testemunha abstrata de
coplanaridade coincide com o plano canônico gerado pelo trio; em particular,
o quarto ponto pertence a esse plano. -/
theorem projectiveValveDirectionOnPlane_of_coplanar
    (p q r s : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hnotcol : ¬projectiveValveCollinear p q r)
    (hcop : projectiveValveCoplanar p q r s) :
    projectiveValveDirectionOnPlane s p q r := by
  rcases hcop with ⟨M, hMfinite, hMrank, hsubset⟩
  letI : Module.Finite K M.submodule := hMfinite
  have hpM : p ∈ M := hsubset (by simp)
  have hqM : q ∈ M := hsubset (by simp)
  have hrM : r ∈ M := hsubset (by simp)
  have hsM : s ∈ M := hsubset (by simp)
  have hpU : p ∈ M.submodule.projectivization := by
    simpa using hpM
  have hqU : q ∈ M.submodule.projectivization := by
    simpa using hqM
  have hrU : r ∈ M.submodule.projectivization := by
    simpa using hrM
  have hsU : s ∈ M.submodule.projectivization := by
    simpa using hsM
  have hpLe : p.submodule ≤ M.submodule :=
    (Submodule.mem_projectivization_iff_submodule_le M.submodule p).mp hpU
  have hqLe : q.submodule ≤ M.submodule :=
    (Submodule.mem_projectivization_iff_submodule_le M.submodule q).mp hqU
  have hrLe : r.submodule ≤ M.submodule :=
    (Submodule.mem_projectivization_iff_submodule_le M.submodule r).mp hrU
  have hlineLe : projectiveValveLineSubspace p q ≤ M.submodule :=
    sup_le hpLe hqLe
  have hplaneLe : projectiveValvePlaneSubspace p q r ≤ M.submodule :=
    sup_le hlineLe hrLe
  have hLower : 3 ≤ Module.finrank K M.submodule := by
    calc
      3 = Module.finrank K (projectiveValvePlaneSubspace p q r) :=
        (projectiveValvePlaneSubspace_finrank_eq_three
          p q r hpq hnotcol).symm
      _ ≤ Module.finrank K M.submodule :=
        Submodule.finrank_mono hplaneLe
  have hMrankEq : Module.finrank K M.submodule = 3 :=
    le_antisymm hMrank hLower
  have hsubspace :
      M.submodule = projectiveValvePlaneSubspace p q r :=
    projectiveValvePlaneSubspace_unique
      p q r hpq hnotcol M.submodule hMrankEq hpU hqU hrU
  change s ∈ (projectiveValvePlaneSubspace p q r).projectivization
  rw [← hsubspace]
  exact hsU

/-- Para um trio não colinear, coplanaridade e incidência no plano canônico
são a mesma condição. -/
theorem projectiveValveCoplanar_iff_directionOnPlane
    (p q r s : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hnotcol : ¬projectiveValveCollinear p q r) :
    projectiveValveCoplanar p q r s ↔
      projectiveValveDirectionOnPlane s p q r := by
  constructor
  · exact projectiveValveDirectionOnPlane_of_coplanar
      p q r s hpq hnotcol
  · exact projectiveValveCoplanar_of_directionOnPlane
      p q r s hpq hnotcol

/-- A coplanaridade é simétrica nos dois primeiros pontos. -/
theorem projectiveValveCoplanar_swap
    (p q r s : ProjectiveValveDirection K) :
    projectiveValveCoplanar p q r s ↔
      projectiveValveCoplanar q p r s := by
  have hset :
      ({p, q, r, s} : Set (ProjectiveValveDirection K)) =
        ({q, p, r, s} : Set (ProjectiveValveDirection K)) := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  unfold projectiveValveCoplanar
  rw [hset]

/-- A coplanaridade é invariável por rotação cíclica dos quatro pontos. -/
theorem projectiveValveCoplanar_rotate
    (p q r s : ProjectiveValveDirection K) :
    projectiveValveCoplanar p q r s ↔
      projectiveValveCoplanar q r s p := by
  have hset :
      ({p, q, r, s} : Set (ProjectiveValveDirection K)) =
        ({q, r, s, p} : Set (ProjectiveValveDirection K)) := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  unfold projectiveValveCoplanar
  rw [hset]

variable [CharZero K]

/-- Para um trio não colinear, a coplanaridade do quarto ponto é lida
exatamente pela contenção de sua órbita no subgrupo-plano. -/
theorem projectiveValveCoplanar_iff_orbit_le_plane
    (p q r s : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hnotcol : ¬projectiveValveCollinear p q r) :
    projectiveValveCoplanar p q r s ↔
      projectiveValveDirectionOrbit s ≤ projectiveValvePlane p q r :=
  (projectiveValveCoplanar_iff_directionOnPlane
    p q r s hpq hnotcol).trans
      (projectiveValveDirectionOnPlane_iff_orbit_le
        (K := K) s p q r)

/-- A não coplanaridade equivale à falha de contenção da quarta órbita no
plano multiplicativo dos três primeiros pontos. -/
theorem projectiveValveNotCoplanar_iff_orbit_not_le_plane
    (p q r s : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hnotcol : ¬projectiveValveCollinear p q r) :
    ¬projectiveValveCoplanar p q r s ↔
      ¬projectiveValveDirectionOrbit s ≤ projectiveValvePlane p q r :=
  not_congr
    (projectiveValveCoplanar_iff_orbit_le_plane
      p q r s hpq hnotcol)

end CarrySelfAdjointOperator.ProjectiveValve
