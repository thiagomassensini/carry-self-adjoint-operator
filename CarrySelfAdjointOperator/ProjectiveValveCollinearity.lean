import CarrySelfAdjointOperator.ProjectiveValveLineIncidence

/-!
# Colinearidade da válvula projetiva

A geometria de linhas já prova que dois pontos projetivos distintos determinam
um único subespaço de dimensão dois e que pertencimento à linha equivale à
contenção da órbita multiplicativa.

Este arquivo liga essa geometria à noção simétrica de colinearidade da Mathlib.
Para `p ≠ q`, um terceiro ponto `r` é colinear com `p,q` exatamente quando
pertence à linha determinada por eles, ou, equivalentemente, quando sua órbita
está contida no subgrupo multiplicativo dessa linha.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries
open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K]

/-- Três direções da válvula são colineares quando formam um conjunto
colinear no espaço projetivo canônico das curvaturas formais. -/
noncomputable abbrev projectiveValveCollinear
    (p q r : ProjectiveValveDirection K) : Prop :=
  Projectivization.IsCollinear
    ({p, q, r} : Set (ProjectiveValveDirection K))

/-- Pertencer à linha determinada por dois pontos distintos implica
colinearidade com esse par. -/
theorem projectiveValveCollinear_of_directionOnLine
    (p q r : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hr : projectiveValveDirectionOnLine r p q) :
    projectiveValveCollinear p q r := by
  change
    Projectivization.IsCollinear
      ({p, q, r} : Set (ProjectiveValveDirection K))
  rw [Projectivization.IsCollinear_iff]
  refine
    ⟨(projectiveValveLineSubspace p q).projectivization,
      ?_, ?_, ?_⟩
  · rw [Projectivization.Subspace.submodule.apply_symm_apply,
      projectiveValveLineSubspace_eq_span_pair]
    exact Module.Finite.span_of_finite K (Set.toFinite _)
  · rw [Projectivization.Subspace.submodule.apply_symm_apply,
      projectiveValveLineSubspace_finrank_eq_two p q hpq]
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hxp | hx
    · subst x
      exact projectiveValveDirection_mem_lineSubspace_left p q
    · rcases hx with hxq | hxr
      · subst x
        exact projectiveValveDirection_mem_lineSubspace_right p q
      · subst x
        exact hr

/-- Para um par distinto, toda colinearidade é realizada pela linha canônica
que esse par determina. -/
theorem projectiveValveDirectionOnLine_of_collinear
    (p q r : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hcol : projectiveValveCollinear p q r) :
    projectiveValveDirectionOnLine r p q := by
  change
    Projectivization.IsCollinear
      ({p, q, r} : Set (ProjectiveValveDirection K)) at hcol
  rw [Projectivization.IsCollinear_iff] at hcol
  rcases hcol with ⟨M, hMfinite, hMrank, hsubset⟩
  letI : Module.Finite K M.submodule := hMfinite
  have hpM : p ∈ M := hsubset (by simp)
  have hqM : q ∈ M := hsubset (by simp)
  have hrM : r ∈ M := hsubset (by simp)
  have hpU : p ∈ M.submodule.projectivization := by
    simpa using hpM
  have hqU : q ∈ M.submodule.projectivization := by
    simpa using hqM
  have hrU : r ∈ M.submodule.projectivization := by
    simpa using hrM
  have hpLe : p.submodule ≤ M.submodule :=
    (Submodule.mem_projectivization_iff_submodule_le M.submodule p).mp hpU
  have hqLe : q.submodule ≤ M.submodule :=
    (Submodule.mem_projectivization_iff_submodule_le M.submodule q).mp hqU
  have hlineLe : projectiveValveLineSubspace p q ≤ M.submodule :=
    sup_le hpLe hqLe
  have hLower : 2 ≤ Module.finrank K M.submodule := by
    calc
      2 = Module.finrank K (projectiveValveLineSubspace p q) :=
        (projectiveValveLineSubspace_finrank_eq_two p q hpq).symm
      _ ≤ Module.finrank K M.submodule :=
        Submodule.finrank_mono hlineLe
  have hMrankEq : Module.finrank K M.submodule = 2 :=
    le_antisymm hMrank hLower
  have hsubspace :
      M.submodule = projectiveValveLineSubspace p q :=
    projectiveValveLineSubspace_unique
      p q hpq M.submodule hMrankEq hpU hqU
  change r ∈ (projectiveValveLineSubspace p q).projectivization
  rw [← hsubspace]
  exact hrU

/-- Para `p ≠ q`, colinearidade e incidência na linha de `p,q` são a mesma
condição. -/
theorem projectiveValveCollinear_iff_directionOnLine
    (p q r : ProjectiveValveDirection K)
    (hpq : p ≠ q) :
    projectiveValveCollinear p q r ↔
      projectiveValveDirectionOnLine r p q := by
  constructor
  · exact projectiveValveDirectionOnLine_of_collinear p q r hpq
  · exact projectiveValveCollinear_of_directionOnLine p q r hpq

/-- A colinearidade é simétrica nos dois primeiros pontos. -/
theorem projectiveValveCollinear_swap
    (p q r : ProjectiveValveDirection K) :
    projectiveValveCollinear p q r ↔
      projectiveValveCollinear q p r := by
  have hset :
      ({p, q, r} : Set (ProjectiveValveDirection K)) =
        ({q, p, r} : Set (ProjectiveValveDirection K)) := by
    ext x
    simp [or_comm, or_left_comm, or_assoc]
  change
    Projectivization.IsCollinear
        ({p, q, r} : Set (ProjectiveValveDirection K)) ↔
      Projectivization.IsCollinear
        ({q, p, r} : Set (ProjectiveValveDirection K))
  rw [hset]

/-- A colinearidade é invariável por rotação cíclica dos três pontos. -/
theorem projectiveValveCollinear_rotate
    (p q r : ProjectiveValveDirection K) :
    projectiveValveCollinear p q r ↔
      projectiveValveCollinear q r p := by
  have hset :
      ({p, q, r} : Set (ProjectiveValveDirection K)) =
        ({q, r, p} : Set (ProjectiveValveDirection K)) := by
    ext x
    simp [or_comm, or_left_comm, or_assoc]
  change
    Projectivization.IsCollinear
        ({p, q, r} : Set (ProjectiveValveDirection K)) ↔
      Projectivization.IsCollinear
        ({q, r, p} : Set (ProjectiveValveDirection K))
  rw [hset]

variable [CharZero K]

/-- Para um par distinto, a colinearidade do terceiro ponto é lida exatamente
pela contenção de sua órbita no subgrupo da linha. -/
theorem projectiveValveCollinear_iff_orbit_le_line
    (p q r : ProjectiveValveDirection K)
    (hpq : p ≠ q) :
    projectiveValveCollinear p q r ↔
      projectiveValveDirectionOrbit r ≤ projectiveValveLine p q := by
  rw [projectiveValveCollinear_iff_directionOnLine p q r hpq,
    projectiveValveDirectionOnLine_iff_orbit_le]

/-- A não colinearidade equivale à falha de contenção da órbita na linha. -/
theorem projectiveValveNotCollinear_iff_orbit_not_le_line
    (p q r : ProjectiveValveDirection K)
    (hpq : p ≠ q) :
    ¬projectiveValveCollinear p q r ↔
      ¬projectiveValveDirectionOrbit r ≤ projectiveValveLine p q :=
  not_congr (projectiveValveCollinear_iff_orbit_le_line p q r hpq)

end CarrySelfAdjointOperator.ProjectiveValve
