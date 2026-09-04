import CarrySelfAdjointOperator.ProjectiveValveCoplanarity

/-!
# Geometria do espaço tridimensional da válvula projetiva

A geometria já constrói pontos, linhas, planos, colinearidade e coplanaridade.
O próximo passo estrutural é o espaço projetivo tridimensional gerado por
quatro direções não coplanares.

Seu subespaço linear subjacente é a soma do plano dos três primeiros pontos
com a reta do quarto. Quando o quarto ponto não pertence ao plano, essa soma
tem posto exatamente quatro. No lado multiplicativo, o espaço é o menor
subgrupo de massas normalizadas que contém as quatro órbitas escalares.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries
open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K]

/-- Subespaço linear subjacente ao espaço projetivo tridimensional gerado por
quatro direções. Sua dimensão linear esperada é quatro. -/
noncomputable abbrev projectiveValveThreeSpaceSubspace
    (p q r s : ProjectiveValveDirection K) :
    Submodule K (PowerSeries K) :=
  projectiveValvePlaneSubspace p q r ⊔ s.submodule

/-- O plano dos três primeiros pontos está contido no espaço do quarteto. -/
theorem projectiveValvePlaneSubspace_le_threeSpaceSubspace
    (p q r s : ProjectiveValveDirection K) :
    projectiveValvePlaneSubspace p q r ≤
      projectiveValveThreeSpaceSubspace p q r s :=
  le_sup_left

/-- O primeiro ponto pertence ao espaço gerado pelo quarteto. -/
theorem projectiveValveDirection_mem_threeSpaceSubspace_first
    (p q r s : ProjectiveValveDirection K) :
    p ∈ (projectiveValveThreeSpaceSubspace p q r s).projectivization := by
  rw [Submodule.mem_projectivization_iff_submodule_le]
  exact le_trans
    (le_trans
      (show p.submodule ≤ projectiveValveLineSubspace p q from le_sup_left)
      (show projectiveValveLineSubspace p q ≤
        projectiveValvePlaneSubspace p q r from le_sup_left))
    (show projectiveValvePlaneSubspace p q r ≤
      projectiveValveThreeSpaceSubspace p q r s from le_sup_left)

/-- O segundo ponto pertence ao espaço gerado pelo quarteto. -/
theorem projectiveValveDirection_mem_threeSpaceSubspace_second
    (p q r s : ProjectiveValveDirection K) :
    q ∈ (projectiveValveThreeSpaceSubspace p q r s).projectivization := by
  rw [Submodule.mem_projectivization_iff_submodule_le]
  exact le_trans
    (le_trans
      (show q.submodule ≤ projectiveValveLineSubspace p q from le_sup_right)
      (show projectiveValveLineSubspace p q ≤
        projectiveValvePlaneSubspace p q r from le_sup_left))
    (show projectiveValvePlaneSubspace p q r ≤
      projectiveValveThreeSpaceSubspace p q r s from le_sup_left)

/-- O terceiro ponto pertence ao espaço gerado pelo quarteto. -/
theorem projectiveValveDirection_mem_threeSpaceSubspace_third
    (p q r s : ProjectiveValveDirection K) :
    r ∈ (projectiveValveThreeSpaceSubspace p q r s).projectivization := by
  rw [Submodule.mem_projectivization_iff_submodule_le]
  exact le_trans
    (show r.submodule ≤ projectiveValvePlaneSubspace p q r from le_sup_right)
    (show projectiveValvePlaneSubspace p q r ≤
      projectiveValveThreeSpaceSubspace p q r s from le_sup_left)

/-- O quarto ponto pertence ao espaço gerado pelo quarteto. -/
theorem projectiveValveDirection_mem_threeSpaceSubspace_fourth
    (p q r s : ProjectiveValveDirection K) :
    s ∈ (projectiveValveThreeSpaceSubspace p q r s).projectivization := by
  rw [Submodule.mem_projectivization_iff_submodule_le]
  exact le_sup_right

/-- Se o quarteto não é coplanar, o representante do quarto ponto não pertence
ao plano dos três primeiros. -/
theorem projectiveValveRep_not_mem_planeSubspace_of_not_coplanar
    (p q r s : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hnotcol : ¬projectiveValveCollinear p q r)
    (hnotcop : ¬projectiveValveCoplanar p q r s) :
    s.rep ∉ projectiveValvePlaneSubspace p q r := by
  intro hs
  have hsSubmoduleLe :
      s.submodule ≤ projectiveValvePlaneSubspace p q r := by
    rw [Projectivization.submodule_eq,
      Submodule.span_singleton_le_iff_mem]
    exact hs
  have hsOnPlane : projectiveValveDirectionOnPlane s p q r := by
    change s ∈ (projectiveValvePlaneSubspace p q r).projectivization
    exact
      (Submodule.mem_projectivization_iff_submodule_le
        (projectiveValvePlaneSubspace p q r) s).2 hsSubmoduleLe
  exact hnotcop
    ((projectiveValveCoplanar_iff_directionOnPlane
      p q r s hpq hnotcol).2 hsOnPlane)

/-- Quatro pontos não coplanares geram um subespaço de dimensão linear
exatamente quatro, isto é, um espaço projetivo tridimensional. -/
theorem projectiveValveThreeSpaceSubspace_finrank_eq_four
    (p q r s : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hnotcol : ¬projectiveValveCollinear p q r)
    (hnotcop : ¬projectiveValveCoplanar p q r s) :
    Module.finrank K (projectiveValveThreeSpaceSubspace p q r s) = 4 := by
  letI : Module.Finite K (projectiveValvePlaneSubspace p q r) :=
    Module.finite_of_finrank_eq_succ
      (projectiveValvePlaneSubspace_finrank_eq_three p q r hpq hnotcol)
  have hdisjoint :
      Disjoint (projectiveValvePlaneSubspace p q r) s.submodule := by
    rw [Projectivization.submodule_eq]
    exact Submodule.disjoint_span_singleton_of_notMem
      (projectiveValveRep_not_mem_planeSubspace_of_not_coplanar
        p q r s hpq hnotcol hnotcop)
  have hdim :=
    Submodule.finrank_sup_add_finrank_inf_eq
      (projectiveValvePlaneSubspace p q r) s.submodule
  rw [hdisjoint.eq_bot, finrank_bot, add_zero,
    projectiveValvePlaneSubspace_finrank_eq_three p q r hpq hnotcol,
    Projectivization.finrank_submodule] at hdim
  simpa only [projectiveValveThreeSpaceSubspace] using hdim

/-- **Quatro pontos não coplanares determinam um único espaço projetivo
tridimensional.**

Todo subespaço de dimensão linear quatro que contém os quatro pontos coincide
com o subespaço canônico gerado por eles. -/
theorem projectiveValveThreeSpaceSubspace_unique
    (p q r s : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hnotcol : ¬projectiveValveCollinear p q r)
    (hnotcop : ¬projectiveValveCoplanar p q r s)
    (U : Submodule K (PowerSeries K))
    (hUrank : Module.finrank K U = 4)
    (hpU : p ∈ U.projectivization)
    (hqU : q ∈ U.projectivization)
    (hrU : r ∈ U.projectivization)
    (hsU : s ∈ U.projectivization) :
    U = projectiveValveThreeSpaceSubspace p q r s := by
  have hpLe : p.submodule ≤ U :=
    (Submodule.mem_projectivization_iff_submodule_le U p).mp hpU
  have hqLe : q.submodule ≤ U :=
    (Submodule.mem_projectivization_iff_submodule_le U q).mp hqU
  have hrLe : r.submodule ≤ U :=
    (Submodule.mem_projectivization_iff_submodule_le U r).mp hrU
  have hsLe : s.submodule ≤ U :=
    (Submodule.mem_projectivization_iff_submodule_le U s).mp hsU
  have hlineLe : projectiveValveLineSubspace p q ≤ U :=
    sup_le hpLe hqLe
  have hplaneLe : projectiveValvePlaneSubspace p q r ≤ U :=
    sup_le hlineLe hrLe
  have hspaceLe : projectiveValveThreeSpaceSubspace p q r s ≤ U :=
    sup_le hplaneLe hsLe
  letI : Module.Finite K U :=
    Module.finite_of_finrank_eq_succ hUrank
  symm
  apply Submodule.eq_of_le_of_finrank_eq hspaceLe
  rw [projectiveValveThreeSpaceSubspace_finrank_eq_four
      p q r s hpq hnotcol hnotcop,
    hUrank]

variable [CharZero K]

/-- Subgrupo multiplicativo associado ao espaço projetivo tridimensional
gerado por quatro direções. -/
noncomputable abbrev projectiveValveThreeSpace
    (p q r s : ProjectiveValveDirection K) :
    Subgroup (NormalizedProjectiveMass K) :=
  projectiveValveSubspaceMasses
    (projectiveValveThreeSpaceSubspace p q r s)

/-- O espaço multiplicativo é o sup do plano dos três primeiros pontos com a
órbita do quarto. -/
theorem projectiveValveThreeSpace_eq_plane_sup_orbit
    (p q r s : ProjectiveValveDirection K) :
    projectiveValveThreeSpace p q r s =
      projectiveValvePlane p q r ⊔ projectiveValveDirectionOrbit s := by
  unfold projectiveValveThreeSpace projectiveValvePlane
  rw [projectiveValveSubspaceMasses_sup,
    ← projectiveValveDirectionOrbit_eq_subspaceMasses (K := K) s]

/-- O plano dos três primeiros pontos está contido no espaço multiplicativo. -/
theorem projectiveValvePlane_le_threeSpace
    (p q r s : ProjectiveValveDirection K) :
    projectiveValvePlane p q r ≤ projectiveValveThreeSpace p q r s := by
  rw [projectiveValveThreeSpace_eq_plane_sup_orbit]
  exact le_sup_left

/-- A órbita do quarto ponto está contida no espaço multiplicativo. -/
theorem projectiveValveDirectionOrbit_le_threeSpace_fourth
    (p q r s : ProjectiveValveDirection K) :
    projectiveValveDirectionOrbit s ≤ projectiveValveThreeSpace p q r s := by
  rw [projectiveValveThreeSpace_eq_plane_sup_orbit]
  exact le_sup_right

/-- Incidência no espaço tridimensional e contenção da órbita multiplicativa
são a mesma condição. -/
theorem projectiveValveDirectionOrbit_le_threeSpace_iff_mem
    (t p q r s : ProjectiveValveDirection K) :
    projectiveValveDirectionOrbit t ≤ projectiveValveThreeSpace p q r s ↔
      t ∈ (projectiveValveThreeSpaceSubspace p q r s).projectivization := by
  rw [projectiveValveDirectionOrbit_eq_subspaceMasses (K := K) t]
  unfold projectiveValveThreeSpace
  rw [projectiveValveSubspaceMasses_le_iff,
    Submodule.mem_projectivization_iff_submodule_le]

/-- O espaço é o menor subgrupo que contém as quatro órbitas geradoras. -/
theorem projectiveValveThreeSpace_le_iff
    (p q r s : ProjectiveValveDirection K)
    (H : Subgroup (NormalizedProjectiveMass K)) :
    projectiveValveThreeSpace p q r s ≤ H ↔
      projectiveValveDirectionOrbit p ≤ H ∧
      projectiveValveDirectionOrbit q ≤ H ∧
      projectiveValveDirectionOrbit r ≤ H ∧
      projectiveValveDirectionOrbit s ≤ H := by
  rw [projectiveValveThreeSpace_eq_plane_sup_orbit,
    sup_le_iff, projectiveValvePlane_le_iff]
  tauto

/-- No lado multiplicativo, todo subespaço de dimensão quatro contendo um
quarteto não coplanar produz exatamente o espaço da válvula determinado pelo
quarteto. -/
theorem projectiveValveSubspaceMasses_eq_threeSpace_of_finrank_four
    (p q r s : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hnotcol : ¬projectiveValveCollinear p q r)
    (hnotcop : ¬projectiveValveCoplanar p q r s)
    (U : Submodule K (PowerSeries K))
    (hUrank : Module.finrank K U = 4)
    (hpU : p ∈ U.projectivization)
    (hqU : q ∈ U.projectivization)
    (hrU : r ∈ U.projectivization)
    (hsU : s ∈ U.projectivization) :
    projectiveValveSubspaceMasses U =
      projectiveValveThreeSpace p q r s := by
  change
    projectiveValveSubspaceMasses U =
      projectiveValveSubspaceMasses
        (projectiveValveThreeSpaceSubspace p q r s)
  rw [projectiveValveThreeSpaceSubspace_unique
    p q r s hpq hnotcol hnotcop U hUrank hpU hqU hrU hsU]

end CarrySelfAdjointOperator.ProjectiveValve
