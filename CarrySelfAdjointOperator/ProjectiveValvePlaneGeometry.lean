import CarrySelfAdjointOperator.ProjectiveValveCollinearity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Geometria dos planos da válvula projetiva

A geometria de linhas já identifica colinearidade com incidência na linha e
com contenção da órbita multiplicativa. O próximo salto estrutural é o plano
gerado por três direções não colineares.

O subespaço subjacente é a soma da linha dos dois primeiros pontos com a reta
do terceiro. Quando o terceiro ponto não pertence à linha, essa soma tem
posto exatamente três. No lado multiplicativo, o plano é o menor subgrupo de
massas normalizadas que contém as três órbitas escalares.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries
open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K]

/-- Subespaço linear subjacente ao plano gerado por três direções. -/
noncomputable abbrev projectiveValvePlaneSubspace
    (p q r : ProjectiveValveDirection K) :
    Submodule K (PowerSeries K) :=
  projectiveValveLineSubspace p q ⊔ r.submodule

/-- A linha dos dois primeiros pontos está contida no plano do trio. -/
theorem projectiveValveLineSubspace_le_planeSubspace
    (p q r : ProjectiveValveDirection K) :
    projectiveValveLineSubspace p q ≤
      projectiveValvePlaneSubspace p q r :=
  le_sup_left

/-- O primeiro ponto pertence ao plano gerado pelo trio. -/
theorem projectiveValveDirection_mem_planeSubspace_left
    (p q r : ProjectiveValveDirection K) :
    p ∈ (projectiveValvePlaneSubspace p q r).projectivization := by
  rw [Submodule.mem_projectivization_iff_submodule_le]
  exact le_trans
    (show p.submodule ≤ projectiveValveLineSubspace p q from le_sup_left)
    (show projectiveValveLineSubspace p q ≤
      projectiveValvePlaneSubspace p q r from le_sup_left)

/-- O segundo ponto pertence ao plano gerado pelo trio. -/
theorem projectiveValveDirection_mem_planeSubspace_middle
    (p q r : ProjectiveValveDirection K) :
    q ∈ (projectiveValvePlaneSubspace p q r).projectivization := by
  rw [Submodule.mem_projectivization_iff_submodule_le]
  exact le_trans
    (show q.submodule ≤ projectiveValveLineSubspace p q from le_sup_right)
    (show projectiveValveLineSubspace p q ≤
      projectiveValvePlaneSubspace p q r from le_sup_left)

/-- O terceiro ponto pertence ao plano gerado pelo trio. -/
theorem projectiveValveDirection_mem_planeSubspace_right
    (p q r : ProjectiveValveDirection K) :
    r ∈ (projectiveValvePlaneSubspace p q r).projectivization := by
  rw [Submodule.mem_projectivization_iff_submodule_le]
  exact le_sup_right

/-- Se o trio não é colinear, o representante do terceiro ponto não pertence
à linha dos dois primeiros. -/
theorem projectiveValveRep_not_mem_lineSubspace_of_not_collinear
    (p q r : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hnotcol : ¬projectiveValveCollinear p q r) :
    r.rep ∉ projectiveValveLineSubspace p q := by
  intro hr
  have hrSubmoduleLe :
      r.submodule ≤ projectiveValveLineSubspace p q := by
    rw [Projectivization.submodule_eq]
    exact Submodule.span_singleton_le_iff_mem.mpr hr
  have hrOnLine : projectiveValveDirectionOnLine r p q := by
    rw [Submodule.mem_projectivization_iff_submodule_le]
    exact hrSubmoduleLe
  exact hnotcol
    ((projectiveValveCollinear_iff_directionOnLine p q r hpq).2 hrOnLine)

/-- Três pontos não colineares geram um subespaço de dimensão exatamente três. -/
theorem projectiveValvePlaneSubspace_finrank_eq_three
    (p q r : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hnotcol : ¬projectiveValveCollinear p q r) :
    Module.finrank K (projectiveValvePlaneSubspace p q r) = 3 := by
  letI : Module.Finite K (projectiveValveLineSubspace p q) :=
    Module.finite_of_finrank_eq_succ
      (projectiveValveLineSubspace_finrank_eq_two p q hpq)
  have hdisjoint :
      Disjoint (projectiveValveLineSubspace p q) r.submodule := by
    rw [Projectivization.submodule_eq]
    exact Submodule.disjoint_span_singleton_of_notMem
      (projectiveValveRep_not_mem_lineSubspace_of_not_collinear
        p q r hpq hnotcol)
  have hdim :=
    Submodule.finrank_sup_add_finrank_inf_eq
      (projectiveValveLineSubspace p q) r.submodule
  rw [hdisjoint.eq_bot,
    projectiveValveLineSubspace_finrank_eq_two p q hpq,
    Projectivization.finrank_submodule,
    Submodule.finrank_bot] at hdim
  simpa [projectiveValvePlaneSubspace] using hdim

/-- **Três pontos não colineares determinam um único plano.**

Todo subespaço de dimensão três que contém os três pontos coincide com o
subespaço canônico gerado por eles. -/
theorem projectiveValvePlaneSubspace_unique
    (p q r : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hnotcol : ¬projectiveValveCollinear p q r)
    (U : Submodule K (PowerSeries K))
    (hUrank : Module.finrank K U = 3)
    (hpU : p ∈ U.projectivization)
    (hqU : q ∈ U.projectivization)
    (hrU : r ∈ U.projectivization) :
    U = projectiveValvePlaneSubspace p q r := by
  have hpLe : p.submodule ≤ U :=
    (Submodule.mem_projectivization_iff_submodule_le U p).mp hpU
  have hqLe : q.submodule ≤ U :=
    (Submodule.mem_projectivization_iff_submodule_le U q).mp hqU
  have hrLe : r.submodule ≤ U :=
    (Submodule.mem_projectivization_iff_submodule_le U r).mp hrU
  have hlineLe : projectiveValveLineSubspace p q ≤ U :=
    sup_le hpLe hqLe
  have hplaneLe : projectiveValvePlaneSubspace p q r ≤ U :=
    sup_le hlineLe hrLe
  letI : Module.Finite K U :=
    Module.finite_of_finrank_eq_succ hUrank
  symm
  apply Submodule.eq_of_le_of_finrank_eq hplaneLe
  rw [projectiveValvePlaneSubspace_finrank_eq_three p q r hpq hnotcol,
    hUrank]

variable [CharZero K]

/-- Subgrupo multiplicativo associado ao plano gerado por três direções. -/
noncomputable abbrev projectiveValvePlane
    (p q r : ProjectiveValveDirection K) :
    Subgroup (NormalizedProjectiveMass K) :=
  projectiveValveSubspaceMasses (projectiveValvePlaneSubspace p q r)

/-- O plano multiplicativo é o sup da linha dos dois primeiros pontos com a
órbita do terceiro. -/
theorem projectiveValvePlane_eq_line_sup_orbit
    (p q r : ProjectiveValveDirection K) :
    projectiveValvePlane p q r =
      projectiveValveLine p q ⊔ projectiveValveDirectionOrbit r := by
  change
    projectiveValveSubspaceMasses
        (projectiveValveLineSubspace p q ⊔ r.submodule) =
      projectiveValveLine p q ⊔ projectiveValveDirectionOrbit r
  rw [projectiveValveSubspaceMasses_sup,
    ← projectiveValveLine_eq_subspaceMasses_lineSubspace p q,
    ← projectiveValveDirectionOrbit_eq_subspaceMasses r]

/-- A linha dos dois primeiros pontos está contida no plano multiplicativo. -/
theorem projectiveValveLine_le_plane
    (p q r : ProjectiveValveDirection K) :
    projectiveValveLine p q ≤ projectiveValvePlane p q r := by
  rw [projectiveValvePlane_eq_line_sup_orbit]
  exact le_sup_left

/-- A órbita do terceiro ponto está contida no plano multiplicativo. -/
theorem projectiveValveDirectionOrbit_le_plane_right
    (p q r : ProjectiveValveDirection K) :
    projectiveValveDirectionOrbit r ≤ projectiveValvePlane p q r := by
  rw [projectiveValvePlane_eq_line_sup_orbit]
  exact le_sup_right

/-- Incidência no plano e contenção da órbita multiplicativa são a mesma
condição. -/
theorem projectiveValveDirectionOrbit_le_plane_iff_mem
    (s p q r : ProjectiveValveDirection K) :
    projectiveValveDirectionOrbit s ≤ projectiveValvePlane p q r ↔
      s ∈ (projectiveValvePlaneSubspace p q r).projectivization := by
  change
    projectiveValveSubspaceMasses s.submodule ≤
        projectiveValveSubspaceMasses
          (projectiveValvePlaneSubspace p q r) ↔
      s ∈ (projectiveValvePlaneSubspace p q r).projectivization
  rw [projectiveValveSubspaceMasses_le_iff,
    Submodule.mem_projectivization_iff_submodule_le]

/-- O plano é o menor subgrupo que contém as três órbitas geradoras. -/
theorem projectiveValvePlane_le_iff
    (p q r : ProjectiveValveDirection K)
    (H : Subgroup (NormalizedProjectiveMass K)) :
    projectiveValvePlane p q r ≤ H ↔
      projectiveValveDirectionOrbit p ≤ H ∧
      projectiveValveDirectionOrbit q ≤ H ∧
      projectiveValveDirectionOrbit r ≤ H := by
  rw [projectiveValvePlane_eq_line_sup_orbit,
    sup_le_iff, projectiveValveLine_le_iff]
  tauto

/-- No lado multiplicativo, todo subespaço de dimensão três contendo um trio
não colinear produz exatamente o plano da válvula determinado por esse trio. -/
theorem projectiveValveSubspaceMasses_eq_plane_of_finrank_three
    (p q r : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hnotcol : ¬projectiveValveCollinear p q r)
    (U : Submodule K (PowerSeries K))
    (hUrank : Module.finrank K U = 3)
    (hpU : p ∈ U.projectivization)
    (hqU : q ∈ U.projectivization)
    (hrU : r ∈ U.projectivization) :
    projectiveValveSubspaceMasses U = projectiveValvePlane p q r := by
  change
    projectiveValveSubspaceMasses U =
      projectiveValveSubspaceMasses
        (projectiveValvePlaneSubspace p q r)
  rw [projectiveValvePlaneSubspace_unique
    p q r hpq hnotcol U hUrank hpU hqU hrU]

end CarrySelfAdjointOperator.ProjectiveValve
