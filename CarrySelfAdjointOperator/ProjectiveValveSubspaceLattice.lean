import CarrySelfAdjointOperator.ProjectiveValveSubspaceGeometry

/-!
# Reticulado dos subespaços da válvula projetiva

O arquivo de geometria de subespaços associa a cada submódulo de curvaturas

`U ≤ K⟦X⟧`

o subgrupo das massas normalizadas cuja curvatura pertence a `U`.

Já sabemos que essa associação reflete inclusões, preserva interseções e
recupera as órbitas escalares em posto um. Aqui fechamos a operação dual:

* o subespaço nulo corresponde ao subgrupo trivial;
* o subespaço total corresponde ao grupo total de massas normalizadas;
* soma de subespaços corresponde ao sup dos subgrupos de massas;
* duas direções projetivas determinam o menor subgrupo de massas que contém
  ambas as órbitas.

Assim a linha projetiva gerada por duas direções aparece como o caso de posto
no máximo dois da mesma correspondência de subespaços.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries
open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K] [CharZero K]

/-- O subespaço nulo produz apenas a massa unidade. -/
@[simp] theorem projectiveValveSubspaceMasses_bot :
    projectiveValveSubspaceMasses
        (⊥ : Submodule K (PowerSeries K)) = ⊥ := by
  apply bot_unique
  intro A hA
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  change A.1 = (1 : PowerSeries K)
  have hCurv : projectiveValveCurvature A.1 = 0 := by
    change projectiveValveCurvature A.1 ∈
      (⊥ : Submodule K (PowerSeries K)) at hA
    simpa using hA
  calc
    A.1 = projectiveValveMass (projectiveValveCurvature A.1) :=
      (projectiveValveMass_projectiveValveCurvature A.1 A.2).symm
    _ = projectiveValveMass (0 : PowerSeries K) := by rw [hCurv]
    _ = 1 := projectiveValveMass_zero (K := K)

/-- O subespaço total produz todo o grupo de massas normalizadas. -/
@[simp] theorem projectiveValveSubspaceMasses_top :
    projectiveValveSubspaceMasses
        (⊤ : Submodule K (PowerSeries K)) = ⊤ := by
  apply top_unique
  intro A _hA
  change projectiveValveCurvature A.1 ∈
    (⊤ : Submodule K (PowerSeries K))
  exact Submodule.mem_top

/-- Soma de subespaços vira o subgrupo gerado pelos dois subgrupos de massas. -/
@[simp] theorem projectiveValveSubspaceMasses_sup
    (U V : Submodule K (PowerSeries K)) :
    projectiveValveSubspaceMasses (U ⊔ V) =
      projectiveValveSubspaceMasses U ⊔
        projectiveValveSubspaceMasses V := by
  apply le_antisymm
  · intro A hA
    change projectiveValveCurvature A.1 ∈ U ⊔ V at hA
    rcases (Submodule.mem_sup.mp hA) with
      ⟨D, hDU, E, hEV, hDE⟩
    let AD : NormalizedProjectiveMass K :=
      ⟨projectiveValveMass D,
        projectiveValveMass_constantCoeff D⟩
    let AE : NormalizedProjectiveMass K :=
      ⟨projectiveValveMass E,
        projectiveValveMass_constantCoeff E⟩
    have hAD : AD ∈ projectiveValveSubspaceMasses U := by
      change
        (⟨projectiveValveMass D,
            projectiveValveMass_constantCoeff D⟩ :
          NormalizedProjectiveMass K) ∈
            projectiveValveSubspaceMasses U
      exact projectiveValveMass_mem_subspaceMasses
        (K := K) U hDU
    have hAE : AE ∈ projectiveValveSubspaceMasses V := by
      change
        (⟨projectiveValveMass E,
            projectiveValveMass_constantCoeff E⟩ :
          NormalizedProjectiveMass K) ∈
            projectiveValveSubspaceMasses V
      exact projectiveValveMass_mem_subspaceMasses
        (K := K) V hEV
    have hProduct :
        AD * AE ∈
          projectiveValveSubspaceMasses U ⊔
            projectiveValveSubspaceMasses V :=
      Subgroup.mul_mem_sup hAD hAE
    have hAeq : A = AD * AE := by
      apply Subtype.ext
      change A.1 = projectiveValveMass D * projectiveValveMass E
      calc
        A.1 =
            projectiveValveMass (projectiveValveCurvature A.1) :=
          (projectiveValveMass_projectiveValveCurvature A.1 A.2).symm
        _ = projectiveValveMass (D + E) :=
          congrArg
            (projectiveValveMass :
              PowerSeries K → PowerSeries K)
            hDE.symm
        _ = projectiveValveMass D * projectiveValveMass E :=
          projectiveValveMass_add D E
    rw [hAeq]
    exact hProduct
  · apply sup_le
    · exact
        (projectiveValveSubspaceMasses_le_iff
          (K := K) U (U ⊔ V)).2 le_sup_left
    · exact
        (projectiveValveSubspaceMasses_le_iff
          (K := K) V (U ⊔ V)).2 le_sup_right

/-- O subgrupo de massas determinado pelas duas direções projetivas `p` e
`q`. Ele corresponde ao subespaço linear gerado pelas duas retas. -/
noncomputable def projectiveValveLine
    (p q : ProjectiveValveDirection K) :
    Subgroup (NormalizedProjectiveMass K) :=
  projectiveValveSubspaceMasses (p.submodule ⊔ q.submodule)

/-- A linha projetiva é exatamente o sup das duas órbitas escalares. -/
theorem projectiveValveLine_eq_sup_orbits
    (p q : ProjectiveValveDirection K) :
    projectiveValveLine p q =
      projectiveValveDirectionOrbit p ⊔
        projectiveValveDirectionOrbit q := by
  unfold projectiveValveLine
  rw [projectiveValveSubspaceMasses_sup,
    ← projectiveValveDirectionOrbit_eq_subspaceMasses p,
    ← projectiveValveDirectionOrbit_eq_subspaceMasses q]

/-- A órbita da primeira direção está contida na linha determinada pelo par. -/
theorem projectiveValveDirectionOrbit_le_line_left
    (p q : ProjectiveValveDirection K) :
    projectiveValveDirectionOrbit p ≤ projectiveValveLine p q := by
  rw [projectiveValveLine_eq_sup_orbits]
  exact le_sup_left

/-- A órbita da segunda direção está contida na linha determinada pelo par. -/
theorem projectiveValveDirectionOrbit_le_line_right
    (p q : ProjectiveValveDirection K) :
    projectiveValveDirectionOrbit q ≤ projectiveValveLine p q := by
  rw [projectiveValveLine_eq_sup_orbits]
  exact le_sup_right

/-- A linha é o menor subgrupo que contém as órbitas das duas direções. -/
theorem projectiveValveLine_le_iff
    (p q : ProjectiveValveDirection K)
    (H : Subgroup (NormalizedProjectiveMass K)) :
    projectiveValveLine p q ≤ H ↔
      projectiveValveDirectionOrbit p ≤ H ∧
        projectiveValveDirectionOrbit q ≤ H := by
  rw [projectiveValveLine_eq_sup_orbits, sup_le_iff]

/-- A linha não depende da ordem dos dois pontos. -/
@[simp] theorem projectiveValveLine_comm
    (p q : ProjectiveValveDirection K) :
    projectiveValveLine p q = projectiveValveLine q p := by
  unfold projectiveValveLine
  rw [sup_comm]

/-- Um ponto repetido gera apenas sua própria órbita unidimensional. -/
@[simp] theorem projectiveValveLine_self
    (p : ProjectiveValveDirection K) :
    projectiveValveLine p p = projectiveValveDirectionOrbit p := by
  rw [projectiveValveLine_eq_sup_orbits, sup_idem]

end CarrySelfAdjointOperator.ProjectiveValve
