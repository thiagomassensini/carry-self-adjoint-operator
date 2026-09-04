import CarrySelfAdjointOperator.ProjectiveValveSubspaceLattice
import Mathlib.LinearAlgebra.Projectivization.Collinear

/-!
# Geometria das linhas da válvula projetiva

O reticulado de subespaços já define o subgrupo multiplicativo gerado por duas
direções projetivas. Este arquivo identifica o subespaço linear subjacente,
prova que ele tem posto exatamente dois quando os pontos são distintos e
transporta para a válvula o teorema clássico de unicidade da linha por dois
pontos.

Assim, para `p ≠ q`, a linha da válvula não é apenas o sup abstrato de duas
órbitas: ela é a imagem multiplicativa do único subespaço bidimensional que
contém as duas direções.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries
open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K] [CharZero K]

/-- Subespaço linear subjacente à linha determinada por duas direções. -/
noncomputable abbrev projectiveValveLineSubspace
    (p q : ProjectiveValveDirection K) :
    Submodule K (PowerSeries K) :=
  p.submodule ⊔ q.submodule

/-- A linha multiplicativa é exatamente o subgrupo associado ao seu subespaço
linear subjacente. -/
@[simp] theorem projectiveValveLine_eq_subspaceMasses_lineSubspace
    (p q : ProjectiveValveDirection K) :
    projectiveValveLine p q =
      projectiveValveSubspaceMasses
        (projectiveValveLineSubspace p q) :=
  rfl

omit [CharZero K] in
/-- O subespaço da linha é o span dos representantes canônicos dos dois
pontos. -/
theorem projectiveValveLineSubspace_eq_span_pair
    (p q : ProjectiveValveDirection K) :
    projectiveValveLineSubspace p q =
      Submodule.span K
        ({p.rep, q.rep} : Set (PowerSeries K)) := by
  calc
    projectiveValveLineSubspace p q =
        (K ∙ p.rep) ⊔ (K ∙ q.rep) := by
      change p.submodule ⊔ q.submodule =
        (K ∙ p.rep) ⊔ (K ∙ q.rep)
      rw [Projectivization.submodule_eq,
        Projectivization.submodule_eq]
    _ = Submodule.span K
        ({p.rep, q.rep} : Set (PowerSeries K)) := by
      symm
      exact
        Submodule.span_insert p.rep
          ({q.rep} : Set (PowerSeries K))

omit [CharZero K] in
/-- A primeira direção pertence à linha determinada pelo par. -/
theorem projectiveValveDirection_mem_lineSubspace_left
    (p q : ProjectiveValveDirection K) :
    p ∈ (projectiveValveLineSubspace p q).projectivization := by
  rw [Submodule.mem_projectivization_iff_submodule_le]
  exact le_sup_left

omit [CharZero K] in
/-- A segunda direção pertence à linha determinada pelo par. -/
theorem projectiveValveDirection_mem_lineSubspace_right
    (p q : ProjectiveValveDirection K) :
    q ∈ (projectiveValveLineSubspace p q).projectivization := by
  rw [Submodule.mem_projectivization_iff_submodule_le]
  exact le_sup_right

omit [CharZero K] in
/-- Duas direções distintas geram um subespaço de dimensão exatamente dois. -/
theorem projectiveValveLineSubspace_finrank_eq_two
    (p q : ProjectiveValveDirection K)
    (hpq : p ≠ q) :
    Module.finrank K (projectiveValveLineSubspace p q) = 2 := by
  rw [projectiveValveLineSubspace_eq_span_pair]
  have hlin : LinearIndependent K ![p.rep, q.rep] :=
    (Projectivization.linearIndependent_pair_iff_ne
      (K := K) (V := PowerSeries K)
      (D := p) (D' := q)).2 hpq
  rw [← Matrix.range_cons_cons_empty p.rep q.rep ![]]
  simpa using finrank_span_eq_card hlin

omit [CharZero K] in
/-- **Dois pontos projetivos distintos determinam uma única linha.**

Todo subespaço de dimensão dois que contém `p` e `q` coincide com o subespaço
canônico gerado por suas duas direções. -/
theorem projectiveValveLineSubspace_unique
    (p q : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (U : Submodule K (PowerSeries K))
    (hUrank : Module.finrank K U = 2)
    (hpU : p ∈ U.projectivization)
    (hqU : q ∈ U.projectivization) :
    U = projectiveValveLineSubspace p q := by
  exact
    Projectivization.line_unique
      (K := K) (V := PowerSeries K)
      hpq U (projectiveValveLineSubspace p q)
      hUrank
      (projectiveValveLineSubspace_finrank_eq_two p q hpq)
      hpU hqU
      (projectiveValveDirection_mem_lineSubspace_left p q)
      (projectiveValveDirection_mem_lineSubspace_right p q)

/-- Uma direção pertence à linha projetiva exatamente quando sua órbita está
contida no subgrupo multiplicativo da linha. -/
theorem projectiveValveDirectionOrbit_le_line_iff_mem
    (r p q : ProjectiveValveDirection K) :
    projectiveValveDirectionOrbit r ≤ projectiveValveLine p q ↔
      r ∈ (projectiveValveLineSubspace p q).projectivization := by
  rw [projectiveValveDirectionOrbit_eq_subspaceMasses,
    projectiveValveLine_eq_subspaceMasses_lineSubspace,
    projectiveValveSubspaceMasses_le_iff,
    Submodule.mem_projectivization_iff_submodule_le]

/-- No lado multiplicativo, qualquer subespaço de posto dois contendo os dois
pontos produz exatamente a linha da válvula determinada por eles. -/
theorem projectiveValveSubspaceMasses_eq_line_of_finrank_two
    (p q : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (U : Submodule K (PowerSeries K))
    (hUrank : Module.finrank K U = 2)
    (hpU : p ∈ U.projectivization)
    (hqU : q ∈ U.projectivization) :
    projectiveValveSubspaceMasses U = projectiveValveLine p q := by
  rw [projectiveValveLineSubspace_unique p q hpq U hUrank hpU hqU]
  rfl

end CarrySelfAdjointOperator.ProjectiveValve
