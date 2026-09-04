import CarrySelfAdjointOperator.ProjectiveValveLineGeometry

/-!
# Incidência e regeneração das linhas da válvula projetiva

A geometria de linhas já prova que duas direções projetivas distintas geram
um único subespaço de dimensão dois. A consequência natural é a propriedade de
regeneração:

* quaisquer dois pontos distintos de uma linha geram novamente a mesma linha;
* a igualdade de duas linhas pode ser reconhecida pela incidência de um par de
  geradores;
* no lado multiplicativo, isso equivale à contenção das duas órbitas escalares.

Assim a linha deixa de depender do par escolhido para apresentá-la. O par é
somente uma base projetiva da mesma geometria bidimensional.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries
open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K]

/-- A direção `r` pertence à linha projetiva determinada por `p` e `q`. -/
noncomputable abbrev projectiveValveDirectionOnLine
    (r p q : ProjectiveValveDirection K) : Prop :=
  r ∈ (projectiveValveLineSubspace p q).projectivization

/-- O primeiro gerador pertence à linha que ele determina. -/
@[simp] theorem projectiveValveDirectionOnLine_left
    (p q : ProjectiveValveDirection K) :
    projectiveValveDirectionOnLine p p q :=
  projectiveValveDirection_mem_lineSubspace_left p q

/-- O segundo gerador pertence à linha que ele determina. -/
@[simp] theorem projectiveValveDirectionOnLine_right
    (p q : ProjectiveValveDirection K) :
    projectiveValveDirectionOnLine q p q :=
  projectiveValveDirection_mem_lineSubspace_right p q

/-- **Regeneração da linha por dois de seus pontos.**

Se `p ≠ q` determinam uma linha e `r ≠ s` são dois pontos dessa linha, então o
subespaço gerado por `r,s` é exatamente o subespaço gerado por `p,q`. -/
theorem projectiveValveLineSubspace_eq_of_pair_on_line
    (p q r s : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hrs : r ≠ s)
    (hr : projectiveValveDirectionOnLine r p q)
    (hs : projectiveValveDirectionOnLine s p q) :
    projectiveValveLineSubspace r s =
      projectiveValveLineSubspace p q := by
  symm
  exact
    projectiveValveLineSubspace_unique
      r s hrs
      (projectiveValveLineSubspace p q)
      (projectiveValveLineSubspace_finrank_eq_two p q hpq)
      hr hs

/-- Para dois pares distintos, igualdade dos subespaços de linha equivale a o
segundo par pertencer à linha do primeiro. -/
theorem projectiveValveLineSubspace_eq_iff_pair_on_line
    (p q r s : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hrs : r ≠ s) :
    projectiveValveLineSubspace r s =
        projectiveValveLineSubspace p q ↔
      projectiveValveDirectionOnLine r p q ∧
        projectiveValveDirectionOnLine s p q := by
  constructor
  · intro hlines
    constructor
    · change r ∈ (projectiveValveLineSubspace p q).projectivization
      rw [← hlines]
      exact projectiveValveDirection_mem_lineSubspace_left r s
    · change s ∈ (projectiveValveLineSubspace p q).projectivization
      rw [← hlines]
      exact projectiveValveDirection_mem_lineSubspace_right r s
  · rintro ⟨hr, hs⟩
    exact
      projectiveValveLineSubspace_eq_of_pair_on_line
        p q r s hpq hrs hr hs

variable [CharZero K]

/-- Incidência projetiva e contenção da órbita multiplicativa são a mesma
condição. -/
theorem projectiveValveDirectionOnLine_iff_orbit_le
    (r p q : ProjectiveValveDirection K) :
    projectiveValveDirectionOnLine r p q ↔
      projectiveValveDirectionOrbit r ≤ projectiveValveLine p q :=
  (projectiveValveDirectionOrbit_le_line_iff_mem
    (K := K) r p q).symm

/-- Dois pontos distintos já pertencentes a uma linha regeneram também o mesmo
subgrupo multiplicativo da linha. -/
theorem projectiveValveLine_eq_of_pair_on_line
    (p q r s : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hrs : r ≠ s)
    (hr : projectiveValveDirectionOnLine r p q)
    (hs : projectiveValveDirectionOnLine s p q) :
    projectiveValveLine r s = projectiveValveLine p q := by
  have hsub :
      projectiveValveLineSubspace r s =
        projectiveValveLineSubspace p q :=
    projectiveValveLineSubspace_eq_of_pair_on_line
      p q r s hpq hrs hr hs
  calc
    projectiveValveLine r s =
        projectiveValveSubspaceMasses
          (projectiveValveLineSubspace r s) :=
      projectiveValveLine_eq_subspaceMasses_lineSubspace r s
    _ = projectiveValveSubspaceMasses
          (projectiveValveLineSubspace p q) := by
      rw [hsub]
    _ = projectiveValveLine p q :=
      (projectiveValveLine_eq_subspaceMasses_lineSubspace p q).symm

/-- Para dois pares de pontos distintos, duas linhas multiplicativas são iguais
exatamente quando as órbitas do segundo par estão contidas na primeira linha. -/
theorem projectiveValveLine_eq_iff_pair_orbits_le
    (p q r s : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hrs : r ≠ s) :
    projectiveValveLine r s = projectiveValveLine p q ↔
      projectiveValveDirectionOrbit r ≤ projectiveValveLine p q ∧
        projectiveValveDirectionOrbit s ≤ projectiveValveLine p q := by
  constructor
  · intro hlines
    constructor
    · rw [← hlines]
      exact projectiveValveDirectionOrbit_le_line_left r s
    · rw [← hlines]
      exact projectiveValveDirectionOrbit_le_line_right r s
  · rintro ⟨hr, hs⟩
    apply projectiveValveLine_eq_of_pair_on_line p q r s hpq hrs
    · exact
        (projectiveValveDirectionOrbit_le_line_iff_mem
          (K := K) r p q).mp hr
    · exact
        (projectiveValveDirectionOrbit_le_line_iff_mem
          (K := K) s p q).mp hs

/-- Forma puramente incidencial da regeneração: se duas direções distintas têm
suas órbitas dentro de uma linha, elas geram essa linha inteira. -/
theorem projectiveValveLine_eq_of_pair_orbits_le
    (p q r s : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hrs : r ≠ s)
    (hr : projectiveValveDirectionOrbit r ≤ projectiveValveLine p q)
    (hs : projectiveValveDirectionOrbit s ≤ projectiveValveLine p q) :
    projectiveValveLine r s = projectiveValveLine p q :=
  (projectiveValveLine_eq_iff_pair_orbits_le
    p q r s hpq hrs).2 ⟨hr, hs⟩

end CarrySelfAdjointOperator.ProjectiveValve
