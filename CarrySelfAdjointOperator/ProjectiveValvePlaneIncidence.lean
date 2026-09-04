import CarrySelfAdjointOperator.ProjectiveValvePlaneGeometry

/-!
# Incidência e regeneração dos planos da válvula projetiva

A geometria de planos já prova que um trio não colinear gera um único
subespaço de dimensão três e o correspondente subgrupo multiplicativo de
massas normalizadas.

Este arquivo formaliza a consequência natural:

* qualquer trio não colinear contido em um plano regenera o mesmo plano;
* a igualdade de dois planos pode ser reconhecida pela incidência de um trio
  gerador;
* no lado multiplicativo, essa incidência é exatamente a contenção das três
  órbitas escalares.

Assim, o plano deixa de depender do trio particular usado para apresentá-lo.
O trio é apenas uma base projetiva do mesmo subespaço tridimensional.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries
open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K]

/-- A direção `s` pertence ao plano projetivo determinado por `p,q,r`. -/
noncomputable abbrev projectiveValveDirectionOnPlane
    (s p q r : ProjectiveValveDirection K) : Prop :=
  s ∈ (projectiveValvePlaneSubspace p q r).projectivization

/-- O primeiro gerador pertence ao plano que ele determina. -/
@[simp] theorem projectiveValveDirectionOnPlane_left
    (p q r : ProjectiveValveDirection K) :
    projectiveValveDirectionOnPlane p p q r :=
  projectiveValveDirection_mem_planeSubspace_left p q r

/-- O segundo gerador pertence ao plano que ele determina. -/
@[simp] theorem projectiveValveDirectionOnPlane_middle
    (p q r : ProjectiveValveDirection K) :
    projectiveValveDirectionOnPlane q p q r :=
  projectiveValveDirection_mem_planeSubspace_middle p q r

/-- O terceiro gerador pertence ao plano que ele determina. -/
@[simp] theorem projectiveValveDirectionOnPlane_right
    (p q r : ProjectiveValveDirection K) :
    projectiveValveDirectionOnPlane r p q r :=
  projectiveValveDirection_mem_planeSubspace_right p q r

/-- **Regeneração do plano por três de seus pontos.**

Se `p,q,r` geram um plano e `a,b,c` são três pontos não colineares desse
plano, então o subespaço gerado por `a,b,c` é exatamente o plano original. -/
theorem projectiveValvePlaneSubspace_eq_of_triple_on_plane
    (p q r a b c : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hpqr : ¬projectiveValveCollinear p q r)
    (hab : a ≠ b)
    (habc : ¬projectiveValveCollinear a b c)
    (ha : projectiveValveDirectionOnPlane a p q r)
    (hb : projectiveValveDirectionOnPlane b p q r)
    (hc : projectiveValveDirectionOnPlane c p q r) :
    projectiveValvePlaneSubspace a b c =
      projectiveValvePlaneSubspace p q r := by
  symm
  exact
    projectiveValvePlaneSubspace_unique
      a b c hab habc
      (projectiveValvePlaneSubspace p q r)
      (projectiveValvePlaneSubspace_finrank_eq_three p q r hpq hpqr)
      ha hb hc

/-- Para dois trios não colineares, igualdade dos subespaços de plano equivale
a o segundo trio pertencer ao plano do primeiro. -/
theorem projectiveValvePlaneSubspace_eq_iff_triple_on_plane
    (p q r a b c : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hpqr : ¬projectiveValveCollinear p q r)
    (hab : a ≠ b)
    (habc : ¬projectiveValveCollinear a b c) :
    projectiveValvePlaneSubspace a b c =
        projectiveValvePlaneSubspace p q r ↔
      projectiveValveDirectionOnPlane a p q r ∧
        projectiveValveDirectionOnPlane b p q r ∧
        projectiveValveDirectionOnPlane c p q r := by
  constructor
  · intro hplanes
    constructor
    · change a ∈ (projectiveValvePlaneSubspace p q r).projectivization
      rw [← hplanes]
      exact projectiveValveDirection_mem_planeSubspace_left a b c
    · constructor
      · change b ∈ (projectiveValvePlaneSubspace p q r).projectivization
        rw [← hplanes]
        exact projectiveValveDirection_mem_planeSubspace_middle a b c
      · change c ∈ (projectiveValvePlaneSubspace p q r).projectivization
        rw [← hplanes]
        exact projectiveValveDirection_mem_planeSubspace_right a b c
  · rintro ⟨ha, hb, hc⟩
    exact
      projectiveValvePlaneSubspace_eq_of_triple_on_plane
        p q r a b c hpq hpqr hab habc ha hb hc

variable [CharZero K]

/-- Incidência projetiva no plano e contenção da órbita multiplicativa são a
mesma condição. -/
theorem projectiveValveDirectionOnPlane_iff_orbit_le
    (s p q r : ProjectiveValveDirection K) :
    projectiveValveDirectionOnPlane s p q r ↔
      projectiveValveDirectionOrbit s ≤ projectiveValvePlane p q r :=
  (projectiveValveDirectionOrbit_le_plane_iff_mem
    (K := K) s p q r).symm

/-- Três pontos não colineares já pertencentes a um plano regeneram o mesmo
subgrupo multiplicativo do plano. -/
theorem projectiveValvePlane_eq_of_triple_on_plane
    (p q r a b c : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hpqr : ¬projectiveValveCollinear p q r)
    (hab : a ≠ b)
    (habc : ¬projectiveValveCollinear a b c)
    (ha : projectiveValveDirectionOnPlane a p q r)
    (hb : projectiveValveDirectionOnPlane b p q r)
    (hc : projectiveValveDirectionOnPlane c p q r) :
    projectiveValvePlane a b c = projectiveValvePlane p q r := by
  have hsub :
      projectiveValvePlaneSubspace a b c =
        projectiveValvePlaneSubspace p q r :=
    projectiveValvePlaneSubspace_eq_of_triple_on_plane
      p q r a b c hpq hpqr hab habc ha hb hc
  unfold projectiveValvePlane
  rw [hsub]

/-- Para dois trios não colineares, duas massas-plano são iguais exatamente
quando as órbitas do segundo trio estão contidas no primeiro plano. -/
theorem projectiveValvePlane_eq_iff_triple_orbits_le
    (p q r a b c : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hpqr : ¬projectiveValveCollinear p q r)
    (hab : a ≠ b)
    (habc : ¬projectiveValveCollinear a b c) :
    projectiveValvePlane a b c = projectiveValvePlane p q r ↔
      projectiveValveDirectionOrbit a ≤ projectiveValvePlane p q r ∧
        projectiveValveDirectionOrbit b ≤ projectiveValvePlane p q r ∧
        projectiveValveDirectionOrbit c ≤ projectiveValvePlane p q r := by
  constructor
  · intro hplanes
    constructor
    · rw [← hplanes]
      exact le_trans
        (projectiveValveDirectionOrbit_le_line_left a b)
        (projectiveValveLine_le_plane a b c)
    · constructor
      · rw [← hplanes]
        exact le_trans
          (projectiveValveDirectionOrbit_le_line_right a b)
          (projectiveValveLine_le_plane a b c)
      · rw [← hplanes]
        exact projectiveValveDirectionOrbit_le_plane_right a b c
  · rintro ⟨ha, hb, hc⟩
    apply
      projectiveValvePlane_eq_of_triple_on_plane
        p q r a b c hpq hpqr hab habc
    · exact
        (projectiveValveDirectionOnPlane_iff_orbit_le
          (K := K) a p q r).2 ha
    · exact
        (projectiveValveDirectionOnPlane_iff_orbit_le
          (K := K) b p q r).2 hb
    · exact
        (projectiveValveDirectionOnPlane_iff_orbit_le
          (K := K) c p q r).2 hc

/-- Forma puramente incidencial da regeneração do plano: se três direções não
colineares têm suas órbitas dentro de um plano, elas geram esse plano inteiro. -/
theorem projectiveValvePlane_eq_of_triple_orbits_le
    (p q r a b c : ProjectiveValveDirection K)
    (hpq : p ≠ q)
    (hpqr : ¬projectiveValveCollinear p q r)
    (hab : a ≠ b)
    (habc : ¬projectiveValveCollinear a b c)
    (ha : projectiveValveDirectionOrbit a ≤ projectiveValvePlane p q r)
    (hb : projectiveValveDirectionOrbit b ≤ projectiveValvePlane p q r)
    (hc : projectiveValveDirectionOrbit c ≤ projectiveValvePlane p q r) :
    projectiveValvePlane a b c = projectiveValvePlane p q r :=
  (projectiveValvePlane_eq_iff_triple_orbits_le
    p q r a b c hpq hpqr hab habc).2 ⟨ha, hb, hc⟩

end CarrySelfAdjointOperator.ProjectiveValve
