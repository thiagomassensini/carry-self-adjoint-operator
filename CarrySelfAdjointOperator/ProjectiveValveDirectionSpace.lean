import CarrySelfAdjointOperator.ProjectiveValveOrbitIncidence
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Espaço projetivo das direções da válvula

As órbitas escalares da válvula já satisfazem:

* `projectiveValveOrbit (r • D) = projectiveValveOrbit D` para `r ≠ 0`;
* órbitas não triviais iguais correspondem exatamente a geradores proporcionais;
* órbitas de direções distintas se intersectam apenas na massa unidade.

Portanto a órbita depende somente da classe projetiva da curvatura. Este
arquivo usa a `Projectivization` canônica da Mathlib para transformar essa
observação em um mapa bem definido e injetivo do espaço projetivo das séries
formais para os subgrupos de massas normalizadas. Sua imagem é o espaço das
órbitas projetivas da válvula.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries
open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K] [CharZero K]

/-- Direções projetivas de curvaturas formais não nulas. -/
abbrev ProjectiveValveDirection (K : Type*) [Field K] :=
  Projectivization K (PowerSeries K)

/-- A órbita multiplicativa determinada por uma direção projetiva.

A definição é independente do representante porque multiplicar uma
curvatura por um escalar não nulo apenas reparametriza a mesma órbita. -/
noncomputable def projectiveValveDirectionOrbit :
    ProjectiveValveDirection K →
      Subgroup (NormalizedProjectiveMass K) :=
  Projectivization.lift
    (K := K)
    (fun D : {D : PowerSeries K // D ≠ 0} =>
      projectiveValveOrbit D.1)
    (by
      rintro ⟨-, hD⟩ ⟨E, -⟩ r rfl
      have hr : r ≠ 0 := by
        rintro rfl
        simp at hD
      exact projectiveValveOrbit_smul_eq E hr)

/-- Em um representante explícito, o mapa de direções devolve sua órbita. -/
@[simp] theorem projectiveValveDirectionOrbit_mk
    (D : PowerSeries K) (hD : D ≠ 0) :
    projectiveValveDirectionOrbit
        (Projectivization.mk K D hD) =
      projectiveValveOrbit D := rfl

/-- Toda direção projetiva produz uma órbita não trivial. -/
theorem projectiveValveDirectionOrbit_ne_bot
    (p : ProjectiveValveDirection K) :
    projectiveValveDirectionOrbit p ≠ ⊥ := by
  induction p using Projectivization.ind with
  | h D hD =>
      rw [projectiveValveDirectionOrbit_mk]
      intro hOrbit
      exact hD ((projectiveValveOrbit_eq_bot_iff D).mp hOrbit)

/-- A órbita determina unicamente a direção projetiva que a gerou. -/
theorem projectiveValveDirectionOrbit_injective :
    Function.Injective
      (projectiveValveDirectionOrbit (K := K)) := by
  intro p q hpq
  induction p using Projectivization.ind with
  | h D hD =>
      induction q using Projectivization.ind with
      | h E hE =>
          have hOrbit :
              projectiveValveOrbit D = projectiveValveOrbit E := by
            simpa using hpq
          rcases
              (projectiveValveOrbit_eq_iff_nonzero_smul D E hE).mp hOrbit with
            ⟨r, _hr, hED⟩
          have hmk :
              Projectivization.mk K E hE =
                Projectivization.mk K D hD :=
            (Projectivization.mk_eq_mk_iff' K E D hE hD).2
              ⟨r, hED.symm⟩
          exact hmk.symm

/-- Duas direções são iguais exatamente quando produzem a mesma órbita. -/
theorem projectiveValveDirectionOrbit_eq_iff
    (p q : ProjectiveValveDirection K) :
    projectiveValveDirectionOrbit p =
        projectiveValveDirectionOrbit q ↔
      p = q := by
  constructor
  · intro hpq
    exact (projectiveValveDirectionOrbit_injective (K := K)) hpq
  · intro hpq
    subst q
    rfl

/-- O espaço das órbitas projetivas é a imagem do mapa direção--órbita. -/
abbrev ProjectiveValveOrbitSpace
    (K : Type*) [Field K] [CharZero K] :=
  Set.range (projectiveValveDirectionOrbit (K := K))

/-- O espaço projetivo de curvaturas é equivalente ao espaço de órbitas
multiplicativas não triviais que elas geram. -/
noncomputable def projectiveValveDirectionEquivOrbitSpace :
    ProjectiveValveDirection K ≃ ProjectiveValveOrbitSpace K :=
  Equiv.ofInjective
    (projectiveValveDirectionOrbit (K := K))
    (projectiveValveDirectionOrbit_injective (K := K))

/-- A equivalência direção--órbita tem como valor subjacente o subgrupo da
órbita correspondente. -/
@[simp] theorem projectiveValveDirectionEquivOrbitSpace_apply_val
    (p : ProjectiveValveDirection K) :
    (projectiveValveDirectionEquivOrbitSpace p).1 =
      projectiveValveDirectionOrbit p := rfl

/-- Caracterização concreta dos subgrupos que pertencem ao espaço de órbitas:
são exatamente órbitas de curvaturas não nulas. -/
theorem mem_projectiveValveOrbitSpace_iff
    (O : Subgroup (NormalizedProjectiveMass K)) :
    O ∈ Set.range (projectiveValveDirectionOrbit (K := K)) ↔
      ∃ D : PowerSeries K,
        D ≠ 0 ∧ projectiveValveOrbit D = O := by
  constructor
  · rintro ⟨p, rfl⟩
    induction p using Projectivization.ind with
    | h D hD =>
        exact ⟨D, hD, rfl⟩
  · rintro ⟨D, hD, rfl⟩
    exact ⟨Projectivization.mk K D hD, rfl⟩

/-- Incidência no espaço projetivo: duas direções distintas produzem órbitas
que se intersectam apenas na massa unidade, e direções iguais produzem a
mesma órbita. -/
theorem projectiveValveDirectionOrbit_inf_eq_bot_iff_ne
    (p q : ProjectiveValveDirection K) :
    projectiveValveDirectionOrbit p ⊓
        projectiveValveDirectionOrbit q = ⊥ ↔
      p ≠ q := by
  induction p using Projectivization.ind with
  | h D hD =>
      induction q using Projectivization.ind with
      | h E hE =>
          rw [projectiveValveDirectionOrbit_mk,
            projectiveValveDirectionOrbit_mk,
            projectiveValveOrbit_inf_eq_bot_iff_ne D E hE]
          simpa using
            not_congr
              (projectiveValveDirectionOrbit_eq_iff
                (Projectivization.mk K D hD)
                (Projectivization.mk K E hE))

end CarrySelfAdjointOperator.ProjectiveValve
