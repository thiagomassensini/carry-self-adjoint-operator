import CarrySelfAdjointOperator.ProjectiveValveFlowRigidity
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Órbitas da válvula projetiva

Fixada uma curvatura formal `D`, o fluxo

`Φ_D(t) = projectiveValveMass (t • D)`

é um homomorfismo do grupo aditivo dos escalares, apresentado pelo type tag
`Multiplicative`, para o grupo das massas normalizadas.

Este arquivo toma a imagem desse homomorfismo como a órbita multiplicativa de
`D`. Para `D ≠ 0`, a rigidez já provada identifica essa órbita com uma cópia
exata do grupo aditivo dos escalares. Além disso, multiplicar o gerador por um
escalar não nulo apenas reparametriza a mesma órbita, e órbitas iguais são
exatamente direções projetivas iguais.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries

variable {K : Type*} [Field K] [CharZero K]

/-- Subgrupo de massas percorrido pelo fluxo gerado por `D`. -/
noncomputable def projectiveValveOrbit
    (D : PowerSeries K) : Subgroup (NormalizedProjectiveMass K) :=
  (projectiveValveFlowHom D).range

/-- Pertencer à órbita significa ser algum ponto escalar do fluxo. -/
theorem mem_projectiveValveOrbit_iff
    (D : PowerSeries K) (A : NormalizedProjectiveMass K) :
    A ∈ projectiveValveOrbit D ↔
      ∃ t : K, projectiveValveFlow D t = A := by
  change A ∈ (projectiveValveFlowHom D).range ↔ _
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t.toAdd, ?_⟩
    simpa using ht
  · rintro ⟨t, ht⟩
    refine ⟨Multiplicative.ofAdd t, ?_⟩
    simpa using ht

/-- Todo ponto do fluxo pertence à órbita de seu gerador. -/
theorem projectiveValveFlow_mem_orbit
    (D : PowerSeries K) (t : K) :
    projectiveValveFlow D t ∈ projectiveValveOrbit D := by
  rw [mem_projectiveValveOrbit_iff]
  exact ⟨t, rfl⟩

/-- O homomorfismo do fluxo é injetivo para todo gerador não nulo. -/
theorem projectiveValveFlowHom_injective_of_ne
    (D : PowerSeries K) (hD : D ≠ 0) :
    Function.Injective (projectiveValveFlowHom D) := by
  intro s t hst
  change projectiveValveFlow D s.toAdd =
    projectiveValveFlow D t.toAdd at hst
  change s.toAdd = t.toAdd
  exact projectiveValveFlow_injective_of_ne D hD hst

/-- Uma órbita não degenerada é uma cópia multiplicativa exata do grupo
aditivo dos escalares. -/
noncomputable def projectiveValveOrbitEquiv
    (D : PowerSeries K) (hD : D ≠ 0) :
    Multiplicative K ≃* projectiveValveOrbit D := by
  simpa [projectiveValveOrbit] using
    (MonoidHom.ofInjective
      (projectiveValveFlowHom_injective_of_ne D hD))

/-- A órbita é trivial exatamente para o gerador nulo. -/
theorem projectiveValveOrbit_eq_bot_iff
    (D : PowerSeries K) :
    projectiveValveOrbit D = ⊥ ↔ D = 0 := by
  constructor
  · intro hOrbit
    have hmem : projectiveValveFlow D 1 ∈ projectiveValveOrbit D :=
      projectiveValveFlow_mem_orbit D 1
    rw [hOrbit] at hmem
    have hflow : projectiveValveFlow D 1 = 1 := by
      simpa using hmem
    have hcurv : (1 : K) • D = 0 :=
      (projectiveValveFlow_eq_one_iff D 1).mp hflow
    simpa using hcurv
  · intro hD
    subst D
    apply MonoidHom.range_eq_bot_iff.mpr
    ext t
    change projectiveValveFlow (0 : PowerSeries K) t.toAdd = 1
    exact projectiveValveFlow_zero_generator t.toAdd

/-- Escalar um gerador por um escalar não nulo não altera sua órbita. -/
theorem projectiveValveOrbit_smul_eq
    (D : PowerSeries K) {r : K} (hr : r ≠ 0) :
    projectiveValveOrbit (r • D) = projectiveValveOrbit D := by
  ext A
  rw [mem_projectiveValveOrbit_iff, mem_projectiveValveOrbit_iff]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t * r, ?_⟩
    exact (projectiveValveFlow_reparameterize D r t).symm
  · rintro ⟨t, rfl⟩
    refine ⟨t * r⁻¹, ?_⟩
    calc
      projectiveValveFlow (r • D) (t * r⁻¹) =
          projectiveValveFlow D ((t * r⁻¹) * r) :=
        projectiveValveFlow_reparameterize D r (t * r⁻¹)
      _ = projectiveValveFlow D t := by
        rw [mul_assoc, inv_mul_cancel₀ hr, mul_one]

/-- Duas órbitas coincidem exatamente quando os geradores representam a mesma
direção projetiva. A hipótese `E ≠ 0` força o escalar de mudança a ser não
nulo; o enunciado simétrico segue trocando `D` e `E`. -/
theorem projectiveValveOrbit_eq_iff_nonzero_smul
    (D E : PowerSeries K) (hE : E ≠ 0) :
    projectiveValveOrbit D = projectiveValveOrbit E ↔
      ∃ r : K, r ≠ 0 ∧ E = r • D := by
  constructor
  · intro hOrbit
    have hmem : projectiveValveFlow E 1 ∈ projectiveValveOrbit D := by
      rw [hOrbit]
      exact projectiveValveFlow_mem_orbit E 1
    rw [mem_projectiveValveOrbit_iff] at hmem
    rcases hmem with ⟨r, hrFlow⟩
    have hval := congrArg
      (fun A : NormalizedProjectiveMass K => A.1) hrFlow
    change projectiveValveMass (r • D) =
      projectiveValveMass ((1 : K) • E) at hval
    have hscaled : r • D = (1 : K) • E :=
      projectiveValveMass_injective hval
    have hED : E = r • D := by
      simpa using hscaled.symm
    have hr : r ≠ 0 := by
      intro hr0
      apply hE
      rw [hED, hr0, zero_smul]
    exact ⟨r, hr, hED⟩
  · rintro ⟨r, hr, rfl⟩
    exact (projectiveValveOrbit_smul_eq D hr).symm

end CarrySelfAdjointOperator.ProjectiveValve
