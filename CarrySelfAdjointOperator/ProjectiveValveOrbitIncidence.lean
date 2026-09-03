import CarrySelfAdjointOperator.ProjectiveValveOrbit

/-!
# Incidência das órbitas da válvula projetiva

Cada curvatura formal `D` produz a órbita multiplicativa

`𝒪_D = { projectiveValveMass (t • D) | t ∈ K }`.

A classificação projetiva das órbitas já mostra que `𝒪_D = 𝒪_E` exatamente
quando os geradores não nulos pertencem à mesma direção escalar. Este arquivo
registra a incidência correspondente:

* um ponto não unitário comum força igualdade das órbitas;
* duas órbitas ou coincidem, ou sua interseção é apenas a massa unidade;
* para uma órbita não trivial, interseção trivial equivale a direções
  projetivas distintas.

Tudo permanece algébrico e formal. Não entram topologia, limites ou aplicações
externas.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries

variable {K : Type*} [Field K] [CharZero K]

/-- Um ponto não unitário comum a duas órbitas força que elas sejam a mesma
órbita projetiva. -/
theorem projectiveValveOrbit_eq_of_common_nontrivial_point
    (D E : PowerSeries K)
    {A : NormalizedProjectiveMass K}
    (hAD : A ∈ projectiveValveOrbit D)
    (hAE : A ∈ projectiveValveOrbit E)
    (hA : A ≠ 1) :
    projectiveValveOrbit D = projectiveValveOrbit E := by
  rw [mem_projectiveValveOrbit_iff] at hAD hAE
  rcases hAD with ⟨s, hsA⟩
  rcases hAE with ⟨t, htA⟩
  have hs : s ≠ 0 := by
    intro hs0
    apply hA
    calc
      A = projectiveValveFlow D s := hsA.symm
      _ = projectiveValveFlow D 0 := by rw [hs0]
      _ = 1 := projectiveValveFlow_zero D
  have ht : t ≠ 0 := by
    intro ht0
    apply hA
    calc
      A = projectiveValveFlow E t := htA.symm
      _ = projectiveValveFlow E 0 := by rw [ht0]
      _ = 1 := projectiveValveFlow_zero E
  have hE : E ≠ 0 := by
    intro hE0
    apply hA
    calc
      A = projectiveValveFlow E t := htA.symm
      _ = projectiveValveFlow (0 : PowerSeries K) t := by rw [hE0]
      _ = 1 := projectiveValveFlow_zero_generator t
  have hflow :
      projectiveValveFlow D s = projectiveValveFlow E t :=
    hsA.trans htA.symm
  have hval := congrArg
    (fun B : NormalizedProjectiveMass K => B.1) hflow
  change projectiveValveMass (s • D) =
    projectiveValveMass (t • E) at hval
  have hscaled : s • D = t • E :=
    projectiveValveMass_injective hval
  have hED : E = (t⁻¹ * s) • D := by
    calc
      E = 1 • E := by simp
      _ = (t⁻¹ * t) • E := by simp [ht]
      _ = t⁻¹ • (t • E) := by rw [smul_smul]
      _ = t⁻¹ • (s • D) := by rw [← hscaled]
      _ = (t⁻¹ * s) • D := by rw [smul_smul]
  have hts : t⁻¹ * s ≠ 0 :=
    mul_ne_zero (inv_ne_zero ht) hs
  exact
    (projectiveValveOrbit_eq_iff_nonzero_smul D E hE).2
      ⟨t⁻¹ * s, hts, hED⟩

/-- Para uma órbita não trivial, duas órbitas coincidem exatamente quando
possuem algum ponto comum diferente da massa unidade. -/
theorem exists_common_nontrivial_point_iff_orbit_eq
    (D E : PowerSeries K)
    (hE : E ≠ 0) :
    (∃ A : NormalizedProjectiveMass K,
        A ∈ projectiveValveOrbit D ∧
        A ∈ projectiveValveOrbit E ∧
        A ≠ 1) ↔
      projectiveValveOrbit D = projectiveValveOrbit E := by
  constructor
  · rintro ⟨A, hAD, hAE, hA⟩
    exact projectiveValveOrbit_eq_of_common_nontrivial_point
      D E hAD hAE hA
  · intro hOrbit
    refine ⟨projectiveValveFlow E 1, ?_,
      projectiveValveFlow_mem_orbit E 1, ?_⟩
    · rw [hOrbit]
      exact projectiveValveFlow_mem_orbit E 1
    · intro hOne
      have hscaled : (1 : K) • E = 0 :=
        (projectiveValveFlow_eq_one_iff E 1).mp hOne
      apply hE
      simpa using hscaled

/-- Duas órbitas projetivas ou coincidem, ou sua interseção é o subgrupo
trivial. -/
theorem projectiveValveOrbit_inf_eq_bot_or_eq
    (D E : PowerSeries K) :
    projectiveValveOrbit D ⊓ projectiveValveOrbit E = ⊥ ∨
      projectiveValveOrbit D = projectiveValveOrbit E := by
  classical
  by_cases hbot :
      projectiveValveOrbit D ⊓ projectiveValveOrbit E = ⊥
  · exact Or.inl hbot
  · right
    have hex :
        ∃ A : NormalizedProjectiveMass K,
          A ∈ projectiveValveOrbit D ⊓ projectiveValveOrbit E ∧
          A ≠ 1 := by
      by_contra hnone
      apply hbot
      apply le_antisymm
      · intro A hA
        have hAone : A = 1 := by
          by_contra hAne
          exact hnone ⟨A, hA, hAne⟩
        subst A
        simp
      · exact bot_le
    rcases hex with ⟨A, hA, hAne⟩
    exact projectiveValveOrbit_eq_of_common_nontrivial_point
      D E hA.1 hA.2 hAne

/-- Se `E` gera uma órbita não trivial, interseção trivial equivale a órbitas
distintas. -/
theorem projectiveValveOrbit_inf_eq_bot_iff_ne
    (D E : PowerSeries K)
    (hE : E ≠ 0) :
    projectiveValveOrbit D ⊓ projectiveValveOrbit E = ⊥ ↔
      projectiveValveOrbit D ≠ projectiveValveOrbit E := by
  constructor
  · intro hInf hEq
    have hEbot : projectiveValveOrbit E = ⊥ := by
      simpa [hEq] using hInf
    exact hE ((projectiveValveOrbit_eq_bot_iff E).mp hEbot)
  · intro hNe
    rcases projectiveValveOrbit_inf_eq_bot_or_eq D E with hbot | hEq
    · exact hbot
    · exact (hNe hEq).elim

/-- Forma projetiva da incidência: para `E ≠ 0`, as órbitas se intersectam
apenas na unidade exatamente quando `E` não é múltiplo escalar não nulo de
`D`. -/
theorem projectiveValveOrbit_inf_eq_bot_iff_not_nonzero_smul
    (D E : PowerSeries K)
    (hE : E ≠ 0) :
    projectiveValveOrbit D ⊓ projectiveValveOrbit E = ⊥ ↔
      ¬ ∃ r : K, r ≠ 0 ∧ E = r • D := by
  rw [projectiveValveOrbit_inf_eq_bot_iff_ne D E hE,
    projectiveValveOrbit_eq_iff_nonzero_smul D E hE]

end CarrySelfAdjointOperator.ProjectiveValve
