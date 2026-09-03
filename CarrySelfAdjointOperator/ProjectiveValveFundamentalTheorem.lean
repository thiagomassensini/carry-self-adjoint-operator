import CarrySelfAdjointOperator.GreenMultiplicativeValveMass

/-!
# Teorema Fundamental da Válvula Projetiva

A composição Green -> integral logarítmica -> exponencial já constrói uma
massa formal normalizada que, na coordenada projetiva, satisfaz

`A' = D * A`,  `A(0) = 1`.

Este arquivo fecha a direção inversa: essa solução é única. A prova não introduz
uma recorrência paralela. Ela lê a equação diferencial como um canal
multiplicativo `X * D`, transporta-a pela ponte sequência/série e reutiliza a
unicidade de `towerMass`.

Assim, para toda curvatura projetiva `D`, existe exatamente uma massa
normalizada resolvendo a equação de primeira ordem.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries
open CarrySelfAdjointOperator.ProjectiveDepth
open CarrySelfAdjointOperator.MultiplicativeValve
open CarrySelfAdjointOperator.GreenMultiplicativeValveBridge

variable {K : Type*} [Field K] [CharZero K]

/-- Massa canônica associada diretamente a uma curvatura escrita na coordenada
projetiva. Transportamos `D` de volta à coordenada original e aplicamos a
construção Green-multiplicativa já fechada. -/
noncomputable def projectiveValveMass (D : PowerSeries K) : PowerSeries K :=
  projectiveGreenMass (fromProjective D)

/-- A massa projetiva canônica é normalizada em `1`. -/
@[simp] theorem projectiveValveMass_constantCoeff (D : PowerSeries K) :
    constantCoeff (projectiveValveMass D) = 1 := by
  unfold projectiveValveMass
  exact projectiveGreenMass_constantCoeff (fromProjective D)

/-- A massa projetiva canônica resolve `A' = D * A`. -/
theorem derivative_projectiveValveMass (D : PowerSeries K) :
    d⁄dX K (projectiveValveMass D) = D * projectiveValveMass D := by
  unfold projectiveValveMass
  rw [derivative_projectiveGreenMass]
  rw [toProjective_fromProjective]

/-- Duas massas normalizadas que resolvem a mesma equação formal de primeira
ordem são iguais.

A equação `A' = D*A` equivale a dizer que `A` possui canal multiplicativo
`X*D`. A unicidade já provada para `towerMass` fecha a comparação. -/
theorem normalized_projective_ode_unique
    (D A B : PowerSeries K)
    (hA0 : constantCoeff A = 1)
    (hB0 : constantCoeff B = 1)
    (hA : d⁄dX K A = D * A)
    (hB : d⁄dX K B = D * B) :
    A = B := by
  let a : ℕ → K := fun n => coeff n A
  let b : ℕ → K := fun n => coeff n B
  let channel : ℕ → K := fun n => coeff n (X * D)

  have hmkA : mk a = A := by
    ext n
    simp [a]
  have hmkB : mk b = B := by
    ext n
    simp [b]
  have hmkChannel : mk channel = X * D := by
    ext n
    simp [channel]

  have hlogA : IsLogDerivChannel A (X * D) := by
    unfold IsLogDerivChannel
    change (X * D) * A = X * (d⁄dX K A)
    rw [hA]
    ac_rfl
  have hlogB : IsLogDerivChannel B (X * D) := by
    unfold IsLogDerivChannel
    change (X * D) * B = X * (d⁄dX K B)
    rw [hB]
    ac_rfl

  have hTowerA : IsTowerChannel a channel := by
    apply (isTowerChannel_iff_isLogDerivChannel a channel).mpr
    rw [hmkA, hmkChannel]
    exact hlogA
  have hTowerB : IsTowerChannel b channel := by
    apply (isTowerChannel_iff_isLogDerivChannel b channel).mpr
    rw [hmkB, hmkChannel]
    exact hlogB

  have ha0 : a 0 = 1 := by
    dsimp [a]
    rw [coeff_zero_eq_constantCoeff_apply, hA0]
  have hb0 : b 0 = 1 := by
    dsimp [b]
    rw [coeff_zero_eq_constantCoeff_apply, hB0]

  have hab : a = b :=
    towerMass_unique a b channel ha0 hb0 hTowerA hTowerB

  calc
    A = mk a := hmkA.symm
    _ = mk b := congrArg (fun s : ℕ → K => mk s) hab
    _ = B := hmkB

/-- A solução normalizada construída pela geometria é a única solução da
Equação projetiva para a curvatura dada. -/
theorem projectiveValveMass_unique
    (D A : PowerSeries K)
    (hA0 : constantCoeff A = 1)
    (hA : d⁄dX K A = D * A) :
    A = projectiveValveMass D := by
  exact normalized_projective_ode_unique D A (projectiveValveMass D)
    hA0 (projectiveValveMass_constantCoeff D)
    hA (derivative_projectiveValveMass D)

/-- **Teorema Fundamental da Válvula Projetiva.** Para toda curvatura formal
`D`, existe exatamente uma massa `A` com `A(0)=1` e `A'=D*A`. -/
theorem existsUnique_projectiveValveMass (D : PowerSeries K) :
    ∃! A : PowerSeries K,
      constantCoeff A = 1 ∧ d⁄dX K A = D * A := by
  refine ⟨projectiveValveMass D, ?_, ?_⟩
  · exact ⟨projectiveValveMass_constantCoeff D,
      derivative_projectiveValveMass D⟩
  · intro A hA
    exact projectiveValveMass_unique D A hA.1 hA.2

/-- A construção direta na coordenada projetiva coincide com a massa Green
quando a curvatura já veio transportada da coordenada original. -/
@[simp] theorem projectiveValveMass_toProjective (C : PowerSeries K) :
    projectiveValveMass (toProjective C) = projectiveGreenMass C := by
  unfold projectiveValveMass
  rw [fromProjective_toProjective]

end CarrySelfAdjointOperator.ProjectiveValve
