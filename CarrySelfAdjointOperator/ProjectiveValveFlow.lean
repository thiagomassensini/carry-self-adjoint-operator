import CarrySelfAdjointOperator.ProjectiveValveGroup

/-!
# Fluxo escalar da válvula projetiva

O isomorfismo de grupos da válvula projetiva identifica soma de curvaturas
com produto de massas normalizadas. Fixada uma curvatura formal `D`, a reta
escalar

` t ↦ t • D `

produz então uma família multiplicativa de massas

` Φ_D(t) = projectiveValveMass (t • D) `.

Este arquivo registra que `Φ_D(0)=1`, `Φ_D(s+t)=Φ_D(s)Φ_D(t)` e
`Φ_D(-t)=Φ_D(t)⁻¹`, e empacota a família como um homomorfismo do grupo
aditivo dos escalares, lido pelo type tag `Multiplicative`, para o grupo das
massas normalizadas.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries

variable {K : Type*} [Field K] [CharZero K]

/-- Fluxo da válvula projetiva ao longo da reta escalar gerada por `D`. -/
noncomputable def projectiveValveFlow
    (D : PowerSeries K) (t : K) : NormalizedProjectiveMass K :=
  ⟨projectiveValveMass (t • D),
    projectiveValveMass_constantCoeff (t • D)⟩

/-- A série subjacente ao fluxo é a massa da curvatura escalada. -/
@[simp] theorem projectiveValveFlow_val
    (D : PowerSeries K) (t : K) :
    (projectiveValveFlow D t).1 = projectiveValveMass (t • D) := rfl

/-- Tempo zero é a massa unidade. -/
@[simp] theorem projectiveValveFlow_zero
    (D : PowerSeries K) :
    projectiveValveFlow D 0 = 1 := by
  apply Subtype.ext
  simp [projectiveValveFlow]

/-- Tempo um recupera a massa canônica de `D`. -/
@[simp] theorem projectiveValveFlow_one
    (D : PowerSeries K) :
    (projectiveValveFlow D 1).1 = projectiveValveMass D := by
  simp [projectiveValveFlow]

/-- A adição dos parâmetros compõe multiplicativamente o fluxo. -/
theorem projectiveValveFlow_add
    (D : PowerSeries K) (s t : K) :
    projectiveValveFlow D (s + t) =
      projectiveValveFlow D s * projectiveValveFlow D t := by
  apply Subtype.ext
  change projectiveValveMass ((s + t) • D) =
    projectiveValveMass (s • D) * projectiveValveMass (t • D)
  rw [add_smul, projectiveValveMass_add]

/-- Inverter o parâmetro inverte a massa do fluxo. -/
@[simp] theorem projectiveValveFlow_neg
    (D : PowerSeries K) (t : K) :
    projectiveValveFlow D (-t) = (projectiveValveFlow D t)⁻¹ := by
  apply Subtype.ext
  change projectiveValveMass ((-t) • D) =
    (projectiveValveMass (t • D))⁻¹
  rw [neg_smul, projectiveValveMass_neg]

/-- Diferença de parâmetros corresponde a quociente de massas. -/
theorem projectiveValveFlow_sub
    (D : PowerSeries K) (s t : K) :
    projectiveValveFlow D (s - t) =
      projectiveValveFlow D s * (projectiveValveFlow D t)⁻¹ := by
  rw [sub_eq_add_neg, projectiveValveFlow_add, projectiveValveFlow_neg]

/-- A curvatura da massa no tempo `t` é exatamente `t • D`. -/
@[simp] theorem projectiveValveFlow_curvature
    (D : PowerSeries K) (t : K) :
    projectiveValveCurvature (projectiveValveFlow D t).1 = t • D := by
  exact projectiveValveCurvature_projectiveValveMass (t • D)

/-- Cada ponto do fluxo resolve a equação projetiva cuja curvatura é `t • D`. -/
theorem derivative_projectiveValveFlow
    (D : PowerSeries K) (t : K) :
    d⁄dX K (projectiveValveFlow D t).1 =
      (t • D) * (projectiveValveFlow D t).1 := by
  change d⁄dX K (projectiveValveMass (t • D)) =
    (t • D) * projectiveValveMass (t • D)
  exact derivative_projectiveValveMass (t • D)

/-- A família `t ↦ Φ_D(t)` como subgrupo a um parâmetro.

`Multiplicative K` é apenas o grupo aditivo de `K` apresentado com notação
multiplicativa, para que o contradomínio seja o grupo multiplicativo das
massas normalizadas. -/
noncomputable def projectiveValveFlowHom
    (D : PowerSeries K) :
    Multiplicative K →* NormalizedProjectiveMass K where
  toFun t := projectiveValveFlow D t.toAdd
  map_one' := by
    change projectiveValveFlow D 0 = 1
    exact projectiveValveFlow_zero D
  map_mul' s t := by
    change projectiveValveFlow D (s.toAdd + t.toAdd) =
      projectiveValveFlow D s.toAdd * projectiveValveFlow D t.toAdd
    exact projectiveValveFlow_add D s.toAdd t.toAdd

@[simp] theorem projectiveValveFlowHom_apply
    (D : PowerSeries K) (t : Multiplicative K) :
    projectiveValveFlowHom D t = projectiveValveFlow D t.toAdd := rfl

end CarrySelfAdjointOperator.ProjectiveValve
