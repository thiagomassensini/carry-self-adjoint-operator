import CarrySelfAdjointOperator.ProjectiveValveAlgebra
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Grupo da válvula projetiva

A álgebra da válvula projetiva já prova que

`projectiveValveMass (D + E) = projectiveValveMass D * projectiveValveMass E`

e que a curvatura logarítmica desfaz essa construção nas massas normalizadas.

Este arquivo transforma essas leis em estrutura formal:

* as séries de termo constante `1` formam um grupo comutativo sob produto;
* a soma das curvaturas, vista multiplicativamente pelo type tag
  `Multiplicative`, é isomorfa a esse grupo;
* `projectiveValveMass` e `projectiveValveCurvature` são os dois lados do
  isomorfismo.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries

variable {K : Type*} [Field K]

namespace NormalizedProjectiveMass

/-- A massa unidade é normalizada. -/
instance : One (NormalizedProjectiveMass K) where
  one := ⟨1, by simp⟩

/-- O produto de duas massas normalizadas continua normalizado. -/
instance : Mul (NormalizedProjectiveMass K) where
  mul A B := ⟨A.1 * B.1, by simp [A.2, B.2]⟩

/-- A inversa formal de uma massa normalizada continua normalizada. -/
instance : Inv (NormalizedProjectiveMass K) where
  inv A := ⟨A.1⁻¹, by simp [A.2]⟩

@[simp] theorem val_one :
    (1 : NormalizedProjectiveMass K).1 = (1 : PowerSeries K) := rfl

@[simp] theorem val_mul (A B : NormalizedProjectiveMass K) :
    (A * B).1 = A.1 * B.1 := rfl

@[simp] theorem val_inv (A : NormalizedProjectiveMass K) :
    A⁻¹.1 = A.1⁻¹ := rfl

/-- As massas normalizadas formam um grupo comutativo sob multiplicação de
séries formais. O inverso é o inverso formal da série. -/
instance : CommGroup (NormalizedProjectiveMass K) :=
  { Group.ofLeftAxioms
      (fun A B C => by
        apply Subtype.ext
        exact mul_assoc A.1 B.1 C.1)
      (fun A => by
        apply Subtype.ext
        exact one_mul A.1)
      (fun A => by
        apply Subtype.ext
        exact PowerSeries.inv_mul_cancel A.1 (by
          rw [A.2]
          exact one_ne_zero)) with
    mul_comm := fun A B => by
      apply Subtype.ext
      exact mul_comm A.1 B.1 }

end NormalizedProjectiveMass

variable [CharZero K]

/-- **Isomorfismo de grupos da válvula projetiva.**

O grupo aditivo das curvaturas é lido multiplicativamente por
`Multiplicative`. A massa projetiva é o mapa direto e a curvatura logarítmica
é o mapa inverso. -/
noncomputable def projectiveValveGroupEquiv :
    Multiplicative (PowerSeries K) ≃* NormalizedProjectiveMass K where
  toFun D :=
    ⟨projectiveValveMass D.toAdd,
      projectiveValveMass_constantCoeff D.toAdd⟩
  invFun A :=
    Multiplicative.ofAdd (projectiveValveCurvature A.1)
  left_inv D := by
    change
      Multiplicative.ofAdd
          (projectiveValveCurvature (projectiveValveMass D.toAdd)) =
        Multiplicative.ofAdd D.toAdd
    rw [projectiveValveCurvature_projectiveValveMass]
  right_inv A := by
    apply Subtype.ext
    exact projectiveValveMass_projectiveValveCurvature A.1 A.2
  map_mul' D E := by
    apply Subtype.ext
    change projectiveValveMass (D.toAdd + E.toAdd) =
      projectiveValveMass D.toAdd * projectiveValveMass E.toAdd
    exact projectiveValveMass_add D.toAdd E.toAdd

@[simp] theorem projectiveValveGroupEquiv_apply
    (D : Multiplicative (PowerSeries K)) :
    (projectiveValveGroupEquiv D).1 = projectiveValveMass D.toAdd := rfl

@[simp] theorem projectiveValveGroupEquiv_symm_apply
    (A : NormalizedProjectiveMass K) :
    (projectiveValveGroupEquiv.symm A).toAdd =
      projectiveValveCurvature A.1 := rfl

/-- A construção de massa é um homomorfismo multiplicativo depois de ler a
soma de curvaturas pelo type tag `Multiplicative`. -/
noncomputable def projectiveValveMassHom :
    Multiplicative (PowerSeries K) →* NormalizedProjectiveMass K :=
  projectiveValveGroupEquiv.toMonoidHom

/-- A extração de curvatura é o homomorfismo inverso. -/
noncomputable def projectiveValveCurvatureHom :
    NormalizedProjectiveMass K →* Multiplicative (PowerSeries K) :=
  projectiveValveGroupEquiv.symm.toMonoidHom

end CarrySelfAdjointOperator.ProjectiveValve
