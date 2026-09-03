import CarrySelfAdjointOperator.ProjectiveDepthCoordinate

/-!
# Inversa formal da coordenada projetiva da profundidade

A coordenada projetiva

`Y = X / (1 - X)`

possui a inversa formal

`X = Y / (1 + Y)`.

Este arquivo constrói essa inversa sem divisão por séries: usa a série
alternada `1 / (1 + X) = ∑ (-1)^n X^n`, prova as duas relações definidoras e
fecha os dois percursos de substituição.
-/

namespace CarrySelfAdjointOperator.ProjectiveDepth

open PowerSeries
open CarrySelfAdjointOperator.DiscreteValve

variable {R : Type*} [CommRing R]

/-- Série geométrica alternada `1 / (1 + X) = ∑ (-1)^n X^n`. -/
noncomputable def inverseGeometricSeries : PowerSeries R :=
  mk fun n => (-1 : R) ^ n

/-- `(1 + X)` inverte a série geométrica alternada. -/
theorem one_add_X_mul_inverseGeometricSeries :
    (1 + X) * inverseGeometricSeries = (1 : R⟦X⟧) := by
  ext n
  cases n with
  | zero =>
      simp [inverseGeometricSeries]
  | succ n =>
      simp only [add_mul, one_mul, map_add, coeff_succ_X_mul,
        inverseGeometricSeries, coeff_mk, coeff_one, Nat.succ_ne_zero,
        ↓reduceIte]
      rw [pow_succ]
      ring

/-- Coordenada projetiva inversa: `X / (1 + X)`. -/
noncomputable def inverseCoordinate : PowerSeries R :=
  X * inverseGeometricSeries

/-- A coordenada inversa também é centrada. -/
@[simp] theorem inverseCoordinate_constantCoeff :
    constantCoeff (inverseCoordinate (R := R)) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, inverseCoordinate]
  simp

/-- Relação definidora sem divisão: `(1 + X) * inverseCoordinate = X`. -/
theorem one_add_X_mul_inverseCoordinate :
    (1 + X) * inverseCoordinate (R := R) = X := by
  rw [inverseCoordinate]
  calc
    (1 + X) * (X * inverseGeometricSeries) =
        X * ((1 + X) * inverseGeometricSeries) := by ring
    _ = X := by
      rw [one_add_X_mul_inverseGeometricSeries, mul_one]

/-- `1 - inverseCoordinate` é a série alternada `1 / (1 + X)`. -/
theorem one_sub_inverseCoordinate_eq_inverseGeometricSeries :
    1 - inverseCoordinate (R := R) = inverseGeometricSeries := by
  rw [inverseCoordinate]
  have h := one_add_X_mul_inverseGeometricSeries (R := R)
  rw [add_mul, one_mul] at h
  rw [← h]
  ring

/-- A coordenada direta admite substituição formal. -/
theorem coordinate_hasSubst :
    HasSubst (coordinate (R := R)) :=
  HasSubst.of_constantCoeff_zero' coordinate_constantCoeff

/-- A coordenada inversa admite substituição formal. -/
theorem inverseCoordinate_hasSubst :
    HasSubst (inverseCoordinate (R := R)) :=
  HasSubst.of_constantCoeff_zero' inverseCoordinate_constantCoeff

/-- Primeiro percurso: `Y(X)` avaliada em `X = Y/(1+Y)` devolve `X`. -/
theorem coordinate_subst_inverseCoordinate :
    (coordinate (R := R)).subst (inverseCoordinate (R := R)) = X := by
  have hinverse : HasSubst (inverseCoordinate (R := R)) :=
    inverseCoordinate_hasSubst
  have htransportRaw := congrArg
    (fun F : PowerSeries R => F.subst (inverseCoordinate (R := R)))
    (one_sub_X_mul_coordinate (R := R))
  have htransport :
      (1 - inverseCoordinate (R := R)) *
          ((coordinate (R := R)).subst (inverseCoordinate (R := R))) =
        inverseCoordinate (R := R) := by
    simpa [subst_mul hinverse, subst_sub hinverse, subst_X hinverse] using
      htransportRaw
  calc
    (coordinate (R := R)).subst (inverseCoordinate (R := R)) =
        ((1 + X) * (1 - inverseCoordinate (R := R))) *
          ((coordinate (R := R)).subst (inverseCoordinate (R := R))) := by
      rw [one_sub_inverseCoordinate_eq_inverseGeometricSeries,
        one_add_X_mul_inverseGeometricSeries, one_mul]
    _ = (1 + X) *
        ((1 - inverseCoordinate (R := R)) *
          ((coordinate (R := R)).subst (inverseCoordinate (R := R)))) := by
      ring
    _ = (1 + X) * inverseCoordinate (R := R) := by
      rw [htransport]
    _ = X := one_add_X_mul_inverseCoordinate

/-- Segundo percurso: `X(Y)` avaliada em `Y = X/(1-X)` devolve `X`. -/
theorem inverseCoordinate_subst_coordinate :
    (inverseCoordinate (R := R)).subst (coordinate (R := R)) = X := by
  have hcoordinate : HasSubst (coordinate (R := R)) :=
    coordinate_hasSubst
  have htransportRaw := congrArg
    (fun F : PowerSeries R => F.subst (coordinate (R := R)))
    (one_add_X_mul_inverseCoordinate (R := R))
  have htransport :
      (1 + coordinate (R := R)) *
          ((inverseCoordinate (R := R)).subst (coordinate (R := R))) =
        coordinate (R := R) := by
    simpa [subst_mul hcoordinate, subst_add hcoordinate, subst_X hcoordinate] using
      htransportRaw
  calc
    (inverseCoordinate (R := R)).subst (coordinate (R := R)) =
        ((1 - X) * (1 + coordinate (R := R))) *
          ((inverseCoordinate (R := R)).subst (coordinate (R := R))) := by
      rw [one_add_coordinate_eq_geometricSeries,
        one_sub_X_mul_geometricSeries, one_mul]
    _ = (1 - X) *
        ((1 + coordinate (R := R)) *
          ((inverseCoordinate (R := R)).subst (coordinate (R := R)))) := by
      ring
    _ = (1 - X) * coordinate (R := R) := by
      rw [htransport]
    _ = X := one_sub_X_mul_coordinate

end CarrySelfAdjointOperator.ProjectiveDepth
