import CarrySelfAdjointOperator.DiscreteValveSeries

/-!
# Coordenada projetiva da profundidade

A válvula aditiva produz o multiplicador de Green

`X / (1 - X)^2`.

A coordenada formal

`Y = X / (1 - X) = X * geometricSeries`

tem derivada `dY/dX = 1 / (1 - X)^2`. Portanto o operador graduado de
profundidade `X * d/dX`, depois da substituição por `Y`, carrega exatamente o
multiplicador de Green:

`X * d/dX (F ∘ Y) = (X / (1-X)^2) * (F' ∘ Y)`.

Este arquivo formaliza essa identidade como regra da cadeia no anel de séries
formais. Nenhuma aplicação externa ou condição espectral entra no enunciado.
-/

namespace CarrySelfAdjointOperator.ProjectiveDepth

open PowerSeries
open CarrySelfAdjointOperator.DiscreteValve

variable {R : Type*} [CommRing R]

/-- Coordenada projetiva da profundidade: `Y = X / (1-X)`. -/
noncomputable def coordinate : PowerSeries R :=
  X * geometricSeries

/-- A coordenada projetiva é centrada: seu termo constante é zero. -/
@[simp] theorem coordinate_constantCoeff :
    constantCoeff (coordinate (R := R)) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coordinate]
  simp

/-- Relação definidora sem divisão: `(1-X) * Y = X`. -/
theorem one_sub_X_mul_coordinate :
    (1 - X) * coordinate (R := R) = X := by
  rw [coordinate]
  calc
    ((1 : PowerSeries R) - X) * (X * geometricSeries) =
        X * (((1 : PowerSeries R) - X) * geometricSeries) := by
      ac_rfl
    _ = X := by
      rw [one_sub_X_mul_geometricSeries, mul_one]

/-- A série geométrica é `1 + Y`. -/
theorem one_add_coordinate_eq_geometricSeries :
    1 + coordinate (R := R) = geometricSeries := by
  rw [coordinate]
  calc
    (1 : PowerSeries R) + X * geometricSeries =
        ((1 : PowerSeries R) - X) * geometricSeries + X * geometricSeries := by
      rw [one_sub_X_mul_geometricSeries]
    _ = geometricSeries := by
      rw [sub_mul, one_mul, sub_add_cancel]

/-- O quadrado da série geométrica é o núcleo de Green. -/
theorem geometricSeries_mul_self_eq_greenKernelSeries :
    (geometricSeries : PowerSeries R) * geometricSeries = greenKernelSeries := by
  ext n
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [geometricSeries, greenKernelSeries]

/-- A derivada da coordenada projetiva é o núcleo de Green:
`dY/dX = 1/(1-X)^2`. -/
theorem coordinate_derivativeFun :
    (coordinate (R := R)).derivativeFun = greenKernelSeries := by
  ext n
  rw [coeff_derivativeFun, coordinate, coeff_succ_X_mul,
    geometricSeries, coeff_mk, greenKernelSeries, coeff_mk]
  ring

/-- Campo de velocidade projetivo do operador de profundidade. -/
noncomputable def greenVelocity : PowerSeries R :=
  X * greenKernelSeries

/-- A graduação aplicada à própria coordenada produz o multiplicador de Green. -/
theorem euler_coordinate :
    X * (coordinate (R := R)).derivativeFun = greenVelocity := by
  rw [coordinate_derivativeFun]
  rfl

/-- O mesmo campo é `Y(1+Y)`. -/
theorem greenVelocity_eq_coordinate_mul_one_add :
    greenVelocity (R := R) =
      coordinate * (1 + coordinate) := by
  calc
    greenVelocity (R := R) = X * greenKernelSeries := rfl
    _ = X * (geometricSeries * geometricSeries) := by
      rw [geometricSeries_mul_self_eq_greenKernelSeries]
    _ = coordinate * geometricSeries := by
      simp [coordinate, mul_assoc]
    _ = coordinate * (1 + coordinate) := by
      rw [one_add_coordinate_eq_geometricSeries]

/-- O multiplicador reduzido da válvula aditiva vira literalmente `Y^2`. -/
theorem coordinate_sq_eq_X_sq_mul_greenKernelSeries :
    coordinate (R := R) ^ 2 = X ^ 2 * greenKernelSeries := by
  rw [coordinate, ← geometricSeries_mul_self_eq_greenKernelSeries]
  ring

/-- **Entrelaçamento Euler--Green pela regra da cadeia.**

Para toda série formal `F`, substituir `Y = X/(1-X)` transforma a derivada
ordinária na variável projetiva no operador graduado de profundidade, com o
campo de velocidade de Green como coeficiente:

`X * (F ∘ Y)' = greenVelocity * (F' ∘ Y)`.
-/
theorem euler_subst_coordinate (F : PowerSeries R) :
    X * (d⁄dX R (F.subst (coordinate (R := R)))) =
      greenVelocity *
        ((d⁄dX R F).subst (coordinate (R := R))) := by
  have hcoordinate : HasSubst (coordinate (R := R)) :=
    HasSubst.of_constantCoeff_zero' coordinate_constantCoeff
  rw [derivative_subst R hcoordinate]

  change
    X *
        ((d⁄dX R F).subst (coordinate (R := R)) *
          (coordinate (R := R)).derivativeFun) =
      greenVelocity *
        ((d⁄dX R F).subst (coordinate (R := R)))

  rw [coordinate_derivativeFun]
  unfold greenVelocity
  ac_rfl

end CarrySelfAdjointOperator.ProjectiveDepth
