import CarrySelfAdjointOperator.ProjectiveDepthInverse

/-!
# Equivalência formal da coordenada projetiva de profundidade

As identidades

`coordinate.subst inverseCoordinate = X`

e

`inverseCoordinate.subst coordinate = X`

já mostram que `Y = X/(1-X)` e `X = Y/(1+Y)` são coordenadas formais inversas.
Este arquivo promove esses dois percursos a uma mudança de coordenada em toda
série formal e registra as identidades jacobianas que serão consumidas pela
ponte entre a integral de Green e a válvula multiplicativa.
-/

namespace CarrySelfAdjointOperator.ProjectiveDepth

open PowerSeries

variable {R : Type*} [CommRing R]

/-- Substituir `X` numa série formal não altera a série. -/
theorem subst_X_eq_self (F : PowerSeries R) :
    F.subst (X : PowerSeries R) = F := by
  have h := PowerSeries.map_algebraMap_eq_subst_X (R := R) (S := R) F
  simp [h.symm]

/-- Transporte de uma série da coordenada original `X` para a coordenada
projetiva `Y`: compor com `X(Y) = Y/(1+Y)`. -/
noncomputable def toProjective (F : PowerSeries R) : PowerSeries R :=
  F.subst (inverseCoordinate (R := R))

/-- Transporte de volta à coordenada original: compor com
`Y(X) = X/(1-X)`. -/
noncomputable def fromProjective (F : PowerSeries R) : PowerSeries R :=
  F.subst (coordinate (R := R))

/-- Transportar para `Y` e voltar para `X` devolve a série original. -/
@[simp] theorem fromProjective_toProjective (F : PowerSeries R) :
    fromProjective (toProjective F) = F := by
  unfold fromProjective toProjective
  rw [PowerSeries.subst_comp_subst_apply
    (inverseCoordinate_hasSubst (R := R))
    (coordinate_hasSubst (R := R))]
  rw [inverseCoordinate_subst_coordinate (R := R)]
  exact subst_X_eq_self F

/-- Transportar de `Y` para `X` e retornar a `Y` também devolve a série. -/
@[simp] theorem toProjective_fromProjective (F : PowerSeries R) :
    toProjective (fromProjective F) = F := by
  unfold fromProjective toProjective
  rw [PowerSeries.subst_comp_subst_apply
    (coordinate_hasSubst (R := R))
    (inverseCoordinate_hasSubst (R := R))]
  rw [coordinate_subst_inverseCoordinate (R := R)]
  exact subst_X_eq_self F

/-- A mudança projetiva de profundidade como equivalência de conjuntos de
séries formais. As leis algébricas continuam disponíveis pelas propriedades
de `subst`. -/
noncomputable def coordinateChangeEquiv :
    PowerSeries R ≃ PowerSeries R where
  toFun := toProjective
  invFun := fromProjective
  left_inv := fromProjective_toProjective
  right_inv := toProjective_fromProjective

/-- O transporte para a coordenada projetiva preserva soma. -/
theorem toProjective_add (F G : PowerSeries R) :
    toProjective (F + G) = toProjective F + toProjective G := by
  unfold toProjective
  exact PowerSeries.subst_add (inverseCoordinate_hasSubst (R := R)) F G

/-- O transporte para a coordenada projetiva preserva produto. -/
theorem toProjective_mul (F G : PowerSeries R) :
    toProjective (F * G) = toProjective F * toProjective G := by
  unfold toProjective
  exact PowerSeries.subst_mul (inverseCoordinate_hasSubst (R := R)) F G

/-- O transporte de volta preserva soma. -/
theorem fromProjective_add (F G : PowerSeries R) :
    fromProjective (F + G) = fromProjective F + fromProjective G := by
  unfold fromProjective
  exact PowerSeries.subst_add (coordinate_hasSubst (R := R)) F G

/-- O transporte de volta preserva produto. -/
theorem fromProjective_mul (F G : PowerSeries R) :
    fromProjective (F * G) = fromProjective F * fromProjective G := by
  unfold fromProjective
  exact PowerSeries.subst_mul (coordinate_hasSubst (R := R)) F G

/-- Jacobiano do percurso `Y(X(Y)) = Y`:

`(Y' ∘ X(Y)) * X'(Y) = 1`.
-/
theorem coordinate_inverse_jacobian :
    ((d⁄dX R (coordinate (R := R))).subst
        (inverseCoordinate (R := R))) *
      d⁄dX R (inverseCoordinate (R := R)) = 1 := by
  have h := congrArg (fun F : PowerSeries R => d⁄dX R F)
    (coordinate_subst_inverseCoordinate (R := R))
  rw [PowerSeries.derivative_subst R
      (inverseCoordinate_hasSubst (R := R)),
    PowerSeries.derivative_X] at h
  exact h

/-- Jacobiano do percurso inverso `X(Y(X)) = X`:

`(X' ∘ Y(X)) * Y'(X) = 1`.
-/
theorem inverse_coordinate_jacobian :
    ((d⁄dX R (inverseCoordinate (R := R))).subst
        (coordinate (R := R))) *
      d⁄dX R (coordinate (R := R)) = 1 := by
  have h := congrArg (fun F : PowerSeries R => d⁄dX R F)
    (inverseCoordinate_subst_coordinate (R := R))
  rw [PowerSeries.derivative_subst R
      (coordinate_hasSubst (R := R)),
    PowerSeries.derivative_X] at h
  exact h

/-- O núcleo de Green transportado pela coordenada inversa cancela exatamente
o seu jacobiano. Esta é a identidade que reduz a composição das duas válvulas
a uma derivada ordinária em `Y`. -/
theorem greenKernel_subst_inverse_mul_inverseDerivative :
    (PowerSeries.subst (a := inverseCoordinate (R := R))
        (f := (CarrySelfAdjointOperator.DiscreteValve.greenKernelSeries (R := R))) ) *
      d⁄dX R (inverseCoordinate (R := R)) = 1 := by
  have hcoordDeriv :
      d⁄dX R (coordinate (R := R)) =
        (CarrySelfAdjointOperator.DiscreteValve.greenKernelSeries (R := R)) := by
    calc
      d⁄dX R (coordinate (R := R)) = (coordinate (R := R)).derivativeFun := rfl
      _ = (CarrySelfAdjointOperator.DiscreteValve.greenKernelSeries (R := R)) := coordinate_derivativeFun (R := R)
  have hsub : (PowerSeries.subst (a := inverseCoordinate (R := R))
      (f := d⁄dX R (coordinate (R := R))) *
        d⁄dX R (inverseCoordinate (R := R)) = 1) := by
    simpa using (coordinate_inverse_jacobian (R := R))
  calc
    (PowerSeries.subst (a := inverseCoordinate (R := R))
        (f := (CarrySelfAdjointOperator.DiscreteValve.greenKernelSeries (R := R))) ) *
        d⁄dX R (inverseCoordinate (R := R))
        = (PowerSeries.subst (a := inverseCoordinate (R := R))
            (f := d⁄dX R (coordinate (R := R))) *
              d⁄dX R (inverseCoordinate (R := R))) := by
      apply congrArg (fun F => F * d⁄dX R (inverseCoordinate (R := R)))
      exact congrArg (PowerSeries.subst (a := inverseCoordinate (R := R))) hcoordDeriv.symm
    _ = 1 := hsub

/-- A identidade jacobiana espelhada na coordenada original. -/
theorem inverseDerivative_subst_coordinate_mul_greenKernel :
    ((d⁄dX R (inverseCoordinate (R := R))).subst
        (coordinate (R := R))) *
      (CarrySelfAdjointOperator.DiscreteValve.greenKernelSeries (R := R)) = 1 := by
  have hcoordDeriv :
      d⁄dX R (coordinate (R := R)) =
        (CarrySelfAdjointOperator.DiscreteValve.greenKernelSeries (R := R)) := by
    calc
      d⁄dX R (coordinate (R := R)) = (coordinate (R := R)).derivativeFun := rfl
      _ = (CarrySelfAdjointOperator.DiscreteValve.greenKernelSeries (R := R)) := coordinate_derivativeFun (R := R)
  have hsub : (d⁄dX R (inverseCoordinate (R := R))).subst
      (coordinate (R := R)) * (d⁄dX R (coordinate (R := R))) = 1 := by
    simpa using (inverse_coordinate_jacobian (R := R))
  calc
    ((d⁄dX R (inverseCoordinate (R := R))).subst
        (coordinate (R := R))) *
      (CarrySelfAdjointOperator.DiscreteValve.greenKernelSeries (R := R))
      = (d⁄dX R (inverseCoordinate (R := R))).subst
          (coordinate (R := R)) * (d⁄dX R (coordinate (R := R))) := by
        exact congrArg (fun F =>
          (d⁄dX R (inverseCoordinate (R := R))).subst (coordinate (R := R)) * F) hcoordDeriv.symm
    _ = 1 := hsub

end CarrySelfAdjointOperator.ProjectiveDepth
