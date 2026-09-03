import CarrySelfAdjointOperator.GreenMultiplicativeValveBridge

/-!
# Massa multiplicativa gerada pela curvatura de Green

A ponte anterior constrói, para cada curvatura formal `C`, o potencial
logarítmico `greenLogPotential C` e prova que, na coordenada projetiva,

`d/dY (toProjective (greenLogPotential C)) = toProjective C`.

Aqui exponenciamos esse potencial. A massa resultante é exatamente a massa da
válvula multiplicativa associada ao canal residual de Green e, depois do
transporte projetivo, satisfaz a equação diferencial intrínseca

`A' = C * A`,  com `A(0) = 1`.

Assim a composição

`curvatura -> Green -> integral logarítmica -> exponencial`

se reduz, na coordenada projetiva, à solução normalizada da equação de primeira
ordem acima.
-/

namespace CarrySelfAdjointOperator.ProjectiveDepth

open PowerSeries

variable {R : Type*} [CommRing R]

/-- O transporte para a coordenada projetiva preserva o termo constante,
porque a coordenada inversa tem termo constante zero. -/
theorem constantCoeff_toProjective (F : PowerSeries R) :
    constantCoeff (toProjective F) = constantCoeff F := by
  have hinverse : HasSubst (inverseCoordinate (R := R)) :=
    inverseCoordinate_hasSubst
  unfold toProjective
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hinverse,
    finsum_eq_single _ 0 fun d hd => by
      rw [coeff_zero_eq_constantCoeff_apply, map_pow,
        inverseCoordinate_constantCoeff, zero_pow hd, smul_zero]]
  simp [coeff_zero_eq_constantCoeff_apply]

end CarrySelfAdjointOperator.ProjectiveDepth

namespace CarrySelfAdjointOperator.GreenMultiplicativeValveBridge

open PowerSeries
open CarrySelfAdjointOperator.ProjectiveDepth
open CarrySelfAdjointOperator.MultiplicativeValve

variable {K : Type*} [Field K] [CharZero K]

/-- Massa multiplicativa obtida exponenciando o potencial logarítmico de Green. -/
noncomputable def greenMassSeries (C : PowerSeries K) : PowerSeries K :=
  expSeries (greenLogPotential C)

/-- A massa Green possui a normalização multiplicativa canônica. -/
@[simp] theorem greenMassSeries_constantCoeff (C : PowerSeries K) :
    constantCoeff (greenMassSeries C) = 1 := by
  unfold greenMassSeries
  exact constantCoeff_expSeries (greenLogPotential C)
    (greenLogPotential_constantCoeff C)

/-- A massa exponencial possui exatamente o canal residual de Green. -/
theorem isLogDerivChannel_greenMassSeries (C : PowerSeries K) :
    IsLogDerivChannel (greenMassSeries C) (greenChannelSeries C) := by
  unfold greenMassSeries
  have h := isLogDerivChannel_expSeries (greenLogPotential C)
    (greenLogPotential_constantCoeff C)
  have hgrad := X_mul_derivative_greenLogPotential C
  change X * (greenLogPotential C).derivativeFun = greenChannelSeries C at hgrad
  rwa [hgrad] at h

/-- A construção exponencial coincide com a integração recursiva `towerMass`
do canal de Green. -/
theorem mk_towerMass_greenChannel (C : PowerSeries K) :
    mk (towerMass (greenChannel C)) = greenMassSeries C := by
  rw [mk_towerMass_eq_expSeries (greenChannel C) (greenChannel_zero C)]
  rfl

/-- Regra diferencial da massa antes da mudança projetiva:
`A' = A * K'`. -/
theorem derivative_greenMassSeries (C : PowerSeries K) :
    d⁄dX K (greenMassSeries C) =
      greenMassSeries C * d⁄dX K (greenLogPotential C) := by
  apply PowerSeries.X_mul_cancel
  have hchannel := isLogDerivChannel_greenMassSeries C
  unfold IsLogDerivChannel at hchannel
  calc
    X * (d⁄dX K (greenMassSeries C)) =
        greenChannelSeries C * greenMassSeries C := hchannel.symm
    _ = (X * (d⁄dX K (greenLogPotential C))) * greenMassSeries C := by
      rw [X_mul_derivative_greenLogPotential C]
    _ = X * (greenMassSeries C * d⁄dX K (greenLogPotential C)) := by
      ac_rfl

/-- Massa Green escrita na coordenada projetiva `Y`. -/
noncomputable def projectiveGreenMass (C : PowerSeries K) : PowerSeries K :=
  toProjective (greenMassSeries C)

/-- A mudança projetiva preserva a normalização `A(0)=1`. -/
@[simp] theorem projectiveGreenMass_constantCoeff (C : PowerSeries K) :
    constantCoeff (projectiveGreenMass C) = 1 := by
  unfold projectiveGreenMass
  rw [constantCoeff_toProjective, greenMassSeries_constantCoeff]

/-- **Equação intrínseca da massa na coordenada projetiva.**

A massa gerada pela curvatura satisfaz

`d/dY A(Y) = C(Y) * A(Y)`

após transportar tanto `A` quanto `C` pela coordenada inversa
`X(Y)=Y/(1+Y)`. -/
theorem derivative_projectiveGreenMass (C : PowerSeries K) :
    d⁄dX K (projectiveGreenMass C) =
      toProjective C * projectiveGreenMass C := by
  have hinverse : HasSubst (inverseCoordinate (R := K)) :=
    inverseCoordinate_hasSubst
  have hpotential :
      ((d⁄dX K (greenLogPotential C)).subst
          (inverseCoordinate (R := K))) *
        d⁄dX K (inverseCoordinate (R := K)) =
      C.subst (inverseCoordinate (R := K)) := by
    have h := derivative_toProjective_greenLogPotential C
    unfold toProjective at h
    rw [PowerSeries.derivative_subst K hinverse] at h
    exact h
  unfold projectiveGreenMass toProjective
  rw [PowerSeries.derivative_subst K hinverse]
  rw [derivative_greenMassSeries C]
  rw [PowerSeries.subst_mul hinverse]
  calc
    (((greenMassSeries C).subst (inverseCoordinate (R := K))) *
          ((d⁄dX K (greenLogPotential C)).subst
            (inverseCoordinate (R := K)))) *
        d⁄dX K (inverseCoordinate (R := K)) =
      ((greenMassSeries C).subst (inverseCoordinate (R := K))) *
        (((d⁄dX K (greenLogPotential C)).subst
            (inverseCoordinate (R := K))) *
          d⁄dX K (inverseCoordinate (R := K))) := by
      ac_rfl
    _ = ((greenMassSeries C).subst (inverseCoordinate (R := K))) *
        (C.subst (inverseCoordinate (R := K))) := by
      rw [hpotential]
    _ = (C.subst (inverseCoordinate (R := K))) *
        ((greenMassSeries C).subst (inverseCoordinate (R := K))) := by
      ac_rfl

end CarrySelfAdjointOperator.GreenMultiplicativeValveBridge
