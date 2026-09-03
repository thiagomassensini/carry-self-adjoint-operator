import CarrySelfAdjointOperator.ProjectiveDepthEquivalence
import CarrySelfAdjointOperator.MultiplicativeValve

/-!
# Ponte entre a integral de Green e a válvula multiplicativa

A válvula aditiva transforma uma curvatura formal `C` no canal residual

`B = greenVelocity * C = X/(1-X)^2 * C`.

Como `B(0)=0`, esse residual já possui exatamente a normalização exigida pela
integração logarítmica da válvula multiplicativa. Definimos então o potencial

`K = logIntegral B`,

que satisfaz `X K' = B`. A coordenada projetiva `Y = X/(1-X)` e sua inversa
cancelam o núcleo de Green pelo jacobiano, produzindo a identidade intrínseca

`d/dY (K ∘ X(Y)) = C ∘ X(Y)`.

Este é o primeiro entrelaçamento literal das duas válvulas. Nenhuma aplicação
externa ou condição espectral entra no enunciado.
-/

namespace CarrySelfAdjointOperator.GreenMultiplicativeValveBridge

open PowerSeries
open CarrySelfAdjointOperator.ProjectiveDepth
open CarrySelfAdjointOperator.DiscreteValve
open CarrySelfAdjointOperator.MultiplicativeValve

variable {K : Type*} [Field K]

/-- Série-canal produzida pela integral de Green a partir de uma curvatura. -/
noncomputable def greenChannelSeries (C : PowerSeries K) : PowerSeries K :=
  greenVelocity (R := K) * C

/-- Coeficientes do canal Green, na forma consumida por `logIntegral`. -/
noncomputable def greenChannel (C : PowerSeries K) : ℕ → K :=
  fun n => coeff n (greenChannelSeries C)

/-- O canal Green é automaticamente centrado. -/
@[simp] theorem greenChannel_zero (C : PowerSeries K) :
    greenChannel C 0 = 0 := by
  simp [greenChannel, greenChannelSeries,
    CarrySelfAdjointOperator.ProjectiveDepth.greenVelocity,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- Reempacotar os coeficientes do canal recupera a série original. -/
theorem mk_greenChannel (C : PowerSeries K) :
    mk (greenChannel C) = greenChannelSeries C := by
  ext n
  simp [greenChannel]

/-- Potencial logarítmico obtido integrando o residual de Green. -/
noncomputable def greenLogPotential (C : PowerSeries K) : PowerSeries K :=
  logIntegral (greenChannel C)

/-- O potencial Green-logarítmico possui termo constante zero. -/
@[simp] theorem greenLogPotential_constantCoeff (C : PowerSeries K) :
    constantCoeff (greenLogPotential C) = 0 := by
  unfold greenLogPotential
  exact constantCoeff_logIntegral (greenChannel C)

variable [CharZero K]

/-- A graduação do potencial recupera exatamente o canal de Green. -/
theorem X_mul_derivative_greenLogPotential (C : PowerSeries K) :
    X * (d⁄dX K (greenLogPotential C)) = greenChannelSeries C := by
  unfold greenLogPotential
  change X * (logIntegral (greenChannel C)).derivativeFun = greenChannelSeries C
  rw [X_mul_derivativeFun_logIntegral (greenChannel C) (greenChannel_zero C)]
  exact mk_greenChannel C

/-- Removendo o deslocamento `X`, a derivada do potencial é o núcleo de Green
multiplicando a curvatura. A injetividade de `X * ·` vale para séries formais
sem hipótese adicional de domínio. -/
theorem derivative_greenLogPotential (C : PowerSeries K) :
    d⁄dX K (greenLogPotential C) =
      greenKernelSeries (R := K) * C := by
  apply PowerSeries.X_mul_cancel
  calc
    X * (d⁄dX K (greenLogPotential C)) =
        greenChannelSeries C :=
      X_mul_derivative_greenLogPotential C
    _ = X * (greenKernelSeries (R := K) * C) := by
      unfold greenChannelSeries
      unfold CarrySelfAdjointOperator.ProjectiveDepth.greenVelocity
      ac_rfl

/-- **Colapso projetivo das duas válvulas.**

Depois de transportar o potencial para `Y` pela coordenada inversa
`X(Y)=Y/(1+Y)`, sua derivada ordinária é exatamente a curvatura transportada:

`d/dY (toProjective K) = toProjective C`.
-/
theorem derivative_toProjective_greenLogPotential (C : PowerSeries K) :
    d⁄dX K (toProjective (greenLogPotential C)) = toProjective C := by
  have hinverse : HasSubst (inverseCoordinate (R := K)) :=
    inverseCoordinate_hasSubst
  unfold toProjective
  rw [PowerSeries.derivative_subst K hinverse]
  rw [derivative_greenLogPotential C]
  rw [PowerSeries.subst_mul hinverse]
  calc
    (((greenKernelSeries (R := K)).subst (inverseCoordinate (R := K))) *
          (C.subst (inverseCoordinate (R := K)))) *
        d⁄dX K (inverseCoordinate (R := K)) =
      (((greenKernelSeries (R := K)).subst (inverseCoordinate (R := K))) *
          d⁄dX K (inverseCoordinate (R := K))) *
        (C.subst (inverseCoordinate (R := K))) := by
      ac_rfl
    _ = 1 * (C.subst (inverseCoordinate (R := K))) := by
      rw [greenKernel_subst_inverse_mul_inverseDerivative (R := K)]
    _ = C.subst (inverseCoordinate (R := K)) := by
      rw [one_mul]

end CarrySelfAdjointOperator.GreenMultiplicativeValveBridge
