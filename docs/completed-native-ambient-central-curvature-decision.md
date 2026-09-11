# Decisão da curvatura transversal central do carrier ambient

Base formal: 4bc859ced7b2dce40cd8fc053d183389db0c6aa4.

Esta rodada testa somente a entrada central (0,0) do carrier ambient/source-matched. O resultado é negativo, por uma desigualdade estrita kernel-checked; nenhum limite de câmeras, sewing estático, carrier TFVD enriquecido ou construção all-order é usado.

## Fórmulas exatas

A energia vertical já existente é
~~~lean
completedNativeVerticalModulusEnergy z y :=
  ‖completedNativeOperatorCharacteristic
      (z + Complex.I * (y : ℂ))‖ ^ 2
~~~

Logo, na linha central:
~~~lean
completedNativeVerticalModulusEnergy 0 y
  = ‖completedNativeOperatorCharacteristic (Complex.I * (y : ℂ))‖ ^ 2
~~~
(teorema completedNativeVerticalModulusEnergy_zero_apply).

A curvatura exata já formalizada no repositório é:
~~~lean
iteratedDeriv 2 (completedNativeVerticalModulusEnergy 0) 0
  =
4 * ‖completedNativeOperatorCharacteristic 0‖ ^ 2 *
  canonicalCompletedNativeLogDerivativeMoment 0
~~~
(teorema completedNativeVerticalModulusEnergy_secondDerivative_zero_eq_moment_zero).

O alvo da curvatura transversal usa a energia ordinária, sem o peso da característica:
~~~lean
4 * ‖canonicalCompletedC3DirichletGradientState
      (operatorHeightParameter 0) ...‖ ^ 2
~~~

O defeito explícito da rodada é:
~~~lean
canonicalCompletedAmbientCentralCurvatureDefect :=
  iteratedDeriv 2 (completedNativeVerticalModulusEnergy 0) 0 -
    4 * ‖canonicalCompletedC3DirichletGradientState
      (operatorHeightParameter 0) ...‖ ^ 2
~~~

A expansão exata é provada por canonicalCompletedAmbientCentralCurvatureDefect_eq_characteristicWeightedMoment_sub_gradient.

## Decisão

Os bounds analíticos existentes dão:
~~~text
‖completedNativeOperatorCharacteristic 0‖ ≤ 1/2
canonicalCompletedNativeLogDerivativeMoment 0 < 1/16
1/16 <
  ‖canonicalCompletedC3DirichletGradientState
    (operatorHeightParameter 0) ...‖²
~~~

O módulo transforma o primeiro bound em
~~~lean
4 * ‖completedNativeOperatorCharacteristic 0‖² *
  canonicalCompletedNativeLogDerivativeMoment 0 < 1/16
~~~
e o segundo bound do gradiente em
~~~lean
1/4 <
  4 * ‖canonicalCompletedC3DirichletGradientState
    (operatorHeightParameter 0) ...‖².
~~~

Portanto:
~~~lean
canonicalCompletedAmbientCentralCurvatureDefect < 0
~~~
pelo teorema canonicalCompletedAmbientCentralCurvatureDefect_neg, e em particular:
~~~lean
iteratedDeriv 2 (completedNativeVerticalModulusEnergy 0) 0 ≠
  4 * ‖canonicalCompletedC3DirichletGradientState
    (operatorHeightParameter 0) ...‖²
~~~
pelo teorema completedNativeVerticalModulusEnergy_secondDerivative_zero_ne_four_gradientEnergy.

O mesmo resultado é expresso diretamente no Gram normalizado:
~~~lean
canonicalCompletedNativeLogDerivativeMoment 0 <
  ‖canonicalCompletedC3NormalizedAmbientResponseState 0 ...‖²
~~~
(teorema canonicalCompletedC3NormalizedAmbientResponseState_zero_norm_sq_gt_moment_zero).
Assim, norm_sq_canonicalCompletedC3NormalizedAmbientResponseState_zero_ne_moment_zero segue também do iff de curvatura do gate ambient.

## Origem do defeito

A segunda derivada é a curvatura do módulo quadrado da característica completada ao longo da linha vertical. A regra do produto e a simetria par no centro reduzem os termos de primeira variação, mas preservam o fator ‖completedNativeOperatorCharacteristic 0‖². Esse fator contém a normalização de completion da característica e não aparece na energia do gradiente ordinário. O resultado não é um termo de câmera nem uma escolha de fase.

Não há um termo de boundary separado introduzido por este módulo. Os canais de completion que entram na curvatura estão codificados na característica completada e no teorema exato de curvatura existente. Não houve descarte de residual, ajuste de constante, aproximação numérica ou hipótese adicional.

## Status do carrier

O carrier ambient não passa o teste 00 para a métrica e o estado especificados pelo gate atual:
~~~lean
‖canonicalCompletedC3NormalizedAmbientResponseState 0 ...‖²
  ≠ canonicalCompletedNativeLogDerivativeMoment 0
~~~

Este é um no-go para esta realização ambient/source-matched. Ele não exclui um carrier ou uma métrica nativa diferente. Os no-go anteriores para o carrier ordinary + log-jet + residual e para o Taylor complexo não foram contornados nem reutilizados como alvo.

Nenhuma câmera, limite de atlas/cutoff, sixCamera, hipótese Genuine/zero, Jacobi, Hankel, HP, Weyl, Gpre, TFVD sewing ou scalarização Gamma foi usada.

## Next central gate

Para prosseguir com o carrier ambient atual seria necessário primeiro uma identidade geométrica nova que reconciliasse a curvatura ponderada da característica completada com a energia ordinária do gradiente. O módulo atual formaliza essa exigência como um defeito estritamente negativo e encerra a investigação all-order desse carrier nesta rodada.
