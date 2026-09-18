# Checkpoint 022 — charts nativos e de resíduos diferenciados

## Estado

Foram validados com `lake env lean` e `lake build --wfail` os módulos:

```text
CarrySelfAdjointOperator/FiveFieldNativeCoordinateDifferentiation.lean
CarrySelfAdjointOperator/FiveFieldNativeCoordinateStateDifferentiation.lean
CarrySelfAdjointOperator/FiveFieldResidueCoordinateDifferentiation.lean
```

## Pontes fechadas

`twoJumpNativeCoordinateVector_hasDerivAt` diferencia o chart
`(log (R₁/R₀), log (R₂/R₀), r₁, r₂)`. A fórmula é

```text
(dR₁/R₁ - dR₀/R₀, dR₂/R₂ - dR₀/R₀, dr₁, dr₂).
```

As hipóteses dos dois primeiros canais são a não-nulidade dos denominadores e
a pertença dos quocientes ao `Complex.slitPlane`, que é a condição correta
para derivar `Complex.log`.

`twoJumpNativeVector_hasDerivAt_c1` e
`twoJumpNativeVector_hasDerivAt_c2` compõem esse chart com a derivada iterada
do estado finito nas duas amplitudes do script.

Independentemente, `twoJumpResidueCoordinateVector_hasDerivAt` diferencia o
chart matricial usado por `twoJumpResidueCoordinateLinear`. Assim, quando uma
família matricial variacional for fornecida, a saída de coordenadas pode ser
ligada ao funcional de reconstrução sem repetir a álgebra de quocientes.

## Auditoria

Os quatro theorems auditados dependem somente dos axiomas padrão:

```text
[propext, Classical.choice, Quot.sound]
```

## Limite explícito

Nenhuma dessas pontes identifica a derivada do estado finito com a tangente
física do operador. Ainda falta uma família matricial variacional e a prova de
que seus coeficientes Laurent satisfazem o witness de momentos usado em
`FiveFieldTangentWitnessBridge`. Também não foi assumida uma admissibilidade
global da órbita nem uma conclusão assintótica.
