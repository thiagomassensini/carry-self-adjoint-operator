# Checkpoint 021 — derivada iterada do ladder finito

## Estado

Foram validados com `lake env lean` e `lake build --wfail` os módulos:

```text
CarrySelfAdjointOperator/FiveFieldLadderDifferentiation.lean
CarrySelfAdjointOperator/FiveFieldLadderInitialStepDifferentiation.lean
CarrySelfAdjointOperator/FiveFieldLadderStateDifferentiation.lean
```

## Pontes fechadas

`twoJumpLadderStep_hasDerivAt` diferencia uma transição racional para uma
família de estados com derivadas coordenadas. As fórmulas explícitas cobrem
`α`, `nr₁`, `nr₂`, `nr₀`, `β` e os dois resíduos.

`twoJumpLadderStep_hasDerivAt_initial_c1` e
`twoJumpLadderStep_hasDerivAt_initial_c2` aplicam essa ponte ao estado inicial
já diferenciado nas amplitudes `a₁` e `a₂`.

`twoJumpLadderState_hasDerivAt_c1` e
`twoJumpLadderState_hasDerivAt_c2` iteram a construção até um nível finito
`n`. A hipótese é local e finita: para cada `m < n`, os três campos de
resíduo usados como denominadores e o escalar `β m` são não nulos. No nível
zero, a única hipótese analítica é a não-nulidade da altura inicial, que já é
necessária para a derivada inicial.

## Auditoria

Os quatro theorems principais retornam somente:

```text
[propext, Classical.choice, Quot.sound]
```

## Limite explícito

Esta camada ainda não define `native_vector`, não diferencia os logaritmos das
coordenadas normalizadas e não identifica a derivada paramétrica com a
tangente física do operador. Também não fornece uma prova global de
admissibilidade da órbita. O próximo gate mínimo é escolher uma definição
Lean explícita para as coordenadas nativas e provar sua derivada sob as
hipóteses de não-nulidade correspondentes, ou então formalizar primeiro a
ponte de coeficientes que recebe a derivada já reconstruída.
