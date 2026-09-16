# Checkpoint 019 — recorrência racional do ladder finito

## Estado

O módulo `CarrySelfAdjointOperator/FiveFieldLadderRecurrence.lean` foi
validado com `lake env lean` e `lake build --wfail`.

A camada registra a transição exata da família finita auditada no script:

```text
alpha_n = (2 n + 1) - t1 R1 - t2 R2
nr1 = (t1 - alpha_n) R1 - r1
nr2 = (t2 - alpha_n) R2 - r2
nr0 = -(n+1) + nr1 + nr2
beta = nr0^2/R0 - nr1^2/R1 - nr2^2/R2
R1_next = nr1^2/(beta R1)
R2_next = nr2^2/(beta R2)
```

O estado de seis campos é ordenado como
`(R0,R1,R2,r0,r1,r2)`, com `R0_next = 1 + R1_next + R2_next`.
`twoJumpLadderState` é a iteração `Nat.rec` dessa transição a partir do
estado inicial do checkpoint 018.

## Pontes fechadas

Foram provados os lemas de projeção de todos os canais da transição e o
lema `twoJumpLadderStep_matches_script_update`, que expõe diretamente as
fórmulas de `nr1`, `nr2` e `nr0` usadas pelo script. Também foi provado que
o estado no índice `1` é exatamente um passo aplicado ao estado inicial.

## Auditoria

Os teoremas principais
`twoJumpLadderState_succ`,
`twoJumpLadderStep_matches_script_update` e
`twoJumpLadderState_one_eq_step_initial`
dependem somente de:

```text
[propext, Classical.choice, Quot.sound]
```

## Limite deliberado

As divisões são as divisões totais de `ℂ`; nenhuma positividade ou
não-nulidade foi incorporada à definição. O módulo ainda não prova a
diferenciabilidade da camada `n = 1`, não define `native_vector` e não
identifica a derivada paramétrica com a tangente física. O próximo passo
mínimo é adicionar as hipóteses de não-nulidade necessárias para derivar a
primeira transição, sem inferir qualquer bridge físico automaticamente.
