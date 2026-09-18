# Checkpoint 023 — invariantes exatos do estado finito

## Estado

O módulo `CarrySelfAdjointOperator/FiveFieldLadderStateInvariants.lean` foi
validado com `lake env lean` e `lake build --wfail`.

## Identidades registradas

Para todo nível finito `n`, a representação Lean da escada satisfaz:

```text
state n 0 = 1 + state n 1 + state n 2
state n 3 = -n + state n 4 + state n 5.
```

São exatamente as duas reconstruções feitas pelo script depois de cada
atualização. A prova é uma indução direta sobre `n`; não usa as divisões nem
qualquer hipótese de não-nulidade.

## Auditoria

Os theorems
`twoJumpLadderState_R0_eq_one_add` e
`twoJumpLadderState_r0_eq_neg_level_add` dependem somente de:

```text
[propext, Classical.choice, Quot.sound]
```

## Limite

As invariantes conferem a codificação do estado, mas não fornecem
admissibilidade da órbita nem uma identidade com os objetos analíticos do
operador. O próximo uso seguro é simplificar bridges algébricos que dependam
de `R₀` e `r₀`; a identificação de uma família variacional física continua
sendo uma obrigação separada.
