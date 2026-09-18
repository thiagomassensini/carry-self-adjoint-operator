# Checkpoint 020 — derivada algébrica de uma transição do ladder

## Estado

O módulo `CarrySelfAdjointOperator/FiveFieldLadderDifferentiation.lean` foi
validado com `lake env lean` e com `lake build --wfail`.

Ele formaliza a derivada complexa, em modo forward, de uma transição racional
da escada finita de seis campos. A entrada é uma família
`s : ℂ → Fin 6 → ℂ` com derivadas coordenadas `ds`; a saída é a derivada
explícita de `twoJumpLadderStep` na ordem `(R₀,R₁,R₂,r₀,r₁,r₂)`.

## Hipóteses exatas

O theorem
`NativeCarryFiveFieldCapstone.twoJumpLadderStep_hasDerivAt` usa somente:

```text
s x 0 ≠ 0
s x 1 ≠ 0
s x 2 ≠ 0
twoJumpLadderBeta n t1 t2 (s x) ≠ 0
```

Essas são precisamente as não-nulidades dos denominadores que aparecem na
transição. A prova diferencia `α`, `nr₁`, `nr₂`, `nr₀`, `β` e os dois resíduos,
e fecha as seis coordenadas por `hasDerivAt_pi`.

## Auditoria

O theorem depende somente dos axiomas padrão:

```text
[propext, Classical.choice, Quot.sound]
```

## Limite e próximo passo

Esta é uma ponte algébrica local. Ela ainda não fornece as hipóteses de
não-nulidade para os parâmetros físicos, não prova a derivada iterada de
`twoJumpLadderState` e não identifica a derivada paramétrica com a tangente
física do operador.

O próximo passo mínimo é aplicar esta ponte à família inicial já diferenciada
em `FiveFieldInitialStateDifferentiation.lean`, mantendo explícitas as
hipóteses de não-nulidade. Só depois faz sentido iterar a construção sob uma
hipótese de admissibilidade ao longo da órbita.
