# Checkpoint 018 — camada inicial diferenciada do estado de dois saltos

## Estado

O módulo `CarrySelfAdjointOperator/FiveFieldInitialStateDifferentiation.lean`
foi compilado com `lake env lean` e com `lake build --wfail`.

Ele formaliza a camada `n = 0` da família finita de dois saltos:

```text
h₀ = 1 + a₁ exp(-t₁) + a₂ exp(-t₂)
R₁ = (-a₁ exp(-t₁))/h₀
R₂ = (-a₂ exp(-t₂))/h₀
state₀ = (1 + R₁ + R₂, R₁, R₂, 0, 0, 0).
```

Sob `h₀ ≠ 0`, foram provadas as derivadas complexas da função
`a₁ ↦ state₀(t₁,t₂,a₁,a₂)` e da função
`a₂ ↦ state₀(t₁,t₂,a₁,a₂)`, com os numeradores quocientes diferenciados
explicitamente e as seis coordenadas fechadas por `hasDerivAt_pi`.

## Resultado Lean

```text
twoJumpInitialState_hasDerivAt_c1
twoJumpInitialState_hasDerivAt_c2
```

Ambos dependem somente dos axiomas padrão reportados pelo Lean:

```text
[propext, Classical.choice, Quot.sound]
```

## Escopo e próximo bloqueio

Esta camada ainda não afirma a recorrência para `n > 0`, não define o vetor
de coordenadas logarítmicas e não identifica essas derivadas paramétricas
com o vetor tangente físico do operador. O próximo passo mínimo é transportar
essas fórmulas para a primeira atualização da recorrência, introduzindo
somente as hipóteses de não-nulidade que aparecerem na assinatura real.
Não se deve inferir uma identificação física sem um bridge explícito.
