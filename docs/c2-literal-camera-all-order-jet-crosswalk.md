# Crosswalk C2 literal para jets de todas as ordens

Este módulo registra a ponte aritmética entre os blocos literais da câmera C2 e a família existente de observáveis logarítmicos/Taylor. A base desta rodada é o commit `a7f9d531af9e4148f2d56856be7d084e68160ea2`; nenhum operador, momento ou Gram novo foi introduzido.

## Resultado formal

Para `order m k : ℕ), o módulo define apenas o readout mínimo

```lean
c2FiberAllOrderBracket order m k
```

como a segunda diferença de `realLogPowerDirichletPower order (1 / 2 : ℂ)` nos pontos
`2 ^ k * m - 1`, `2 ^ k * m`, `2 ^ k * m + 1`.

A avaliação linear mínima de `FormalStencil` é

```lean
evalFormalStencil (value : ℕ → ℂ)
```

e reutiliza `atom`, `centerStencil`, `centeredBracketStencil`, `finiteStencil` e a fatoração C2 já provada.

Os teoremas principais são:

- `c2CenterStencil_eval_logPower_eq_fiberAllOrderBracket`: cada bloco `centerStencil 2 j`, aplicado ao observável de qualquer ordem, é exatamente o bracket da fibra determinada por `c2AlignedIndexCore j` e `c2AlignedIndexDepth j`.
- `c2CenterStencil_nativeTaylorCoefficient_eq_fiberBracket`: a mesma igualdade para a família existente `nativeDirichletSlopeTaylorCoefficient`.
- `c2FiniteCamera_allOrderReadout_eq_seed_add_fiberBracketSum`: a avaliação de qualquer observável na câmera finita é a semente mais a soma dos brackets dos índices `j < M`.
- `c2FiniteCamera_allOrderLogPowerReadout_eq_seed_add_fiberBracketSum` e `c2FiniteCamera_nativeTaylorCoefficient_eq_seed_add_fiberBracketSum`: especializações da soma finita para as duas famílias anteriores.
- `c2Tower_logPower_criticalAmplitude_eq_stirling_newtonJet`: especialização em base `2` do teorema existente `ProjectiveDepth.tower_log_power_criticalAmplitude_eq_stirling_newtonJet`. Ela transporta a potência logarítmica da torre pura `2^k` para os modos Newton por Stirling.

A prova do bloco usa a identidade de centro/pernas já existente; não recria a decomposição `(m,k)` nem os stencils C2.

## O que permanece separado

A família contínua `realLogPowerDirichletPower`, a família discreta `nativeDirichletSlopeTaylorCoefficient` e os jets crus completados têm tipos e normalizações diferentes. Esta rodada prova as duas avaliações finitas acima, mas não declara que elas são a mesma função.

O teorema de Newton/Stirling disponível cobre diretamente a torre `p^k` (nesta rodada, `p = 2`). A extensão para o centro geral `2^k m`, com o termo adicional `log m` e a combinação binomial/Stirling correspondente, ainda não está tipada por uma API existente e ficou como residual explícito.

Também não foi adicionado um limite de raw jets. Os raw jets completados vivem em vetores finitos indexados por `Fin`, enquanto a câmera usada neste módulo é a avaliação de stencils em `ℕ → ℂ`; não há, no pin atual, uma ponte tipada pronta que permita aplicar o mesmo funcional e passar o limite sem inventar casts.

As correções das pernas permanecem nos teoremas C2 anteriores. Nenhum termo `log(2^k m ± 1)` foi substituído pelo log do centro, e nenhuma forma fechada adicional foi assumida.

## Next Hankel Gate

1. A família obtida é a dos readouts finitos de segunda diferença dos observáveis log-power e dos coeficientes Taylor nativos, indexados por ordem `r` e pela fibra `(m_j,k_j)`.
2. Ela ainda não está empacotada aqui como uma única família em um `InnerProductSpace ℝ`; os valores são complexos e o módulo só trata avaliação linear.
3. Há pairings em carriers Taylor/Green existentes, mas nenhum teorema novo desta rodada identifica os pairings dos readouts C2 com uma matriz de momentos.
4. A dependência apenas em `i + j` não foi provada.
5. O setor ímpar com `i + j + 1` também não foi identificado nesta ponte.
6. Para construir `IsMomentGramRepresentation`, `IsShiftedMomentGramRepresentation` ou `IsGreenWronskianMomentKernelGramRepresentation`, ainda faltam uma realização vetorial real apropriada e teoremas de pairing/identificação com os momentos; positividade não foi postulada nem demonstrada aqui.

Assim, o resultado desta rodada é estritamente o crosswalk

```
índice C2 -> (m_j,k_j) -> bracket literal -> log/Taylor readout
```

em toda ordem finita suportada pelas APIs existentes.
