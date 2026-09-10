# Completed native return-metric readout crosswalk

## Escopo e resultado

Esta rodada testa a métrica de retorno que já é forçada pela análise Green
normalizada. O pin fornece a API `ReturnMetric` para matrizes finitas, mas seus
mapas de endpoint e bulk são matrizes entre tipos `Fintype`. Os espaços do
Green completo (`State`, `ConcreteExternalSpace` e `BulkGreenSpace`) são
Hilbertianos, não são esses tipos finitos. Portanto não foi criada uma matriz
finita artificial nem uma nova completion.

Foi formalizada a elevação contínua-linear da mesma fórmula:

```text
G_return = 1 + P† P
```

para os mapas canônicos da análise Green:

```text
endpoint = normalizedExternal
bulk     = normalizedBulk
poisson  = ambientPoisson
```

A elevação satisfaz exatamente a identidade de retorno e tem kernel Gram
positivo. O teste de centro, porém, é negativo para esta realização concreta:
seu valor central é a energia do gradiente ordinário completado, estritamente
maior que o momento nativo `h₀`. Assim esta realização não fornece a costura
nativa pedida; o fato é um diagnóstico da escolha de estado/métrica, sem
recalibração.

**Resultado primário: Outcome C — a especialização natural fecha a isometria e
um kernel positivo, mas falha no momento de ordem zero.** A interface matricial
finita da API upstream permanece um seam separado (Outcome D de tipagem), e o
resultado não afirma que nenhuma outra realização de retorno possa funcionar.

## Peças Lean

O módulo novo é
[`CompletedNativeReturnMetricReadoutCrosswalk.lean`](../CarrySelfAdjointOperator/CompletedNativeReturnMetricReadoutCrosswalk.lean).

Os resultados load-bearing são:

- `clmReturnMetric_isSelfAdjoint` e `clmReturnMetric_isPositive`;
- `clmEndpoint_returnMetric_pullback_isometry`;
- `canonicalNativeGreenFrameParsevalSplit`;
- `canonicalNativeGreenFramePoisson_intertwines`;
- `canonicalNativeGreenFrameReturnMetric_isometry`;
- `canonicalNativeGreenFrameReturnReadout_eq_kernel`;
- `canonicalNativeGreenFrameReturnKernel_eq_state_inner`;
- `canonicalNativeGreenFrameReturnKernel_posSemidef`;
- `canonicalNativeReturnMetricCentralKernel_eq_gradient_energy`;
- `canonicalNativeReturnMetricCentralDefect_eq_energy_sub_native`;
- `canonicalNativeReturnMetricCentralDefect_pos`;
- `canonicalNativeReturnMetricCentralKernel_ne_nativeMoment`.

A auditoria isolada está em
[`CompletedNativeReturnMetricReadoutCrosswalkAudit.lean`](../CarrySelfAdjointOperator/CompletedNativeReturnMetricReadoutCrosswalkAudit.lean).

## Tipos e especialização concreta

A API finita upstream usa
`Matrix endpoint spectral ℂ`, `Matrix bulk endpoint ℂ` e uma matriz de câmera.
Não há no pin um construtor que escolha esses quatro tipos e os conecte ao
estado nativo completado.

A especialização Hilbertiana que o código suporta é:

| papel | declaração | tipo |
|---|---|---|
| estado completo | `canonicalNativeGreenFrameOperator` | `State →L[ℂ] ConcreteAnalysisSpace` |
| endpoint/external | `canonicalNativeGreenFrameExternal` | `State →L[ℂ] ConcreteExternalSpace` |
| bulk | `canonicalNativeGreenFrameBulk` | `State →L[ℂ] BulkGreenSpace` |
| Poisson | `canonicalNativeGreenFramePoisson` | `ConcreteExternalSpace →L[ℂ] BulkGreenSpace` |
| métrica | `canonicalNativeGreenFrameReturnMetric` | `ConcreteExternalSpace →L[ℂ] ConcreteExternalSpace` |
| estado de prova central | `canonicalCentralCompletedGradientGreenFrameSource` | `State` |

A orientação é a da análise Green: o mapa `endpoint` recebe um estado e produz
um dado externo. Ela é a transposta conceitual da matriz `endpointMap` da API
finita, e não uma igualdade de matrizes por cast.

O retorno concreto é

```lean
1 + canonicalNativeGreenFramePoisson† ∘L
      canonicalNativeGreenFramePoisson
```

isto é, exatamente o `I + P†P` da `ReturnMetric`, agora como
`ContinuousLinearMap` em espaços completos.

## Cancelamento de retorno

`canonicalNativeGreenFramePoisson_intertwines` prova

```text
P ∘ normalizedExternal = normalizedBulk.
```

`canonicalNativeGreenFrameParsevalSplit` prova

```text
E† ∘ E + B† ∘ B = 1.
```

A lemma genérica `clmEndpoint_returnMetric_pullback_isometry` transporta essas
duas identidades para

```text
E† ∘ (1 + P†P) ∘ E = 1.
```

A especialização é `canonicalNativeGreenFrameReturnMetric_isometry`. Não há
câmera, limite de atlas, parâmetro numérico ou hipótese Genuine nessa prova.

## Kernel polarizado

O readout comprimido Hilbertiano é

```lean
canonicalNativeGreenFrameReturnReadout x y :=
  inner ℂ (E x) ((1 + P†P) (E y)).
```

`canonicalNativeGreenFrameReturnReadout_eq_kernel` abre-o na fatoração

```text
⟪E x,E y⟫ + ⟪P(E x),P(E y)⟫.
```

O teorema `canonicalNativeGreenFrameReturnKernel_eq_state_inner` mostra que,
para a análise Parseval canônica, essa soma é exatamente `⟪x,y⟫`. Portanto
`canonicalNativeGreenFrameReturnKernel_posSemidef` transforma qualquer família
finita de estados em uma matriz `Matrix.gram`; sua positividade é incondicional.

Esta é uma realização positiva e lossless da análise Green. Ela não é ainda o
readout `dslope` do operador nativo: nenhum teorema no pin identifica o
readout acima com `completedGreenNormalizedResponse`, com o numerador
Wronskiano ou com `canonicalCompletedNativePolarizedDslopeKernel`.

## Teste de ordem zero

O estado central escolhido é
`canonicalCentralCompletedGradientGreenFrameSource`. O cálculo formal é:

```text
Re K_return(center, center)
  = infiniteReflectedGreenEnergy (1/2)
  = ‖canonicalCentralCompletedDirichletGradientState‖².
```

Os teoremas de calibração já provados dão

```text
h₀ < 1/16 < infiniteReflectedGreenEnergy (1/2).
```

Logo `canonicalNativeReturnMetricCentralDefect_pos` prova que

```text
Re K_return(center, center) - h₀ > 0,
```

and `canonicalNativeReturnMetricCentralKernel_ne_nativeMoment` prova a
não igualdade correspondente. O defeito exato é
`canonicalNativeReturnMetricCentralDefect_eq_energy_sub_native`.

Isto elimina esta escolha de estado/métrica como kernel nativo já no centro.
Não foi escolhida constante, fase ou escala para corrigir o valor.

## Divisão-free Wronskian seam

A álgebra finita `ReturnMetricPolarizedKernel` continua disponível para
matrizes: suas identidades division-free com separação são abstratas e
positivas. Nesta rodada, contudo, não existe no grafo atual um
`endpointMap/bulkMap/poisson` matricial finito que represente o estado Green
completado, nem um `stateReadout` que ligue o kernel Hilbertiano ao
Wronskiano nativo.

Assim não foi afirmado:

```text
return-metric numerator = completed-native Wronskian numerator
return kernel = dslope kernel
```

O seam restante é precisamente um mapa/readout nativo que, com tipos
compatíveis, prove essa igualdade. O teste de centro mostra que o mapa
ordinário de gradiente usado acima não pode ser esse mapa sem trocar a
realização; a troca não foi inventada nesta rodada.

## Relação com `carryTfvdTraceMetric`

`CarryTfvdTraceMetricKernel.lean` não foi identificado com a métrica de retorno.
Suas declarações são uma realização positiva própria:
`carryTfvdCausalSecondDifference_inner_eq_bracket_add_trace`,
`carryTfvdMetricState_injective` (para `0 < q < 1`) e
`carryTfvdMetricState_gram_posSemidef`. Não há um crosswalk tipado entre seus
mapas e `normalizedExternal`, `normalizedBulk`, `ambientPoisson` ou o kernel
nativo nesta rodada. A comparação permanece aberta, sem sugerir que as duas
formas sejam iguais.

## Next Return-Metric Gate

1. **endpointMap nativo:** `normalizedExternal` da análise Green canônica,
   como `State →L[ℂ] ConcreteExternalSpace`.
2. **bulkMap:** `normalizedBulk`, como `State →L[ℂ] BulkGreenSpace`.
3. **Poisson:** `ambientPoisson` da mesma análise.
4. **`E† G E = I`:** fechado por
   `canonicalNativeGreenFrameReturnMetric_isometry`.
5. **generalidade:** a lemma CLM é genérica em `H`, `E`, `B`; a instância
   concreta usa `canonicalCarryInfinitePartition`, sem câmera.
6. **câmera no kernel final:** nenhuma.
7. **kernel construído:** `canonicalNativeGreenFrameReturnReadout` e sua forma
   fatorada `canonicalNativeGreenFrameReturnKernel`.
8. **fatoração:** `⟪E x,E y⟫ + ⟪P E x,P E y⟫`, incondicional.
9. **PSD:** toda seção finita é `Matrix.gram`.
10. **compressed readout:** exatamente o readout Hilbertiano acima; ele não é a
    matriz `compressedReadout` da API finita.
11. **numerador sem divisão:** não instanciado para o estado nativo; falta o
    `stateReadout`/Wronskian crosswalk.
12. **coincidência Wronskiana:** não provada.
13. **centro:** não coincide; o defeito é estritamente positivo.
14. **kernel `dslope`:** não identificado.
15. **continuidade/cutoff:** nenhuma usada.
16. **inversão:** nenhuma matriz ou operador resolvente foi invertida.
17. **constantes:** nenhuma ajustada.
18. **`sixCamera`:** não usado como fundamento.
19. **limite de atlas:** não usado.
20. **no-go estático:** respeitado; o resultado negativo central é preservado.
21. **novo kernel nativo:** não construído; apenas o graph kernel forçado pela
    análise Green foi nomeado.
22. **Hankel:** não disponível a partir desta especialização, pois falta a
    igualdade com `dslope`/`hₙ`.
23. **operador autoadjunto:** não obtido por esta rota.
24. **Outcome:** C (mismatch central explícito), com o seam de tipos finitos
    registrado separadamente.
25. **próximo theorem mínimo:** fornecer um `stateReadout` e mapas de endpoint,
    bulk e Poisson tipados que satisfaçam simultaneamente a coligação de
    retorno e a igualdade do numerador com o Wronskiano completed-native;
    antes disso, qualquer kernel `dslope` seria uma identificação sem suporte.
26. **HP:** a comparação com os momentos só pode começar depois desse readout;
    não é permitido chamar o graph kernel acima de momento Gram nativo.

## Auditoria

O arquivo de auditoria imprime os axiomas de todas as declarações públicas da
rodada. Cada resultado retorna somente:

```text
propext, Classical.choice, Quot.sound
```

Nenhum `sorry`, `admit` ou axioma de projeto foi adicionado.
