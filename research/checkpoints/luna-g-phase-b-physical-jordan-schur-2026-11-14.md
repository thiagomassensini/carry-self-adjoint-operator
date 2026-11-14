# Luna G — checkpoint da investigação física (Fase B)

Data: 2026-11-14

Repositório: `thiagomassensini/carry-self-adjoint-operator`

Branch isolada: `codex/luna-g-physical-compensation-2026-11-14`

Base: `codex/luna-g-c2-energy-limit-2026-11-14` (entrega da Fase A, PR #118)

## Resultado compilado nesta entrega

O módulo `CompletedNativeChiralJordanSchurCrosswalk.lean` formaliza uma ponte quantitativa entre a leitura da cabeça C2 e os canais Jordan físicos originais. Para cada ordem fixa `n` e todo `ε > 0`, eventualmente em `k`, uniformemente em todos os vetores `x`,

```text
| nativeSourceC2CentralLegReadout n k (nativeSourceC2TailCutoff n k) x
    - (‖nativeSourceJordanPositiveState n k x‖²
       - ‖nativeSourceJordanNegativeState n k x‖²) / 4 |
    ≤ ε ‖x‖².
```

O corte é o cutoff diagonal C2 já escolhido pela Fase A. O limite aqui é radial (`k → ∞`); não é o limite de cutoff (`M → ∞`) nem um limite transversal. Os dois canais e seus cruzamentos continuam dentro das normas originais.

Também foram provadas identidades exatas para vetores reais nas coordenadas de paridade:

```text
nativeSourceFiniteBoundaryEnergy (2*n) (evenParityVector u)
  = 4 * sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment 0 n u

nativeSourceFiniteBoundaryEnergy (2*n) (oddParityVector u)
  = 4 * sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment 1 n u.
```

Sob a hipótese de que o bloco de prefixo (`sourceMomentMatrix ... s n`) é PosDef, o vetor crítico nativo que acrescenta o próximo coeficiente satisfaz

```text
nativeSourceFiniteBoundaryEnergy (2*(n+1)) criticalVector
  = 4 * sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment s n.
```

A energia física assinada dos canais no mesmo vetor converge a esse valor. Após multiplicação pelo coeficiente original `completedNativeRealEvenCharacteristicCoefficient 0 / 4`, ela converge à `nativeSourceSchurRemainder s n` original. Isso mantém a escala da fonte e não supõe que o pivô seguinte seja positivo.

## Identidades e critérios da fonte reutilizados

- `nativeSourceJordan_signed_energy_tendsto`: para cada ordem e entrada, `2(‖v⁺‖² − ‖v⁻‖²)` converge incondicionalmente à energia de fronteira original.
- `nativeSourceNegativeLeakageTrace_tendsto_zero_iff_columns`: para ordem fixa, o traço negativo tende a zero se e somente se cada uma das finitas colunas físicas negativas tende a zero.
- `nativeSourceJordanNegativeState_norm_sq_le_trace`: o traço controla uniformemente todas as entradas, preservando a norma de fonte.
- `nativeSourceBoundary_nonneg_of_asymptotic_channel_dominance`: a dominação assintótica entre canais também é suficiente sem exigir desaparecimento do canal negativo.
- `sourceMomentSchur_critical_direction` e `nativeSourceSchurRemainder_eq`: a direção crítica lê exatamente o próximo Schur e a escala original da característica.

Os dois critérios de canal são suficientes, mas a existência de uma cota de traço ou de dominação para a fonte nativa continua uma obrigação matemática, não uma conclusão desses lemas.

## Investigação das rotas anteriores

- Carry [#89](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/89) dá a identidade Jordan assinada e condições suficientes para passar o sinal. Não fornece o limite das colunas negativas em todas as ordens.
- Carry [#90](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/90) relata certificado externo para ordem 8 e limite radial condicionado a esse cálculo; não é certificado Lean nem resultado para toda ordem.
- Carry [#92](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/92) caracteriza o fechamento pelo sinal dos restos Schur da fonte; não prova esses sinais para a sequência nativa.
- Carry [#93](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/93), [#101](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/101), [#102](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/102), [#103](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/103) e [#104](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/104) documentam obstáculos de sinal para as representações theta/massa/válvula nomeadas. Seus contraexemplos são locais a essas rotas; não excluem toda representação geométrica física.
- Carry [#109](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/109) fornece pontes coeficiente/pivô e reduz uma obrigação crítica, mas não dá o sinal do próximo pivô da fonte.
- Geometry of Numbers [#41](https://github.com/thiagomassensini/geometry-of-numbers/pull/41), [#70](https://github.com/thiagomassensini/geometry-of-numbers/pull/70), [#143](https://github.com/thiagomassensini/geometry-of-numbers/pull/143) e [#316](https://github.com/thiagomassensini/geometry-of-numbers/pull/316) dão identidades de ortogonalização, quatro cruzamentos TFVD, controle de cauda e atualização rank-one de Bézout/Schur. Essas são relações bilineares algébricas. Não identificam por si mesmas essa forma com a métrica hermitiana positiva dos canais físicos nem controlam seu sinal.

## Separação dos índices e da geometria

- `n`: ordem Hankel/bloco de momentos.
- `k`: índice radial de aproximação.
- `M(n,k)`: cutoff em número de células C2, fixado pela construção diagonal da Fase A.
- `j`: profundidade diádica das células e seus pesos/amplitudes dentro da fonte C2.

Os lemas novos comparam `k → ∞` para o cutoff `M(n,k)`; não afirmam uniformidade em `n`, nem estimativa nova somando as escalas de profundidade `j`.

## Primeira obrigação matemática ainda aberta

Falta obter da fonte original, sem usar positividade de energia ou de Hankel como premissa, uma estimativa que controle o canal negativo. Dois alvos suficientes já disponíveis são:

1. `nativeSourceNegativeLeakageTrace n k → 0`, equivalentemente o desaparecimento de cada coluna negativa física para ordem fixa; ou
2. uma dominação quantitativa uniforme das entradas, como `‖v⁻‖² ≤ ‖v⁺‖² + ε_n(k) ‖x‖²`, com `ε_n(k) → 0`.

A nova identidade da direção crítica torna explícita a mesma obrigação em linguagem de pivôs: sob PosDef do prefixo antigo, provar que o próximo `sourceMomentSchur` é positivo (ou fornecer um controle de canal independente que implique isso). A atualização rank-one de Bézout não fornece essa desigualdade. Também não foi encontrada nesta investigação uma desigualdade local, derivada dos pesos `2^{-j}`, que sobreviva ao completamento e controle os quatro cruzamentos físicos. Não se conclui positividade Hankel incondicional nem a hipótese `InfinitePositiveRealNativeZeros`.

## Validação

- Módulo novo e auditoria compilados com warnings como erros.
- `lake build --wfail` da raiz concluído com sucesso (10,241 jobs antes da última extensão apenas algébrica da auditoria; os módulos atualizados foram reconstruídos depois).
- Auditoria transitiva das seis declarações novas: apenas `[propext, Classical.choice, Quot.sound]`.
- Nenhum `sorry`, `admit` ou axioma foi adicionado.

## Dependências de publicação

- Fase A Carry: PR [#118](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/118), branch `codex/luna-g-c2-energy-limit-2026-11-14`.
- Certificados finitos GoN (ordens `1 ≤ n ≤ 6`, dimensões pares `2,4,6,8,10,12`): PR [#331](https://github.com/thiagomassensini/geometry-of-numbers/pull/331), downstream da Fase A.
- Esta fase deve ser aberta como PR novo contra a branch da Fase A, sem mudar os PRs anteriores.
