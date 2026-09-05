# Mapa — controle quiral de dois pontos e trace dinâmico completado

Data: 2026-09-05. Repositório: `thiagomassensini/carry-self-adjoint-operator`.
Base: `d3681d0dbd915e6b92d5123b8bb88ceb1b9166b6`, descendente de
`225a85d9e8e3e0a3b659c5b6ad821458770b3195`, com a dinâmica da PR #51 integrada.
Branch desta rodada: `agent/chiral-two-point-control`.

## Resultado e alcance

A desigualdade proposta de dois pontos está provada no Lean, para passos
radiais suficientemente pequenos. A fonte analítica desse controle já existia:
os limites certificados dos momentos theta provam a positividade da matriz
Pick radial de tamanho dois. Esta rodada extrai a desigualdade explícita,
preserva as amplitudes dos vetores quirais existentes e transporta a estimativa
para o trace dinâmico com todas as caudas e completion.

Não há hipótese matemática nova no endpoint canônico. O resultado não prova
contratividade em toda ordem, não constrói certificado HP e não identifica o
Gamma antigo com o Gram nativo. A branch fica separada, sem merge em `main`.

Arquivo novo: [CompletedNativeChiralTwoPointControl.lean](../CarrySelfAdjointOperator/CompletedNativeChiralTwoPointControl.lean).
Contém 19 teoremas e uma definição: `chiralTwoPointTraceMargin`, um polinômio
escalar para medir o determinante. Nenhum operador, momento, Jacobi, Gamma ou
estado de Hilbert foi redefinido.

## 1. Oito é o fator exato

Os pontos existentes são

$$
z_0=\frac{i}{k+1},\qquad z_1=\frac{2i}{k+1}.
$$

Aqui `k` controla o passo radial. Os cutoffs das cabeças são outros índices,
`M` e `N`, independentes de `k`. Também não se identifica altura com parâmetro
de resolvente.

Se $q_j=q(z_j)$ é `completedNativeHermiteBiehlerChiralQuotient`, a matriz
Pick existente é $(k+1)$ vezes a matriz da pergunta. O novo teorema
`canonicalCompletedNativeRadialChiralPickSampleMatrix_two_det` calcula

$$
\det K^{\mathrm{Pick}}_{k,2}
=\frac{(k+1)^2}{72}
\left[(1-|q_0|^2)(1-|q_1|^2)-8|q_1-q_0|^2\right].
$$

Portanto, `..._two_det_nonneg_iff` fornece a equivalência exata entre
determinante não negativo e

$$
8|q_1-q_0|^2\le(1-|q_0|^2)(1-|q_1|^2).
$$

`canonicalCompletedNativeChiralTwoPoint_variation_eventually` prova essa
desigualdade para todo `k` suficientemente grande.
`canonicalCompletedNativeChiralTwoPoint_diagonals_eventually` prova também
$|q_0|^2\le1$ e $|q_1|^2\le1$ no mesmo sentido eventual.
Não se fornece um valor numérico para o limiar de `k`.

## 2. De onde vem a estimativa, sem hipótese circular

Os resultados reutilizados encontram-se nestes módulos:

| Peça existente | Arquivo | Uso nesta rodada |
|---|---|---|
| `completedNativeXiCosineMoment_strict_kurtosis` | [CompletedNativeXiThetaMomentBounds.lean](../CarrySelfAdjointOperator/CompletedNativeXiThetaMomentBounds.lean) | Prova analítica efetiva da desigualdade estrita dos primeiros momentos theta. |
| `canonicalCompletedNativeXiCosineLowMomentCertificate` e `canonicalCompletedNativeLowOrderHerglotzCurvaturePositive` | [CompletedNativeXiCosineMomentHerglotzGate.lean](../CarrySelfAdjointOperator/CompletedNativeXiCosineMomentHerglotzGate.lean) | Identificam os coeficientes nativos e fecham as curvaturas baixas sem hipótese adicional. |
| `canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef` | [CompletedNativeXiCosineMomentHerglotzGate.lean](../CarrySelfAdjointOperator/CompletedNativeXiCosineMomentHerglotzGate.lean) | Endpoint de positividade de dois pontos já disponível antes desta rodada. |
| `canonicalCompletedNativeRadialChiralMultiplierContractiveAt_iff_pickPosSemidef` | [CompletedNativeRadialChiralMultiplier.lean](../CarrySelfAdjointOperator/CompletedNativeRadialChiralMultiplier.lean) | Converte PSD em controle de todas as combinações complexas da família de dois vetores. |
| `canonicalCompletedNativeRadialDslopeSampleMatrix_posSemidef_iff_pick` e a realização assinada | [CompletedNativeProjectiveChiralCarrier.lean](../CarrySelfAdjointOperator/CompletedNativeProjectiveChiralCarrier.lean), [CompletedNativeRadialChiralMultiplier.lean](../CarrySelfAdjointOperator/CompletedNativeRadialChiralMultiplier.lean) | Preservam a identificação escalar e as amplitudes originais. |

A entrada analítica é, literalmente,

```lean
completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 2 <
  3 * completedNativeXiCosineMoment 1 ^ 2
```

A cadeia existente passa pela desigualdade de quarta ordem, pelos dois
primeiros momentos logarítmicos, pelo determinante radial e pela congruência
Cayley. O módulo [CompletedNativeRadialHerglotzTwoPoint.lean](../CarrySelfAdjointOperator/CompletedNativeRadialHerglotzTwoPoint.lean)
já calcula o primeiro coeficiente não nulo do determinante reduzido como
$4h_0h_1$. Esse cálculo não foi refeito.

O nome `Herglotz` identifica os módulos e as matrizes existentes; nenhuma
propriedade Herglotz global foi postulada. Também não foram usados RH, listas
de zeros, alturas espectrais, fitting ou positividade do Hankel nativo como
premissa.

## 3. A comparação pedida vale para as combinações, incluindo amplitudes

O novo teorema
`canonicalCompletedNativeChiralTwoPoint_projective_energy_eventually` afirma

$$
\left\|\sum_{j=0}^{1}c_j u_j^-\right\|^2
\le
\left\|\sum_{j=0}^{1}c_j u_j^+\right\|^2
\quad\text{para todo }(c_0,c_1)\in\mathbb C^2,
$$

eventualmente em `k`, com os dois canais de
`canonicalCompletedNativeRadialProjectiveChiralState`. A amplitude
`completedNativeNormalizedPositiveChiralAmplitude` não é removida ou
recalibrada. A prova usa a contratatividade existente com os coeficientes
$c_j$ multiplicados pela amplitude já definida.

`canonicalCompletedNativeChiralTwoPoint_native_posSemidef_eventually` chega
ao `canonicalCompletedNativeRadialDslopeSampleMatrix k 2` usando a
congruência já demonstrada. A identidade assinada do kernel permanece a
mesma.

## 4. O que exatamente o bordo deve controlar

A convenção do repositório é

$$
C=-F',\qquad P=C+iF,\qquad N=C-iF,\qquad q=N/P.
$$

Os novos lemas algébricos verificam

$$
N_1P_0-N_0P_1=2i(C_1F_0-C_0F_1),
\qquad |P_j|^2-|N_j|^2=4\operatorname{Im}(C_j\overline{F_j}).
$$

Definimos somente o escalar diagnóstico

$$
\mathcal M((F_0,C_0),(F_1,C_1))
=\operatorname{Im}(C_0\overline{F_0})\operatorname{Im}(C_1\overline{F_1})
-2|C_1F_0-C_0F_1|^2.
$$

`chiralTwoPoint_variation_iff_trace_margin` prova que, quando $P_0,P_1\ne0$,
a desigualdade com fator oito equivale a $\mathcal M\ge0$. Isso é a
estimativa de bordo sem divisões:

$$
\boxed{2|C_1F_0-C_0F_1|^2
\le\operatorname{Im}(C_0\overline{F_0})\operatorname{Im}(C_1\overline{F_1}).}
$$

Não foi necessário dividir por $F$. A não anulação dos denominadores quirais
é obtida pela regularidade eventual já existente quando se especializa aos
pontos canônicos; não permanece como hipótese do teorema eventual.

Como verificação do papel do cruzamento, o witness algébrico
`chiralTwoPoint_diagonals_do_not_control_cross` usa os traces $(1,i)$ e
$(1,3i)$. Suas energias orientadas diagonais são positivas, mas a margem é
$-5$. São traces arbitrários, não pontos canônicos e não um contraexemplo
ao resultado nativo eventual. Isso separa o controle diagonal do controle
polarizado que foi efetivamente obtido.

## 5. Encaixe exato com a dinâmica, em todos os cutoffs

`nativeC3Dynamic_completedTracePair_eq` avalia o par já existente
`canonicalC3BracketTfvdCompletedTracePair M z` com:

- cabeça ordinária lida por retorno + variância;
- log-head forçado por `nativeC3BlockDynamicLogJet`, incluindo a semente;
- `realCpBracketCutoffTail` e `canonicalC3LogJetCutoffTail`;
- o fator de câmera e sua derivada;
- `nativeXiCompletionFactor` e `nativeXiCompletionBoundaryCompanion`.

Essa avaliação reutiliza
`nativeC3DynamicLogHead_eq_returnVariance`,
`c3ReturnVariance_dressedTrace_eq_F_negFprime` e
`canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime`.
Ela conserva a rotação por $i$ no log-jet.

`nativeC3Dynamic_chiralTwoPointTraceMargin_eq` transporta a margem do par
completado nos cutoffs independentes `M,N` para o mesmo $(F,-F')$ nativo.
O endpoint novo principal é:

```lean
theorem nativeC3Dynamic_chiralTwoPointTraceMargin_allCutoff_eventually :
    ∀ᶠ k : ℕ in atTop, ∀ M N : ℕ,
      0 ≤ chiralTwoPointTraceMargin
        (canonicalC3BracketTfvdCompletedTracePair M (canonicalCompletedC3RadialTiltPoint k 0))
        (canonicalC3BracketTfvdCompletedTracePair N (canonicalCompletedC3RadialTiltPoint k 1))
```

O limiar radial funciona para todos os cutoffs simultaneamente porque as
cabeças completadas pelas respectivas caudas dão identidades exatas.
A dinâmica recupera e transporta o trace; o controle de sinal nesta prova
vem dos limites theta certificados. Não se atribui esse controle apenas à
equação afim do clock.

## 6. Obrigação posterior e auditoria

A obrigação de toda ordem continua sendo a proposição já existente:

```lean
CarrySelfAdjointOperator.CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive
```

Sua definição é:

```lean
∀ N : ℕ, ∀ᶠ k : ℕ in atTop,
  CanonicalCompletedNativeRadialChiralMultiplierContractiveAt k N
```

Esta rodada fornece `N = 2`. Não fornece o quantificador sobre `N`, um
limiar radial explícito, não degenerescência em toda ordem ou o certificado
HP. Nenhuma nova estrutura esconde essa obrigação. O no-go do Gamma antigo
permanece separado da representação assinada usada aqui.

Integração: `CarrySelfAdjointOperator.lean`, `Audit.lean` e
`KernelConstructionAudit.lean`. As dependências, `lake-manifest.json` e
`lean-toolchain` são preservados.

Comandos de validação:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralTwoPointControl
lake env lean research/chiral-two-point-control-2026-09-05/axioms.lean
bash scripts/audit.sh
git diff --check
```

O workflow contém os 14 estágios habituais mais `ObservableJetAudit`,
totalizando 15 builds, além da inspeção estática. O resultado final e os
hashes de proveniência estão em
[validation.json](../research/chiral-two-point-control-2026-09-05/validation.json).

Os 19 `#print axioms` foram conferidos. O teorema principal depende apenas de:

```text
[propext, Classical.choice, Quot.sound]
```

Os logs completos ficam em
[full-audit.log](../research/chiral-two-point-control-2026-09-05/full-audit.log) e
[axioms.log](../research/chiral-two-point-control-2026-09-05/axioms.log).
Não foram necessários testes numéricos para substituir as provas existentes.
