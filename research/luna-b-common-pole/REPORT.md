# Luna B — cancelamento do polo comum C2

## A. Origem e proveniência

Trabalho feito em `thiagomassensini/carry-self-adjoint-operator`, na branch isolada `agent/luna-b-common-pole-20261114`. O SHA-base consultado e usado foi `045369f6dedcb2e75e9aefed1d12c9f73b9a2532` (`origin/main` no início da tarefa). A árvore compartilhada não foi editada; o trabalho ocorreu em `/home/thlinux/worktrees/csa-common-pole-20261114`.

As definições originais usadas são:

- `operatorHeightParameter` e `nativeXiCompletionFactor` em `CompletedOperatorCharacteristic.lean`;
- `factor 2 = c2Factor` em `NativeCarrySpectralWeyl.Camera.Factors`;
- `completedNativeCharacteristic 2 M`, a cabeça C2 mais sua cauda completa, em `CompletedNativeCharacteristic.lean`;
- `nativeXiCompletionFactor_mul_completedNativeCharacteristic`, que dá o cross identity sem divisão;
- a normalização existente `nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment`.

A câmera usada é explicitamente a câmera 2: `c2OriginalCameraDenominator_eq_original_Q` mostra
`(1 - 2^(1-s)) * (1 + 2^(-s))`, com `s = operatorHeightParameter z`. A completion é o `nativeXiCompletionFactor` original, que contém o fator `s(s-1)/2`, `π^(-s/2)` escrito pela exponencial e `Gamma(s/2)`. O bracket é o `completedNativeCharacteristic 2 M`; não foi redefinido a partir dos momentos.

Nenhum pin foi alterado. SHA dos pins principais no `lake-manifest.json`: `NativeCarryC3Crosswalk` `150cfc7fb08da96bf8117f15869cc2b819d593c2`, `NativeCarrySpectralWeyl` `298d83c9351e308a5213b9f5ac32e44087f98a9f`, `CPFormal` `65d50f6db1208708e109982ba97e1d51d3039956`, `geometry-of-numbers` `d7cc54f5c485320f1fada33118e9e6101488819a`, Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`. Toolchain: Lean `v4.32.0`.

## B. Resultados demonstrados em Lean

Em `CommonPoleHankelCancellation.lean`:

- `geometricPoleHankel_eq_smul_outerProduct`: para quaisquer amplitude `α`, razão `ρ`, deslocamento `s` e dimensão `n`, a matriz Hankel geométrica é exatamente `(α ρ^s)` vezes o produto externo de `vᵢ=ρ^i`;
- `geometricPoleHankel_quadratic`: a forma quadrática é `α ρ^s (Σᵢ xᵢρ^i)^2`;
- `commonPoleOddCoefficient_quadratic`: especializa a sequência `p(j)=-2(-4)^j`;
- `commonPoleOddCoefficient_channels_cancel`: `p` e `-p` cancelam para todo vetor, dimensão e deslocamento, inclusive vetor escolhido independentemente como direção crítica.

Em `CompletedNativeCommonPoleCancellation.lean`:

- regras genéricas de produto e quociente para `R_X=-X'/(2X)`;
- `commonPoleHeightFactor_response` e `commonPoleOddResponse_eq`, com a parte ímpar `-2z/(1+4z²)`;
- diferença dividida multiplicada por seus dois denominadores, válida também na diagonal;
- fora da diagonal, `commonPoleOddResponse_dividedDifference`; o numerador `-2+8zw` é registrado como soma de dois termos separáveis;
- a recorrência formal dos coeficientes, `commonPoleOddFormalSeries_rational_identity` e a unicidade do formal que resolve `(1+4X²)R(X)=-2X`. Para a ordem ímpar `2j+1`, o coeficiente é `-2(-4)^j`.

Em `CompletedNativeCommonPoleAdapter.lean`:

- cross identity C2 exato, identidade `F=A B/Q` quando `Q≠0`, e forma reduzida `F=a B/q` como igualdade de germes no centro crítico;
- cancelamento exato dos canais `R_A-R_Q = R_a-R_q` antes de extrair coeficientes;
- igualdade de todos os jets centrados dos dois canais;
- normalizações `-F'/F=2R_F` e `nativeSourceOddBoundaryCoefficient j=2*primeDepthGeometricMoment j` (esta última reutiliza o teorema existente de provenance).

## C. Lei geral do polo comum e forma Hankel

Para `p(j)=-2(-4)^j`, a matriz no deslocamento `s` é

`Bᵖ_{ij} = -2(-4)^s (-4)^i (-4)^j`.

Logo

`ΣᵢΣⱼ xᵢxⱼ p(s+i+j) = -2(-4)^s (Σᵢxᵢ(-4)^i)^2`.

O canal oposto tem exatamente o sinal negativo e cancela. A identidade não requer inversibilidade, sinal dos coeficientes, positividade de prefixos ou que `x` venha de uma construção particular. Em especial ela continua válida para qualquer vetor crítico de Schur. Nenhuma afirmação de posto numérico além da igualdade explícita com produto externo é necessária para este resultado.

## D. Cancelamento de resposta e jets da fonte C2

Defina `X(z)=operatorHeightParameter(z)-1`, `A(z)=nativeXiCompletionFactor(z)`, `Q(z)=factor 2 (operatorHeightParameter z)`, `a=A/X`, `q=Q/X` e `B_M(z)=completedNativeCharacteristic 2 M (operatorHeightParameter z)`. O teorema existente dá

`A(z) B_M(z) = Q(z) F(z)`.

Onde `Q` e `X` são não nulos, Lean demonstra `F(z)=a(z) B_M(z)/q(z)`. Como `operatorHeightParameter(0)=1/2`, `X(0)=-1/2`; `Q(0)≠0` segue do limite C2 existente no native line. Portanto a forma reduzida vale no germe crítico sem prolongamento em `s=1`.

As regras de produto dão `R_A=R_X+R_a` e `R_Q=R_X+R_q`. A subtração elimina `R_X` exatamente. O resultado é primeiro uma igualdade de germes, e `Filter.EventuallyEq.iteratedDeriv_eq` a transporta para cada ordem de jet. Assim o termo de polo, cujos coeficientes ímpares são `p(j)`, cancela antes de qualquer caixa ou estimativa independente dos canais.

A normalização permanece explícita: o operador usa `-F'/F=2R_F`; o coeficiente nativo existente é duas vezes `primeDepthGeometricMoment`. Não se identificou a resposta inteira `R_X` com o kernel canônico; somente sua parte ímpar participa do Hankel acima.

## E. Proveniência e alcance finito

Classificação: **PARTIAL estrutural**. Foram provadas identidades algébricas e de germes, uniformes em dimensão e ordem. Nenhuma desigualdade de sinal para a parte restante da fonte foi demonstrada. Não se conclui positividade de qualquer Hankel da fonte nem positividade all-order.

O termo `p` é apenas o canal algébrico de Taylor da parte ímpar do fator comum `s-1`; não é uma altura nativa ou um átomo físico acrescentado à fonte.

## F. Limitações e contraexemplos de escopo

A sequência geométrica produz um bloco de posto um, mas o restante dos coeficientes da fonte pode determinar qualquer sinal. A lei de cancelamento, isoladamente, não força sinal para o bloco total. Não foi introduzida Gram positiva, medida positiva, zeros espectrais ou identidade theta como premissa.

## G. Obrigações ainda abertas

- O prolongamento removível de `q(s)=Q(s)/(s-1)` em `s=1`, incluindo o valor derivado de `Q'(1)`, não foi formalizado; não é necessário no germe usado em `s=1/2`.
- Estimativas independentes dos coeficientes restantes e positividade das duas torres Hankel permanecem fora deste prompt e abertas.

## H. Validação

O script `scripts/validate-luna-b-common-pole.py` compila explicitamente os cinco módulos B1/B2/B3, canários e auditoria, com `-DwarningAsError=true`; também verifica tokens de prova proibidos, `git diff --check` e dependências de axiomas dos teoremas públicos.

Execução concluída com sucesso: `validated 5 Lean modules; 26 axiom reports use only accepted foundations`. Cada declaração auditada depende somente de `propext`, `Classical.choice` e `Quot.sound`. Os canários em `CommonPoleRegression.lean` verificam `p(0)=-2`, `p(1)=8`, o bloco unidimensional e a identidade multiplicada na diagonal. Os novos módulos de pesquisa são compilados explicitamente pelo script; o build raiz não foi usado como substituto dessa validação.

A verificação GitHub `Exact-checkout Lean theorem audit` da PR #114 falhou em `scripts/static_audit.sh`. A auditoria estática global encontra três palavras em comentários de arquivos já presentes em `origin/main`: `axiom` em `CompletedNativeChiralReturnLeakageControl.lean` e `NativeSourceAllOrderSchur.lean`, e `admit` em `NativeMomentPrefixNoBootstrap.lean`. A mesma busca em `origin/main` retorna exatamente essas três ocorrências; os cinco módulos Lean desta PR não contêm nenhum dos tokens verificados. Portanto, esta falha reproduz-se na base e não indica escape de confiança introduzido por esta mudança. O check ainda aparece como falho no GitHub; o script compartilhado não foi alterado neste trabalho.

## I. Próxima obrigação mínima

Para avançar de identidade estrutural a uma margem de sinal C2, obter uma caixa independente para o restante do canal reduzido `R_a-R_q`, preservando sua correlação com o bracket completo `B_M`.

Estado de entrega: PR #114 está aberta em draft contra `main`, sem merge. A compilação/auditoria Lean específica passou; o único check reportado pelo GitHub está bloqueado pelas três correspondências preexistentes acima.
