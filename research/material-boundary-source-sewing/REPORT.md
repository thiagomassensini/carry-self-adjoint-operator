# Bordos materiais universais e costura da fonte quiral original

## Resultado

**PASS:** uma identidade nova de vetores inteiros, válida para toda câmera b≥2 e todo cutoff M, separa o estêncil literal em seu núcleo periódico e um bordo explícito de unidades. A identidade é transportada aos vetores materiais com o relógio original e, depois, às entradas e às duas pernas da fonte quiral completada. Para dois inputs independentes, todos os cruzamentos são conservados, incluindo os dezesseis setores núcleo/bordo × Green/residual analítico.

**NO-GO localizado:** substituir o estêncil par pelo prefixo periódico completo sem sua correção antipodal muda a fonte por exatamente uma coluna completada original. Em C4, essa coluna é não nula para toda grade radial suficientemente fina, em cada cutoff material fixo. Há ainda uma testemunha material exata de cruzamento misto igual a −4 no primeiro cutoff. Nenhuma testemunha é obtida definindo um defeito genérico como diferença de dois resultados desconhecidos.

**OPEN:** a identidade entre a energia positiva material/global Green e a forma quiral assinada, a instanciação física dos dois quadrados finito/Naimark, e o anulamento do defeito Gram canônico. Este incremento resolve uma obrigação de bordos e transporte; não prova positividade all-order ou o fechamento do operador infinito.

## Proveniência e preservação

Objetivo integral preservado em `GOAL.md`. Repositório principal `thiagomassensini/carry-self-adjoint-operator`, no host `llm`, base `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`, main após PR #106. O remoto foi conferido antes da branch `agent/material-boundary-source-sewing`. Nenhuma worktree foi criada. Os dois arquivos não rastreados `C2OddTfvdTransport.lean`/`C2OddTfvdTransportAudit.lean` foram preservados byte a byte. Os demais checkouts foram apenas consultados e compilados, sem alterações de código ou branch.

Não houve mudança de fonte, pesos, amplitudes, câmera, normalização, métrica, característica, bordos, caudas ou pins. Só há módulos matemáticos novos, imports para sua exposição, registros de auditoria e documentação/evidência. Os objetos históricos permanecem idênticos. Nenhuma Gram positiva nova foi construída; Cholesky, whitening, zeros, alturas, Jacobi e certificados de momentos theta não são premissas das novas provas.

`INVENTORY.md` cobre todas as declarações pedidas nos quatro repositórios. O PR #15 do native-carry-spectral-weyl foi conferido e compilado separadamente, continuando OPEN e fora dos pins consumidos. Os commits dos checkouts consultados e dos pacotes realmente usados são distintos e registrados em `evidence/provenance.json`.

## 1. A igualdade inteira, antes de qualquer readout

Escreva ell_b=cameraSlope b e w_b=cameraBoundaryWidth b. C2 tem ell_2=4, w_2=1; as câmeras naturais têm ell_b=b e w_b=floor(b/2). Os objetos novos são especificados independentemente do resultado:

    B_(b,M) = sum_(1≤p≤ell_b*M) profile(b,p) atom(p)
    E_(b,M) = sum_(0≤r<w_b) atom(ell_b*M+r+1).

`NativeMaterialCameraBoundary.finiteStencil_eq_core_add_border` prova, no módulo livre inteiro original,

    finiteStencil b M = B_(b,M) + E_(b,M),    b≥2, M≥0.

A prova reutiliza as fórmulas originais dos coeficientes, demonstra que TODOS os coeficientes no bordo emitido são um e trata separadamente C2, câmeras ímpares e pares. No antipodal par o valor periódico é dois, mas o literal é um; essa unidade não é descartada. Isso expõe vetorialmente uma informação que antes aparecia nas decomposições escalares do Gram e no experimento finito do PR #15.

Os nomes públicos centrais são `unitBorderStencil_apply`, `finiteCoefficient_border_one`, `finiteStencil_eq_core_add_border`. Não se introduz uma forma positiva auxiliar ou um momento-alvo para provar a identidade.

## 2. Estados completos, relógio e índices

`materialCameraJet_core_border` aplica a identidade ao estêncil atuando sobre um vetor material complexo arbitrário x, no Hilbert finito original, depois de r potências do mesmo relógio log(position). `materialCameraTemporalJet_core_border` conserva a fase temporal obrigatória (−i)^r. As duas quadraturas estão no vetor complexo inteiro; não se toma parte real ou norma para construir o transporte.

`cameraMaterialFamily_core_border` sintetiza primeiro todas as câmeras com coeficientes complexos arbitrários a. `completedMaterialTransport` é a combinação linear das colunas completadas ORIGINAIS, com os coeficientes materiais fornecidos. `completedMaterialTransport_source_chart` prova que esse mapa coincide com a síntese SourceJet existente aplicada ao encoder físico de derivadas do polinômio material. O encoder é o já provado `physicalEndpointJetInput`, não uma inversa de Gram.

`originalCamera_source_input_core_border` aplica essa ligação ao estêncil literal inteiro, com janela par determinada por seu próprio polinômio. Assim a igualdade alcança efetivamente as ENTRADAS do par quiral e conserva todo o suporte, sem identificar silenciosamente duas listas de coordenadas.

| Parâmetro/índice | Significado mantido |
|---|---|
| p=i+1 | posição material positiva original |
| b | label da câmera; o alinhamento C2 e todos os raios vêm do estêncil original |
| M, L | cutoffs materiais de centros, independentes nos dois inputs |
| N | dimensão do carrier material finito |
| r, s | ordens do relógio/derivadas temporais, com suas fases |
| a no encoder | ordem da derivada do polinômio no endpoint; não é profundidade material |
| j=p−1 no produtor | grau radial do levantamento positivo já existente, explicitamente dado pelo produtor |
| k | refinamento da grade radial original; seu passo é o `canonicalCompletedC3RadialSecondStep k` existente |
| q | parâmetro do operador Green físico, 0<q<1; a identidade vale para todo q nessa faixa |

A igualdade material truncada vale para qualquer N. Para conter literalmente todos os sítios de uma família é preciso N≥max_b finiteCameraWindow(b,M). O resultado de estêncil e sua imagem por `originalMaterialCompletedSource` contêm todo o suporte sem esse truncamento. A janela polinomial escolhida no teorema de input garante a inclusão. Não se identifica profundidade com ordem temporal, label com voz prima ou passo radial com relógio material.

## 3. Dois inputs e todos os produtos cruzados

`completed_camera_two_inputs` usa famílias de labels distintas, câmeras b e c, coeficientes independentes a e z, cutoffs M e L, ordens r e s e vetores materiais independentes x e y. Depois das igualdades vetoriais, avalia somente a FORMA ORIGINAL

    J(u,v) = (inner(u.incident,v.incident) − inner(u.returned,v.returned))/2.

O resultado guarda, para todo par ordenado de câmeras, os quatro termos B/B, B/E, E/B e E/E, com fator conjugate(a_i)*z_j. Não se substitui J pelo produto interno positivo do carrier material ou pelo Gram periódico.

`originalMaterialSource_border_columns` calcula a imagem do bordo como a soma explícita das colunas completadas k, ell_b*M+r. Os fatores de completamento e o retorno de cada coluna permanecem nos objetos originais.

`physicalGreenPiece` usa os operadores físicos originais `physicalPairGreenResolvent`, `physicalGreenBulkBoundary` e `physicalGreenResidualNumerator`. A soma dos dois canais reconstrói exatamente cada peça material. `originalCamera_four_vector_channels` e `cameraFourChannels_synthesis` provam a igualdade de estados

    fonte literal = sum_cameras a_b sum_(piece∈{núcleo,bordo}) sum_(t∈{G,R}) Phi_(b,piece,t).

`completedStencilFamily_signed_sixteen_sectors` polariza duas sínteses independentes desses mesmos estados. Para cada par de câmeras são mantidos os dezesseis termos: os quatro pares materiais e, em cada um, GG/GR/RG/RR. R inclui o numerador analítico completo; nenhum residual é presumido zero. Esses operadores Green do carrier Cauchy não são automaticamente identificados com o GreenFrame global positivo. A forma segue assinada e a identidade não demonstra seu sinal.

## 4. Regressões e a primeira contribuição que não pode desaparecer

As regressões Lean são universais em M, inclusive M=0:

    C2: finiteStencil 2 M = B_(2,M) + atom(4M+1)
    C3: finiteStencil 3 M = B_(3,M) + atom(3M+1)
    C4: finiteStencil 4 M = B_(4,M) + atom(4M+1) + atom(4M+2)
    C5: finiteStencil 5 M = B_(5,M) + atom(5M+1) + atom(5M+2).

`first_mixed_material_border_cross` verifica no kernel, no carrier material de oito posições com amostras unitárias (contendo as janelas completas C2 e C5 nesse cutoff), que no cutoff 1

    inner(E_C2, B_C5) = −4.

O bordo C2 é a unidade em p=5; o coeficiente do núcleo C5 nessa posição é −4. Portanto os termos mistos materiais não podem ser apagados em uma identidade geral de energia. Esta testemunha está na métrica material original; não é um valor do kernel quiral.

Para toda câmera par b≥4, `even_antipodal_source_difference` deriva dos coeficientes originais, antes de avaliar a forma, o defeito exato

    fonte(prefixo periódico até bM+b/2) − fonte(estêncil literal)
      = canonicalCompletedNativeRadialProjectiveChiralState k (bM+b/2−1).

`original_completed_column_ne_zero` prova que essa coluna é não nula sob a regularidade da amplitude original. A condição não contém positividade do próximo pivô nem momentos theta. `c4_antipodal_source_error_eventually_ne_zero` usa a regularidade eventual já existente da fonte para obter uma testemunha sem essa hipótese pontual: para cada M fixo, em toda grade k suficientemente fina, os DOIS ESTADOS C4 são diferentes. Essa é a primeira unidade antipodal omitida, não um residual apenas nomeado. Não se infere que seu valor energético assinado seja não nulo: um vetor não nulo pode ser isotrópico para J.

## 5. Classificação e limites do incremento

| Estado | Enunciado que o justifica |
|---|---|
| PASS | `finiteStencil_eq_core_add_border`, universal em câmera/cutoff, no módulo inteiro original |
| PASS | `materialCameraTemporalJet_core_border`, `originalCamera_source_input_core_border`, com relógio, fase e encoder existentes |
| PASS | `completed_camera_two_inputs`, `completedStencilFamily_signed_sixteen_sectors`, antes/depois da síntese completa |
| PASS | regressões C2/C3/C4/C5 em todo cutoff e produto cruzado material exatamente −4 |
| CONDICIONAL | não anulamento de uma coluna para k específico, dado `completedNativeNormalizedPositiveChiralAmplitude(...)≠0`; condição explícita de regularidade, não de sinal |
| NO-GO | `c4_antipodal_source_error_eventually_ne_zero`: o candidato que omite a unidade antipodal não é a fonte literal, para cada M e k suficientemente fino |
| OPEN | igualdade de pareamento que transportaria a energia positiva nativa/Green global à forma quiral assinada |
| OPEN | instanciação física de `NaimarkProjectorIntertwiningSeam` e controle de comutadores/domínios |
| OPEN | anulação efetiva de `canonicalCompletedNativeGreenMomentGramDefect` e sinal all-order |

A identificação de uma energia positiva com J exigirá uma desigualdade/identidade física adicional para os mesmos vetores, com retorno e correções. O transporte finito aqui construído não é afirmado isométrico ou uniformemente condicionado. Não se substituem as interfaces abertas por uma Gram ajustada, nem se extrapola deste resultado para HP/Herglotz ou um operador infinito.

## 6. Validação e reprodução

No checkout principal do llm:

    python3 research/material-boundary-source-sewing/validate.py

O runner registra vinte comandos obrigatórios com seus diretórios, duração e exit codes: preservação/proveniência; inventário dos 43 símbolos novos; build separado do PR #15; quatro inventários Lean; build explícito dos quatro módulos novos e auditoria direta pelo kernel; seis registries históricos; `lake build --wfail`; build e execução do `CarrySelfAdjointOperator.Audit` integrado; diff e preservação final. Os imports raiz expõem os módulos novos e a auditoria integrada inclui seu guard.

`NativeMaterialBoundarySewingAudit` registra `#print axioms` de TODAS as 43 declarações novas, incluindo definições e regressões, e aplica `#audit_physical_sewing` a tipos e corpos transitivamente. O fecho contém 6.227 dependências e permite somente `propext`, `Classical.choice`, `Quot.sound`. Nenhum `sorry`, `admit`, axioma customizado, `unsafe` ou `native_decide` foi adicionado. A aritmética finita do testemunho −4 é reduzida por Lean.

O scanner textual histórico `scripts/static_audit.sh` rejeita três palavras em COMENTÁRIOS preexistentes de `NativeMomentPrefixNoBootstrap`, `NativeSourceAllOrderSchur` e `CompletedNativeChiralReturnLeakageControl`. Seu exit code bruto é 1; o log é preservado como `historical-raw-static.log.gz`. Não se anuncia esse script como aprovado. O novo verificador confirma que o conjunto bruto de três ocorrências é idêntico ao commit base e verifica o código novo sem comentários, além do guard transitivo do kernel. Nenhum módulo histórico foi editado para ocultar essas ocorrências.

`evidence/commands.json` conserva os vinte comandos exigidos. `VALIDATION.json` vincula os hashes das fontes, imports, registries, objetivo, relatório, scripts e logs comprimidos deterministicamente. `verify_evidence.py` reconfere o pacote, os exit codes, as 43 raízes e os axiomas. Builds são incrementais nos pins preservados; não se anuncia uma reconstrução limpa de todas as dependências. Os checks Lean dos inventários são desta rodada. Native e geometria usam seus checkouts consultados; GreenFrame usa o runtime/cache consumido pelo operador, depois da comparação byte a byte dos cinco módulos originais com o checkout consultado. A tentativa inicial nesse checkout encontrou ausência de oleans; o log `green-checkout-cache-miss.log.gz` é preservado. Nenhuma alteração de pin ou recompilação gigante foi usada para contornar isso.

Publicação em commit focado e PR descritivo, sem merge automático conforme solicitado. O SHA da entrega, o link e o estado do PR acompanham a mensagem final e o manifesto de entrega. Os quatro checkouts de pesquisa e os trabalhos locais são preservados.
