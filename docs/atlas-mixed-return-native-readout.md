# Mapa — atlas relacional, retorno misto e readout nativo

Conferência de 2026-09-05. Base: `225a85d9e8e3e0a3b659c5b6ad821458770b3195`, branch `agent/projective-valve-moment-frontier`.

**O atlas ajudou a fechar uma identificação concreta:** o raio residual derivado do Gram de câmeras, aplicado às características efetivas com cabeça e cauda completas, recupera o escalar nativo. Removendo seu fator calculado e aplicando a completude nativa, recuperamos a característica do autoadjunto, seus jets de todas as ordens e sua massa formal recíproca. **A identidade desse readout com a resposta do kernel positivo de retorno continua aberta.**

A nota de entrada é `Downloads/hp/ATLAS_RELACIONAL_MESTRE_PERSISTENCIA_ESTRUTURAL.md`, snapshot de 17 de agosto. Foi lida integralmente e preservada. Seu hash e as fontes consumidas estão no [registro de proveniência](../research/mixed-return-readout-2026-09-05/note-sources.json). Os estados antigos de PR/CI e os rótulos de pendência não foram usados como diagnóstico atual.

## 1. A seta fechada nesta rodada

Na ordem de câmeras $(2,3,4,5,6,7)$, a rodada anterior demonstrou

$$
v_*=(-6,-3,2,0,3,0)^T,\qquad Gv_*=(278/3)e_6,\qquad v_*^TGv_*=278.
$$

Aqui $e_6$ designa o eixo da câmera de base 6. Portanto o raio é ortogonal, na métrica $G$, aos outros cinco eixos. Esses coeficientes vêm da geometria de retorno; não foram escolhidos ajustando os momentos de altura.

Para cada câmera, usamos o objeto efetivamente definido em [CompletedNativeCharacteristic](../CarrySelfAdjointOperator/CompletedNativeCharacteristic.lean):

$$
\mathcal C_b^{[M_b]}(s)
=\operatorname{head}_{b,M_b}(s)
+\sum_{j\ge0}\operatorname{centerTerm}_b(s,j+M_b).
$$

O corte conta centros completos. A cauda é a soma analítica dos centros restantes. Cada câmera pode ter um $M_b$ diferente, inclusive zero: a igualdade concerne à apresentação completada; não afirma que uma cabeça vazia ou um prefixo finito determine a cauda.

Definimos a combinação literal

$$
\mathcal M_{\mathbf M}(s)
=-6\mathcal C_2^{[M_2]}(s)-3\mathcal C_3^{[M_3]}(s)
+2\mathcal C_4^{[M_4]}(s)+3\mathcal C_6^{[M_6]}(s).
$$

Escrevendo $d_2(s)=1-2^{1-s}$, o cálculo dos fatores fornece

$$
-6A_2(s)-3A_3(s)+2A_4(s)+3A_6(s)=-4d_2(s)A_3(s).
$$

Da fatorização já demonstrada de cada câmera, agora resulta no Lean

$$
\boxed{\mathcal M_{\mathbf M}(s)=-4d_2(s)A_3(s)\,Z_{\rm nat}(s)},
\qquad -1<\Re s<1.
$$

O sinal negativo pertence à orientação do raio escolhido. A igualdade conserva todas as pernas, as caudas e os cruzamentos da combinação. Mudanças independentes dos cortes deixam $\mathcal M$ invariante nesse domínio.

## 2. A normalização da energia modal também foi identificada

O pacote Weyl já definia a amplitude modal mista como $d_2 A_3 Z_{\rm nat}$. A nova prova mostra que ela é $-\mathcal M/4$ para as câmeras reais da construção, em vez de usar apenas aquela definição como identificação.

Com $s(t)=\frac12+it$, a normalização pelo comprimento do raio dá

$$
\boxed{\frac{|\mathcal M_{\mathbf M}(s(t))|^2}{278}
=\frac8{139}|d_2(s(t))A_3(s(t))Z_{\rm nat}(s(t))|^2
=E_{\rm mixed}(t).}
$$

O coeficiente é exatamente $16/278=8/139$, sem ajuste numérico. Esse é o módulo ao quadrado do readout modal completo. A igualdade não identifica, por si, sua energia escalar com o Gram dos momentos da log derivada.

## 3. Da combinação geométrica à característica e aos jets

Defina $D(s)=-4d_2(s)A_3(s)$ e denote por $\gamma(t)$ o `nativeXiCompletionFactor` do operador. A característica obtida do readout é

$$
\widehat{\mathcal M}_{\mathbf M}(t)
=\gamma(t)\frac{\mathcal M_{\mathbf M}(s(t))}{D(s(t))}.
$$

Os dois fatores de câmera são não nulos em toda a linha $s(t)$. Assim, o Lean demonstra igualdade de funções em toda a reta real:

$$
\boxed{\widehat{\mathcal M}_{\mathbf M}(t)=F(t).}
$$

Aqui $F$ é precisamente `completedNativeOperatorCharacteristic`, com a mesma completude usada no autoadjunto. Não é a identificação de $n$ com $\log n$: a variável derivada neste enunciado é a altura $t$, transportada explicitamente por $s(t)$.

A igualdade identifica todas as derivadas e, em particular,

$$
f_n=\frac{F^{(2n)}(0)}{(2n)!}
=\frac{\widehat{\mathcal M}_{\mathbf M}^{(2n)}(0)}{(2n)!}.
$$

As partes reais são as usadas no módulo de coeficientes nativos. Se $\Phi(v)=\sum_n f_n v^n$, a massa formal extraída da combinação é

$$
\mathfrak M_{\rm mixed}(v)=\left(\frac{\Phi(v)}{\Phi(0)}\right)^{-1}.
$$

O teorema anterior `projectiveValveMass_nativeMoments_eq_reciprocal` identifica essa mesma série com a válvula dos momentos nativos. Isso conecta o readout geométrico ao lado escalar da obrigação. Não demonstra que os momentos de um observável positivo escolhido a partir da medida de retorno sejam esses $h_n$.

## 4. Declarações novas e localização

Todas estão em [MixedReturnNativeReadout.lean](../CarrySelfAdjointOperator/MixedReturnNativeReadout.lean), integradas ao import geral e à auditoria de construção de kernels.

| Declaração | Conteúdo verificado |
| --- | --- |
| `mixedReturnCompletedCameraReadout_eq_four_cameras` | Ação literal do raio nas câmeras 2, 3, 4 e 6 |
| `mixedReturn_cameraFactor_identity` | Fator $-4d_2A_3$ calculado das definições |
| `mixedReturnCompletedCameraReadout_eq_nativeScalar` | Readout completo igual ao escalar nativo vestido |
| `mixedReturnCompletedCameraReadout_eq_modalAmplitude` | Realização efetiva da amplitude modal mista |
| `mixedReturnCompletedCameraReadout_cutoff_independent` | Independência dos seis cortes completados |
| `mixedReturnCompletedCameraReadout_normalized_energy` | Normalização exata $8/139$ |
| `mixedReturnCompletedHeightCharacteristic_eq` | Recuperação da característica nativa em toda altura real |
| `iteratedDeriv_mixedReturnCompletedHeightCharacteristic` | Transporte de todas as derivadas |
| `mixedReturnEvenCoefficient_eq_native` | Identificação dos coeficientes pares |
| `mixedReturnReciprocalMass_eq_native` | Identificação da massa formal recíproca |

## 5. Como as peças do atlas entram, e quais entradas ainda exigem prova

| Peça conferida na fonte | O que ela já fornece | Aplicação à obrigação atual |
| --- | --- | --- |
| [CPFormal — StructuralPersistence](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Logic/StructuralPersistence.lean), `RestrictedCodec`, `ReadoutAtlas`, `minimal_view_invariance` | Reconstrução sem perda e transporte de uma leitura comum, com decomposição interior + bordo fornecida | O campo `read_valid` exige a igualdade da leitura escolhida. Para leitura quadrática, precisamos provar a igualdade dessa forma; ela não decorre de identificar somente $F$ |
| [Weyl — GreenCameraCoupling](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/298d83c9351e308a5213b9f5ac32e44087f98a9f/NativeCarrySpectralWeyl/Boundary/GreenCameraCoupling.lean) | Reconstrução a partir do porto externo, bulk e fonte Gamma | Recebe `stateReadout : H →L[ℝ] RealifiedCameraComplexification`; ainda é necessário construir e justificar o mapa específico da realização desejada |
| [C3 — CanonicalNaimarkStateReadout](https://github.com/thiagomassensini/native-carry-c3-crosswalk/blob/150cfc7fb08da96bf8117f15869cc2b819d593c2/NativeCarryC3Crosswalk/CanonicalNaimarkStateReadout.lean) | Readout canônico como adjunto de Naimark composto com uma realização; inversa à esquerda no setor coerente | Requer fornecer `stateRealization` limitada; não constrói automaticamente a realização aritmética com o Gram de altura |
| [CompletedC3ValveGreenNaturality](../CarrySelfAdjointOperator/CompletedC3ValveGreenNaturality.lean) | Ledger, porto, fonte Gamma e par escalar ligados ao mesmo estado estruturado | A existência de duas projeções do mesmo estado está demonstrada; a preservação da forma Green entre elas permanece a condição seguinte |
| [CompletedC3ValveCauchyNaturalityFrontier](../CarrySelfAdjointOperator/CompletedC3ValveCauchyNaturalityFrontier.lean) | Equivalência entre compatibilidade da forma de bordo e scalarização Gamma/Cauchy | A equivalência localiza a igualdade necessária, mas exige prova de um dos lados |
| [Laboratório de colagem pelo mesmo inteiro](../research/geometric-kernel-search-2026-09-04/graph/source_labs/native_carry_residual_native_return_identification_lab.py) | Fórmulas de análises residual e nodal com Gram comum $\operatorname{diag}\rho(n)$; transporte após whitening compatível com $\log n$ | A fonte já estava arquivada na busca de 4 de setembro. A colagem preserva o estado aritmético; ainda precisa transportar a resposta/medida para os momentos de altura |

O laboratório foi relido nesta rodada, sem nova execução numérica. O manifesto anterior registra sua cópia entre as fontes; o resumo das execuções não registra uma execução desse laboratório específico. Portanto não se atribui a ele um novo teste aprovado aqui.

## 6. Correção concreta ao reutilizar a nota

Na seção 5.3 do atlas, a fórmula impressa para a câmera natural par é

$$
1-(b/2)^{-s}-(b-2)b^{-s}.
$$

A [definição consumida de `evenFactor`](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/298d83c9351e308a5213b9f5ac32e44087f98a9f/NativeCarrySpectralWeyl/Camera/Factors.lean) é

$$
\boxed{A_b(s)=1+(b/2)^{-s}-(b+2)b^{-s}\quad(b>2\text{ par}).}
$$

A câmera 2 mantém seu fator excepcional $(1+2^{-s})(1-2^{1-s})$. A nova identidade do modo misto foi provada usando essas definições efetivas. Não se transportou a fórmula antiga silenciosamente nem se alterou o original do atlas.

## 7. A igualdade que falta para fechar o kernel

A origem geométrica do raio e seu readout escalar agora estão conectados. Falta construir, na realização de retorno pertinente e com os bordos correspondentes, uma resposta que satisfaça

$$
\boxed{t\langle u,(I-t^2S^2)^{-1}u\rangle
=-\frac{\widehat{\mathcal M}_{\mathbf M}'(t)}{2\widehat{\mathcal M}_{\mathbf M}(t)}
=-\frac{F'(t)}{2F(t)}.}
$$

Essa é a forma da rota de observável positivo limitado: $S$ simétrico, no domínio local do resolvente e onde $F\ne0$. Uma realização por operador não limitado exige também as condições de domínio correspondentes; não está coberta automaticamente por essa interface.

[PositiveObservableParityKernel](../CarrySelfAdjointOperator/PositiveObservableParityKernel.lean) já constrói, para um $S,u$ fornecido, o estado $(r_t,tSr_t)$, onde $r_t=(I-t^2S^2)^{-1}u$, e prova que seu Gram polarizado é a diferença dividida dessa resposta. Para o certificado estrito, a mesma órbita deve ter independência em todas as ordens.

A obrigação pode ser testada sem divisão: para os momentos geométricos $m_n=\langle u,S^{2n}u\rangle$ e os $f_n$ extraídos acima,

$$
f_0m_n+\sum_{k=0}^{n-1}m_kf_{n-k}+(n+1)f_{n+1}=0\quad\text{para todo }n.
$$

Já em $n=0$, a condição exige $f_0\|u\|^2+f_1=0$, ou seja, a massa da fonte deve ser o momento nativo $h_0$. A normalização do raio de câmeras, sozinha, não fornece essa igualdade.

É exatamente `positiveObservableNativeConvolutionDefect S u n = 0`, em [PositiveObservableNativeMomentBridge](../CarrySelfAdjointOperator/PositiveObservableNativeMomentBridge.lean). O novo módulo identifica os $f_n$ do readout misto; **não afirma essa anulação para os $m_n$ de uma realização de retorno ainda não identificada**.

Para procurar a peça nas notas, os alvos mais específicos agora são: uma fórmula para a resposta resolvente do raio residual após a completude; um transporte de medida que produza a massa $\Phi(0)/\Phi$; ou uma identidade Green bilinear que inclua os fatores $D$, $\gamma$ e seus termos de bordo. A invariância de um observável já identificado pode então ser transportada pelo atlas.

## 8. Validação e continuidade

O build específico e as 14 etapas da auditoria completa passaram com `--wfail`. Os dez teoremas usam somente `propext`, `Classical.choice` e `Quot.sound`. A evidência da auditoria, os teoremas e os axiomas transitivos estão em [verification.json](../research/mixed-return-readout-2026-09-05/verification.json). Não foram introduzidos `sorry`, axiomas de pesquisa, hipóteses de positividade nativa ou ajustes numéricos. Os pins foram preservados.

Continuidade: [fonte de retorno e medida mista](camera-return-defect-source-map.md), [kernel Hilbert R/B](c3-projective-hilbert-readout-kernel.md), [válvula e momentos nativos](ponte-valvula-momentos-nativos.md). O fechamento completo do Gram nativo permanece pendente; esta rodada não deve ser descrita como certificado HP concluído.
