# Mapa — kernel Hilbert R/B e readout completado nativo

Rodada de 2026-09-05. Base de trabalho: `643b917046891f9a119b2e05bd2ecb197bc4bce2`, no branch `agent/projective-valve-moment-frontier`.

## Resultado da tentativa

Integramos a realização Hilbert R/B das notas e construímos, em Lean, duas saídas com proveniência explícita: o **kernel positivo do estado ponderado reconstruído** e o **readout escalar com cabeça, cauda exata, fator da câmera e completion**. O readout recupera a característica nativa e sua massa recíproca em todas as ordens.

A igualdade entre a energia dessa realização e o kernel dos momentos nativos permanece aberta. Um teste exato demonstra que a métrica transportada do estado original, sem construir um estado de resposta, tem massa central diferente da exigida. O teste delimita esse candidato específico; não exclui a construção de outros observáveis ou fontes a partir do ledger completo.

## 1. Peças recuperadas das notas

Os três fontes estavam arquivados em `research/hp-notes-audit-2026-09-04/original-lean/`, já recompilados na rodada anterior. Agora fazem parte do import geral e da auditoria de axiomas.

| Fonte integrado | Teoremas | Peça disponível |
| --- | ---: | --- |
| [FiniteCanonicalCameraReadout](../CarrySelfAdjointOperator/FiniteCanonicalCameraReadout.lean) | 4 | Readout canônico $R=G^{-1/2}C$, síntese $R^T$ e coisometria |
| [FiniteEnrichedCameraState](../CarrySelfAdjointOperator/FiniteEnrichedCameraState.lean) | 8 | Setor complementar $B=I-R^TR$, Parseval enriquecido e decomposição Green |
| [C3ProjectiveHilbertRBBridge](../CarrySelfAdjointOperator/C3ProjectiveHilbertRBBridge.lean) | 20 | Recuperação Hilbert, produto interno transportado, reconstrução R/B real e imaginária, compatibilidade total entre cortes |

Foram preservados os corpos das provas. A integração qualifica imports, transfere `#print axioms` à auditoria e remove uma instância implícita não utilizada em três assinaturas por meio de `omit [DecidableEq state] in`. Os originais continuam preservados byte a byte.

A identidade finita é

$$
R^TR+B^TB=I.
$$

Ela conserva todos os cruzamentos por polarização. A compatibilidade entre cortes demonstrada no terceiro arquivo é a da **reconstrução total** dos dois setores. Não afirma que as projeções visível e cega, consideradas separadamente, comutem com cada restrição.

## 2. Kernel construído no Hilbert completado

Para $0<q<1$ fixo, o estado usado pelo fonte é

$$
x_{q,t}(n)=q^n(n+1)^{-1/2-it},\qquad n\ge0.
$$

O índice e o peso são os de `nativeCarryWeightedRealSpectralState`; a expressão não identifica por convenção profundidade, $\log n$, altura e variável projetiva. A recuperação TFVD $\mathcal R_q$ é inversa à esquerda da análise projetiva $\mathcal A_q$. A métrica transportada dá

$$
K_q(t,u)
=\langle\mathcal R_q\mathcal A_qx_{q,t},
         \mathcal R_q\mathcal A_qx_{q,u}\rangle
=\langle x_{q,t},x_{q,u}\rangle.
$$

O novo [C3ProjectiveHilbertReadoutKernel](../CarrySelfAdjointOperator/C3ProjectiveHilbertReadoutKernel.lean) demonstra:

| Declaração | Resultado verificado |
| --- | --- |
| `completedProjectiveHilbertKernel_eq_inner` | Igualdade complexa completa, incluindo os produtos cruzados |
| `completedProjectiveHilbertKernel_finiteSection_posSemidef` | Cada seção finita é positiva semidefinida |
| `finiteWeightedState_inner_tendsto_completedProjectiveHilbertKernel` | Os produtos internos dos estados truncados convergem para o kernel completado |
| `one_le_norm_nativeCarryWeightedRealSpectralState` | A semente inicial de módulo um permanece no estado |
| `one_le_completedProjectiveHilbertKernel_diagonal` | $\operatorname{Re}K_q(t,t)\ge1$ |
| `completedProjectiveHilbertKernel_zero_ne_nativeMoment` | $\operatorname{Re}K_q(0,0)\ne h_0$ |

O limite é em $M\to\infty$, com $q$ fixo. Não é um resultado de limite $q\to1$. A positividade demonstrada aqui é semidefinida; independência de jets em todas as ordens precisa ser provada na realização que efetivamente identificar os momentos.

## 3. Do estado reconstruído à massa nativa

Denote por $O_{q,M}$ o `carryWeightedFiniteChartObserver`, que desfaz o peso nos índices finitos apropriados. O novo readout é

$$
F_{q,M}(t)=\Gamma_{\rm nat}(t)
\frac{
 O_{q,M}(\mathcal R_q\mathcal A_q x_{q,t}^{(M)})
 +T_{3,M}(\tfrac12+it)
}{c_3(\tfrac12+it)}.
$$

Aqui $\Gamma_{\rm nat}$ designa o fator completo `nativeXiCompletionFactor`, incluindo seus prefatores; $T_{3,M}$ é `realCpBracketCutoffTail`, e $c_3$ é `cpChartFactor`. O uso dessa cauda corresponde exatamente à cabeça produzida pelo observador.

**A cauda analítica é um termo explícito adicional do readout.** A prova não diz que uma janela finita, isolada, determina a cauda, nem que esse readout seja um funcional linear uniformemente limitado no Hilbert. De fato, os mapas crus de desponderação $x\mapsto q^{-n}x_n$ não têm uma cota uniforme em $n$ sobre todo o espaço $\ell^2$, conforme o teorema específico recuperado.

A cadeia provada, para todo $M$ e todo $t$ real, é

$$
F_{q,M}(t)=F(t),\qquad
\partial_t^rF_{q,M}(t)=F^{(r)}(t).
$$

Escrevendo formalmente $F(t)=\Phi(t^2)$ e extraindo os coeficientes pares **dessa fórmula de readout**, obtemos

$$
A_{q,M}(v)
=\left(\frac{\Phi(v)}{\Phi(0)}\right)^{-1}
=\operatorname{Valve}\!\left(\sum_{n\ge0}h_nv^n\right).
$$

Essa igualdade de massas é de séries formais. A definição de `completedProjectiveStateReciprocalMass` usa os coeficientes do readout; não usa os $h_n$ para definir a massa. A identificação posterior reutiliza a [ponte da válvula nativa](ponte-valvula-momentos-nativos.md).

| Declaração | Localização do passo |
| --- | --- |
| `completedProjectiveStateCharacteristic_eq` | Cabeça + cauda + câmera + completion = característica nativa |
| `iteratedDeriv_completedProjectiveStateCharacteristic` | Jets de todas as ordens, com a inclusão real–complexa explícita |
| `completedProjectiveStateEvenCoefficient_eq_native` | Coeficientes pares iguais aos nativos |
| `completedProjectiveStateReciprocalMass_eq_native` | Massa do readout = $\widehat\Phi^{-1}$ |
| `completedProjectiveStateReciprocalMass_eq_valveNativeMoments` | Massa do readout = válvula dos momentos nativos |

A fórmula escalar vale até para cortes pequenos porque inclui a cauda exata. Para argumentos com incidências finitas, continua valendo a geometria dos centros: `canonicalC3_geometricallyCompleteCutoff_iff` exige $M\ge1$ e horizonte $N\ge3M+1$; dois centros completos são realizados por $M=2,N=7$. Ver [calibração dos cortes](../CarrySelfAdjointOperator/CompletedC3GeometricCutoffCalibration.lean).

## 4. Resultado do teste e obrigação restante

Para $a(t)=-F'(t)/(2F(t))$, o kernel procurado deve satisfazer

$$
\langle\widehat\Psi(x),\widehat\Psi(z)\rangle
=\frac{a(z)-a(x)}{z-x},
\qquad K(0,0)=a'(0)=h_0.
$$

O estado original tem $x_{q,0}(0)=1$. O Lean já prova $h_0<1/16$. Portanto,

$$
\operatorname{Re}K_q(0,0)\ge1>\frac1{16}>h_0.
$$

Isso impede usar **esse kernel transportado sem modificação** como a identidade procurada. Não é uma conclusão sobre todas as métricas ou todos os estados de resposta. Uma normalização que acerte somente o centro também não demonstra as identidades em ordens superiores.

A rota do observável positivo agora tem uma interface Lean diretamente ligada ao readout acima. Para um operador real limitado simétrico $S$ e uma fonte $u$, coloque

$$
m_n=\langle u,S^{2n}u\rangle=\|S^nu\|^2.
$$

As obrigações concretas são construir $S,u$ a partir da geometria completa e provar

$$
\boxed{\operatorname{Valve}\!\left(\sum_{n\ge0}m_nv^n\right)=A_{q,M}(v)},
\qquad \{S^nu:n\ge0\}\text{ linearmente independente}.
$$

`positiveObservable_isNativeMomentSequence_iff_completedProjectiveReadoutMass` demonstra que a igualdade da caixa equivale à obrigação dos momentos nativos. `completedNativeRealHPCarrierCertificate_of_positiveObservable_readoutMass` entrega o certificado quando recebe essa igualdade, a simetria e a independência. **São pontes condicionais; a rodada não construiu um par que satisfaça essas entradas.**

O estado de resposta suficiente já tem uma fórmula testada em Lean em [PositiveObservableParityKernel](../CarrySelfAdjointOperator/PositiveObservableParityKernel.lean):

$$
r_t=(I-t^2S^2)^{-1}u,\qquad
\widehat\Psi(t)=(r_t,tSr_t).
$$

Seu produto interno é a diferença dividida do readout $t\langle u,r_t\rangle$ no domínio do resolvente. A identificação desse readout com $a(t)$ deve respeitar esse domínio e as condições analíticas; a igualdade formal não é uma avaliação automática em toda a reta.

## 5. Próxima localização da busca

| Trabalho | Fontes úteis | O que conferir |
| --- | --- | --- |
| Construir a fonte e o observável de resposta | [CarryTfvdTraceMetricKernel](../CarrySelfAdjointOperator/CarryTfvdTraceMetricKernel.lean), [ReturnMetricPolarizedKernel](../CarrySelfAdjointOperator/ReturnMetricPolarizedKernel.lean) | Energia de retorno e identificação do readout completo, conservando os cruzamentos |
| Passar da cabeça escalar à forma Green | `NativeCarryC3Crosswalk/FiniteChartGreenTransport.lean`, no pin consumido | A identidade contém o fluxo Green acoplado; converter readouts exige acompanhar esse termo |
| Manter Gamma, pares e bordos no mesmo estado | [CompletedC3ValveGreenNaturality](../CarrySelfAdjointOperator/CompletedC3ValveGreenNaturality.lean), [CompletedC3ValveCauchyNaturalityFrontier](../CarrySelfAdjointOperator/CompletedC3ValveCauchyNaturalityFrontier.lean) | Compatibilidade da forma Green com a energia da realização escolhida |
| Testar a igualdade da caixa sem divisão | [PositiveObservableNativeMomentBridge](../CarrySelfAdjointOperator/PositiveObservableNativeMomentBridge.lean) | Anulação de `positiveObservableNativeConvolutionDefect S u n` para todo $n$ |
| Obter os dois Grams estritos | Mesmo módulo e incidências BR2 | Independência transportada para a própria órbita que identifica os momentos |

O readout linear da cabeça não foi substituído pela forma Green bilinear. A identidade de `FiniteChartGreenTransport` tem o formato cabeça + fluxo acoplado = forma Green + bordo; a cauda deve ser acrescentada aos termos correspondentes. Essa é uma localização concreta para continuar a busca, preservando as correções.

## 6. Verificação reproduzível

São 32 teoremas recuperados e 13 novos no módulo de kernel/readout, incluindo as duas pontes condicionais. Todos estão em `KernelConstructionAudit`. Os comandos de verificação são:

```bash
lake build --wfail CarrySelfAdjointOperator.C3ProjectiveHilbertReadoutKernel
bash scripts/audit.sh
```

O build específico e as 14 etapas de `scripts/audit.sh` passaram com `--wfail`. As 45 declarações usam apenas `propext`, `Classical.choice` e `Quot.sound`. O resultado de cada etapa, os hashes, as declarações e os axiomas transitivos estão na [evidência desta rodada](../research/projective-hilbert-readout-2026-09-05/verification.json). O log completo fica arquivado junto dela. Os pins das dependências foram mantidos. Não foram usados zeros conhecidos nem ajuste numérico; o teste do candidato é uma desigualdade provada em Lean.

Continuidade: [mapa das notas HP](mapa-notas-hp-jets-retorno-atualizado.md), [ponte da válvula](ponte-valvula-momentos-nativos.md), [busca geométrica anterior](identificacao-geometrica-kernel-carry.md).

## Pista adicional de 2026-09-05: retorno universal

O grep das notas levou ao [defeito de retorno e fonte geométrica](camera-return-defect-source-map.md). A nova fatorização Lean prova que o complemento da variância de câmeras é um quadrado positivo; o resíduo da câmera 6 fornece uma direção explícita de fonte. O mapa registra as transpostas, a medida do modo misto e a distinção entre selecionar essa fonte e identificar o Gram nativo.
