# Costura retorno–Gamma: fonte exata e primeiro termo residual

Data: 2026-09-05. Repositório: `thiagomassensini/carry-self-adjoint-operator`.
Base exata: `225a85d9e8e3e0a3b659c5b6ad821458770b3195`.
Branch: `agent/return-gamma-source-sewing`.

> Continuação: o [teste da câmera 5 sobre o Gamma completo](c3-gamma-camera-five-trace-no-go.md) prova que o defeito bruto é não nulo perto do centro e nega a scalarization canônica. O texto abaixo conserva o estado da investigação na base desta primeira redução.

**Resultado: identificação da fonte e redução exata formalizadas; sewing Gamma–Wronskiano aberto.** A projeção mista do source existente não é o readout misto do vetor de resultantes da nota dinâmica. O complemento do próprio source fornece um testemunho não nulo de bordo invisível ao readout misto. Isso exclui uma fatoração universal do bordo apenas por esse readout; não exclui uma compensação dos cruzamentos na família canônica.

Nenhum operador, Gamma, Jacobi ou momento nativo foi reconstruído. Nenhum pin foi alterado. Não se assumiu positividade nativa, RH, zeros, alturas espectrais ou Herglotz. A variável `operatorHeightParameter z` aparece por sua definição existente; não se introduziu uma identificação entre altura e resolvente.

## 1. Arquivos e proveniência

| Arquivo | Papel nesta rodada |
|---|---|
| [C3MixedReturnSourceTrace.lean](../CarrySelfAdjointOperator/C3MixedReturnSourceTrace.lean) | Novo: 9 teoremas, normalização intrínseca e projeção exata do source |
| [C3MixedReturnTraceObstruction.lean](../CarrySelfAdjointOperator/C3MixedReturnTraceObstruction.lean) | Novo: 18 teoremas, diferença explícita, complemento não nulo, testemunho de bordo e redução do sewing |
| [MixedReturnNativeReadout.lean](../CarrySelfAdjointOperator/MixedReturnNativeReadout.lean) | Reutilizado **sem alteração** do commit `6468bbede9e1ffcd4f4a1fb260b55ec970968077`: 10 teoremas já existentes sobre as resultantes completadas |
| [CarrySelfAdjointOperator.lean](../CarrySelfAdjointOperator.lean) | Importa os três módulos |
| [KernelConstructionAudit.lean](../CarrySelfAdjointOperator/KernelConstructionAudit.lean) | Imprime os axiomas das 27 provas novas e das 10 reutilizadas |
| [Audit.lean](../CarrySelfAdjointOperator/Audit.lean) | Inclui as três conclusões centrais no audit geral |

Os 27 arquivos preexistentes consultados na base, seus hashes e o módulo reutilizado estão em [source-provenance.json](../research/return-gamma-source-sewing-2026-09-05/source-provenance.json). As notas guiam a investigação; nenhuma derivação da nota foi importada como hipótese Lean.

## 2. Etapa A — origem → mapa → destino

As seis câmeras estão ordenadas por **rótulos 2, 3, 4, 5, 6, 7**. Portanto câmera 6 é o índice `4 : Fin 6`, não a última coordenada.

O source existente embala coeficientes do porto Green:

$$
c=(a_0,a_1,a_2,b_0,b_1,b_2),\qquad
\operatorname{source}(c)=\operatorname{cameraEmbedding}(c)
$$

em dois canais reais, para as partes real e imaginária. A fidelidade desse empacotamento já está provada em `canonicalC3SixCameraSourceMap_injective`.

A ponte preexistente encontrada é:

```lean
canonicalCompletedOperatorC3State_eq_greenBoundaryPair
finiteC3GenuineBracketGreenBoundaryPair_snd_apply
```

Ela identifica a segunda perna com `positiveDirichletGradient s n`. É a perna horizontal Green; não se deve renomeá-la como o vetor de resultantes nem como o readout log-jet. O transporte enriquecido contém também readouts de valor/log-jet e dados de bordo em campos próprios; a função que constrói este source seleciona seu `.greenPort`.

A normalização é determinada pela métrica existente:

$$
v=(-6,-3,2,0,3,0),\quad Gv=\frac{278}{3}e_{\text{câmera }6},
\quad v^TGv=278,\quad p=\frac{\operatorname{cameraEmbedding}(v)}{\sqrt{278}}.
$$

Os novos `sixCameraReturnVector_norm_sq` e `sixCameraReturnUnitVector_norm_sq` verificam no `CameraHilbert` os valores 278 e 1. O cálculo usa o `gramKernel` efetivo de `cameraEmbedding`, conectando os rótulos da fonte à métrica; não é uma calibração de energia.

O teorema `sixCameraReturnReadout_sourceMap` prova, para todo porto:

$$
\mathcal R(\operatorname{source}(c))=\frac{v^TGc}{\sqrt{278}}
=\frac{\sqrt{278}}{3}b_1.
$$

Consequentemente, `sixCameraReturnReadout_canonicalSource_eq_powers` prova exatamente:

$$
\boxed{\mathcal R(\operatorname{canonicalSource}(z))
=\frac{\sqrt{278}}{3}\left(3^{-s(z)}-2^{-s(z)}\right).}
$$

### Por que isso difere da nota dinâmica

No whitening, **coeficientes** embutidos no Hilbert correspondem a $G^{1/2}c$. As **resultantes** $\chi$ da nota correspondem a $G^{-1/2}\chi$. Com $p_*=G^{1/2}v/\sqrt{278}$, os respectivos readouts são $v^TGc/\sqrt{278}$ e $v^T\chi/\sqrt{278}$. Identificá-los exigiria provar a relação apropriada entre $Gc$ e $\chi$.

A identidade já formalizada e reutilizada para as resultantes é:

```lean
mixedReturnCompletedCameraReadout_eq_nativeScalar
```

Ela preserva o head+tail de cada câmera, com cutoffs independentes, e dá

$$
\frac{v^T\chi(s)}{\sqrt{278}}
=-\frac4{\sqrt{278}}(1-2^{1-s})(1-3^{1-s})Z_{\rm nat}(s).
$$

O novo `canonicalC3ReturnReadout_sub_dynamicAmplitude` calcula a diferença entre esses dois objetos:

$$
\frac{\sqrt{278}}3(3^{-s}-2^{-s})
+\frac4{\sqrt{278}}(1-2^{1-s})(1-3^{1-s})Z_{\rm nat}(s).
$$

Há um testemunho exato em `canonicalC3ReturnReadout_ne_dynamic_at_zeroExponent`: para $z=i/2$, $s(z)=0$, a projeção do source é zero e a combinação completada de câmeras é $4/\sqrt{278}\ne0$. **Esse ponto está no domínio escalar nativo, na borda da faixa Genuine mais estreita.** Não é apresentado como um contraexemplo situado no interior dessa faixa.

A identificação da característica vestida também já existe no módulo reutilizado:

```lean
mixedReturnCompletedCameraReadout_eq_nativeScalar
  → mixedReturnCompletedHeightCharacteristic_eq
  → iteratedDeriv_mixedReturnCompletedHeightCharacteristic
  → mixedReturnEvenCoefficient_eq_native
  → mixedReturnReciprocalMass_eq_native
```

Ela divide pelo fator de câmera provadamente não nulo na linha crítica e aplica `nativeXiCompletionFactor`. Não renomeia `nativeScalar` como a característica completada e não identifica seus Grams.

## 3. Etapa B — complemento concreto que sobrevive no bordo

A componente na direção de retorno, com a projeção determinada por $G$, é:

$$
Pc=(-2b_1,-b_1,\tfrac23b_1,0,b_1,0).
$$

`sixCameraMixedReturnPortPart_sourceMap` a identifica com $(b_1/3)v$ nos dois canais reais. O complemento inteiro é mantido:

$$
c-Pc=(a_0+2b_1,a_1+b_1,a_2-\tfrac23b_1,b_0,0,b_2).
$$

`sixCameraReturnReadout_portRemainder` prova que seu readout misto é zero. A ligação com o novo defeito de retorno usa a orientação **GT−H**:

```lean
sixCameraSlopeDefect_mulVec
sixCameraReturnCompression_annihilates_cameraSixZero
```

O primeiro mostra que $(GT-H)c$ depende somente da coordenada da câmera 6. O segundo prova

$$
c_4=0\ \Longrightarrow\ A G^{1/2}c=0,
\qquad A=G^{-1/2}(H-GT)G^{-1/2}.
$$

Assim, o complemento fica invisível também ao quadrado de retorno $A^*A$ em coordenadas whitened. Não houve troca de GT−H por TG−H.

O primeiro termo explícito que permanece no complemento é:

```lean
canonicalC3ReturnPortRemainder_cameraFive
```

$$
\boxed{(c(z)-Pc(z))_{\text{câmera }5}
=\operatorname{positiveDirichletGradient}(s(z),0)=2^{-s(z)}-1.}
$$

A cadeia efetivamente usada para seu bordo não nulo é:

```text
positiveDirichletGradient_ne_zero_of_mem_genuineCriticalStrip
  → canonicalC3SixCameraSourceMap_injective
  → canonicalC3ReturnSourceRemainder_ne_zero
  → carryGammaSource_injective
  → canonicalC3ReturnGammaRemainder_energy_pos
  → carryGammaPolarizedBoundaryReadout_diagonal_eq_norm_sq
  → canonicalC3ReturnRemainder_boundary_ne_zero
  → not_gammaBoundary_factors_through_sixCameraReturnReadout
```

O último teorema tem escopo preciso: para `hz : z.im ≠ 0` e `hs : operatorHeightParameter z ∈ genuineCriticalStrip`, **não existe** função $B:\mathbb C\to\mathbb C$ que recupere, para **todas** as fontes do Gamma existente, seu bordo diagonal a partir apenas de `sixCameraReturnReadout`. Os testemunhos são o complemento do próprio source canônico e a fonte zero. Têm o mesmo readout misto e bordos diferentes.

Isto é uma obstrução à perda desse complemento. Não é um teorema de impossibilidade do sewing na família canônica, nem um argumento que confunda posto nas câmeras com dimensão de uma órbita na dilatação.

## 4. Menor igualdade residual desta decomposição

Escreva $m_z=\Gamma(z)\operatorname{source}(Pc(z))$ e $r_z=\Gamma(z)\operatorname{source}(c(z)-Pc(z))$, usando o **mesmo** `carryGammaComplexState`. A soma é o Gamma canônico por `canonicalC3GammaState_eq_returnPart_add_remainder`.

A cadeia algébrica usada é:

```text
canonicalCompletedC3Source_eq_returnPart_add_remainder
  → map_add do carryGammaSource
  → canonicalC3GammaState_eq_returnPart_add_remainder
  + canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel
  + inner_add_left / inner_add_right
  → canonicalC3RawGammaWronskianDefect_eq_returnFourTerms
  → canonicalC3RawGammaWronskianDefect_eq_zero_iff_returnBalance
```

O último teorema é a redução exata do defeito já nomeado, sem divisão por $F$. O goal seguinte foi emitido pelo Lean e está copiado literalmente de [residual-goal.txt](../research/return-gamma-source-sewing-2026-09-05/residual-goal.txt):

```text
z w : ℂ
hz : z.im ≠ 0
hw : w.im ≠ 0
mZ : CarryGammaComplexNaimark := carryGammaComplexState z hz (canonicalC3ReturnSourcePart z)
mW : CarryGammaComplexNaimark := carryGammaComplexState w hw (canonicalC3ReturnSourcePart w)
rZ : CarryGammaComplexNaimark := carryGammaComplexState z hz (canonicalC3ReturnSourceRemainder z)
rW : CarryGammaComplexNaimark := carryGammaComplexState w hw (canonicalC3ReturnSourceRemainder w)
⊢ (w - (starRingEnd ℂ) z) * (⟪mZ, rW⟫_ℂ + ⟪rZ, mW⟫_ℂ + ⟪rZ, rW⟫_ℂ) =
    completedGreenWronskian completedNativeOperatorCharacteristic completedNativeOperatorBoundaryCompanion w z -
      (w - (starRingEnd ℂ) z) * ⟪mZ, mW⟫_ℂ
```

O diagnóstico é um `example` intencionalmente incompleto executado fora do projeto; seu texto está arquivado como `.lean.txt`. Não integra o build. Não se adicionou hipótese circular, nova estrutura de certificado ou prova fictícia desse goal.

A norma positiva de $r_z$ não determina os dois cruzamentos. É exatamente sua compensação com o Wronskiano que permanece por provar. Os lemas do right inverse já existentes continuam válidos; eles não fornecem automaticamente essa compatibilidade de trace.

## 5. Endpoint existente preservado

Se o goal acima for provado no domínio exigido pela costura, a continuação usa diretamente:

```text
canonicalCompletedC3NormalizedPolarizedGammaKernel_eq_dslope_iff_rawWronskian
  + canonicalCompletedC3NormalizedPolarizedGammaKernel_posSemidef
  + canonicalCompletedC3AllCutoffRealKernelReadout_eq_dslope
  + canonicalCompletedC3AllCutoffRealAxisKernelForwardDifference_tendsto_moment
  + canonicalCompletedC3AllCutoffRealAxisKernelParityForwardDifference_tendsto
```

com as condições de domínio e não anulação já declaradas nesses teoremas, e as pontes existentes até `HasCompletedNativeRealAxisNormalizedGreenKernel` e `completedNativeRealHPCarrierCertificate_of_concreteC3Sewing` / `completedNativeRealHPCarrierCertificate_of_concreteC3Kernel`. Essa cadeia **não foi aplicada como se o sewing estivesse fechado**. O certificado e a equivalência espectral posterior não foram reconstruídos.

## 6. Verificação e limites

Os comandos, a contagem de estágios, os hashes e a saída de axiomas estão em [verification.json](../research/return-gamma-source-sewing-2026-09-05/verification.json) e [new-theorem-axioms.txt](../research/return-gamma-source-sewing-2026-09-05/new-theorem-axioms.txt).

As únicas condições das conclusões centrais são as condições de domínio existentes (`hz`, `hw`, faixa Genuine ou domínio escalar quando aplicável). Nenhuma nova hipótese matemática foi usada para a identificação, o testemunho ou a redução. A igualdade residual não foi assumida.

As notas prioritárias utilizadas foram os mapas de retorno e Hilbert/RB, a nota dinâmica, a nota Weyl de retorno, a identidade Green–Gamma de duas variáveis, o crosswalk C3 de todas as ordens, o fechamento analítico C3, a nota de escape dos stencils, o estado enriquecido/Parseval e o atlas relacional. Os caminhos e hashes locais estão no arquivo de proveniência das notas. Cópias com sufixos diferentes foram tratadas como versões a identificar, não como teoremas adicionais.

Esta rodada entrega a **redução exata com testemunho**, sem merge: a identificação Gamma/native Gram permanece aberta.
