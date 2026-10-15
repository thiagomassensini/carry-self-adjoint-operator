# Mapa de declarações: fonte Carry real → Green → alturas

Snapshot principal: `bde8af97a34923563965128b7748e8ac088d7d9b` (PR #105). Levantamento de 15/10/2026, anterior à nova formalização desta investigação. A validação executável da rodada acompanha a entrega final.

**O bloco de alturas e seu adjunto são construídos sobre Hilbert real. A entrada física canônica ainda exige uma identidade de pareamento. O antigo certificado Taylor complexo não é uma entrada por preencher: sua impossibilidade já foi formalizada. Existe uma interface real corrigida, também já formalizada.**

## Versões e critério dos estados

- Principal: `/home/thlinux/carry-self-adjoint-operator`, `main` no snapshot acima.
- Geometria consultada: `e1084b43533255b399b82dc307b536d7dfdca07f`; pin consumido: `d7cc54f5c485320f1fada33118e9e6101488819a`.
- Primos consultado pelo commit remoto `e2a723b4ec3e645539de0b9ca881951d93259cda`; pin consumido: `65d50f6db1208708e109982ba97e1d51d3039956`. O checkout de pesquisa sujo não foi trocado nem editado.
- Os três arquivos de geometria e os dois arquivos de packaging pedidos são idênticos byte a byte entre essas versões consultadas e os pins consumidos. Isso não afirma identidade de todo o repositório.

`PROVADO` identifica uma declaração existente, com suas hipóteses explícitas; não certifica uma instanciação física omitida. `CONDICIONAL` destaca o elo que recebe uma hipótese física ainda não construída. `NO-GO` refere-se à representação expressamente indicada. `NÃO FORMALIZADO` registra a ligação que não foi localizada nas fontes examinadas, sem alegar inexistência em qualquer arquivo histórico possível.

## Geometria e transporte de coordenadas

| Módulo e declarações | Espaço/dados e conteúdo | Estado |
|---|---|---|
| `RealCriticalDepthState`: `realCriticalDepthState_energy`, `balancedCarryDepth_realState_realizes_formalMass` | Par real com energia explícita `x²+y²`; índices `(b,k,theta)`. Massa de profundidade e amplitude já existentes. O ângulo é livre nessa camada. O produto bruto não é declarado Hilbert pela energia da norma sup. | **PROVADO**. Não identifica `k` com ordem de jet nem o ângulo com relógio espectral. |
| `C2FiberRealDynamics`: `c2FiberRealState_energy`, `c2CenterFiberRealState_succ_eq_fixedStep`, `c2LegFiberRealState_succ_eq_fixedStep_add_logDefect` | Ponto material `2^k*m+epsilon`; rotação por `−t log(ponto)`, amplitude de profundidade. O centro tem passo fixo; as pernas conservam o defeito logarítmico. Positividade de núcleo e ponto é explícita. | **PROVADO**. Trocar o incremento das pernas por `log 2` é refutado pelo exemplo `c2FiberPoint_right_log_increment_lt`. |
| `RealCarryTfvd`: `realCarryTfvdSynthesis_comp_analysis`, `realCriticalCarryTfvdGreenValveCapstone` | `CarryVerticalL2` real → interior + dois dados de bordo → reconstrução. `eta` nasce da amplitude; `0<eta<1`. Gauge preserva o deslocamento de índice do Green. | **PROVADO**. Reconstrução não é uma igualdade com o Gram dos momentos. |
| `CpNativeCarryRealPlaneComplexPackaging`: `nativeCarryRealPlaneComplexPackaging_finiteChartAt`, `normSq_packaged_nativeCarryFiniteSaturatedChart` | Packaging aditivo injetivo do par real em `ℂ`; comuta com a câmera inteira e preserva a energia resultante. | **PROVADO**. A equivalência de kernels de operadores não limitados não faz parte desse teorema. |
| `CpNativeCarryComplexOperatorSameAsReal`: `nativeCarryComplexOperatorBoundaryClosesAt_iff`, `isNativeCarryComplexOperatorZero_iff_real` | Homeomorfismo `ℂ ≃L[ℝ] ℝ×ℝ` transporta o limite de bordo e seu predicado de fechamento. | **PROVADO** como equivalência de predicados de fechamento. O nome “mesmo operador” não fornece sozinho uma conjugação de `LinearPMap` com domínio e adjunto. |
| `RealLinearPMapComplexification`: `RealHilbertComplexification.complexInner_re/im`, `complexification_adjoint_eq_realAdjoint` | Dobra um Hilbert real: `WithLp 2(E×E)`. O pareamento complexo usa a métrica real das duas quadraturas e o cruzamento orientado. Para `T`, domínio natural `D(T)×D(T)`, ação `(Tx,Ty)`. | **PROVADO**. Complexificação fiel posterior, não hipótese de que `E` original já carregue uma estrutura complexa compatível com `T`. |
| `NativeGammaNaimarkComplexProjection`: `nativeComplexNaimarkPort_eq_original`, `nativeComplexNaimarkAdjoint_eq_original`, `nativeComplexNaimark_hilbertAdjoint` | Complexificação coordenada da isometria Naimark real e de seu adjunto; mesmo produto `L²`, sem outra métrica. | **PROVADO**. |
| `NativeGammaSixCameraProjection`: `nativeSixCameraProjection_metricLedger`, `nativeSixCameraExterior_orthogonal` | Projeção sobre as seis câmeras, na métrica original `nativeSixCameraGram`; complemento ortogonal. | **PROVADO**. A comparação literal de cada projeção com seu lifting real deve ser demonstrada, não inferida apenas por igualdade de nomes. |
| `NativeGammaNaimarkHaloEscape`: `nativeComplexGlobalNaimarkEscape_eq_realComplexification`, `nativeGammaSixCameraEscape_pairing` | Escape global já identificado com a complexificação da projeção real. Pareamento do escape finito = halo + escape global, com dois argumentos independentes. | **PROVADO**. |

Fontes dos cinco módulos upstream: [geometria no pin consumido](https://github.com/thiagomassensini/geometry-of-numbers/tree/d7cc54f5c485320f1fada33118e9e6101488819a/GeometryOfNumbers/Analysis) e [Primos no pin consumido](https://github.com/thiagomassensini/primos/tree/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic).

## Fonte completada e três setores

| Declaração existente | Conteúdo e limite | Estado |
|---|---|---|
| `CompletedNativeSourceThreeSectorSewing.nativeNaimarkThreeSector_inner` (namespace `GammaMaterialSewing`) | Polarização completa para vetores ambientes arbitrários, setores observado/halo/escape. | **PROVADO** sobre o Hilbert complexo construído do par real. |
| `nativeCompletedResolvedCorrection_globalEscape`, `nativeCompletedGlobalEscape_fourTerms_zero` | `R=Gamma+Q`, `ER=0`, `EQ=−EGamma`; os quatro pareamentos do escape cancelam. | **PROVADO**. `Q` é a correção resolvida TFVD; não é apenas o termo escalar derivativo do dressing. |
| `nativeCompletedWronskianDefect_eq_twoSectorBoundary` | `D4(z,w)=(w−conj z) K_R(z,w)−W_F(w,z)`; mantém o par completado `(F,−F')`, as hipóteses de strip, os quatro canais e a ordem dos argumentos. | **PROVADO**. `D4=0` não foi concluído. |
| `CompletedNativeChiralReturnGammaCorrectionCancellation.coisometricFourChannelBalance_eq_rawGamma_add_gram_difference` (namespace `ChiralReturn`) | As três correções coisométricas sintetizam a diferença dos Grams; o residual Gamma–Wronskiano permanece assinado. | **PROVADO** em toda família finita, sem estimativa geral de sinal. |
| `CompletedNativeCorrectedMaterialAtlas.canonicalCompletedNativeCorrectedMaterialAtlas_completedWronskianSewing_iff_defect_limit_zero` | Readouts físicos de prefixos, quatro cantos, log-jet e fluxo Green já estão ligados; o fechamento com Wronskiano equivale ao limite zero do defeito nomeado. | **CONDICIONAL** nessa costura final; a equivalência é provada. |
| `hasCorrectedNativeChiralBoundaryTransport_iff_expandedStructuralSignature` | Uma primeira coluna material precisa igualar, em toda ordem `p`, a assinatura estrutural de ordem `p+1`, com cabeça, cauda, completação e correção de carta. | **CONDICIONAL** para uma fonte material efetiva; não identifica profundidade com `p`. |
| `NativeCompletedVectorGreenReadout.parityEnergyVector_readout` | A energia original em qualquer dimensão é o readout fixo de uma resposta vetorial quadrática totalmente cruzada. | **PROVADO** como readout; não é uma norma de síntese linear de jets. |

As fontes principais estão no [PR #105](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/105) e no [snapshot principal](https://github.com/thiagomassensini/carry-self-adjoint-operator/tree/bde8af97a34923563965128b7748e8ac088d7d9b/CarrySelfAdjointOperator).

## Operadores genuinamente reais e seus domínios

| Declarações | Dados e domínios | Estado |
|---|---|---|
| `LinearPMap.realAdjointDomain`, `realAdjoint` | Domínio maximal dos funcionais representáveis. Exige densidade de `D(T)` para unicidade do representante; não exige extensão limitada de `T`. | **PROVADO**, construção real anterior à complexificação. |
| `realOffDiagonal`, `realAdjoint_realOffDiagonal_eq` | `(x,y) ↦ (C y,A x)`, domínio `D(A)×D(C)`. Auto-adjunção exige adjuntos maximais recíprocos e as densidades escritas. | **PROVADO** sob essas hipóteses explícitas. |
| `realReciprocalOffDiagonal`, `realAdjoint_realReciprocalOffDiagonal_eq` | Bloco `(T⁻¹ y,(T*)⁻¹ x)` nos domínios naturais das inversas, isto é, nas imagens correspondentes. Fechamento, densidades e trivialidade do núcleo aparecem explicitamente. | **PROVADO**, independente de um operador complexo prévio. |
| `kernelOrthogonalReduction`, `reducedRealReciprocalOffDiagonalBundle` | Restrição a `(ker T)ᗮ`, com domínio `D(T) ∩ (ker T)ᗮ`. Dá o bloco reduzido sem impor a antiga hipótese de massa zero. | **PROVADO** para `T` real fechado e densidades exigidas. |
| `closedGreenJetEnergyFactor`, `closedGreenJetEnergyAdjointSquare` | Fecha o fator real dos cores pares/ímpares e constrói `B*B`. Core, fecho, domínio e adjunto são distintos. | **CONDICIONAL** à realização real do kernel de momentos e independência global dos dois setores. A construção operatória é provada. |
| `canonicalCompletedGreenJetReducedReciprocalSignedHeightData` | Operador real reduzido autoadjunto após completação automática dos jets. | **CONDICIONAL** a `hrep`, `heven`, `hodd`; não pede o defeito cabeça–cauda do carrier pleno. |
| `complexifiedClosedGreenJetReciprocalSignedHeightOperator` | Dobra o operador real já construído. `mem_..._domain_iff` exige ambas as quadraturas no domínio real. Auto-adjunção complexa transportada com igualdade de domínios. | **PROVADO** como etapa posterior condicional aos mesmos dados reais. |

O bloco par/ímpar `E_even ⊕ E_odd` do operador recíproco não é a duplicação de quadraturas `E ⊕ E`. Não se pode usar automaticamente a rotação `J(x,y)=(-y,x)` entre espaços de paridades diferentes ou assumir que o bloco real já comuta com tal `J`. Para complexificá-lo, dobra-se o **carrier inteiro** do bloco.

## A interface de alturas que pode e a que não pode receber a fonte

`CompletedNativeGreenWeylReducedHeightCertificate` tem quatro campos: momentos logarítmicos, `HasCanonicalCompletedNativeGreenMomentJets`, independência par e independência ímpar. Seu jet é `canonicalCompletedNativeGreenParityJet`, definido por derivadas complexas do ledger normalizado. O construtor real final dessa interface obtém a parte real de um Gram complexo anterior: nessa especialização, trata-se de realificação de jets complexos.

**NO-GO já existente:** `CompletedNativeHPGateAudit.not_completedNativeGreenWeylReducedHeightCertificate` prova a negação desse certificado, para todo `xiState` e toda sequência de momentos. O motivo é `canonicalCompletedNativeGreenParityJet_firstOdd_eq_zero`, incompatível com a independência ímpar. Reempacotar isometricamente os mesmos jets não resolve esse zero. Não vamos tentar preencher essa interface refutada.

**Interface real corrigida já existente:** `CompletedNativeRealHPCarrierCertificate jet`, em `CompletedNativeHPGateAudit.lean`, pede o Gram real canônico e as independências. Seu `toReducedMaximalSelfAdjointHeightData` usa o mesmo construtor real de alturas já existente. `CanonicalCompletedNativeRealTfvdGreenMomentTransport` e `completedNativeRealHPCarrierCertificate_of_centerLegReadout` conectam o carrier TFVD infinito a essa interface, se o pareamento físico centro–pernas for demonstrado. A rota é condicional nessa identificação; não substitui o operador por outro.

Fonte: [CompletedNativeHPGateAudit.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/bde8af97a34923563965128b7748e8ac088d7d9b/CarrySelfAdjointOperator/CompletedNativeHPGateAudit.lean). O arquivo contém matemática pública, além de comandos de auditoria; excluir arquivos `*Audit*` de uma busca esconderia essa peça.

## Calibração e primeira identidade que falta

As fontes já registram os testes que a ligação deve passar:

\[
g(v_{e0},v_{e0})=h_0,\quad
g(v_{e0},v_{o0})=0,\quad
g(v_{e1},v_{e0})=h_1,\quad
g(v_{o0},v_{o0})=h_1.
\]

As identidades correspondentes de defeito estão em `CompletedNativeTfvdSixSourceCenterLegBridge`: `..._even_zero_even_zero`, `..._even_zero_odd_zero`, `..._even_one_even_zero`, `..._odd_zero_odd_zero`. O jet projetivo bruto falha já na ordem zero (`...Defect_evenZero_ne_zero`); o jet Taylor complexo radial falha no primeiro ímpar, com norma zero e `h1>0`. São **NO-GOs desses candidatos**, não da teoria inteira.

Para o candidato ambiente `R` do PR #105, escrevendo `a+ib=w−conj z`, `g=Re K_R` e `omega=Im K_R`, a comparação correta tem duas equações simultâneas:

\[
\operatorname{Re}D_4=ag-b\omega-\operatorname{Re}W_F,\qquad
\operatorname{Im}D_4=a\omega+bg-\operatorname{Im}W_F.
\]

A apresentação real pode conservar essas duas equações; ela não as torna zero. A calibração central exige os limites/derivadas e normalizações apropriados. Não se obtém `h0` dividindo pela separação na diagonal.

**Primeira costura ainda não localizada como teorema efetivo da fonte física:** construir o transporte da síntese posicional completa para os jets TFVD/Green corretos e provar seu pareamento polarizado normalizado em dois argumentos, com cabeça, cauda, conexão e os dois cruzamentos. Na interface existente, é a identificação de readout `HasCanonicalCompletedNativeTfvdGreenCenterLegReadout` para uma família efetivamente derivada dessa fonte, ou um kernel normalizado e um transporte de incidência para os mesmos vetores-limite. As identidades escalares de readout e a reconstrução TFVD não fornecem esse pareamento por si.

**NÃO FORMALIZADO nesta etapa do levantamento:** essa instanciação física sem defeito, sua compatibilidade dinâmica e o vínculo de domínio entre o estado físico e os jets corretos. A maquinaria de adjunto e do operador real vem depois dessa ligação e já tem construtores para recebê-la.
