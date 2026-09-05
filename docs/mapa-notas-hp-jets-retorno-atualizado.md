# Mapa das notas HP: jets completos, métrica de retorno e identificação nativa

Data da conferência: 2026-09-04. Repositório de trabalho: `carry-self-adjoint-operator`, branch `agent/projective-valve-moment-frontier`, base `62f69205a5f80554d576b4969d658674c670efc4`. Este documento complementa os seis mapas anteriores; os rótulos de situação nas notas antigas não foram tomados como conclusões atuais.

## 1. Resultado e alcance

As notas contêm peças úteis **e provas Lean locais que ainda não estavam integradas ao autoadjunto**. Recuperamos `C3ProjectiveCompletedJetBridge.lean`: oito teoremas existentes, com os corpos das provas preservados, agora importados e incluídos na auditoria de axiomas. O módulo liga os estados finitos ponderados ao estado infinito comum e registra a invariância de jets/readouts C3 completados.

Os nove fontes Lean encontrados em `Downloads/hp` recompilaram com Lean 4.32.0 e as dependências fixadas pelo projeto. Dois avisos de variáveis de seção não utilizadas permanecem no arquivo histórico `FiniteEnrichedCameraState`; não são falhas de prova. O último fonte precisou apenas compilar sua dependência `GreenCameraCoupling`. Os antigos arquivos `.olean` não foram usados como evidência.

Cobertura: inventário dos 64 arquivos diretos; 21 Markdown, dos quais um backup e 20 notas distintas; leitura detalhada das duas notas solicitadas e leitura temática das demais, sem alegar auditoria linha a linha de toda a pasta. Foram comparados fontes das dependências consumidas, o branch de trabalho e sete snapshots de `origin/main`. Os originais em Downloads foram preservados.

**A identificação final da energia geométrica com os momentos da log derivada continua sem prova nesta auditoria.** Há resultados atuais que substituem pendências antigas sobre completion, passagem ao limite ponderada, jets, polarização e construção condicional do operador infinito.

Evidências: [inventário com hashes](../research/hp-notes-audit-2026-09-04/hp-inventory.json), [compilações dos nove fontes](../research/hp-notes-audit-2026-09-04/local-lean-checks.json), [snapshots consultados](../research/hp-notes-audit-2026-09-04/snapshots.json), [reprodução](../research/hp-notes-audit-2026-09-04/README.md).

[Índice de declarações com arquivo e linha](../research/hp-notes-audit-2026-09-04/declaration-index.md).

## 2. Peça recuperada: completar antes de identificar a métrica

Fonte integrado: [C3ProjectiveCompletedJetBridge.lean](../CarrySelfAdjointOperator/C3ProjectiveCompletedJetBridge.lean). [Original arquivado](../research/hp-notes-audit-2026-09-04/original-lean/C3ProjectiveCompletedJetBridge.lean).

| Declaração | Conteúdo exato | Uso e condição |
| --- | --- | --- |
| `nativeGpreFiniteWeightedRealSpectralState_eq_partialSum` | Estado finito = soma dos vetores coordenados com índice menor que `3*M+1` | Mesmo estado, mesmo peso; `0 ≤ q < 1` |
| `nativeGpreFiniteWeightedRealSpectralState_tendsto` | Convergência forte em `ℓ²` para o estado ponderado sem cutoff | `q` fixo; não é um teorema de limite `q → 1` |
| `nativeGpreTfvdProjectiveAnalysis_finiteWeightedState_tendsto` | Continuidade transporta a convergência pela análise TFVD/proveniência | Limite na topologia da família projetiva |
| `nativeGpreTfvdProjectiveAnalysis_completedState_compatible` | Família completada é compatível em todos os atlas finitos | Fornece um estado comum às câmeras |
| `c3CompletedIteratedJet_eq` | Derivada de ordem `r` da cabeça + derivada da cauda = derivada do bracket completo | Dentro de `bracketDomain` |
| `c3CompletedIteratedJet_cutoff_invariant` | Jets completos independem de `M` | Toda ordem `r` |
| `finiteC3CanonicalEnrichedTfvdPairTailReadout_cutoff_invariant` | Invariância do readout enriquecido com cauda | Hipóteses de peso, chart e domínio explícitas |
| `finiteC3EnrichedTfvdPairTailDefect_cutoff_invariant` | Invariância do defeito TFVD/Green completado | Preserva os canais tipados; não descarta o bordo |

As quatro primeiras declarações estão em `CPFormal.Analytic.Cp`; as quatro últimas em `NativeCarryC3Crosswalk`.

O arquivo recuperado **não identifica literalmente a projeção Hilbert cega com a cauda escalar**. Essas operações têm tipos diferentes. A ponte passa pelo estado reconstruído comum e pelos readouts demonstrados.

### Outros fontes locais verificados

| Fonte arquivado | Peça disponível | O que a declaração ainda recebe |
| --- | --- | --- |
| [FiniteCanonicalCameraReadout](../research/hp-notes-audit-2026-09-04/original-lean/FiniteCanonicalCameraReadout.lean) | Readout canônico por branqueamento; `R Rᵀ = I` | Positividade do Gram das linhas |
| [FiniteEnrichedCameraState](../research/hp-notes-audit-2026-09-04/original-lean/FiniteEnrichedCameraState.lean) | Parseval visível/cego, reconstrução e decomposição Green exatas | Câmera finita com o Gram positivo |
| [FiniteStencilCutoffRefinement](../research/hp-notes-audit-2026-09-04/original-lean/FiniteStencilCutoffRefinement.lean) | Refinamento por blocos de centros; correção da semente no dobramento | O stencil literal e o corte especificado |
| [CanonicalNaimarkStateReadout](../research/hp-notes-audit-2026-09-04/original-lean/CanonicalNaimarkStateReadout.lean) | Readout = adjunto Naimark composto com a realização; reconstrução coerente | `stateRealization` contínua no ambiente Naimark |
| [ExactCutoffCameraGram](../research/hp-notes-audit-2026-09-04/original-lean/ExactCutoffCameraGram.lean) | Gram literal = termo linear + resíduo; limite exato do resíduo normalizado | Cutoffs e câmeras declarados |
| [C3ProjectiveHilbertRBBridge](../research/hp-notes-audit-2026-09-04/original-lean/C3ProjectiveHilbertRBBridge.lean) | Realização Hilbert projetiva, reconstrução e transporte do estado total R/B | Não prova transporte isométrico de cada subespaço R/B separadamente |
| [C3CameraStencilEscapeClosure](../research/hp-notes-audit-2026-09-04/original-lean/C3CameraStencilEscapeClosure.lean) | Stencil normalizado: coordenadas tendem a zero, Gram não nulo, sem limite forte no ambiente indicado | Obstrução daquele ambiente `ℓ²`; não de toda realização abstrata ou rigged |
| [C3TwoVariableGreenGamma](../research/hp-notes-audit-2026-09-04/original-lean/C3TwoVariableGreenGamma.lean) | Green holomorfo em dois parâmetros, C3 bruto e conversão condicional Wronskian → Gram | A identidade com o Wronskian escalar escolhido permanece uma entrada |

Só a primeira ponte foi integrada à superfície de imports nesta rodada. Os demais fontes ficam arquivados com hashes e logs, prontos para reutilização sem confundir um arquivo local verificado com um módulo já publicado por um pacote.

## 3. Conferência da nota TFVD_DEFECT_JETS_GREEN_POSITIVE_CARRY_OPERATOR_AUDIT

[Nota original arquivada](../research/hp-notes-audit-2026-09-04/original-notes/TFVD_DEFECT_JETS_GREEN_POSITIVE_CARRY_OPERATOR_AUDIT.md).

### 3.1 A direção causal é preservada

A sequência carry → pushforward → TFVD → Green → Weyl é uma orientação de construção legítima. A ausência histórica de um crosswalk em determinado corpus não prova que ele seja impossível ou que precise vir de fora da geometria. Também não converte, por si, uma identidade entre nomes em uma igualdade entre operadores.

Os nove módulos da seção 5 continuam disponíveis em `primos`, tanto no pacote consumido quanto no snapshot atual. Abaixo, `Cp…` significa `CPFormal/Analytic/Cp….lean` no [snapshot primos e2a723b4](https://github.com/thiagomassensini/primos/tree/e2a723b4ec3e645539de0b9ca881951d93259cda/CPFormal/Analytic).

| Módulo e declaração | O que já está demonstrado | O que não deve ser inferido |
| --- | --- | --- |
| `CpFiniteSeededTfvdGreenIdentity`: `finiteCanonicalSeededTfvdGreen_identity`, `finiteCanonicalSeededTfvdGreen_signed_identity` | Identidade finita exata e versão assinada | Cancelamento bilinear de todos os bordos no limite não segue só do endpoint escalar |
| `CpNativeGpreHilbertGluedGreenDefect`: `nativeGpreHilbertGluedGreenDefect_eq_verticalWronskian` | Defeito Hilbert colado = Wronskian vertical inicial; proveniência cancela antes da compressão escalar | Anular esse Wronskian exige o domínio/par apropriado |
| `CpTfvdSeededFiniteBesselConservation`: `canonicalEnrichedPrimeCarryDefectProvenanceState_norm_sq_eq_finiteSeededTfvdBesselEnergy` | Energia positiva TFVD/Bessel exata | Não identifica automaticamente `h_k` de altura |
| Mesmo módulo: `canonicalProvenanceState_pythagoras_seededTfvdBesselLedger_of_realizesOn` | Pitágoras completo quando os readouts são realizados | A hipótese `realizesOn` precisa de prova para o estado escolhido |
| `CpNativeCarrySelfAdjointBoundaryRelation` | Relações de bordo simétricas e exclusão da relação complexa total | Simetria de relação não é a realização concreta do certificado espectral |
| `CpNativeCarryReflectedLogBoundaryCayley` | Relação refletida/Cayley tipada | A condição de bordo é parte da construção |
| `CpNativeCarrySelfAdjointBoundaryPencil`: `NativeCarrySelfAdjointBoundaryPencilRealization` | Interface com operador, autoadjunção e equivalência de ressonância | Declarar a estrutura não constrói sua instância |
| `CpC2GpreGreenActivationGuard`: `c2GpreCameraPairCompression_zero_with_positive_carryEnergy` | Compressão escalar pode zerar com energia positiva | É um contraexemplo a essa compressão coerciva, não à reconstrução enriquecida |
| `CpTfvdGpreCollapseInterface`: `IsSeededTfvdGpreMomentCollapseAt` | Nomeia uma realização simultânea indexada por `p : Nat.Primes` | Esses “momentos nativos” não são, por definição, os `h_k` da log derivada |
| `CpTfvdSeededNativeMomentSourceAudit`: `exists_seededTfvdNativeMomentSource_iff_re_eq_half` | Para cutoff não vazio, existência daquela fonte de momentos primos equivale à meia abscissa | A equivalência caracteriza a força daquela obrigação; não proíbe uma prova geométrica |

O termo “momento” precisa sempre carregar seu índice e readout. O arquivo `CpMinimalProvenanceQuotient` também fornece `minimalProvenance_factorization`: quocientar por `ker Q ∩ ker A` preserva os dois canais. Assim, um contraexemplo ao quociente mais grosseiro não elimina o quociente enriquecido.

### 3.2 Jets finitos e função infinita

A construção do laboratório é útil e coerente:

$$
G_N=L_NL_N^\top,\qquad
J_N=L_N^{-1}K_NL_N^{-\top},\qquad
\Gamma_N(v)=(I-vJ_N)^{-1}u_N.
$$

Ela fornece os kernels de diferenças divididas de `v q_N(v)` e de `q_N(v)`, com a inserção de `J_N` no segundo. A positividade do segundo exige a positividade de `K_N` ou uma identificação independente com uma energia `B^*B`.

A função racional `q_N` reproduz o bloco de momentos usado na construção, até `h_{2N-1}`. Não se pode substituir `q_N` por `q` em todas as ordens sem prova adicional. As matrizes ordinária e deslocada de ordem `N` usam justamente esse bloco; o próximo coeficiente já é uma extrapolação da seção finita.

O [mapa de coordenadas e cortes](auditoria-coordenadas-altura-cortes-c3.md) contém a execução anterior do laboratório com momentos nativos. Esta rodada não apresenta novo ajuste espectral.

### 3.3 O operador infinito já tem infraestrutura formal

A pendência antiga “construir domínio e operador infinito” deve ser refinada:

- [GreenJetEnergyFactor](../CarrySelfAdjointOperator/GreenJetEnergyFactor.lean): fator entre os setores par e ímpar, adjunção formal e closabilidade sob representação do Gram e independência.
- [GreenJetMaximalAdjointSquare](../CarrySelfAdjointOperator/GreenJetMaximalAdjointSquare.lean): `closedGreenJetEnergyAdjointSquare_isMaximalRealSelfAdjoint` e `closedGreenJetEnergyAdjointSquare_finiteCompression_eq_canonicalSection`.
- [GreenJetJacobiFiniteCompression](../CarrySelfAdjointOperator/GreenJetJacobiFiniteCompression.lean): compressões canônicas do operador de jets, inclusive após fechamento.
- [CompletedNativeCameraUniversality](../CarrySelfAdjointOperator/CompletedNativeCameraUniversality.lean) e [CompletedNativeTfvdRawAllOrderJetBridge](../CarrySelfAdjointOperator/CompletedNativeTfvdRawAllOrderJetBridge.lean): universo de câmeras, momentos e jets brutos de todas as ordens.

Esses teoremas recebem os dados de representação/independência que suas assinaturas exibem. A infraestrutura existe; sua instanciação pela energia geométrica escolhida continua sendo o ponto específico a resolver.

## 4. Registro de sondas: o que aproveitar agora

[Nota original arquivada](../research/hp-notes-audit-2026-09-04/original-notes/native_carry_registro_pesquisa_sondas_defeito_pt.md).

### 4.1 A identidade polarizada de retorno já está formalizada

Com `E^*E+B^*B=I`, `PE=B` e `G_E=I+P^*P`:

$$
E^*G_EE=I,\qquad
S(z)=C(z-L)^{-1}E^*,
$$

$$
S(z)G_ES(w)^*
=C(z-L)^{-1}(\bar w-L)^{-1}C^*
=\frac{\mathcal B(z)-\mathcal B(w)^*}{\bar w-z},
\qquad
\mathcal B(z)=C(z-L)^{-1}C^*.
$$

A última igualdade usa `L=L^*`, resolventes existentes e `\bar w-z ≠ 0`. A positividade é a do kernel matricial em todas as combinações de pontos, não de cada entrada cruzada isolada.

No branch atual: [ReturnMetricPolarizedKernel](../CarrySelfAdjointOperator/ReturnMetricPolarizedKernel.lean), declarações:

- `polarizedCovariance_eq_direct`;
- `polarizedCovariance_finiteSection_posSemidef`;
- `compressedReadout_sub_adjoint_eq_separation_smul_covariance`;
- `polarizedCovariance_eq_inv_separation_smul_readoutDifference`.

Portanto, a indicação antiga “formalizar primeiro a polarização da métrica de retorno” já foi cumprida. A etapa útil agora é identificar o **readout escalar normalizado** dessa mesma construção com o da característica nativa, preservando os canais de retorno e o limite.

No Weyl, `Finite/ReturnMetric` e `Finite/FunctionalReturnMetric` fornecem os antecessores; `Limits/FiniteFunctionalCovariance` transporta limites quando recebe convergência dos coeficientes. O [README atual do Weyl](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/248249ce098491f4194209d8e698dc5965f1405d/README.md) diferencia álgebra polinomial geral de convergência analítica verificada até grau oito. Não devemos promover essa cobertura a todas as ordens sem a estimativa correspondente.

### 4.2 O readout Naimark tem uma forma canônica, mas pede uma realização

O fonte local verificado prova

$$
R_{\mathrm{cam}}=\iota_{\mathrm{Naimark}}^*\mathcal S,
\qquad
\iota_{\mathrm{Naimark}}^*\iota_{\mathrm{Naimark}}=I.
$$

A escolha de `R_cam` fica determinada **depois** de construir `\mathcal S`, a realização contínua do estado no ambiente Naimark. O [GreenCameraCoupling atual](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/248249ce098491f4194209d8e698dc5965f1405d/NativeCarrySpectralWeyl/Boundary/GreenCameraCoupling.lean) ainda recebe `stateReadout`; sua fórmula para a fonte Gamma não identifica, sozinha, qual realização do estado completo C3 deve entrar ali.

Esta é uma localização concreta para investigar a ponte, aproveitando a reconstrução enriquecida e a convergência ponderada recuperadas.

### 4.3 Modo misto 3–4–6: positividade útil, sequência a identificar

Para `η ≥ 0`, a medida radial da nota satisfaz

$$
w_\eta(\xi)=e^{-\xi}\left[33-8\mathbf1_{\xi\ge\eta\log(3/2)}
-9\mathbf1_{\xi\ge\eta\log2}\right],
\qquad
16e^{-\xi}\le w_\eta(\xi)\le33e^{-\xi}.
$$

Ela fornece um modelo de Gram ordinário e deslocado estritamente positivo em toda ordem. Essa conclusão sobre a integral decorre da positividade do peso e de um polinômio não nulo não desaparecer num intervalo; nesta conferência não foi acrescentada uma formalização Lean dessa medida.

Seus momentos em `ξ` têm crescimento factorial. Os momentos nativos de uma série analítica local têm crescimento no máximo exponencial. Um observável compacto, como `e^{-\xi}`, muda o problema de momentos e pode preservar positividade, mas não prova sua identidade com `h_k`. O [mapa de identificação geométrica](identificacao-geometrica-kernel-carry.md) já registra testes de candidatos; não repetimos a mesma proposta como uma descoberta nova.

## 5. Coordenadas, rotação, cabeça/cauda e centros completos

A [ponte log-wave do primos](https://github.com/thiagomassensini/primos/blob/e2a723b4ec3e645539de0b9ca881951d93259cda/CPFormal/Analytic/CpNativeCarryLogWaveBoundaryEquivalence.lean) é uma pista relevante da nota `GREEN_FRAME_REFLECTION_HEIGHT_WEYL_BRIDGE`:

$$
\phi_z(u)=e^{-(1/2+iz)u},\qquad
\left(i\frac{d}{du}+\frac i2\right)\phi_z=z\phi_z,
\qquad u=\log n.
$$

`nativeCarryLogDilationExpression_wave_eq` verifica a expressão algébrica com o canal derivada fornecido; `nativeCarryLogWave_log_nat_eq_dirichletTerm` identifica a amostra em `log n` com o termo Dirichlet. O primeiro teorema não constitui sozinho uma realização fechada e autoadjunta do operador diferencial, cujo domínio e bordo ainda precisam ser ligados ao estado.

Dicionário que evita uma comparação entre objetos diferentes:

| Símbolo | Papel |
| --- | --- |
| `n` e `log n` | Índice aritmético e coordenada logarítmica da onda |
| `H_log` | Gerador logarítmico do modelo nativo correspondente |
| `t` e `v=t²` | Altura e variável par da característica `F(t)=Φ(t²)` |
| `q(v)=-Φ'(v)/Φ(v)=Σ h_kv^k` | Série que define os momentos usados pelo Jacobi |
| `J` e `T=J^{-1/2}` | Operador positivo de momentos e transformação recíproca de altura, quando definida |
| `z` na sonda de resolvente | Parâmetro espectral da sonda, a identificar com a variável adequada; não uma igualdade automática com `t` |
| `y=1+log x` na POVM de câmeras | Observável logarítmico daquela medida; diferente do observável `1/t²` |

A rotação complexa não altera normas por si. É preciso acompanhar o operador, a variável, o produto interno e o domínio através do transporte demonstrado. A obstrução do antigo carrier de Taylor complexo e a calibração da métrica C3 de três canais têm escopos específicos; nenhuma delas autoriza um “no-go de toda a geometria C3”.

Para cabeça/cauda e cortes, usar os teoremas recuperados e [CompletedC3GeometricCutoffCalibration](../CarrySelfAdjointOperator/CompletedC3GeometricCutoffCalibration.lean). A auditoria anterior já incluiu `M=2`, horizonte bruto sete, com dois centros completos e as duas pernas, além da invariância da completion. Logo, refinar esse corte dentro da **mesma métrica fixa** não remove aquela discrepância. Uma nova realização métrica deve ser avaliada pelos seus próprios teoremas.

## 6. Correções nas notas históricas

1. **Geradora de câmeras, sondas seção 7.** Para `dΣ_bc=(M_0)_{bc}1_{(0,ℓ_{bc}]}dx` e `y=1+log x`:

   $$
   (F_C(s))_{bc}=(G_C)_{bc}\frac{e^{s(1+\log\ell_{bc})}}{1+s},
   \qquad \Re s>-1.
   $$

   A fórmula impressa não recupera `G_C` em `s=0`. A correção vem da integral de `e^s x^s`.

2. **Rank criação–aniquilação, sondas seção 16.** Aplicando literalmente os criadores e os adjuntos truncados na base declarada, os ranks para `n=1,…,8` são `0,2,10,26,54,96,156,236`; a fórmula impressa fornece `0,4,16,40,80,140,224,336`. A [reprodução inteira](../research/hp-notes-audit-2026-09-04/check_note_formulas.py) verifica as imagens distintas dos vetores da base, sem tolerância numérica. Isso corrige a fórmula de rank, não invalida por arrasto toda a construção de criação.

3. **Duas frequências e no-go não linear, sondas seção 14.** A irracionalidade da razão das duas escalas separa frequências na análise linear de coeficientes constantes. Ela, isoladamente, não prova impossibilidade de toda redução não linear do tipo citado. A própria nota distingue a ordem do anulador linear da ordem mínima de uma ODE não linear. Não foi localizado um teorema Lean que justifique a exclusão geral.

4. **“Fechado” e “pendente”.** Nos registros antigos, “fechado” também designa derivação simbólica e experimento. A marca foi substituída aqui por evidência concreta: declaração verificada, resultado com hipóteses, conta reproduzida ou proposta ainda sem identificação.

5. **Completion escalar versus energia da completion.** A proveniência da característica completada e suas identidades entre câmeras já têm módulos no autoadjunto. A observação histórica de que a completion ainda precisava ser introduzida externamente está desatualizada nesse nível escalar. A identificação de sua energia no estado geométrico é uma questão adicional.

## 7. Próxima obrigação: construir a realização e provar a igualdade de momentos

O certificado atual [CompletedNativeRealHPCarrierCertificate](../CarrySelfAdjointOperator/CompletedNativeHPGateAudit.lean) tem **três campos**: `momentKernel`, `evenIndependent` e `oddIndependent`. O antigo requisito de defeito cabeça/cauda para certas construções de altura/injetividade não deve ser acrescentado como um quarto campo universal a esta interface.

Uma rota suficiente, já formalizada em [PositiveObservableNativeMomentBridge](../CarrySelfAdjointOperator/PositiveObservableNativeMomentBridge.lean), consiste em obter geometricamente um operador limitado simétrico `S` e uma fonte `u`. O observável positivo é `S²`, com

$$
m_n=\langle u,S^{2n}u\rangle=\|S^nu\|^2.
$$

Se `Φ(v)=Σ f_nv^n` é a característica par nativa, a igualdade procurada pode ser formulada sem divisão:

$$
D_n=f_0m_n+\sum_{k=0}^{n-1}m_kf_{n-k}+(n+1)f_{n+1}=0
\quad\text{para todo }n.
$$

`positiveObservable_isNativeMomentSequence_iff_defect_zero` prova a equivalência exata; `positiveObservableMoment_eq_native_of_defect_zero` identifica `m=h`. Com independência de `n ↦ S^nu`, `completedNativeRealHPCarrierCertificate_of_positiveObservable` entrega os dois setores estritos e o certificado.

A primeira igualdade calibra a massa: `f_0‖u‖²+f_1=0`. Passar nessa calibração é necessário; não substitui `D_n=0` para todas as ordens.

Ordem proposta para usar o material encontrado:

| Etapa | Reutilizar | Igualdade ou construção que falta nesta rota |
| --- | --- | --- |
| 1. Fixar o mesmo estado completo | Ponte C3 recuperada, Parseval enriquecido, cortes por centros | Escolher o transporte de estados e readouts com todos os canais |
| 2. Realizá-lo no ambiente de retorno | `CanonicalNaimarkStateReadout` e `GreenCameraCoupling` | Construir `stateRealization` e provar sua compatibilidade com a energia nativa |
| 3. Transportar os cruzamentos | `ReturnMetricPolarizedKernel` e limites do Weyl | Estimativas do limite com os parâmetros e normalizações corretos |
| 4. Identificar o readout escalar | Completion/câmeras e fórmula de convolução acima | Provar todos os `D_n=0`, ou uma identidade analítica que os implique |
| 5. Preservar independência | Incidências BR2/rota projetiva e órbita no carrier escolhido | Transportar a independência para **essa mesma realização do Gram** |

Esta é uma rota suficiente; a busca não encontrou um argumento que obrigue toda solução a passar por um único desses modelos. Os teoremas do atlas de energia também continuam úteis, mas os resultados de confinamento em `EmpiricalLimitConfinement` recebem coercividade explícita. Uma energia residual positiva ou um piso de denominador não fornece automaticamente a identificação acima.

## 8. Índice de leitura do diretório HP

Nomes abaixo são relativos a `/home/thlinux/Downloads/hp`. Os hashes, títulos, seções e contagens estão no inventário.

| Etapa de consulta | Notas |
| --- | --- |
| Cronologia e invariantes entre representações | `ATLAS_RELACIONAL_MESTRE_PERSISTENCIA_ESTRUTURAL.md`; `CARRY_GEOMETRY_TFVD_GREEN_WEYL_CAUSAL_CHRONOLOGY.md`; `MEMORIA_DERIVACAO_OPERADOR_AUTOADJUNTO_GENUINE.md` |
| Estado completo, Parseval e limite | `C2_C3_ESTADO_ENRIQUECIDO_PARSEVAL_E_LIMITE_MOVEL.md`; `C3_READOUT_CANONICO_E_COMPLETION_DO_CUTOFF.md`; `C3_CROSSWALK_COMPLETION_PROJETIVA_E_JETS_TODAS_ORDENS.md`; `C3_CANONICO_FECHAMENTO_ANALITICO_TODAS_AS_ORDENS.md` |
| Ambiente Hilbert, projeções e mudança de espaço | `C3_HILBERT_RB_CROSSWALK_E_OBSTRUCAO_UNIFORME.md`; `C3_CAMERA_STENCIL_ESCAPE_E_FECHAMENTO_RIGGED.md` |
| Green, Gamma, retorno e coordenada logarítmica | `C3_GREEN_GAMMA_IDENTIDADE_DUAS_VARIAVEIS.md`; `GREEN_FRAME_REFLECTION_HEIGHT_WEYL_BRIDGE.md`; `native_carry_registro_pesquisa_sondas_defeito_pt.md` |
| Jets, Jacobi e limite projetivo | `TFVD_DEFECT_JETS_GREEN_POSITIVE_CARRY_OPERATOR_AUDIT.md`; `C2_DISCRETE_JACOBIAN_HEIGHT_JACOBI_BRIDGE.md`; `IDENTIDADE_PROJETIVA_EXATA_LIMITE_OPERADOR_ALTURAS.md`; `NATIVE_CARRY_HEIGHT_MOMENT_JACOBI_OPERATOR_LOG.md` |
| Pencils, característica e checagem da realização final | `NATIVE_CARRY_CANONICAL_HEIGHT_WEYL_GATE_LOG.md`; `NATIVE_CARRY_HEIGHT_SPECTRAL_PENCIL_LOG.md`; `NATIVE_CARRY_HILBERT_POLYA_OPERATOR.md` |
| Proveniência aritmética e cutoff | `NATIVE_CARRY_CUTOFF_MANGOLDT_EXPLICIT_FORMULA_LOG.md` |

Mapas anteriores: [costuras](carry-seams-2026-09-04-update.md), [rota projetiva](mapa-rota-valvula-projetiva.md), [repositórios](mapa-garimpo-repositorios-obrigacoes-carry.md), [notas](mapa-notas-costura-energia-momentos-carry.md), [identificação geométrica](identificacao-geometrica-kernel-carry.md), [coordenadas e cortes](auditoria-coordenadas-altura-cortes-c3.md).

## 9. Proveniência de versões

Os snapshots abaixo foram lidos diretamente de Git após atualizar `origin/main`; não houve mudança dos pins do projeto.

| Repositório | Snapshot de main consultado | Pin consumido pelo autoadjunto |
| --- | --- | --- |
| carry-self-adjoint-operator | `4de44de2341089a29665917ed48cd388c68a85e5` | Branch de trabalho parte de `62f69205a5f80554d576b4969d658674c670efc4` |
| primos | `e2a723b4ec3e645539de0b9ca881951d93259cda` | `65d50f6db1208708e109982ba97e1d51d3039956` |
| native-carry-c3-crosswalk | `1e9e06e1d51d176a909c187828f7c880e5d1207d` | `150cfc7fb08da96bf8117f15869cc2b819d593c2` |
| native-carry-spectral-weyl | `248249ce098491f4194209d8e698dc5965f1405d` | `298d83c9351e308a5213b9f5ac32e44087f98a9f` |
| green-frame-theorem | `12445c08087fa0c5fc5b2350f3455e09bc6b8b42` | `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa` |
| genuine-zero-uniform-atlas-energy | `2f5c38321d63752f891ef99622ff0685bc62c0ce` | Fora do manifest deste projeto |
| carry-geometry | `3a64ccebfa3849251b2d564432d693ed19a4b74b` | `1f85b8c3ab5ded27a0782956e1ada0dd8a1b6fd4` |

Verificação: os nove fontes históricos recompilaram; o módulo recuperado passou com `--wfail`; as 14 chamadas de build de `scripts/audit.sh` passaram, incluindo o import geral e a auditoria de axiomas. A recuperação não acrescenta `sorry` nem axiomas novos. Compilar esses resultados condicionais não prova que suas hipóteses já foram satisfeitas pela realização geométrica final.
