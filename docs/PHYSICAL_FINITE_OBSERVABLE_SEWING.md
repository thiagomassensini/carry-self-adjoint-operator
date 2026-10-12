# Costura Física Finita, Vetorial e Observável

Data: 2026-10-12. Repositório: `thiagomassensini/carry-self-adjoint-operator`.
Base efetivamente inspecionada: `91b1c52372d74db8956607183766c042e204a796`,
`main` após PR #77. Execução Lean: host de pesquisa `ssh llm`.

## Resultado e Escopo

O resultado central é uma igualdade do **par completo no carrier original**,
antes de pairing, norma, energia ou readout escalar. A aplicação não assume
uma estrutura de compatibilidade que contenha a conclusão: os coeficientes
são extraídos do `FormalStencil` original e a entrada é definida por derivadas
iteradas do seu polinômio. A identidade fonte–jet é uma consequência de Taylor.

O fechamento é finito, no par do `L²([0,1]; ℂ)` Cauchy original. Não identifica
universalmente esse carrier com o port Weyl/Naimark das câmeras. A rota Green
da fonte inteira é incondicional quanto à regularidade dos nós; a identificação
com a carta de resposta e o produtor TFVD por quocientes é explicitamente regular.

Todas as novas declarações matemáticas estão no namespace
`CarrySelfAdjointOperator.PhysicalSewing`. O registro completo de declarações,
incluindo definições, está em `audit/physical-finite-sewing-registry.json`.

Os três gates solicitados foram lidos integralmente, incluindo demonstrações,
programas, referências e limitações. Foram usados como material de pesquisa;
a autoridade sobre declarações existentes e novas é a fonte Lean efetiva.
Hashes SHA-256 dos arquivos locais consultados:

| Gate | SHA-256 |
| --- | --- |
| Estudo_Historico_Green_Laguerre_2026-10-12.md | `c10ae9a9776a87ffe908e2b19b31d2cf2dbb7d66d2a688a7329f1cc6e66dee4e` |
| Gate_Input_Fisico_Fonte_Jet_C2_2026-10-12.md | `007657c3d83d8135d44522488416258e320456bf29101e869ba07da622fd94ce` |
| Gate_Segundo_Port_Green_Retorno_Completion_2026-10-12.md | `39b1343a3562705a53360ac0ca5b56e1bc542f9d26f6bb3d69b02034af56cdab` |

O material histórico adicional `Pesquisa_Carry_C2_TFVD_Laguerre_Completa.md`
foi consultado como apoio; ele não substituiu o gate de entrada, disponibilizado
durante a tarefa. Os canários sintéticos dos anexos não foram promovidos a
avaliações de F ou certificados Lean.

## Convenções Preservadas

- `N = 2*n` para a API SourceJet; as demais identidades vetoriais valem para `Fin N`.
- `K = k+1`; `h = canonicalCompletedC3RadialSecondStep k = i/K`, com o sinal da fonte.
- `z_j = canonicalCompletedC3RadialTiltPoint k j = (j+1)h`.
- `endpointGauge k a = nativeSourceJetOrderPhase a * h^a`, com fase `(-1)^(a/2)`.
- Posição material positiva `m` corresponde ao grau radial `j=m-1`.
- `materialPolynomial N v = Polynomial.ofFn N v`, antes da amplitude completada.
- Meia densidade original `sqrt(K)*sqrt(u)*u^j`; `cauchyMatrix N` tem entradas
  `1/(i+j+2)`. Nenhuma mudança de métrica foi introduzida.
- `canonicalCompletedNativeProjectiveChiralForm` é a forma original assinada,
  conjugado-linear na primeira entrada. A positividade do diagnóstico não muda sua assinatura.

## Entrada Independente e Produtor Material

`physicalEndpointJetInput` é o mapa linear definido por
`g_a * ((Polynomial.derivative^[a]) (materialPolynomial N v)).eval 1`.
`physicalEndpointJetInput_finite` e `physicalEndpointJetInput_factorials`
provam as fórmulas finitas com fatoriais descendentes e `j!/(j-a)!`.
Os endpoints são de representantes polinomiais, não funcionais pontuais de todo L².

`physicalEndpointJetInput_nativeSourceInput` prova, para quaisquer coeficientes
complexos e sem exigir amplitudes não nulas,

```text
nativeSourceChiralJetInput n k (physicalEndpointJetInput (2*n) k v)
  = fun j => completedNativeNormalizedPositiveChiralAmplitude z_j * v j
```

A prova usa Hasse/Taylor, a fórmula binomial da matriz original e o quadrado
da fase. Não usa a inversa da matriz fonte–jet para definir a entrada.
`physicalEndpointJetInput_wholeSource` compõe com a síntese original.
A amplitude ocorre uma vez: nas colunas projectivas; nas colunas radiais
não projectivas o coeficiente é `A_j*v_j`.

`materialStencilPolynomial` e `materialStencilRadialCoefficients` são os lifts
lineares inteiros literais de `FormalStencil`: `atom (j+1)` vira `X^j` e
`Finsupp.single j 1`. O átomo material zero é explicitamente enviado a zero,
como no lift positivo existente; não se afirma injetividade do ledger irrestrito.
`originalMaterialCompletedSource` aplica o mesmo lift às colunas completadas.

`materialStencilCoefficients s` lê os coeficientes desse polinômio em uma janela
par garantida pelo grau. A janela é conservadora, não necessariamente mínima.
`materialStencilCoefficients_polynomial` e
`materialStencilRadialCoefficients_eq_fin` provam os adaptadores completos.
`materialStencilPolynomial_matches_originalProfile` identifica o representante
com `nativeStencilCauchyProfile`. As provas
`originalMaterialBracket_profile_provenance` e
`originalMaterialCamera_profile_provenance` reutilizam explicitamente
`nativeBracket_profile_factor` e `nativeCamera_profile_seed_centers`.

Aplicações materiais kernel-checked:

- `originalMaterialCompletedSource_bracket`: qualquer distância `r`, centro
  `p+r+1`, pernas positivas `p+1` e `p+2*r+1`, coeficientes `1,-2,1`.
- `originalBracket_physicalFiniteSewing`: esse stencil é SourceJet e Green corrigido.
- `originalMaterialCompletedSource_camera`: seed original mais **todos** os centros.
- `originalCamera_physicalFiniteSewing`: câmera finita completa, não apenas o bulk.
- `originalC2_camera_literal`: seed `V_0`, centros modernos `4*(a+1)` e raio 1.
- `originalNaturalCamera_literal`: para todo `b≥3`, seeds e todos os raios de
  `radiusSet b`, centros `b*(a+1)`; aplica-se literalmente às linhas C3–C7.
- `originalMaterialBracket_threeChannels`: os três canais anteriores de cada
  stencil a distância arbitrária continuam presentes por `completed_stencil_all_distance`.

`firstMaterialBracketCoefficients` é extraído de `centeredBracketStencil 2 1`.
`firstMaterialBracket_polynomial` prova `P=(1-X)^2`, com extensão explícita a
`Fin 4`; `firstMaterialBracket_endpoint_canary` prova `(0,0,2/K²,0)`.
Não foram escolhidos coeficientes a partir dessa resposta.

`extendMaterial` e seus teoremas preservam o polinômio, os jets existentes,
o Finsupp e a fonte inteira ao ampliar a janela por zero. O jet novo na ordem
do comprimento antigo é zero. Assim uma dimensão ímpar não é um estado novo.

## Carta Inteira e TFVD Enriquecido

`twoPortChart`/`twoPortReconstruct` têm os dois roundtrips no par físico.
`twoPortSynthesis N k v s` representa
`sqrt(K/2)*sqrt(u)*(P_s+iP_v, P_s-iP_v)`.
`twoPortEndpoint_reconstruct_entire_pair` recupera ambos os ports de suas
cartas de endpoint, mesmo fora do gráfico da resposta.

Em nós regulares, `normalized_chiral_gap_and_response` prova o gap `sqrt(2)*i`
e a soma normalizada `theta=-F'/F`. `finiteProjectiveSource_eq_twoPorts`
identifica a fonte com `(v,theta*v)`.

Hipóteses necessárias, não ocultas:

- Para essa identificação: `F(z_j)≠0` e a coordenada positiva de
  Hermite–Biehler `E_+(z_j)≠0`, para cada nó da janela.
- Para usar `canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime`:
  `operatorHeightParameter z_j ∈ genuineCriticalStrip`.
- `originalRadialNodes_strip_of_cutoff` prova a condição suficiente
  `2*N < k+1`; não se afirma regularidade da faixa para qualquer corte/profundidade.
- Para os quocientes de estado arbitrário: `Q≠0`, `xi≠0`, `T≠0`.
  `tfvdCanonicalResponse_regular_denominators` deriva esses denominadores para
  o estado canônico da hipótese de faixa e `F≠0`.
- Para o erro cabeça/completo: adicionalmente `T_H≠0`.
  O fator `sqrt(2)` e as gauges são provados não nulos, não hipóteses externas.

`endpointCompletionMatrix` usa diferenças **progressivas literais**.
`physicalEndpointJetInput_completion` deriva
`E(theta*v)_a = Σ_{b≥a}(g_a/g_b) Δ^(b-a)theta_a/(b-a)! * (Ev)_b`.
Não é um campo assumido de uma estrutura de costura.

`tfvdStateTracePair` lê `(F^G,C^G)` do estado
`CanonicalC3BracketTfvdCompletionState M`, mantendo no domínio `transport`,
`valueTail` e `logJetTail`. Seus readouts não substituem o estado enriquecido.
`tfvdStateResponse_threeChannels` prova
`theta^G = xi_c/xi + i Q'/Q + i L/T`.
`tfvdStateResponse_divisionFree` prova a identidade de resposta sem divisões
na conclusão, ainda no domínio explicitamente regular do quociente.
`tfvdCanonicalResponse_eq_original` identifica essa resposta com `-F'/F`.

O produtor independente é `tfvdMaterialSecondCoefficients`; a reconstrução
é `tfvdMaterialWholeSource`. `tfvdMaterialWholeSource_canonical` demonstra
sua igualdade com a fonte, não define o segundo port como `theta*v`.
`materialSourceChannels_eq_tfvdReadouts` reutiliza `source_pair_eq_bracketTfvd`
com coeficientes `c=A*v` e tilt `r=1`. As duas normalizações são certificadas
por `materialSourceValue_normalization` e `materialSourceCompanion_normalization`;
`materialSourceChannels_reconstruct` reutiliza `incident_synthesis_eq_source`
e `returned_synthesis_eq_source` para recuperar o par inteiro.

`tfvdStateHeadTail_responseDefect` prova exatamente
`i*(T_H*L_T-L_H*T_T)/(T_H*(T_H+T_T))`.
`tfvdHeadTail_secondVector`, `tfvdHeadTail_endpointVector` e
`tfvdHeadTail_exactEndpointDefect` transportam o erro aos coeficientes e jets.
`tfvdCanonicalSecondPort_endpointCompletion` compõe o produtor com a matriz
de diferenças de endpoint. Isto identifica readouts/segundo port, **não** os
estados nem carriers das duas rotas chamadas TFVD.

## Probes Fiéis, Diagnóstico e Canários

`secondPortDefect` recebe o candidato `wG` independentemente e define
`d=wG-theta*v`. `mixedPhysicalProbes` é o pairing físico real de cada
`R(e_a)` com `twoPortSynthesis 0 d`.
`mixedPhysicalProbe_originalColumn` identifica esses probes com as colunas
completadas originais, sob regularidade.

- `mixedPhysicalProbes_formula`: `lambda = (-i*K/2) • (H *ᵥ d)`.
- `mixedPhysicalProbes_faithful`: todos os probes zero **se e somente se** `d=0`,
  por `cauchyMatrix_posDef` já existente.
- `mixedPhysicalProbes_decode`: `d=(2*i/K) • (H⁻¹ *ᵥ lambda)`.
- `mixedPhysicalProbes_diagnostic`: `lambda* H⁻¹ lambda=(K²/4)*(d* H d)`.

A inversa é só o decodificador das observações; não define a entrada material.
`diagonalDefect_autopairing_zero` e `nonzeroDiagonalDefect_detected` separam
o autopairing nulo da fidelidade vetorial. `realConstantGauge_preserves_graph_form`
preserva a forma inteira com duas entradas independentes, enquanto
`realConstantGauge_detected` detecta o port alterado quando `c≠0` e `v≠0`.
Não se afirma aqui a classificação geral das ambiguidades de operadores.

## Laguerre, Caudas e Cruzamentos

`laguerreFirstMomentMatrix` é a Vandermonde transposta com colunas escaladas
pelas features existentes. `laguerreFirstMomentMatrix_det_ne_zero` vale em
dimensão arbitrária, inclusive zero. `laguerreFirstMoments_injective` e
`laguerreFirstMoments_decode` certificam observabilidade pelos primeiros `N`
momentos. `twoPortLaguerreFirstMoments_injective` aplica-a separadamente aos
dois ports; não identifica uma cabeça injetiva com uma isometria euclidiana.

`shortHead_synthetic_canary` prova o exemplo exato `v=(3,-5)` e
`theta=(i/8,i/4)`, com cabeça material zero e segunda cabeça `-i/4`.
`shortHead_cannot_determine_synthetic_secondPort` formaliza a insuficiência.
Esses valores de theta são **sintéticos**, não amostras de F.

Para todo corte `R`, `mixedPhysicalProbes_headTail` conserva a cabeça e
`(D_R e_a)*H(D_R d)`; `mixedPhysicalProbes_tail_as_originalGram` identifica
literalmente a expressão da cauda. Reutiliza-se `matrixPairing_head_tail`;
nenhuma cauda de energia ou cruzamento é descartada.

`physicalPair_signed_camera_crosses` conserva todos os pares ordenados de
duas famílias independentes. `physicalPair_camera_fourSectors` mantém os
quatro setores. `twoPort_camera_headTail` e
`twoPort_camera_defect_fourHeadTails` retêm uma cauda em cada setor e par
de labels. `cameraDefectFamily_faithful` observa os defeitos **antes da soma**;
`cameraDefectCancellation_canary` mostra a possível anulação global de `d,-d`.

As features finitas não são a projeção física `P_R` do PR #77. Nenhuma fórmula
de soma de overlaps para `P_R` foi assumida, nem completude/ortonormalidade
Laguerre em toda ordem. Os cutoffs `N`, `R`, `M`, profundidade `k`, tamanho
de câmera e labels materiais continuam separados.

## Capstone, Traços e Ledger Green

`physicalFiniteSewing_capstone`, sem hipóteses sobre amplitudes/nós, prova
para `v : Fin (2*n) → ℂ` e `0<q<1`:

```text
nativeSourceProjectiveBoundaryJetSynthesis n k
  (physicalEndpointJetInput (2*n) k v)
    = finiteProjectiveSource (2*n) k v
    = (q : ℂ) • ((physicalPairGreenResolvent q hq0.le hq1)^2)
        (physicalGreenBulkBoundary q k (finRadialCoefficients (2*n) v)
         + physicalGreenResidualNumerator q k (finRadialCoefficients (2*n) v))
```

O enunciado Lean registra as duas igualdades como conjunção.
`originalMaterial_wholeSource_capstone` substitui o termo central pelo lift
literal `originalMaterialCompletedSource k s` e o Finsupp pelo produtor
`materialStencilRadialCoefficients s`.
`physicalFiniteObservable_capstone` inclui, sob regularidade/faixa, a igualdade
do TFVD completado e o critério necessário e suficiente para um candidato
independente. `originalMaterial_observable_capstone` efetivamente aplica
as quatro conclusões ao produtor material original, não somente a vetores abstratos.

Para `x=materialStencilRadialCoefficients s`, o ledger usado literalmente é:

```text
b = finiteTfvdBulk q x
t0 = finiteTrace0 x = P_x(0)
t1 = finiteTrace1 q x = q⁻¹*P_x'(0)-P_x(0)
B = physicalPairRadialAdvance (physicalCompletedFiniteSource k b)
    + (q⁻¹*t0) • V_0 + (t1-t0) • V_1
E_Green = physicalCompletedFiniteResidual k b
    + 2 • physicalCompletedFiniteResidual k x
    - q • (physicalPairRadialAdvance (physicalCompletedFiniteResidual k x)
           + physicalCompletedFiniteResidual k (coefficientShift x))
```

`finiteTfvdBulk_succ` dá `b_(j+1)=q⁻¹*x_(j+2)-2*x_(j+1)+q*x_j`,
com `b_0=0`. `physicalCompletedFiniteResidual_original` conserva todos os
`radialChiralAnalyticResidual` originais. Para a câmera,
`s=seedStencil b+Σ centerStencil b a`: a seed não foi substituída por dois
traços, nem os centros/raios por seis papéis do ledger.

`finiteTrace0_polynomial`, `finiteTrace1_polynomial` e
`finiteTraces_from_entireEndpointChart` recuperam os traços a partir da carta
inteira/Taylor. Não os confundem com os jets 0 e 1 em `u=1`.
`finiteValve_zeroExtension`, `finiteValve_terminal_coordinates`,
`finiteValve_polynomial` e `finiteValve_physicalGreen` conservam a extensão
para `Fin (N+2)` e os dois novos termos terminais da válvula.
O encoder `physicalEndpointJetInput` e o numerador `E_Green` são objetos distintos.

## Módulos e Auditoria

Cada módulo da tabela tem seu próprio módulo `Audit`, com `#check`,
`#print axioms` de **todas** as declarações públicas, e inspeção transitiva
das constantes nos tipos e corpos pelo comando `#audit_physical_sewing`.

| Módulo | Declarações públicas | Conteúdo |
| --- | ---: | --- |
| NativePhysicalEndpointEncoder | 19 | Derivadas, Taylor, U E = A v, fonte inteira |
| NativePhysicalFiniteSewing | 28 | Fin/Finsupp, zero padding, material, traços, canário |
| NativePhysicalMaterialProducer | 12 | Lift literal, aplicações e proveniência física |
| NativePhysicalTwoPortChart | 19 | Carta ambiente, reconstrução e normalizações |
| NativePhysicalEndpointCompletion | 7 | Diferenças progressivas derivadas |
| NativePhysicalTfvdSecondPort | 21 | Estado enriquecido, segundo port, denominadores, erro de cauda |
| NativePhysicalMixedProbes | 12 | Fidelidade, decodificação, gauge e diagnóstico |
| NativePhysicalLaguerreObservability | 13 | Vandermonde arbitrária, dois ports, cabeça + cauda |
| NativePhysicalCameraCrossings | 13 | Famílias, quatro setores, C2–C7 e cancelamento |
| NativePhysicalValveExtension | 6 | Válvula e termos terminais novos |
| NativePhysicalObservableCapstone | 4 | Capstone regular aplicado e critério vetorial |

Total: 154 declarações matemáticas públicas (115 teoremas e 39 definições),
além do suporte de auditoria.
O verificador `scripts/check_physical_sewing_registry.py` detecta deriva de
inventário ou perda de cobertura. `scripts/audit_physical_finite_sewing.sh`
executa os builds isolados `--wfail`, checks diretos, auditoria estática,
build raiz `--wfail` e `scripts/audit.sh` original. Não atualiza pins.

### Ambiente e Reprodução

```bash
ssh llm
cd /home/thlinux/carry-self-adjoint-operator
export PATH=/home/thlinux/.elan/bin:$PATH
bash scripts/audit_physical_finite_sewing.sh
```

Toolchain efetivo: Lean 4.32.0, Lake 5.0.0-src+8c9756b.
As 16 revisões efetivas dos pacotes coincidem com o manifest; entre elas:
mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`,
geometry-of-numbers `d7cc54f5c485320f1fada33118e9e6101488819a`,
NativeCarrySpectralWeyl `298d83c9351e308a5213b9f5ac32e44087f98a9f` e
CPFormal `65d50f6db1208708e109982ba97e1d51d3039956`.
O ambiente reaproveitou artefatos locais de dependências; os novos módulos
e auditorias foram efetivamente elaborados/checados por Lean, não só lidos.

O build pré-integração é executado na worktree isolada
`/home/thlinux/carry-physical-finite-sewing`; a reprodução após publicação
usa o checkout principal acima. Os dois arquivos C2 preexistentes e não
rastreados do checkout principal foram preservados byte a byte.

Como reprodução suplementar, foi executado o script existente
`python3 scripts/check_native_laguerre_physical_sewing_canaries.py`.
Ele confirmou os defeitos racionais `59/54` e `-157/54` dos dois candidatos
multibase especificados; seu JSON foi preservado com os logs. Isso é evidência
algébrica computacional desses candidatos, não uma prova Lean dos alvos novos,
nem avaliação da característica completada, nem impossibilidade universal.

### Resultados Efetivos

Rodada final em 12/10/2026, aproximadamente 18:30–18:37, UTC-3, no llm.
O HEAD de base dos logs é `91b1c52372d74db8956607183766c042e204a796`;
as fontes novas e alteradas foram checadas na árvore da tarefa antes do commit.
Os hashes das fontes Lean estão em `source-sha256.log`.

| Comando/check efetivo | Resultado |
| --- | --- |
| `bash scripts/audit_physical_finite_sewing.sh .lake/physical-finite-sewing-final-audit` | exit 0, `Physical finite sewing audit passed` |
| `lake build --wfail CarrySelfAdjointOperator.<Modulo>Audit`, para os 11 módulos | 11/11 builds aprovados |
| `lake env lean CarrySelfAdjointOperator/<Modulo>Audit.lean`, para os 11 módulos | 11/11 checks diretos aprovados |
| Inventário estruturado, `#check`, `#print axioms`, guard de tipos/corpos | 154/154 declarações novas; mais 3 critérios globais antigos auditados |
| `bash scripts/static_audit.sh` | exit 0, `static audit passed` |
| `git diff --check` | exit 0, sem diagnósticos |
| `lake build --wfail` | exit 0, `Build completed successfully (10130 jobs)` |
| `bash scripts/audit.sh` original | exit 0, `kernel audit passed`; inclui Audit, BR2Audit, OrderAudit e RecoveredC2GreenAudit |
| Canários racionais suplementares existentes | exit 0, `PASS_EXACT_RATIONAL_NO_GO`, apenas para os candidatos especificados |

As dependências axiomáticas das 154 declarações são subconjuntos do conjunto
padrão `{propext, Classical.choice, Quot.sound}`. Nenhum `sorryAx`, axioma
adicional, obrigação admitida ou hipótese que seja a conclusão foi introduzido.
O guard percorreu os tipos e valores transitivos, entre 1.779 e 5.941 constantes
por módulo; o capstone tem 4 raízes públicas e fecho de 5.941 constantes.
O guard separado dos três critérios anteriores também passou (fecho 5.843).
Não houve erro ou warning nos logs dos checks diretos novos. As mensagens
informativas antigas de táticas no build global não foram tratadas como falhas.

Os logs efetivos ficam em `.lake/physical-finite-sewing-final-audit` durante
a execução e são preservados no pacote de entrega antes da remoção da worktree.
O relatório de entrega registra o commit, PR, estado de main, rechecagem
pós-integração e localização permanente dos logs. A existência de um workflow
sem jobs não conta como build Lean; a validação acima foi executada no ambiente real.

## Fronteiras Globais Não Fechadas

O mismatch Gamma/native permanece exatamente nos critérios anteriores:
`canonicalCompletedC3NativeSourceLocusGreenCompatibility_iff_mismatch_zero`,
`canonicalCompletedC3NativeGreenTraceRelationAt_iff_mismatch_zero` e
`canonicalCompletedC3NativeGreenInverseTraceRealizationExists_iff_mismatch_zero`.
O Audit do capstone confere também esses critérios existentes. Nenhum campo
de compatibilidade ou hipótese de mismatch-zero foi introduzido para obter
o capstone físico finito. A identidade TFVD `(F^G,C^G)=(F,-F')` não prova essa anulação.

Continuam explícitas as obstruções históricas: o bulk esparso FULL-EVEN tem
kernel de dimensão `J+1`, e dois traços fixos não recuperam seus throughflows;
um quociente que apaga proveniência pode perder contribuição aritmética;
retorno cumulativo não ganha cota uniforme no L² de vértices por um endpoint
limitado. A FULL-EVEN histórica tem centros `2m`, não os centros `4m` da C2
moderna. Os relógios material `log(j+1)`, geométrico `log u` e de altura não
foram identificados por mudança de notação.

Ainda não se afirmam: completude Laguerre, ortonormalidade em toda ordem,
fórmula binomial fechada de toda a matriz física, isometria multibase universal,
entrelaçador Weyl→Cauchy, igualdade dos estados TFVD distintos, suporte infinito,
cotas uniformes de cauda/retorno, cálculo funcional completo ou positividade
global da forma quiral assinada. Nada disso é premissa escondida da prova finita.

## Respostas Objetivas

1. A entrada vem de `materialStencilPolynomial` do `FormalStencil` original,
   seguida de `physicalEndpointJetInput`; nunca da inversa da matriz fonte–jet.
2. `originalMaterial_wholeSource_capstone` identifica SourceJet, o par material
   completo e Green; `originalMaterial_observable_capstone` acrescenta TFVD e probes.
3. O segundo port vem de `tfvdMaterialSecondCoefficients` dos estados
   `CanonicalC3BracketTfvdCompletionState`; ambas as caudas continuam nesses estados
   e no determinante exato do erro cabeça/completo.
4. `mixedPhysicalProbes_faithful`, baseado no Gram Cauchy positivo definido original.
5. Nos teoremas de famílias/quatro setores e cabeça+cauda, especialmente
   `twoPort_camera_defect_fourHeadTails` e `mixedPhysicalProbes_headTail`.
6. Resta o gate Gamma/native e os transportes/globais acima. O fechamento finito
   não é uma prova dessas obrigações nem um resultado universal Weyl/Naimark.
