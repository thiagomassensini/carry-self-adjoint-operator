# Mapa — rota da válvula projetiva para o carrier nativo

Este é o mapa de trabalho da rota proposta por Motta em 4 de setembro de 2026.
A base de partida é `main` em `351ec74cc40f7d12d6f31e9450372f223dabb2bd`, após as
PRs #48 e #49. O objetivo é usar as incidências nativas, a geometria projetiva e
os estados Green/TFVD/C3 para demonstrar a realização positiva dos momentos
logarítmicos nativos, com independência em toda ordem.

## 1. Resultado que a rota deve fornecer

Defina `h := canonicalCompletedNativeLogDerivativeMoment`. Para todo `N : ℕ`,
queremos demonstrar geometricamente:

$$
G_N=(h_{i+j})_{i,j<N}>0,\qquad K_N=(h_{i+j+1})_{i,j<N}>0.
$$

Uma forma suficiente é construir mapas reais lineares injetivos
`T_N, S_N : (Fin N → ℝ) →ₗ[ℝ] H_N`, ou carriers distintos para cada paridade,
com as identidades polarizadas

$$
\langle T_Na,T_Nb\rangle=a^{\mathsf T}G_Nb,
\qquad
\langle S_Na,S_Nb\rangle=a^{\mathsf T}K_Nb.
$$

As aplicações devem vir dos dados geométricos. Construí-las usando como
premissa a positividade dos próprios `G_N,K_N` não resolve esta obrigação.

`CanonicalCompletedNativeStieltjesPositivity` já expressa exatamente a
positividade das duas torres em toda ordem. A construção existente transforma
essa proposição em `CompletedNativeRealHPCarrierCertificate`. Não exige uma
constante de coercividade positiva uniforme em `N`. A identificação com um
estado geométrico específico exige ainda compatibilidade entre os transportes.

## 2. Sequência das etapas

| Etapa | Entrega concreta | Estado atual |
| --- | --- | --- |
| 1 | Transporte linear injetivo das incidências de suporte finito às curvaturas projetivas; recuperação dos coeficientes; independência e dimensão dos spans; ligação ao carrier Hilbert existente. | Concluída e compilada em [ProjectiveValveNativeIncidence.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/891853d810135669d871ab6f0ecd2420ac1d204c/CarrySelfAdjointOperator/ProjectiveValveNativeIncidence.lean); ver registro na seção 9. |
| 2 | Identificar quais combinações dessas curvaturas e quais dados de bordo dão o estado nativo que produz os momentos de `F`. | Aberta: a realização Hilbert literal C3 foi refutada para o Gram dos momentos; uma nova realização é necessária. Ver seção 10. |
| 3 | Demonstrar as identidades Gram polarizadas para `G_N` e `K_N`, conservando normalizações, cruzamentos e bordos. | Obrigação central aberta. |
| 4 | Usar a independência transportada para obter positividade estrita para todo `N` e construir o certificado. | Mecanismo formal existente; depende das etapas 2–3. |
| 5 | Aplicar a equivalência espectral da #49; identificar a realização geométrica com o carrier completado e estudar o transporte inverso à altura assinada. | Equivalência de Jacobi pronta sob certificado; identificação concreta e demais questões dependem dos passos anteriores. |

## 3. Etapa 1 — incidências, curvaturas e spans

Trabalhamos inicialmente no espaço real `ℕ →₀ ℝ`. Para uma incidência `v`, a
série original é `C_v(X) = sum_n v(n) X^n`. O transporte é

$$
D_v(Y)=C_v\bigl(Y/(1+Y)\bigr).
$$

A transformação de coordenada tem inversa formal. Portanto, mesmo quando
`D_v` tem infinitos coeficientes, sua origem de suporte finito é recuperável.
O domínio do transporte de volta ao Hilbert será o **range dessas séries**.
Isso não define uma aplicação de todas as séries formais para `ℓ²`.

Peças já disponíveis, dentro de `CarrySelfAdjointOperator/`:

| Arquivo | Declarações para localizar | Uso |
| --- | --- | --- |
| [AllBaseBracketIncidenceIndependence.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/AllBaseBracketIncidenceIndependence.lean) | `cameraBracketIncidence`, `cameraBracketIncidence_apply_alignedCenter`, `cameraBracketIncidence_linearIndependent_of_injective` | Incidência com pesos `1,-2,1`; pivô `-2` no centro próprio; independência finita para base suportada e raio admissível. |
| [AllBaseBracketIncidenceGlobalIndependence.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/AllBaseBracketIncidenceGlobalIndependence.lean) | `evenCameraBracketIncidence_linearIndependent_global`, `oddCameraBracketIncidence_linearIndependent_global` | Independência global de cada paridade. |
| [ProjectiveDepthEquivalence.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/ProjectiveDepthEquivalence.lean) | `toProjective`, `fromProjective`, `fromProjective_toProjective`, `toProjective_fromProjective`, `coordinateChangeEquiv` | Mudança formal `X ↔ Y` e seus dois percursos. |
| [ProjectiveValveEquivalence.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/ProjectiveValveEquivalence.lean) | `projectiveValveCurvature`, `projectiveValveMass_injective`, `projectiveValveCurvature_surjective` | Massa normalizada ↔ curvatura; natureza algébrica da válvula. |
| [ProjectiveValveFiniteSpanGeometry.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/ProjectiveValveFiniteSpanGeometry.lean) | `projectiveValveFiniteSpanSubspace_finrank_eq_card`, `projectiveValveFiniteSpan_eq_iSup_orbits` | Dimensão e subgrupo multiplicativo de uma família independente de tamanho arbitrário. |
| [ProjectiveValveFiniteSpanIncidence.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/ProjectiveValveFiniteSpanIncidence.lean) | `projectiveValveFiniteSpanSubspace_eq_iff_family_on_finiteSpan`, `projectiveValveFiniteSpan_eq_iff_family_orbits_le` | Regenerar o mesmo span com outra família independente de igual cardinalidade. |
| [ProjectiveValveSubspaceGeometry.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/ProjectiveValveSubspaceGeometry.lean) | `projectiveValveSubspaceMasses_le_iff`, `projectiveValveSubspaceMasses_injective` | Preservar e refletir inclusões e distinguir spans. |
| [BR2ProjectiveHilbertIncidenceTransport.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/BR2ProjectiveHilbertIncidenceTransport.lean) | `br2CameraBracketProjectiveHilbertMap`, `br2CameraBracketProjectiveHilbertMap_injective` | Realização já existente das incidências em `CarryVerticalL2`. |

A independência de incidências dentro de uma câmera não implica independência
de uma união arbitrária de câmeras. O transporte deve conservar também as
relações que já existam entre geradores.

## 4. Etapa 2 — vincular a família ao estado nativo

| Arquivo no self-adjoint | Declarações para localizar | Informação conservada / obrigação |
| --- | --- | --- |
| [DiscreteProjectiveReconstruction.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/DiscreteProjectiveReconstruction.lean) | `stateMass`, `eq_iff_boundary_and_stateMass_eq`, `reconstructionEquiv` | A massa com valor inicial e inclinação reconstrói a sequência. O bordo faz parte dos dados. |
| [GreenMultiplicativeValveBridge.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/GreenMultiplicativeValveBridge.lean) | `derivative_toProjective_greenLogPotential` | O jacobiano da mudança projetiva cancela o núcleo Green na identidade formal exata. |
| [CompletedC3ValveNaturality.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/CompletedC3ValveNaturality.lean) | `canonicalCompletedC3ValveNaturality`, `canonicalCpLogJetCommutatorSeries_eq_logScaleOrdinary`, `projectiveValveMass_canonicalCpLogBlock_eq_mul` | Canais ordinário/log-jet efetivos; relações entre canais; soma de curvaturas ↔ produto de massas. |
| [CompletedC3ValveGreenNaturality.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/CompletedC3ValveGreenNaturality.lean) | `canonicalCompletedC3ValveGreenNaturality`, `canonicalCompletedC3ValveLedgerPort_eq_structuredPort`, `canonicalCompletedC3ValveGammaState_eq_ledgerGammaState` | O ledger reconstrói o mesmo port Green e a mesma fonte Gamma; o chart escalar é o par `(-F′,F)`. |
| [CompletedC3ValveCauchyNaturalityFrontier.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/CompletedC3ValveCauchyNaturalityFrontier.lean) | `CanonicalCompletedC3ValveBoundaryNaturalityFrontier`, `canonicalCompletedC3ValveBoundaryNaturalityFrontier_iff_scalarization` | Reescreve a obrigação de compatibilidade da forma de bordo no mesmo estado; a equivalência não prova essa compatibilidade. |
| [CompletedNativeCameraUniversality.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/CompletedNativeCameraUniversality.lean) | `completedNativeCameraUniversality`, `completedNativeCameraLogDerivativeMoment_eq_canonical` | A câmera com cabeça e cauda exata dá os mesmos momentos nativos após normalização. |

A profundidade formal `X,Y`, a altura `t` e o parâmetro de resolvente são dados
distintos. A ponte deve explicitar como o estado dependente da altura produz os
coeficientes nativos; não basta renomear a variável formal. As direções da etapa
1 ainda não são identificadas como os jets de `F` por suas definições.

## 5. Etapa 3 — igualdade da forma e positividade

O kernel exigido pela rota vetorial é `dslope a`, com

$$
a(z)=-\frac{F'(z)}{2F(z)},\qquad
\widehat\Psi(z)=(\sqrt2\,F(z))^{-1}\,\mathrm{state}(z).
$$

`HasCompletedNativeRealAxisNormalizedGreenKernel state` pede, para todos os
pares reais onde `F` não se anula,

$$
\langle\widehat\Psi(x),\widehat\Psi(z)\rangle
  =\operatorname{dslope}a(x,z),
$$

incluindo a derivada no valor diagonal. A alternativa por coeficientes pede
as duas identidades Gram da seção 1 para cada `N`.

| Arquivo | Declarações para localizar | Papel exato |
| --- | --- | --- |
| [CompletedC3FinalReadoutKernelBridge.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/CompletedC3FinalReadoutKernelBridge.lean) | `canonicalCompletedC3AllCutoffOffDiagonalKernelReadout_eq`, `canonicalCompletedC3AllCutoffRealKernelReadout_eq_dslope` | O readout final normalizado é o kernel escalar correto; positividade Hilbert ainda não é uma conclusão. |
| [CompletedC3CausalGreenGramSewing.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/CompletedC3CausalGreenGramSewing.lean) | `canonicalCompletedC3RawGammaGram_eq_causalAdjointSquare`, `canonicalCompletedC3GlobalGreenReadoutIntertwining_iff_causalEnergy` | Adjunto-quadrado causal com retorno de bordo; igualdade final reduzida a uma igualdade concreta de energias. |
| [CanonicalEnrichedBoundaryResidualIdentity.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/CanonicalEnrichedBoundaryResidualIdentity.lean) | `canonicalEnrichedScalarBoundary_eq_green_iff_explicitDefects_cancel` | Cancelamento exato da soma de três canais: proveniência, cruzamentos e resíduos dos readouts. |
| [BR2GreenFrameDslopeLimitBridge.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/BR2GreenFrameDslopeLimitBridge.lean) | `canonicalCompletedGreenFrameParsevalAnalysis_inner`, `canonicalCompletedNativeParsevalGreenFrameState_inner_eq_dslope` | Parseval preserva o produto interno; a segunda declaração recebe a identificação do kernel como hipótese. |
| [CompletedGreenForwardDifferenceVectorLimit.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/CompletedGreenForwardDifferenceVectorLimit.lean) | `hasCompletedNativeGreenKernelTwoStepLimit`, `canonicalCompletedNativeGreenForwardDifferenceLimitParityJet_momentKernel` | O limite escalar conjunto já está provado. A realização Hilbert exata permite construir e identificar os jets limite. |
| [CompletedNativeProjectiveChiralCarrier.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/CompletedNativeProjectiveChiralCarrier.lean) | `canonicalCompletedNativeRadialProjectiveChiralForm_eq_dslope` | Rota alternativa pela diferença de dois Grams; exige controle do sinal. |
| [CompletedNativeRadialChiralMultiplier.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/CompletedNativeRadialChiralMultiplier.lean) | `CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive`, `canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier` | Contratilidade eventual em toda ordem mais não degenerescência é uma entrada alternativa suficiente. |

O Gram da incidência crua ou de seu transporte linear não é declarado igual a
`G_N,K_N`. A etapa 3 deve provar essa identificação para os dados nativos, com
todas as correções efetivas. A geometria de spans por si não define uma métrica.

## 6. Etapas 4–5 — certificado e consequência espectral

- [GreenWronskianHankelBridge.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/GreenWronskianHankelBridge.lean):
  `IsGreenWronskianMomentKernelGramRepresentation` e a decomposição par/ímpar.
- [BR2IncidenceStrictPositivity.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/BR2IncidenceStrictPositivity.lean):
  `BR2BracketIncidenceJetTransport`, `even_linearIndependent`, `odd_linearIndependent`.
- [CanonicalCompletedNativeStieltjesOperator.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/CanonicalCompletedNativeStieltjesOperator.lean):
  `CanonicalCompletedNativeStieltjesPositivity`,
  `infiniteShiftedHankel_posDef_of_prefixes`,
  `completedNativeRealHPCarrierCertificate_of_stieltjesPositivity`,
  `canonicalCompletedNativeStieltjesPositivity_iff_nonempty_carrier`.
- [CompletedNativeHPGateAudit.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/CompletedNativeHPGateAudit.lean):
  `CompletedNativeRealHPCarrierCertificate`, `completedJacobiOrbit_isCyclic`.
- [CompletedNativeJacobiPointSpectrumConverse.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/CompletedNativeJacobiPointSpectrumConverse.lean):
  `completedJacobiEnergyComplexification_hasEigenvalue_iff_nativeZero`.

Sob o certificado, para `lambda > 0`, já está provado
`HasEigenvalue J_C lambda ↔ F((sqrt lambda)⁻¹) = 0`. O caso zero, espectro
contínuo, multiplicidades analíticas e transporte inverso à altura assinada
continuam sendo questões distintas desse teorema.

## 7. Repositórios auxiliares e versões

As versões efetivamente consumidas ficam em `.lake/packages/`. Preservar esses
pins até haver uma necessidade demonstrada de mudança.

| Pacote / repositório | Pin consumido | Fonte útil |
| --- | --- | --- |
| `NativeCarryC3Crosswalk` / native-carry-c3-crosswalk | `150cfc7fb08da96bf8117f15869cc2b819d593c2` | `CompletedTfvdGreenIntertwining.lean` e os ledgers C3 referidos pelas pontes acima. |
| `GreenFrame` / green-frame-theorem | `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa` | `GreenFrame/Concrete/Analysis/CanonicalParseval.lean`, `canonicalParseval`. |
| `NativeCarrySpectralWeyl` / native-carry-spectral-weyl | `298d83c9351e308a5213b9f5ac32e44087f98a9f` | Geometria das câmeras, resolventes e readouts usados nas interfaces C3. |
| `CPFormal` / primos | `65d50f6db1208708e109982ba97e1d51d3039956` | `CPFormal/Analytic/CpNativeGpreTfvdAnalysis.lean`, `CpNativeGpreTfvdProjectiveAnalysis.lean`, `CpMinimalProvenanceQuotient.lean`. |
| `CarryGeometry` / carry-geometry | `1f85b8c3ab5ded27a0782956e1ada0dd8a1b6fd4` | Dependência geométrica consumida pelas câmeras. |
| `FiniteNativeCarryOperator` | `00e9d6beb17226545abf5ddf90bbfede6c7146b0` | Bases suportadas e raios admissíveis. |

`native-carry-geometry` e `genuine-zero-uniform-atlas-energy` são repositórios
adicionais de consulta, não pins diretos deste manifesto. Na consulta anterior,
os mains eram respectivamente `43c7348908c573da826d9dba7d59102931e6a45a` e
`2f5c38321d63752f891ef99622ff0685bc62c0ce`. Confirmar novamente antes de importar
novas declarações; os checkouts avulsos do servidor podem estar atrasados.

Os anexos locais de resolvente forte, Weyl comprimido e frame de probes ficam
como mapas de pesquisa. O operador `H_log = V L V*`, `L e_n = log(n)e_n`, não é
identificado com o Jacobi dos momentos por essas notas. A observação com seis
saídas fixas também não fornece independência em toda ordem. Conservar a
família crescente e o carrier enriquecido ao usar esses resultados.

## 8. Navegação e validação de cada entrega

No servidor:

```bash
ssh llm
cd ~/carry-self-adjoint-operator
rg -n 'NOME_DA_DECLARACAO' CarrySelfAdjointOperator .lake/packages
lake build --wfail CarrySelfAdjointOperator.ProjectiveValveNativeIncidenceAudit
bash scripts/audit.sh
git diff --check
```

Cada etapa deve registrar: enunciados e hipóteses, arquivos, resultado do build,
axiomas impressos pela auditoria, commit/PR e obrigação seguinte. O CI remoto
fica com Motta após a validação no servidor e a integração autorizada.

## 9. Registro da etapa 1

Implementação: [ProjectiveValveNativeIncidence.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/891853d810135669d871ab6f0ecd2420ac1d204c/CarrySelfAdjointOperator/ProjectiveValveNativeIncidence.lean). Auditoria de dependências:
[ProjectiveValveNativeIncidenceAudit.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/891853d810135669d871ab6f0ecd2420ac1d204c/CarrySelfAdjointOperator/ProjectiveValveNativeIncidenceAudit.lean). O módulo entrou no import raiz e a
auditoria específica entrou em `scripts/audit.sh`.

| Declarações novas | Resultado verificado |
| --- | --- |
| `ProjectiveDepth.coordinateChangeLinearEquiv` | A mudança formal existente é uma equivalência linear sobre qualquer anel comutativo de coeficientes. |
| `nativeIncidenceSeries`, `nativeIncidenceSeries_injective` | Incidências reais de suporte finito entram nas séries sem perder coordenadas. |
| `nativeIncidenceProjectiveMap`, `nativeIncidenceProjectiveMap_injective` | Transporte linear injetivo para a coordenada projetiva. |
| `coeff_fromProjective_nativeIncidenceProjectiveMap` | A mudança inversa recupera exatamente cada coeficiente da incidência original. |
| `nativeIncidenceProjectiveMap_sum_eq_zero_iff` | Preserva e reflete todas as relações lineares finitas, inclusive entre câmeras. |
| `nativeBracketProjectiveCurvature_centerCoefficient` | Recupera o pivô `-2` no centro próprio e zero nos outros centros alinhados da mesma câmera. |
| `nativeBracketProjectiveCurvature_linearIndependent`, `nativeBracketProjectiveCurvature_even_linearIndependent`, `nativeBracketProjectiveCurvature_odd_linearIndependent` | Independência para qualquer família finita com índices distintos e para cada família global de paridade. |
| `nativeBracketProjectiveDirection_independent`, `nativeBracketProjectiveDirection_finiteSpan_finrank` | Direções projetivas independentes e dimensão igual à cardinalidade da família finita. |
| `nativeBracketProjectiveDirection_finiteSpan_eq_iSup_orbits` | O subgrupo multiplicativo do span é o supremo das órbitas das direções nativas. |
| `nativeIncidenceProjectiveEquivRange`, `nativeProjectiveCoreToHilbert_injective` | Equivalência sobre a imagem projetiva do núcleo de suporte finito e aplicação injetiva desse núcleo ao Hilbert TFVD existente. |
| `nativeProjectiveCoreToHilbert_incidence`, `nativeProjectiveCoreToHilbert_bracket` | O percurso projetivo chega ao mesmo estado Hilbert da construção original. |

Salvo a equivalência de coordenadas, os nomes acima estão no namespace
`CarrySelfAdjointOperator.ProjectiveValve`. As afirmações de pivô,
independência de brackets e dimensão exigem `IsSupported base` e
`radius ∈ radiusSet base`; a família finita exige índice injetivo. A
injetividade do transporte e o diagrama Hilbert valem para toda incidência de
suporte finito, sem supor independência de uma união arbitrária de câmeras.

Validação no servidor em 4 de setembro de 2026:

- Build específico com `--wfail`: passou, 8.911 jobs.
- As 26 declarações auditadas dependem somente de `propext`, `Classical.choice`
  e `Quot.sound`; nenhuma hipótese matemática foi promovida a axioma.
- Auditoria completa (`bash scripts/audit.sh`): passou, incluindo a biblioteca
  raiz, `Audit`, `BR2Audit` e `OrderAudit`; saída final `kernel audit passed`.
- Auditoria estática e revisão de whitespace: passaram; pins preservados.
- Log específico: `/tmp/carry-native-incidence-focused.log` no servidor.
- Log completo: `/tmp/carry-native-incidence-full-audit.log` no servidor.
- Branch de implementação: `agent/projective-valve-native-incidence`.
- Commit da implementação validada: [891853d](https://github.com/thiagomassensini/carry-self-adjoint-operator/commit/891853d810135669d871ab6f0ecd2420ac1d204c).
- Integração: [PR #50](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/50).

**Próxima obrigação concreta:** escolher, a partir do ledger e dos dados de
bordo, a família que produz os coeficientes de `-F′/(2F)` e provar a igualdade
polarizada com `G_N,K_N`. O transporte desta etapa fornece recuperação,
independência e um diagrama Hilbert comutativo. A identificação dessa métrica
com os momentos nativos permanece aberta; é a etapa 2 seguida da etapa 3.

Para começar a próxima sessão, abrir conjuntamente
[ProjectiveValveNativeIncidence.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/891853d810135669d871ab6f0ecd2420ac1d204c/CarrySelfAdjointOperator/ProjectiveValveNativeIncidence.lean), [CompletedC3ValveGreenNaturality.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/CompletedC3ValveGreenNaturality.lean),
[CompletedC3ValveCauchyNaturalityFrontier.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/CompletedC3ValveCauchyNaturalityFrontier.lean) e
[CompletedC3CausalGreenGramSewing.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/351ec74cc40f7d12d6f31e9450372f223dabb2bd/CarrySelfAdjointOperator/CompletedC3CausalGreenGramSewing.lean). Rastrear o mesmo estado e seus dados de
bordo até o readout final antes de extrair jets ou alegar positividade.


## 10. Tentativa seguinte — a métrica literal C3 não fecha

Em 4 de setembro de 2026, a implementação
[ProjectiveValveMomentFrontier.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/agent/projective-valve-moment-frontier/CarrySelfAdjointOperator/ProjectiveValveMomentFrontier.lean) provou que a realização literal da câmera
C3, raio 1, fornece `c(0,2)=0` e `c(1,1)=6`, embora os dois coeficientes devam
ser o mesmo `h₁` no kernel dos momentos. Isso refuta o certificado para esse
jet específico, preservando os resultados de independência da etapa 1.

A continuação exige uma nova realização do span e duas provas explícitas:

1. `c(p,0) = oddMomentResponseCoefficient h (p+1)`;
2. `c(p,q+1) = c(p+1,q)`.

A equivalência com a recorrência e o construtor do certificado sob essas
obrigações já estão formalizados. O diagnóstico completo está em
[Obrigações Lean da rota](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/agent/projective-valve-moment-frontier/docs/obrigacoes-rota-valvula-projetiva.md), com nomes das
declarações, metas efetivamente impressas e comandos de reprodução.

A identificação nativa não foi concluída. Branch da tentativa:
`agent/projective-valve-moment-frontier`; sem merge no `main`.


## 11. Peso aritmético incorporado e teste do Green ponderado

A origem do peso não ficou como hipótese nova. Em
[ProjectiveValveCarryEnergyFrontier.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/agent/projective-valve-moment-frontier/CarrySelfAdjointOperator/ProjectiveValveCarryEnergyFrontier.lean), o parâmetro do Green foi identificado
com a amplitude derivada: `q_b^k = carryAmplitude b k`, com quadrado igual a
`carryMass b k`. O produto interno TFVD foi decomposto nos quatro canais,
incluindo os cruzamentos e o retorno de bordo.

A nova realização `canonicalProjectiveCarryGreenMap` é injetiva e usa o
parâmetro canônico. Porém [ProjectiveValveCarryGreenObstruction.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/agent/projective-valve-moment-frontier/CarrySelfAdjointOperator/ProjectiveValveCarryGreenObstruction.lean) prova que
a família de respostas C3 transladadas com sementes zero também não satisfaz
a recorrência dos momentos, mesmo com esse peso. O resultado não se aplica
aos jets do estado completado com seus próprios dados de bordo.

Próxima construção: usar o estado nativo dependente da altura, transportar sua
energia ponderada completa e provar as identidades da seção 10 para seus jets.
A seção 6 do diagnóstico registra os teoremas, o teste e seu alcance.

`CarryGeometry.arithmeticCarryUniversality` já está no pin consumido e foi
incluído na auditoria. O `WeightedTransform.lean` consultado está no `main`
`3a64ccebfa3849251b2d564432d693ed19a4b74b` do `carry-geometry`, posterior ao pin
consumido; seu transporte preserva a energia comprimida, o bracket e a
recuperação da origem. Nenhum pin foi alterado nesta tentativa.

Validação final desta tentativa: 30 declarações novas e a universalidade
aritmética auditadas, somente axiomas usuais; build específico com 9.106 jobs e
auditoria completa aprovados. A identidade nativa permanece aberta.
