# Auditoria da incidência nativa e dos primeiros ports material–quiral

Pesquisa no `ssh llm`, 11/10/2026. Repositório principal privado:
`/home/thlinux/carry-self-adjoint-operator`. Baseline:
`a1800062bfadc6f4054babbecbbaa2ac60d414ce` (`main = origin/main` no início).

37 teoremas / 55 declarações novas; 24 declarações anteriores rechecadas na auditoria de proveniência.

## Conclusão científica

**A costura física não foi fechada.** Foi formalizado um candidato independente
de `U` e do primeiro jet radial, a partir da diferença geométrica Cauchy e de
Green **mais** retorno de bordo. Esse candidato falha sob a identificação
literal das coordenadas materiais com o input radial original, mesmo mantendo
seed e ambas as pernas. Há uma expressão vetorial exata do defeito e um
contraexemplo mínimo, com primeira coordenada não nula. A regularidade usada
é a original e vale eventualmente em cada dimensão finita.

Também ficaram certificados individualmente: levantamento do stencil nativo,
bulk explícito, traços verdadeiros da half-density, defeito do relógio,
avanço geométrico com saltos completados e telescoping no carrier quiral
original. Nenhum desses PASS individuais certifica a primeira coluna de momentos.

**NO_GO_SEEDED_GEOMETRIC_PORT_LITERAL_INPUT**: somente o candidato descrito abaixo,
no carrier material geral; não é impossibilidade de toda costura enriquecida,
nem prova de que o canário constante seja um stencil de câmera.

**PASS_NATIVE_INCIDENCE_CAUCHY_BULK** e **PASS_COMPLETED_GEOMETRIC_ADVANCE_RESIDUAL**
são checkpoints de álgebra/representantes, com os domínios documentados.

## Estado dos repositórios e dependências

| Checkout | Estado inicial / papel |
|---|---|
| Principal | `main`, `a1800062...`, sincronizado; dois arquivos não rastreados preexistentes preservados |
| `native-carry-spectral-weyl` | branch `agent/relational-divisibility-gram`, HEAD `871217099a069083791738578b2e44005b31986e`; apenas consulta |
| `geometry-of-numbers` | `main`, HEAD `e1084b43533255b399b82dc307b536d7dfdca07f`; instruções locais lidas, apenas consulta |
| `primos` | branch `agent/release-v0.63.0-c3-carrier-gate`, HEAD `8c4b7fdf65a49d1d0febe8193d56e2cfb2191260`, ahead 5; `CPFormal.lean` modificado e crosswalk não rastreado preservados |

A pesquisa usa as dependências **já instaladas/pinadas** do principal:
NativeCarrySpectralWeyl `298d83c9351e308a5213b9f5ac32e44087f98a9f`, CPFormal
`65d50f6db1208708e109982ba97e1d51d3039956`. O arquivo da identidade TFVD consultado
em `primos` foi comparado byte a byte ao instalado: idêntico.
Não se integrou o PR #15 nem se mudou pin/toolchain. Nenhum worktree novo.

## Auditoria dos objetos e dos trechos existentes

Os nomes abaixo são declarações Lean efetivas, não propostas de relatórios.
A auditoria dedicada de proveniência imprime seus tipos e axiomas. Os novos
teoremas só dependem das construções originais necessárias, sem HP ou hipótese
de positividade. Nomes existentes são reutilizados, não duplicados por aliases.

| Módulo / declaração exata | Tipo, hipótese e trecho efetivamente resolvido |
|---|---|
| `FiniteMaterialTfvdJetTransport`: `MaterialCameraJets.finiteMaterialGradient`, `materialTfvdTaylorPrefix_eq_geometricGreenTaylor`, `materialTfvdTaylorPrefix_Green_response_boundary_tendsto` | `H_(N+1) →ₗ ℂ H_N`, orientação sucessor−atual; Taylor material com `(-I)^r/r!`; Green+bordo tende ao mesmo prefixo, base suportada, ordem/cutoff fixos. Não fornece mapa para jets radiais completados |
| `FiniteMultibaseMaterialJetTower`: `MaterialCameraJets.materialJet_apply`, `materialJet_pairing` | relógio original diagonal `log(i+1)` em `WithLp 2 (Fin N→ℂ)`; pairing move potência real pela primeira entrada conjugada. Não identifica Gram positivo com forma assinada |
| `ExactCutoffCameraGram`: `NativeCarryC3Crosswalk.literalFiniteCameraGram_eq_linear_add_residue` | Gram literal = cutoff × Gram periódico + bordo/defeito exato; bases ≥2. Não é uma identidade entre carriers Cauchy/TFVD |
| `RelationalLogGapCommutator`: `LogGapConnection.sourceCoordinateEnd_commutator_power` | `Module.End ℂ H_(2n)`, identidade operatorial all-order; não comuta `U` com o relógio |
| `ChiralLogGapDefectTransport`: `LogGapConnection.sourceCoordinatePair_jet_signed_defect_expansion` | fonte = base+defeito, pairing com quatro setores ordenados; candidatos de coordenadas, não proveniência física |
| `CompletedNativeChiralJetStorageTransport`: `nativeSourceChiralJetInputMatrix`, `nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource` | matriz com amplitude **uma vez**, fase `(-1)^(a/2)`, `(a! h^a)⁻¹` e pesos progressivos; síntese = `(Incident(Ux),Returned(Ux))`. Bijetividade exige regularidade, automática eventualmente em dimensão fixa |
| `CompletedNativeRadialChiralMultiplier`: `inner_completedNativeRadialChiralCauchyState` | carrier `Lp ℂ 2 volume` em `unitInterval`; Gram `(k+1)/(i+j+2)`. Igualdade incondicional, sem contractividade postulada |
| `CompletedNativeChiralReturnGreenBoundaryTower`: `ChiralReturn.radialEulerPower_green_boundary`, `radialEulerBoundaryJet_secondDifference_zero` | poderes de grau `j+1` e bordo com crosses alternados; canário `[1,-2,1]` cancela ordens 0/1. Esse peso difere da derivada da half-density |
| `CompletedNativeChiralReturnCompletionSplit`: `ChiralReturn.sourceCompanion_eq_native_add_completion`, `source_cross_eq_native_add_completion` | soma vetorial nativa+completion sob domínio crítico; skew original conserva os crosses, sem sinal inferido |
| `FirstEdgeChiralStateComparison`: `FirstEdgeSewing.radialProjectiveEdge_eq_threeChannels`, `radialAnalyticResidual_zero_iff`, `firstEdgeGreenBoundary_source_state_sewing` | decomposição de estados completa; residual zero exige condições reais sobre A/q. Lift anterior usa o jet radial como dicionário, logo não certifica produção independente dos coeficientes pelos ports |
| `MaterialChiralCoordinateCanary`: `MaterialChiralCanary.sourceCoordinateInput_two_zero`, `sourceCoordinateInput_two_one`, `sourceCoordinatePair_injective` | fórmulas exatas de U na dimensão 2; injetividade do par sob característica e coordenada HB não nulas |
| `ProjectiveValveMomentFrontier`: `ProjectiveValve.projectiveIncidenceMomentEquation_iff_boundary_transport`, `not_c3_rawMomentEquation` | gate = primeira coluna correta **e** shift; mapa raw C3 falha formalmente. As hipóteses de uma realização de momentos continuam explícitas |
| `ProjectiveValveNativeIncidence`: `ProjectiveValve.nativeIncidenceProjectiveMap_sum_eq_zero_iff`, `nativeProjectiveCoreToHilbert_bracket` | incidências reais finitas → core projetivo → carrier TFVD original; relações preservadas. Não prova primeira coluna dos momentos completados |
| `NativeMomentProjectiveValveBridge`: `derivative_completedNativeEvenFormalSeries` | formalmente `Phi' = -Q*Phi`; normalização escalar e sinal. Não é uma identificação de Gram ou de posições/alturas |
| `CompletedC3ValveNaturality`: `carryWeightedScalarFirstDifference_gauge`, `carryWeightedScalarSecondDifference_gauge` | `q≠0`; diferenças ponderadas correspondem às aditivas após gauge `q^n`. Razão vertical ≠ quociente quiral completado |
| Spectral Weyl: `NativeCarrySpectralWeyl.Camera.FiniteBridge.centeredBracketStencil`, `evalStencil_finiteStencil` | ledger livre `ℕ→₀ℤ`, seed C2 especial e todos os raios/centros; avaliação no `nativeState` é o operador publicado. É a proveniência do stencil aqui levantado |
| TFVD original: `CPFormal.Analytic.Cp.carryWeightedVerticalTfvd_identity` | para `0<q<1`, Green∘bracket + return∘trace = id no `CarryVerticalL2`; não seleciona coeficientes da completion |

### Domínios e diagrama

```text
stencil nativo em ℕ→₀ℤ (posições positivas)
     │ J_k(e_(j+1)) = sqrt(k+1) sqrt(u) u^j
     ▼
C(unitInterval,ℂ) ── toLp original ──► carrier Cauchy original
     │ multiplicação geométrica por u
     ▼
representantes radiais, seed + saltos reais A/q

H₂ ── (seed, gradiente) ──► ℂ × ℂ¹
                                │ Green + retorno de bordo (q_b)
                                ▼
                      range do prefixo TFVD₁
                                │ lift geométrico proposto, sem U/jet₁
                                ▼
                         par incident/returned
                                │ defeito vetorial exato
                                ▼
                      fonte original no input literal x
```

`FiniteRealSpectralHilbert` é o nome histórico do carrier **complexo** finito.
Base `b`, cutoff `M`, posição material `n=j+1`, raio horizontal `r`, avanço
radial `k`, ordem de jet `a` e índice de feature radial `j` não são identificados
por este diagrama. O lift físico-Cauchy é um candidato de incidência; não é
certificado como isometria da norma nodal nem como TFVD física completa.

## Levantamento da incidência e bulk

Para `p,r∈ℕ`, centro `c=p+r+1` e pernas positivas `p+1,p+2r+1`, o ledger
original é avaliado pela aplicação ℤ-linear `nativeStencilCauchyProfile`.
Sua imagem é

$$
\sqrt{k+1}\sqrt u\,u^p(1-u^r)^2
=(1-u)^2\,\sqrt{k+1}\sqrt u\,u^p
\left(\sum_{q=0}^{r-1}u^q\right)^2.
$$

`nativeBracket_profile_factor` e `nativeBracket_profile_bulk` certificam a
fatoração; `nativeCamera_profile_seed_centers` conserva o seed original e
**todos** os centros da câmera finita antes do readout. Raios permanecem dentro
do `centerStencil` original, incluindo a branch C2. A avaliação para `Lp` usa
somente o mapa original `ContinuousMap.toLp` e sua escala √(k+1).

O ponto 0 não pertence ao modelo físico positivo: a extensão total do lift
manda `atom 0` a zero explicitamente. Não se afirma injetividade no ledger
irrestrito nem identificação de um canal n=0 com n=1. A fatoração e os traços
certificados usam pernas ≥1. Não há preservação de métrica postulada.

A igualdade com a potência fracionária vale em `u>0`; a representação
`√u u^p` dá a extensão contínua correta até `u=0`. A identidade de avanço
`radialContinuousState_advance` certifica `u ψ_j = ψ_(j+1)`.

## Traços e relógios: distinções essenciais

O traço da half-density vale `f(1)=0`, e
`nativeBracket_derivative_one` prova `HasDerivAt f 0 1`. Como `u=1`, esse segundo
traço também é `(u ∂_u f)(1)=0`. A passagem complexa vem do representante real
certificado. Para o stencil clockado, os traços **sem a escala √(k+1)** são

$$
\tau_0=\log(1-r^2/c^2),\qquad
\tau_1=(c-\tfrac12)\tau_0+r\log\frac{c+r}{c-r}.
$$

Hipóteses: `c>0`, `0≤r<c`; para negatividade estrita, `r>0`.
`clockedBracket_value_one` e `clockedBracket_derivative_one` relacionam essas
fórmulas aos representantes verdadeiros, com escala √(k+1) mantida.
`firstNativeBracket_clock_realRepresentative` certifica que o canário é
produzido pelo `materialJet 1` original, não escolhido por ajuste.

O canário mínimo, posições 1/2/3, tem primeiro traço
`√(k+1) log(3/4) ≠ 0`. `firstNativeBracket_clock_no_boundaryZero_profile`
prova que seu vetor Lp não pode coincidir com nenhum perfil **de três nós**
no kernel do traço de endpoint. A prova usa a injetividade da síntese Cauchy
finita existente, não um traço artificialmente contínuo em todo Lp.
Esse no-go requer manter um canal de bordo ao aplicar o relógio à incidência;
não proíbe um transporte com seed e bordo enriquecidos.

O defeito contra multiplicação por `log(u)` é literal:

$$
J(Lb)(u)-\log u\,J(b)(u)
=\sum_{n\in\{c-r,c,c+r\}} b_n(\log n-\log u)J(e_n)(u).
$$

`clockedBracket_logCoordinate_defect` prova a identidade como função real;
o domínio físico de interpretação é `u>0`. Não foi construído um operador
infinito de `log(u)`, nem pressuposto seu domínio Lp.

O Green radial original tem `radialEulerBoundaryJet d 1=Σ d_j(j+1)`.
A derivada da half-density usa `Σ d_j(j+½)`; a diferença é **½ do traço zero**,
certificada por `radialHalfDensityTrace_eq_degreeJet_sub_half`. Não houve
mudança silenciosa de orientação ou offset.

## Avanço geométrico e completion verdadeira

Com os A/q originais, sem valores sintéticos:

$$
G_j=A_j(\psi_j,q_j\psi_j),\qquad
G_{j+1}-uG_j=
(A_{j+1}-A_j)(\psi_{j+1},q_j\psi_{j+1})+
(0,A_{j+1}(q_{j+1}-q_j)\psi_{j+1}).
$$

`completedPair_advance_residual` identifica essa expressão com o
`radialChiralAnalyticResidual` já existente. O avanço foi definido por
multiplicação de **ambas** as pernas pelo mesmo u, não por `ULU⁻¹`.
`completedPair_geometric_telescope` e `completedSource_geometric_telescope`
certificam a reconstrução de estados, inclusive no **carrier Lp original**:

$$
G_j=u^jG_0+\sum_{m=0}^{j-1}u^{j-1-m}R_m.
$$

A ação u aqui usa representantes contínuos tipados, com `continuousPairToSource`
original; não se promete um novo operador em todo Lp. Combinações finitas
transportam essa igualdade por linearidade (`map_sum`/`map_smul`), mantendo
ambas as pernas; não há uma soma de energias locais substituindo a energia
da síntese. O residual não foi identificado com o retorno vertical TFVD.
Seu limite/sinal continuam sem controle novo; o critério exato de zero é o
do PR #68, reutilizado.

## Confronto independente com U

A matriz atual tem

$$
U_{ra}=A_r\,(-1)^{\lfloor a/2\rfloor}(a!h_k^a)^{-1}w_{a,r}.
$$

A síntese incident usa `Σ (Ux)_j ψ_j` e returned usa
`Σ (Ux)_j q_j ψ_j`: **a amplitude não é multiplicada outra vez**.
Na dimensão 2, exatamente

$$
(Ux)_0=A_0(x_0-h_k^{-1}x_1),\qquad
(Ux)_1=A_1h_k^{-1}x_1.
$$

O índice radial 0 é o primeiro nó **deslocado**, `z₀=hₖ`, não a origem analítica `z=0`.
Não se confundiu essa coluna finita com o momento central ou seu limite.

`sourcePair_first_basis` certifica a primeira coluna do **input da fonte**:
`J(e₀)=G₀` em toda seção par não vazia. Isso não é a primeira coluna de momentos
produzida pelos ports físicos.

Defina `F₀=A₀(ψ₁−ψ₀,q₀(ψ₁−ψ₀))`, a diferença geométrica do grafo vestido
**com a completion do seed fixa**, e `R₀` os saltos analíticos verdadeiros.
`geometricFirstPort_channel_provenance` certifica no carrier original que
`F₀ = continuousPairToSource(u·G₀ − G₀)` no representante contínuo:
o dicionário é derivado do avanço geométrico do seed, sem recorrer ao jet ou U.

O candidato independente desta rodada é

$$
P_{\rm geom}(x)=x_0G_0+(x_1-x_0)F_0.
$$

O coeficiente `(x₁−x₀)` vem do `finiteMaterialGradient` original.
`geometricGreenBoundary_port_pair` mostra que **Green + retorno físico**
produzem o estado desse candidato no range TFVD₁; o lift foi definido pelo
F₀ geométrico, sem `U` nem `projectiveChiralDifferenceJet`.
O destino retém o quociente original do seed, não um returned sintético zero.
**Este lift ainda é um candidato algébrico entre carriers; a TFVD não escolhe
por si só esse dicionário Cauchy.**

A identidade vetorial, sem hipótese de sinal, é

$$
J(x)-P_{\rm geom}(x)
=(h_k^{-1}x_1-\Delta x_0)F_0+h_k^{-1}x_1R_0.
$$

O primeiro fator separa o problema de coordenadas/normalização radial;
o segundo multiplica completion real. Não se absorveu um deles no outro.
O candidato não foi definido como `Γ∘U`, nem o defeito foi definido por
referência a uma forma positiva. `geometricPort_signed_defect_pairing`
preserva base, os dois crosses ordenados e defeito–defeito na forma original
`½(inner incident − inner returned)`.

## Canários e escopo dos no-gos

| Dimensão | Resultado certificado |
|---|---|
| 2 | Constante `x=(1,1)` tem seed 1/gradiente 0, logo `P_geom(x)=G₀`, mas `J(x)≠G₀` sob regularidade original. Defeito no primeiro input é `−A₀h⁻¹≠0`. Comparação polarizada para x,y independentes conserva todos os setores |
| 4 | Teorema geral `sourcePair_constant_eventually_ne_seed`, instância `n=2` na auditoria: constante não é o único seed. Não foi inventado um novo lift físico de quatro nós |
| 6 | Mesmo teorema, `n=3`, instância na auditoria. Regularidade eventual fixa, não limite uniforme em n |
| 3 posições físicas | Bracket `[1,-2,1]`, traços sem relógio zerados, traço clockado `√(k+1)log(3/4)≠0` e no-go do kernel finito de bordo |

O constante pertence ao carrier material geral; não se afirmou que ele está
no span das seis câmeras. O resultado exclui a identificação **literal** do
candidato em todo esse carrier, preservando seed. Ele não exclui um mapa
entre observações seed/gradiente e input radial: a observação enriquecida já
é injetiva. O canal adicional exigido precisa reconstruir os coeficientes
radiais apropriados, em vez de ler o gradiente como se fosse o input do jet.

## Defeitos separados e próxima obrigação

| Defeito | O que está identificado / o que falta |
|---|---|
| Incidência | Fatoração e bulk exatos em posições positivas; igualdade vetorial simples. Lift não é identificado com uma isometria material |
| Relógio | Traços τ₀/τ₁ gerados, offset half-density vs grau e diferença literal `log n−log u`; sem operador infinito postulado |
| Amplitude | Canal `(A_(j+1)−A_j)` verdadeiro, não descartado; nenhuma constância ou limite novo |
| Quociente | Canal `A_(j+1)(q_(j+1)−q_j)` verdadeiro, em returned; nenhum sinal ou valor sintético |
| Normalização/input | `h⁻¹x₁−Δx₀`, fases/fatoriais de U auditados; primeira diferença não nula já no input 0 do constante |
| Bordo | Green+return mantidos; clock sai do kernel de traços do bracket. Retorno TFVD vertical ≠ residual analítico completado |
| Métrica | Cauchy Gram `(k+1)/(n+m)` ≠ norma nodal Kronecker. No-go isométrico de endpoints do PR #68 permanece; nenhuma nova métrica |
| Primeira coluna | Coluna seed do U existente confirmada **no lado fonte**; coluna de momentos exigida pela valve não obtida de ports independentes |

**OPEN_NATIVE_PORT_TO_SOURCE_FIRST_COLUMN**: derivar um mapa de coordenadas
radiais a partir do seed, dos ports materiais Green/TFVD, dos traços clockados
e da completion original, com h/fases/fatoriais justificados por proveniência.
A primeira obrigação finita é reproduzir os dois coeficientes acima **sem**
definir o mapa como U. A identidade deve ser de estados incident/returned;
um mero readout ou igualdade de Hankel não basta.

**OPEN_MATERIAL_TO_COMPLETED_CHIRAL_SOURCE_SEWING** continua aberto. A coluna de
momentos de `ProjectiveValveMomentFrontier` não foi investigada como se a
costura já estivesse fechada; seu gate (coluna+shift) segue condicional.
Não se perseguiu positividade all-order, RH ou HP. O no-go de convergência
nodal crítica anterior continua válido; nenhum limite infinito ou troca de
cutoff/dimensão/passo/ordem foi afirmado.

## Novas assinaturas públicas


### `intervalCoordinate`

[NativeIncidenceCauchyPorts.lean, linha 15](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L15)

```lean
def intervalCoordinate : C(unitInterval, ℂ)
```

### `radialContinuousState`

[NativeIncidenceCauchyPorts.lean, linha 18](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L18)

```lean
def radialContinuousState (k j : ℕ) : C(unitInterval, ℂ)
```

### `radialContinuousState_toLp`

[NativeIncidenceCauchyPorts.lean, linha 22](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L22)

```lean
theorem radialContinuousState_toLp (k j : ℕ) :
    ContinuousMap.toLp 2 volume ℂ (radialContinuousState k j) =
      completedNativeRadialChiralCauchyState k j
```

### `radialContinuousState_advance`

[NativeIncidenceCauchyPorts.lean, linha 28](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L28)

```lean
theorem radialContinuousState_advance (k j : ℕ) :
    intervalCoordinate * radialContinuousState k j = radialContinuousState k (j+1)
```

### `nativeStencilCauchyProfile`

[NativeIncidenceCauchyPorts.lean, linha 37](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L37)

```lean
def nativeStencilCauchyProfile (k : ℕ) : FormalStencil →ₗ[ℤ] C(unitInterval, ℂ)
```

### `nativeStencilCauchyProfile_atom`

[NativeIncidenceCauchyPorts.lean, linha 40](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L40)

```lean
theorem nativeStencilCauchyProfile_atom (k j : ℕ) :
    nativeStencilCauchyProfile k (atom (j+1)) = radialContinuousState k j
```

### `nativeBracket_profile_factor`

[NativeIncidenceCauchyPorts.lean, linha 45](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L45)

```lean
theorem nativeBracket_profile_factor (k p r : ℕ) :
    nativeStencilCauchyProfile k (centeredBracketStencil (p+r+1) r) =
      radialContinuousState k p * (1-intervalCoordinate^r)^2
```

### `nativeCamera_profile_seed_centers`

[NativeIncidenceCauchyPorts.lean, linha 61](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L61)

```lean
theorem nativeCamera_profile_seed_centers (k b M : ℕ) :
    nativeStencilCauchyProfile k (finiteStencil b M) =
      nativeStencilCauchyProfile k (seedStencil b) +
        ∑ i ∈ Finset.range M, nativeStencilCauchyProfile k (centerStencil b i)
```

### `nativeBracket_profile_value_one`

[NativeIncidenceCauchyPorts.lean, linha 68](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L68)

```lean
theorem nativeBracket_profile_value_one (k p r : ℕ) :
    nativeStencilCauchyProfile k (centeredBracketStencil (p+r+1) r) 1 = 0
```

### `completedContinuousPair`

[NativeIncidenceCauchyPorts.lean, linha 75](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L75)

```lean
def completedContinuousPair (k j : ℕ) : C(unitInterval, ℂ) × C(unitInterval, ℂ)
```

### `pairGeometricAdvance`

[NativeIncidenceCauchyPorts.lean, linha 81](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L81)

```lean
def pairGeometricAdvance :
    (C(unitInterval, ℂ) × C(unitInterval, ℂ)) →ₗ[ℂ]
      (C(unitInterval, ℂ) × C(unitInterval, ℂ))
```

### `completedPair_advance_residual`

[NativeIncidenceCauchyPorts.lean, linha 90](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L90)

```lean
theorem completedPair_advance_residual (k j : ℕ) :
    (ContinuousMap.toLp 2 volume ℂ
      ((completedContinuousPair k (j+1) - pairGeometricAdvance (completedContinuousPair k j)).1),
     ContinuousMap.toLp 2 volume ℂ
      ((completedContinuousPair k (j+1) - pairGeometricAdvance (completedContinuousPair k j)).2)) =
      radialChiralAnalyticResidual k j
```

### `continuousAdvanceResidual`

[NativeIncidenceCauchyPorts.lean, linha 114](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L114)

```lean
def continuousAdvanceResidual (k j : ℕ) : C(unitInterval, ℂ) × C(unitInterval, ℂ)
```

### `completedPair_geometric_telescope`

[NativeIncidenceCauchyPorts.lean, linha 117](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L117)

```lean
theorem completedPair_geometric_telescope (k j : ℕ) :
    completedContinuousPair k j =
      (pairGeometricAdvance^j) (completedContinuousPair k 0) +
        ∑ m ∈ Finset.range j, (pairGeometricAdvance^(j-1-m)) (continuousAdvanceResidual k m)
```

### `geometricFirstPortLift`

[NativeIncidenceCauchyPorts.lean, linha 142](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L142)

```lean
def geometricFirstPortLift (k : ℕ) :
    (Fin 1 → ℂ) →ₗ[ℂ] CanonicalCompletedNativeProjectiveChiralCarrier
```

### `geometricSupportedTfvdLift`

[NativeIncidenceCauchyPorts.lean, linha 148](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L148)

```lean
def geometricSupportedTfvdLift (k : ℕ) :
    (finiteSlopeCoefficientSynthesisLinearMap 1).range →ₗ[ℂ]
      CanonicalCompletedNativeProjectiveChiralCarrier
```

### `geometricSeededPortPair`

[NativeIncidenceCauchyPorts.lean, linha 156](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L156)

```lean
def geometricSeededPortPair (k : ℕ) (x : FiniteRealSpectralHilbert 2) :
    CanonicalCompletedNativeProjectiveChiralCarrier
```

### `geometricSeededPort_source_defect`

[NativeIncidenceCauchyPorts.lean, linha 163](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L163)

```lean
theorem geometricSeededPort_source_defect (k : ℕ) (x : FiniteRealSpectralHilbert 2) :
    sourceCoordinatePair 1 k x - geometricSeededPortPair k x =
      ((canonicalCompletedC3RadialSecondStep k)⁻¹ * x 1 - finiteMaterialGradient 1 x 0) •
        radialChiralEdgeChannels k 0 0 +
      ((canonicalCompletedC3RadialSecondStep k)⁻¹ * x 1) • radialChiralAnalyticResidual k 0
```

### `geometricGreenBoundary_port_pair`

[NativeIncidenceCauchyPorts.lean, linha 175](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L175)

```lean
theorem geometricGreenBoundary_port_pair
    {b : ℕ} (hb : FiniteNativeCarryOperator.Camera.IsSupported b) (k : ℕ)
    (x : FiniteRealSpectralHilbert 2) :
    let a : Fin 1 → ℂ := fun q => finiteMaterialGradient 1 x q
    let state := finiteWeightedSlopeGreenResponseLinearMap (canonicalBR2CarryAmplitudeRatio b) 1 a +
      finiteWeightedSlopeBoundaryReturnLinearMap (canonicalBR2CarryAmplitudeRatio b)
        (canonicalBR2CarryAmplitudeRatio_pos hb).le (canonicalBR2CarryAmplitudeRatio_lt_one hb) 1 a
    ∃ h : state ∈ (finiteSlopeCoefficientSynthesisLinearMap 1).range,
      x 0 • canonicalCompletedNativeRadialProjectiveChiralState k 0 +
        geometricSupportedTfvdLift k ⟨state,h⟩ = geometricSeededPortPair k x
```

### `geometricSeededPort_constant_no_go`

[NativeIncidenceCauchyPorts.lean, linha 208](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L208)

```lean
theorem geometricSeededPort_constant_no_go (k : ℕ)
    (hreg : ∀ i : Fin 2,
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    let x : FiniteRealSpectralHilbert 2 := WithLp.toLp 2 (fun _ => (1 : ℂ))
    sourceCoordinatePair 1 k x ≠ geometricSeededPortPair k x
```

### `sourcePair_first_basis`

[NativeIncidenceCauchyPorts.lean, linha 228](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L228)

```lean
theorem sourcePair_first_basis {n : ℕ} (hn : 0<n) (k : ℕ) :
    sourceCoordinatePair n k (finiteMaterialBasis (⟨0,by omega⟩ : Fin (2*n))) =
      canonicalCompletedNativeRadialProjectiveChiralState k 0
```

### `sourcePair_constant_ne_seed`

[NativeIncidenceCauchyPorts.lean, linha 250](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L250)

```lean
theorem sourcePair_constant_ne_seed {n : ℕ} (hn : 0<n) (k : ℕ)
    (hreg : ∀ i : Fin (2*n),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    sourceCoordinatePair n k (WithLp.toLp 2 (fun _ => (1 : ℂ))) ≠
      canonicalCompletedNativeRadialProjectiveChiralState k 0
```

### `sourcePair_constant_eventually_ne_seed`

[NativeIncidenceCauchyPorts.lean, linha 262](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L262)

```lean
theorem sourcePair_constant_eventually_ne_seed {n : ℕ} (hn : 0<n) :
    ∀ᶠ k : ℕ in Filter.atTop,
      sourceCoordinatePair n k (WithLp.toLp 2 (fun _ => (1 : ℂ))) ≠
        canonicalCompletedNativeRadialProjectiveChiralState k 0
```

### `geometricPortDefect`

[NativeIncidenceCauchyPorts.lean, linha 272](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L272)

```lean
def geometricPortDefect (k : ℕ) (x : FiniteRealSpectralHilbert 2) :
    CanonicalCompletedNativeProjectiveChiralCarrier
```

### `geometricPort_signed_defect_pairing`

[NativeIncidenceCauchyPorts.lean, linha 280](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L280)

```lean
theorem geometricPort_signed_defect_pairing (k : ℕ) (x y : FiniteRealSpectralHilbert 2) :
    canonicalCompletedNativeProjectiveChiralForm (sourceCoordinatePair 1 k x)
      (sourceCoordinatePair 1 k y) =
    canonicalCompletedNativeProjectiveChiralForm (geometricSeededPortPair k x)
      (geometricSeededPortPair k y) +
    canonicalCompletedNativeProjectiveChiralForm (geometricSeededPortPair k x)
      (geometricPortDefect k y) +
    canonicalCompletedNativeProjectiveChiralForm (geometricPortDefect k x)
      (geometricSeededPortPair k y) +
    canonicalCompletedNativeProjectiveChiralForm (geometricPortDefect k x)
      (geometricPortDefect k y)
```

### `constantSeed_input_first_coordinate_defect`

[NativeIncidenceCauchyPorts.lean, linha 306](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L306)

```lean
theorem constantSeed_input_first_coordinate_defect (k : ℕ) :
    sourceCoordinateInput 1 k (WithLp.toLp 2 (fun _ => (1 : ℂ))) 0 -
      sourceCoordinateInput 1 k (finiteMaterialBasis (0 : Fin 2)) 0 =
      -completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 0) *
        (canonicalCompletedC3RadialSecondStep k)⁻¹
```

### `constantSeed_input_first_coordinate_defect_ne_zero`

[NativeIncidenceCauchyPorts.lean, linha 315](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L315)

```lean
theorem constantSeed_input_first_coordinate_defect_ne_zero (k : ℕ)
    (hA : completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 0) ≠ 0) :
    sourceCoordinateInput 1 k (WithLp.toLp 2 (fun _ => (1 : ℂ))) 0 -
      sourceCoordinateInput 1 k (finiteMaterialBasis (0 : Fin 2)) 0 ≠ 0
```

### `continuousPairToSource`

[NativeIncidenceCauchyPorts.lean, linha 325](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L325)

```lean
def continuousPairToSource : (C(unitInterval, ℂ) × C(unitInterval, ℂ)) →ₗ[ℂ]
    CanonicalCompletedNativeProjectiveChiralCarrier
```

### `completedContinuousPair_toSource`

[NativeIncidenceCauchyPorts.lean, linha 331](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L331)

```lean
theorem completedContinuousPair_toSource (k j : ℕ) :
    continuousPairToSource (completedContinuousPair k j) =
      canonicalCompletedNativeRadialProjectiveChiralState k j
```

### `completedSource_geometric_telescope`

[NativeIncidenceCauchyPorts.lean, linha 341](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L341)

```lean
theorem completedSource_geometric_telescope (k j : ℕ) :
    canonicalCompletedNativeRadialProjectiveChiralState k j =
      continuousPairToSource ((pairGeometricAdvance^j) (completedContinuousPair k 0)) +
      ∑ m ∈ Finset.range j,
        continuousPairToSource ((pairGeometricAdvance^(j-1-m)) (continuousAdvanceResidual k m))
```

### `geometricFirstPort_channel_provenance`

[NativeIncidenceCauchyPorts.lean, linha 352](../CarrySelfAdjointOperator/NativeIncidenceCauchyPorts.lean#L352)

```lean
theorem geometricFirstPort_channel_provenance (k : ℕ) :
    continuousPairToSource
      (pairGeometricAdvance (completedContinuousPair k 0) - completedContinuousPair k 0) =
      radialChiralEdgeChannels k 0 0
```

### `radialRealRepresentative`

[NativeIncidenceClockBoundary.lean, linha 12](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L12)

```lean
def radialRealRepresentative (k j : ℕ) (u : ℝ) : ℝ
```

### `radialRealRepresentative_derivative_one`

[NativeIncidenceClockBoundary.lean, linha 17](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L17)

```lean
theorem radialRealRepresentative_derivative_one (k j : ℕ) :
    HasDerivAt (radialRealRepresentative k j)
      (Real.sqrt ((k : ℝ)+1) * ((j : ℝ)+1/2)) 1
```

### `nativeBracketRealRepresentative`

[NativeIncidenceClockBoundary.lean, linha 34](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L34)

```lean
def nativeBracketRealRepresentative (k p r : ℕ) (u : ℝ) : ℝ
```

### `nativeBracket_profile_realRepresentative`

[NativeIncidenceClockBoundary.lean, linha 38](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L38)

```lean
theorem nativeBracket_profile_realRepresentative (k p r : ℕ) (u : unitInterval) :
    nativeStencilCauchyProfile k (centeredBracketStencil (p+r+1) r) u =
      (nativeBracketRealRepresentative k p r (u : ℝ) : ℂ)
```

### `nativeBracket_derivative_one`

[NativeIncidenceClockBoundary.lean, linha 46](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L46)

```lean
theorem nativeBracket_derivative_one (k p r : ℕ) :
    HasDerivAt (nativeBracketRealRepresentative k p r) 0 1
```

### `nativeBracketCauchyBulk`

[NativeIncidenceClockBoundary.lean, linha 56](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L56)

```lean
def nativeBracketCauchyBulk (k p r : ℕ) : C(unitInterval, ℂ)
```

### `nativeBracket_profile_bulk`

[NativeIncidenceClockBoundary.lean, linha 59](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L59)

```lean
theorem nativeBracket_profile_bulk (k p r : ℕ) :
    nativeStencilCauchyProfile k (centeredBracketStencil (p+r+1) r) =
      (1-intervalCoordinate)^2 * nativeBracketCauchyBulk k p r
```

### `bracketMaterialClockTraces`

[NativeIncidenceClockBoundary.lean, linha 73](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L73)

```lean
def bracketMaterialClockTraces (c r : ℝ) : ℝ × ℝ
```

### `bracketClock_value_closed`

[NativeIncidenceClockBoundary.lean, linha 77](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L77)

```lean
theorem bracketClock_value_closed (c r : ℝ) (hc : 0<c) (hr : 0≤r) (hrc : r<c) :
    (bracketMaterialClockTraces c r).1 = Real.log (1-r^2/c^2)
```

### `bracketClock_derivative_closed`

[NativeIncidenceClockBoundary.lean, linha 87](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L87)

```lean
theorem bracketClock_derivative_closed (c r : ℝ) (hc : 0<c) (hr : 0≤r) (hrc : r<c) :
    (bracketMaterialClockTraces c r).2 =
      (c-1/2)*(bracketMaterialClockTraces c r).1 + r*Real.log ((c+r)/(c-r))
```

### `bracketClock_value_neg`

[NativeIncidenceClockBoundary.lean, linha 96](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L96)

```lean
theorem bracketClock_value_neg (c r : ℝ) (hr : 0<r) (hrc : r<c) :
    (bracketMaterialClockTraces c r).1 < 0
```

### `finiteMaterialCauchyProfile`

[NativeIncidenceClockBoundary.lean, linha 107](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L107)

```lean
def finiteMaterialCauchyProfile (k N : ℕ) (x : FiniteRealSpectralHilbert N) : C(unitInterval, ℂ)
```

### `finiteMaterialCauchyProfile_toLp`

[NativeIncidenceClockBoundary.lean, linha 112](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L112)

```lean
theorem finiteMaterialCauchyProfile_toLp (k N : ℕ) (x : FiniteRealSpectralHilbert N) :
    ContinuousMap.toLp 2 volume ℂ (finiteMaterialCauchyProfile k N x) =
      radialIncidentSynthesis k N (fun i => x i)
```

### `finiteMaterialCauchyProfile_clock_trace`

[NativeIncidenceClockBoundary.lean, linha 118](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L118)

```lean
theorem finiteMaterialCauchyProfile_clock_trace (k N : ℕ) (x : FiniteRealSpectralHilbert N) :
    finiteMaterialCauchyProfile k N (materialJet 1 x) 1 =
      (Real.sqrt ((k : ℝ)+1) : ℂ) *
        ∑ i : Fin N, (Real.log ((i.val+1 : ℕ) : ℝ) : ℂ) * x i
```

### `radialHalfDensityTrace_eq_degreeJet_sub_half`

[NativeIncidenceClockBoundary.lean, linha 131](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L131)

```lean
theorem radialHalfDensityTrace_eq_degreeJet_sub_half {N : ℕ} (d : Fin N → ℂ) :
    (∑ i, d i * ((i.val : ℂ)+1/2)) =
      radialEulerBoundaryJet d 1 - (1/2 : ℂ)*radialEulerBoundaryJet d 0
```

### `firstNativeBracket`

[NativeIncidenceClockBoundary.lean, linha 141](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L141)

```lean
def firstNativeBracket : FiniteRealSpectralHilbert 3
```

### `firstNativeBracket_clock_trace`

[NativeIncidenceClockBoundary.lean, linha 143](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L143)

```lean
theorem firstNativeBracket_clock_trace (k : ℕ) :
    finiteMaterialCauchyProfile k 3 (materialJet 1 firstNativeBracket) 1 =
      (Real.sqrt ((k : ℝ)+1) : ℂ) * (Real.log (3/4 : ℝ) : ℂ)
```

### `firstNativeBracket_clock_trace_ne_zero`

[NativeIncidenceClockBoundary.lean, linha 158](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L158)

```lean
theorem firstNativeBracket_clock_trace_ne_zero (k : ℕ) :
    finiteMaterialCauchyProfile k 3 (materialJet 1 firstNativeBracket) 1 ≠ 0
```

### `clockedBracketRealRepresentative`

[NativeIncidenceClockBoundary.lean, linha 168](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L168)

```lean
def clockedBracketRealRepresentative (k p r : ℕ) (u : ℝ) : ℝ
```

### `clockedBracket_value_one`

[NativeIncidenceClockBoundary.lean, linha 173](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L173)

```lean
theorem clockedBracket_value_one (k p r : ℕ) :
    clockedBracketRealRepresentative k p r 1 =
      Real.sqrt ((k : ℝ)+1) * (bracketMaterialClockTraces ((p+r+1 : ℕ) : ℝ) r).1
```

### `clockedBracket_derivative_one`

[NativeIncidenceClockBoundary.lean, linha 182](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L182)

```lean
theorem clockedBracket_derivative_one (k p r : ℕ) :
    HasDerivAt (clockedBracketRealRepresentative k p r)
      (Real.sqrt ((k : ℝ)+1) * (bracketMaterialClockTraces ((p+r+1 : ℕ) : ℝ) r).2) 1
```

### `clockedBracket_logCoordinate_defect`

[NativeIncidenceClockBoundary.lean, linha 201](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L201)

```lean
theorem clockedBracket_logCoordinate_defect (k p r : ℕ) (u : ℝ) :
    clockedBracketRealRepresentative k p r u -
      Real.log u * nativeBracketRealRepresentative k p r u =
      (Real.log ((p+1 : ℕ) : ℝ)-Real.log u)*radialRealRepresentative k p u -
      2*(Real.log ((p+r+1 : ℕ) : ℝ)-Real.log u)*radialRealRepresentative k (p+r) u +
      (Real.log ((p+2*r+1 : ℕ) : ℝ)-Real.log u)*radialRealRepresentative k (p+2*r) u
```

### `firstNativeBracket_clock_realRepresentative`

[NativeIncidenceClockBoundary.lean, linha 212](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L212)

```lean
theorem firstNativeBracket_clock_realRepresentative (k : ℕ) (u : unitInterval) :
    finiteMaterialCauchyProfile k 3 (materialJet 1 firstNativeBracket) u =
      (clockedBracketRealRepresentative k 0 1 (u : ℝ) : ℂ)
```

### `firstNativeBracket_clock_no_boundaryZero_profile`

[NativeIncidenceClockBoundary.lean, linha 227](../CarrySelfAdjointOperator/NativeIncidenceClockBoundary.lean#L227)

```lean
theorem firstNativeBracket_clock_no_boundaryZero_profile (k : ℕ)
    (y : FiniteRealSpectralHilbert 3) (hy : finiteMaterialCauchyProfile k 3 y 1 = 0) :
    ContinuousMap.toLp 2 volume ℂ (finiteMaterialCauchyProfile k 3 (materialJet 1 firstNativeBracket)) ≠
      ContinuousMap.toLp 2 volume ℂ (finiteMaterialCauchyProfile k 3 y)
```

## Auditoria e execução

A cobertura exata de todas as novas declarações é exigida por
`scripts/check_native_cauchy_ports_registry.py`, pelo registro público e pelo
`NativeIncidenceCauchyPortsAudit`. Canários 2/4/6 são exemplos do mesmo teorema,
não aliases novos. `NativeIncidenceSourceProvenanceAudit` reimprime tipos/axiomas
de 24 declarações reutilizadas, incluindo o operador TFVD original.

Verificações no llm concluídas, 11/10/2026:

- `lake build --wfail CarrySelfAdjointOperator.NativeIncidenceSourceProvenanceAudit`: passou; inclui ambos os módulos novos e auditoria de 55 declarações.
- `lake env lean` de ambos os audits, executado pelo script oficial: passou.
- `bash scripts/static_audit.sh`: passou, cobertura 55 declarações / 37 teoremas.
- `bash scripts/audit.sh`: exit 0 e `kernel audit passed`, reexecutado após a última prova de proveniência; inclui root/Audit/BR2/Order e guards anteriores.
- `git diff --check`: passou.
- Apenas subconjuntos de `propext`, `Classical.choice`, `Quot.sound`; nenhum novo axioma ou escape.
- Histórico do README byte a byte preservado; pins/toolchain sem alteração.
- Arquivos preexistentes e worktrees antigos preservados; nenhum worktree novo.

O log completo da execução final é `/tmp/native-ports-full-audit-final.log`;
auditoria de proveniência em `/tmp/native-ports-provenance-audit.log`.
O estado de Actions e SHAs será registrado após a publicação. Validação no llm
não é execução de GitHub Actions. Nenhum experimento numérico foi usado como prova.

### Dependências fundamentais por declaração

Footprints extraídos dos `#print axioms` da execução final, com guards efetivos.
As assinaturas acima registram as hipóteses matemáticas de cada declaração;
estes são os axiomas fundamentais transitivos, não hipóteses de transporte.

| Declaração nova (namespace `NativeCauchyPorts`) | Footprint |
|---|---|

| `intervalCoordinate` | `propext, Classical.choice, Quot.sound` |
| `radialContinuousState` | `propext, Classical.choice, Quot.sound` |
| `radialContinuousState_toLp` | `propext, Classical.choice, Quot.sound` |
| `radialContinuousState_advance` | `propext, Classical.choice, Quot.sound` |
| `nativeStencilCauchyProfile` | `propext, Classical.choice, Quot.sound` |
| `nativeStencilCauchyProfile_atom` | `propext, Classical.choice, Quot.sound` |
| `nativeBracket_profile_factor` | `propext, Classical.choice, Quot.sound` |
| `nativeCamera_profile_seed_centers` | `propext, Classical.choice, Quot.sound` |
| `nativeBracket_profile_value_one` | `propext, Classical.choice, Quot.sound` |
| `completedContinuousPair` | `propext, Classical.choice, Quot.sound` |
| `pairGeometricAdvance` | `propext, Classical.choice, Quot.sound` |
| `completedPair_advance_residual` | `propext, Classical.choice, Quot.sound` |
| `continuousAdvanceResidual` | `propext, Classical.choice, Quot.sound` |
| `completedPair_geometric_telescope` | `propext, Classical.choice, Quot.sound` |
| `geometricFirstPortLift` | `propext, Classical.choice, Quot.sound` |
| `geometricSupportedTfvdLift` | `propext, Classical.choice, Quot.sound` |
| `geometricSeededPortPair` | `propext, Classical.choice, Quot.sound` |
| `geometricSeededPort_source_defect` | `propext, Classical.choice, Quot.sound` |
| `geometricGreenBoundary_port_pair` | `propext, Classical.choice, Quot.sound` |
| `geometricSeededPort_constant_no_go` | `propext, Classical.choice, Quot.sound` |
| `sourcePair_first_basis` | `propext, Classical.choice, Quot.sound` |
| `sourcePair_constant_ne_seed` | `propext, Classical.choice, Quot.sound` |
| `sourcePair_constant_eventually_ne_seed` | `propext, Classical.choice, Quot.sound` |
| `geometricPortDefect` | `propext, Classical.choice, Quot.sound` |
| `geometricPort_signed_defect_pairing` | `propext, Classical.choice, Quot.sound` |
| `constantSeed_input_first_coordinate_defect` | `propext, Classical.choice, Quot.sound` |
| `constantSeed_input_first_coordinate_defect_ne_zero` | `propext, Classical.choice, Quot.sound` |
| `continuousPairToSource` | `propext, Classical.choice, Quot.sound` |
| `completedContinuousPair_toSource` | `propext, Classical.choice, Quot.sound` |
| `completedSource_geometric_telescope` | `propext, Classical.choice, Quot.sound` |
| `geometricFirstPort_channel_provenance` | `propext, Classical.choice, Quot.sound` |
| `radialRealRepresentative` | `propext, Classical.choice, Quot.sound` |
| `radialRealRepresentative_derivative_one` | `propext, Classical.choice, Quot.sound` |
| `nativeBracketRealRepresentative` | `propext, Classical.choice, Quot.sound` |
| `nativeBracket_profile_realRepresentative` | `propext, Classical.choice, Quot.sound` |
| `nativeBracket_derivative_one` | `propext, Classical.choice, Quot.sound` |
| `nativeBracketCauchyBulk` | `propext, Classical.choice, Quot.sound` |
| `nativeBracket_profile_bulk` | `propext, Classical.choice, Quot.sound` |
| `bracketMaterialClockTraces` | `propext, Classical.choice, Quot.sound` |
| `bracketClock_value_closed` | `propext, Classical.choice, Quot.sound` |
| `bracketClock_derivative_closed` | `propext, Classical.choice, Quot.sound` |
| `bracketClock_value_neg` | `propext, Classical.choice, Quot.sound` |
| `finiteMaterialCauchyProfile` | `propext, Classical.choice, Quot.sound` |
| `finiteMaterialCauchyProfile_toLp` | `propext, Classical.choice, Quot.sound` |
| `finiteMaterialCauchyProfile_clock_trace` | `propext, Classical.choice, Quot.sound` |
| `radialHalfDensityTrace_eq_degreeJet_sub_half` | `propext, Classical.choice, Quot.sound` |
| `firstNativeBracket` | `propext, Classical.choice, Quot.sound` |
| `firstNativeBracket_clock_trace` | `propext, Classical.choice, Quot.sound` |
| `firstNativeBracket_clock_trace_ne_zero` | `propext, Classical.choice, Quot.sound` |
| `clockedBracketRealRepresentative` | `propext, Classical.choice, Quot.sound` |
| `clockedBracket_value_one` | `propext, Classical.choice, Quot.sound` |
| `clockedBracket_derivative_one` | `propext, Classical.choice, Quot.sound` |
| `clockedBracket_logCoordinate_defect` | `propext, Classical.choice, Quot.sound` |
| `firstNativeBracket_clock_realRepresentative` | `propext, Classical.choice, Quot.sound` |
| `firstNativeBracket_clock_no_boundaryZero_profile` | `propext, Classical.choice, Quot.sound` |
