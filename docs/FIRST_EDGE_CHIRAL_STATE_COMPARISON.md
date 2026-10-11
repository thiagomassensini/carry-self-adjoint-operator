# Primeira aresta material e estado quiral completado

Data: 10/10/2026. Pesquisa e validação exclusivamente no `ssh llm`.
Baseline integrado: `65ff1aed8ceb0a4c77b4181d1799e56828396cdf`.

## Resultado e escopo

13 teoremas / 17 declarações públicas. A primeira aresta material **após o relógio**
admite um lift linear do prefixo TFVD suportado para o chart quiral original.
A resposta Green e o retorno de bordo são somados no carrier completo antes de recuperar o coeficiente. O destino mantém incident e returned.
Este é um transporte finito do chart, derivado do primeiro jet radial existente;
não certifica uma correspondência geométrica independente dos índices material e radial.
`OPEN_MATERIAL_TO_COMPLETED_CHIRAL_SOURCE_SEWING` permanece aberto.

Checkpoint local certificado: `PASS_FIRST_EDGE_CLOCKED_SOURCE_CHART_SEWING`.
Não atribuir `PASS_MATERIAL_CHIRAL_ENRICHED_SEWING` ao resultado parcial.

## Auditoria tipada

| Objeto | Domínio → contradomínio | Normalização / restrição |
|---|---|---|
| `materialJet 1` | `FiniteRealSpectralHilbert 2` → mesmo carrier | diagonal `log(j+1)`, métrica original |
| `finiteMaterialGradient 1` | carrier nodal de 2 posições → carrier de uma aresta | orientação `x₁-x₀`; não injetivo sem seed |
| `finiteSlopeCoefficientSynthesisLinearMap 1` | `Fin 1 → ℂ` → `CarryVerticalL2` | síntese TFVD existente, injetiva |
| Green + bordo | coeficientes de uma aresta → `CarryVerticalL2` | `canonicalBR2CarryAmplitudeRatio b`, câmera suportada; cada canal conservado até a soma |
| `firstEdgeSupportedTfvdLift k` | range da síntese TFVD de uma aresta → carrier quiral original | inversa tipada da síntese injetiva seguida do jet radial original; não projeção de um vetor infinito |
| `firstEdgeCoefficientLift k` | `Fin 1 → ℂ` → par quiral original | coeficiente vezes `projectiveChiralDifferenceJet k 1` |
| `radialChiralEdgeChannels k i` | `Fin 3` → carrier quiral original | amplitude, quociente e feature originais em endpoints radiais |
| forma quiral | par de estados quirais → ℂ | `½(inner incident − inner returned)`; conjugação na primeira entrada |

O carrier quiral é o produto de dois `Lp ℂ 2` sobre `unitInterval`, com forma
assinada original. O Green/Parseval concreto usa outro carrier. Nenhuma
isometria global entre esses carriers foi postulada. Base de câmera `b`, passo
radial `k`, aresta material, aresta radial `i`, cutoff e ordem de jet são índices
distintos. A identidade publicada trata dimensão material 2, ordem 1 e primeira
aresta radial; a decomposição radial isolada vale em toda aresta radial `i`.

## Decomposição independente da fonte

Escreva `Cᵢ = completedNativeRadialChiralCauchyState k i`, `Aᵢ` para a amplitude
normalizada completada e `qᵢ` para o quociente Hermite–Biehler original.
O estado original é `Pᵢ = Aᵢ • (Cᵢ, qᵢ • Cᵢ)`.
Definimos diretamente das funções originais:

- `Fᵢ = Aᵢ • (Cᵢ₊₁−Cᵢ, qᵢ • (Cᵢ₊₁−Cᵢ))`;
- `Rᴬᵢ = (Aᵢ₊₁−Aᵢ) • (Cᵢ₊₁, qᵢ • Cᵢ₊₁)`;
- `Rᑫᵢ = (0, Aᵢ₊₁(qᵢ₊₁−qᵢ) • Cᵢ₊₁)`.

Lean prova a igualdade de **estados** `Pᵢ₊₁−Pᵢ = Fᵢ+Rᴬᵢ+Rᑫᵢ`.
O residual analítico `Rᴬᵢ+Rᑫᵢ` foi definido pelos dois saltos independentes,
sem subtrair um objeto positivo ajustado. Ele é zero exatamente quando
`Aᵢ₊₁=Aᵢ` e `Aᵢ₊₁(qᵢ₊₁−qᵢ)=0`. Se `Aᵢ₊₁≠0`, exige também `qᵢ₊₁=qᵢ`.
Não há neste incremento prova de que esse residual seja não nulo para todo `k`,
nem estimativa de limite. Seu sinal não foi presumido.

Esses saltos analíticos **não** são identificados com o retorno TFVD de bordo.
Possuem proveniências e carriers distintos. O log-gap material é um coeficiente
que multiplica o estado radial completo; não se provou que o índice radial seja
uma posição material.

## Canário de seed e primeiro relógio

Com `s=x₀`, `d=x₁−x₀` e o passo radial original `hₖ`, sem alterar fases:

```text
J(x)   = s P₀ + (s+d) hₖ⁻¹ (F₀+Rᴬ₀+Rᑫ₀)
J(Lx)  = log(2) (s+d) hₖ⁻¹ (F₀+Rᴬ₀+Rᑫ₀)
Δ(Lx)₀ = log(2) (s+d).
```

O seed de `Lx` é zero por `log(1)=0`, mas a aresta clocked contém o seed
**original** `s`. Aplicar o lift ao gradiente original sem seed continuaria
violando o no-go anterior. O teorema `sourcePair_two_eq_seed_and_edge`
explicita a informação antes do relógio; a costura TFVD provada é para `J(Lx)`.

```text
x : H₂ ── L ──► Lx ── Δ ──► a : ℂ¹
                  │                 │
                  J                 Green + retorno de bordo
                  │                 │
                  ▼                 ▼
          par quiral original ◄── range(síntese TFVD₁)
                              lift do primeiro jet radial
```

`firstEdgeGreenBoundary_source_state_sewing` prova que a soma completa está
nesse range e que seu lift é **o par quiral**, não apenas seu readout.
A definição usa a inversa da síntese TFVD já injetiva, exclusivamente em sua
imagem finita, e o jet radial definido antes deste trabalho. Não se define
`ULU⁻¹`, não se altera métrica e não se descarta uma cauda arbitrária por projeção.
Nenhuma continuidade ou norma uniforme desse lift foi demonstrada.

## Pairing e obstrução métrica

Para entradas independentes `x,y`, Lean expande a forma de `J(Lx),J(Ly)` em
**nove setores**: todas as combinações dos três canais. Cada termo leva
`conj(aₓ) aᵧ`, conforme a convenção da biblioteca. O sinal incident−returned
fica intacto; a energia original é quatro vezes a parte real dessa forma.
Não se substitui a forma por um Gram positivo.

Há um novo no-go preciso: com ambas as amplitudes não nulas, não existe mapa
linear que preserve o inner e envie individualmente `e₀,e₁` materiais aos
endpoints incident completados `P₀.1,P₁.1`. O produto material é zero e o
produto dos endpoints é `conj(A₀) A₁ (k+1)/3`, não nulo.
Isso não exclui transporte não unitário enriquecido, nem trata `jet₁` como se
fosse o endpoint `P₁`. A hipótese de regularidade é explícita, não uma nova
hipótese de positividade.

## Relação com os checkpoints anteriores

Reutilizados: `sourceCoordinatePair_eq_existingSynthesis`,
`projectiveChiralDifferenceJet_zero`, `projectiveChiralDifferenceJet_one`,
`materialGradient_jet_productRule`,
`finiteWeightedSlopeGreenResponse_add_boundaryReturn`,
`finiteSlopeCoefficientSynthesisLinearMap_injective`,
`inner_completedNativeRadialChiralCauchyState`,
`projectiveChiralForm_smul`.

O comutador all-order, log-gaps, equivalência seed/gradiente e transporte C3
já estão integrados no PR #67 e não foram reprovados como novos resultados.
A nova decomposição radial confronta o mecanismo de Leibniz com amplitude
completada e quociente quiral efetivos. Dimensões 4/6 e ordens superiores têm os
resultados anteriores, mas não receberam neste incremento uma costura física
nova. Ordem zero em dimensão 2 é a identidade seed+primeiro jet; ordem um é o
lift finito provado; a correspondência geométrica all-order permanece aberta.

## Gate mínimo e limites

Construir uma correspondência geométrica independente entre os coeficientes
materiais enriquecidos e os jets radiais completados, em cutoffs e dimensões
arbitrários, preservando seed, ambos os canais, os saltos analíticos e o retorno
TFVD. Mostrar domínio/continuidade antes de passar a limite. Não transportar a
energia como isometria nodal de endpoints, que foi refutada neste modelo.

`finiteParsevalMaterialEmbedding_critical_no_limit` permanece válido.
Não se afirmou reconstrução nodal Hilbert infinita, troca de limites ou limite
uniforme em `k`. `OPEN_SOURCE_BOUNDARY_POSITIVITY_ALL_ORDER` é uma obrigação
independente, intacta. Não foram utilizados experimentos numéricos como prova.

## Assinaturas públicas

```lean
def radialChiralEdgeChannels (k i : ℕ) :
    Fin 3 → CanonicalCompletedNativeProjectiveChiralCarrier
```

```lean
def radialChiralAnalyticResidual (k i : ℕ) :
    CanonicalCompletedNativeProjectiveChiralCarrier
```

```lean
theorem radialProjectiveEdge_eq_threeChannels (k i : ℕ) :
    canonicalCompletedNativeRadialProjectiveChiralState k (i+1) -
      canonicalCompletedNativeRadialProjectiveChiralState k i =
        ∑ j : Fin 3, radialChiralEdgeChannels k i j
```

```lean
theorem radialAnalyticResidual_incident (k i : ℕ) :
    (radialChiralAnalyticResidual k i).1 =
      (completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k (i+1)) -
        completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k i)) •
        completedNativeRadialChiralCauchyState k (i+1)
```

```lean
theorem radialAnalyticResidual_returned (k i : ℕ) :
    (radialChiralAnalyticResidual k i).2 =
      ((completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k (i+1)) -
          completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k i)) *
          completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k i) +
        completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k (i+1)) *
          (completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k (i+1)) -
            completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k i))) •
        completedNativeRadialChiralCauchyState k (i+1)
```

```lean
theorem radialAnalyticResidual_zero_iff (k i : ℕ) :
    radialChiralAnalyticResidual k i = 0 ↔
      completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k (i+1)) =
        completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k i) ∧
      completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k (i+1)) *
        (completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k (i+1)) -
          completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k i)) = 0
```

```lean
theorem radialAnalyticResidual_zero_iff_regular (k i : ℕ)
    (hA : completedNativeNormalizedPositiveChiralAmplitude
      (canonicalCompletedC3RadialTiltPoint k (i+1)) ≠ 0) :
    radialChiralAnalyticResidual k i = 0 ↔
      completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k (i+1)) =
        completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k i) ∧
      completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k (i+1)) =
        completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k i)
```

```lean
theorem projectiveFirstJet_eq_threeChannels (k : ℕ) :
    projectiveChiralDifferenceJet k 1 =
      (canonicalCompletedC3RadialSecondStep k)⁻¹ •
        ∑ j : Fin 3, radialChiralEdgeChannels k 0 j
```

```lean
theorem sourcePair_two_eq_seed_and_edge (k : ℕ) (x : FiniteRealSpectralHilbert 2) :
    sourceCoordinatePair 1 k x =
      x 0 • canonicalCompletedNativeRadialProjectiveChiralState k 0 +
        (x 0 + finiteMaterialGradient 1 x 0) • projectiveChiralDifferenceJet k 1
```

```lean
def firstEdgeCoefficientLift (k : ℕ) :
    (Fin 1 → ℂ) →ₗ[ℂ] CanonicalCompletedNativeProjectiveChiralCarrier where
  toFun a
```

```lean
theorem sourcePair_clock_eq_firstPhysicalEdgeLift (k : ℕ)
    (x : FiniteRealSpectralHilbert 2) :
    sourceCoordinatePair 1 k (materialJet 1 x) =
      firstEdgeCoefficientLift k (fun q => finiteMaterialGradient 1 (materialJet 1 x) q)
```

```lean
theorem sourcePair_clock_eq_threeChannels (k : ℕ) (x : FiniteRealSpectralHilbert 2) :
    sourceCoordinatePair 1 k (materialJet 1 x) =
      ((positiveLogGap 0 * (x 0 + finiteMaterialGradient 1 x 0)) *
        (canonicalCompletedC3RadialSecondStep k)⁻¹) •
        ∑ j : Fin 3, radialChiralEdgeChannels k 0 j
```

```lean
theorem sourcePair_firstEdge_signed_nine_sectors (k : ℕ)
    (x y : FiniteRealSpectralHilbert 2) :
    let ax
```

```lean
def firstEdgeSupportedTfvdLift (k : ℕ) :
    (finiteSlopeCoefficientSynthesisLinearMap 1).range →ₗ[ℂ]
      CanonicalCompletedNativeProjectiveChiralCarrier
```

```lean
theorem firstEdgeSupportedTfvdLift_on_synthesis (k : ℕ) (a : Fin 1 → ℂ) :
    firstEdgeSupportedTfvdLift k
      ((LinearEquiv.ofInjective (finiteSlopeCoefficientSynthesisLinearMap 1)
        (finiteSlopeCoefficientSynthesisLinearMap_injective 1)) a) =
      firstEdgeCoefficientLift k a
```

```lean
theorem firstEdgeGreenBoundary_source_state_sewing
    {b : ℕ} (hb : FiniteNativeCarryOperator.Camera.IsSupported b) (k : ℕ)
    (x : FiniteRealSpectralHilbert 2) :
    let a : Fin 1 → ℂ
```

```lean
theorem no_isometric_firstNode_identification (k : ℕ)
    (hA0 : completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 0) ≠ 0)
    (hA1 : completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 1) ≠ 0) :
    ¬ ∃ T : FiniteRealSpectralHilbert 2 →ₗ[ℂ] CanonicalCompletedNativeChiralCauchyCarrier,
      (∀ x y, inner ℂ (T x) (T y) = inner ℂ x y) ∧
      T (finiteMaterialBasis (0 : Fin 2)) = (canonicalCompletedNativeRadialProjectiveChiralState k 0).1 ∧
      T (finiteMaterialBasis (1 : Fin 2)) = (canonicalCompletedNativeRadialProjectiveChiralState k 1).1
```

## Validação e publicação

Validação no servidor llm, concluída em 10/10/2026:

- `lake build --wfail CarrySelfAdjointOperator.FirstEdgeChiralStateComparison`: passou.
- `lake build --wfail CarrySelfAdjointOperator.FirstEdgeChiralStateComparisonAudit`: passou (9694 jobs).
- `lake env lean CarrySelfAdjointOperator/FirstEdgeChiralStateComparisonAudit.lean`: passou no script oficial.
- `bash scripts/static_audit.sh`: passou; cobertura exata de 17 declarações / 13 teoremas.
- `bash scripts/audit.sh`: exit 0, `kernel audit passed`; inclui root, Audit, BR2, Order e guards existentes.
- `git diff --check`: passou.
- Todos os `#print axioms` novos: apenas `propext`, `Classical.choice`, `Quot.sound`.
- Histórico do README preservado byte a byte; pins/toolchain sem alteração.
- Arquivos não rastreados preexistentes `C2OddTfvdTransport.lean` e `C2OddTfvdTransportAudit.lean` preservados.

Publicação e integração:

- Conteúdo científico: `9d47f5ec6e383ac80c1d8760d94681cb30f65c74`.
- [PR #68](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/68): MERGED por procedimento normal, sem admin/bypass.
- Merge em `main`: `2de24a47c891afb76f2bf34f73f65e25d53d0a35`; ancestralidade e igualdade dos módulos/scripts/registro com o conteúdo auditado verificadas.
- Actions no HEAD publicado: runs `38106598884` e `38106601528`, ambos `startup_failure`.
- API do [run 38106601528](https://github.com/thiagomassensini/carry-self-adjoint-operator/actions/runs/38106601528): `path=BuildFailed`, `event=pull_request`, `jobs=[]`, `total_count=0`.
- `gh run view` sugere problema de workflow, mas não informa diagnóstico específico. Não foi confirmada uma causa de YAML, quota ou cobrança; nenhum job Lean rodou em Actions.
- Antes do merge, PR `CLEAN/MERGEABLE`, sem status checks listados; API da branch informava `protected=false`. API de rulesets indisponível com HTTP 403. O merge normal foi aceito pelo GitHub, sem contorno de proteção.

A auditoria no llm não é uma execução bem-sucedida de Actions. O repositório permaneceu privado. O README e este relatório registram o checkpoint científico sem tentar incluir o SHA do próprio commit de documentação.
