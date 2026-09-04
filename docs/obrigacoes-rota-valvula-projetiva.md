# Obrigações Lean — rota da válvula projetiva

## Resultado da tentativa de 4 de setembro de 2026

**A identificação com os momentos nativos não fechou.** Foi possível provar
obstruções exatas à realização Hilbert literal da etapa 1 e à família de
respostas Green ponderadas dos mesmos brackets com sementes zero. Também foi
possível separar uma realização alternativa em duas obrigações explícitas. O objetivo continua
sendo construir o carrier dos momentos nativos; esta obstrução se refere ao
mapa Hilbert atual da câmera C3, não a toda realização possível do span.

Base examinada: `main = 4de44de2341089a29665917ed48cd388c68a85e5`.
Branch de trabalho: `agent/projective-valve-moment-frontier`.

Implementação: [ProjectiveValveMomentFrontier.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/agent/projective-valve-moment-frontier/CarrySelfAdjointOperator/ProjectiveValveMomentFrontier.lean).
Auditoria: [ProjectiveValveMomentFrontierAudit.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/agent/projective-valve-moment-frontier/CarrySelfAdjointOperator/ProjectiveValveMomentFrontierAudit.lean).

## 1. O teste que impediu a identificação direta

Escreva `u_n := br2CameraBracketVerticalState 3 1 n`. Esses são os brackets
literais da câmera C3, raio 1, com pesos `1,-2,1`, realizados no Hilbert
vertical. O teorema `projectiveIncidenceRawJet_coreToHilbert` prova que o
percurso projetivo da etapa 1 chega exatamente aos mesmos `u_n`.

Defina `c(p,q) := inner ℂ u_p u_q`. O Lean provou:

| Coeficiente | Valor exato | Declaração |
| --- | --- | --- |
| `c(0,2)` | `0` | `c3_rawCoefficient_zero_two` |
| `c(1,1)` | `6` | `c3_rawCoefficient_one_one` |

Na representação nativa, os dois coeficientes devem ser o mesmo `h₁`:

$$
\langle u_0,u_2\rangle=h_1=\langle u_1,u_1\rangle.
$$

Logo, essa realização exigiria `0 = 6`. A contradição usa somente os vetores
finitos e as regras exatas do produto interno; não depende de calcular nenhum
momento nativo.

Foram compilados três resultados de impossibilidade:

- `not_c3_rawMomentEquation moments`: a realização literal não satisfaz a
  recorrência polarizada para nenhuma sequência de momentos.
- `not_c3_rawGreenMomentKernel moments`: ela também não realiza o Gram **real**
  exigido pela interface HP. Bastam a entrada par `(0,1)` e a ímpar `(0,0)`.
- `not_c3_rawHPCarrierCertificate`: o jet literal
  `br2CameraBracketProjectiveHilbertParityJet 3 1` não pode habitar o certificado.

A etapa 1 continua válida: o transporte recupera coeficientes, conserva
relações lineares e fornece independência. Para continuar, a realização
Hilbert dos coeficientes precisa mudar; trocar somente a coordenada formal e
retornar ao mesmo vetor conserva a incompatibilidade acima.

## 2. O que o Lean pede para uma nova realização

Escolher um Hilbert complexo `E` e um mapa real-linear injetivo

```lean
T : LinearMap.range nativeIncidenceProjectiveMap →ₗ[ℝ] E
hT : Function.Injective T
```

Para base suportada e raio admissível, a família considerada é

```lean
projectiveIncidenceRawJet T base radius n =
  T (nativeIncidenceProjectiveEquivRange
    (cameraBracketIncidence base radius n))
```

Seu coeficiente `projectiveIncidenceCoefficient T base radius p q` é o
produto interno complexo dos vetores de ordens `p,q` dessa família.

O novo teorema
`projectiveIncidenceMomentEquation_iff_boundary_transport` prova que a
recorrência polarizada equivale exatamente às duas metas abaixo. Esta é uma
rota suficiente para o certificado; a equivalência é com a recorrência
complexa, sem declarar que toda realização real possível precisa dessa mesma
apresentação complexa.

### Meta A — identificar os coeficientes de bordo

Saída efetiva do Lean, omitindo apenas o contexto repetido:

```lean
⊢ ∀ (p : ℕ),
    projectiveIncidenceCoefficient T base radius p 0 =
      oddMomentResponseCoefficient canonicalCompletedNativeLogDerivativeMoment (p + 1)
```

Em termos de `h := canonicalCompletedNativeLogDerivativeMoment`:

$$
c(p,0)=
\begin{cases}
h_{p/2}, & p\text{ par},\\
0, & p\text{ ímpar}.
\end{cases}
$$

Esta é a identificação com a resposta nativa `-F′/(2F)`, incluindo sua
normalização. Um Gram positivo construído de outra sequência não resolve a
meta.

### Meta B — provar a identidade de deslocamento

Saída efetiva do Lean:

```lean
⊢ ∀ (p q : ℕ),
    projectiveIncidenceCoefficient T base radius p (q + 1) =
      projectiveIncidenceCoefficient T base radius (p + 1) q
```

Ela propaga cada coeficiente pela diagonal de grau total constante:
`c(p,q) = c(p+q,0)`. Com a meta A, fornece todos os blocos `G_N`, `K_N` e a
anulação dos blocos mistos. A aplicação literal
`T = nativeProjectiveCoreToHilbert` já falha aqui, em `p=0,q=1`.

O probe que tenta essa instância termina literalmente em:

```lean
error: unsolved goals
⊢ 0 = 6
```

### Ligação comprovada com o certificado

`realHPCarrierCertificate_of_projectiveMomentEquation` recebe `T`, `hT`, base
suportada, raio admissível e a recorrência. Ele constrói o certificado real
`CompletedNativeRealHPCarrierCertificate` para a família transportada.
A independência das duas paridades vem das incidências nativas da etapa 1;
a hipótese dos momentos permanece explícita.

## 3. Peças que continuam úteis para construir T

| Fonte | Peça / obrigação |
| --- | --- |
| [CompletedC3FinalReadoutKernelBridge.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/4de44de2341089a29665917ed48cd388c68a85e5/CarrySelfAdjointOperator/CompletedC3FinalReadoutKernelBridge.lean) | `canonicalCompletedC3AllCutoffRealKernelReadout_eq_dslope` e `canonicalCompletedC3AllCutoffRealAxisKernelForwardDifference_tendsto_moment`: o ledger já fornece o kernel escalar e os coeficientes-alvo. Falta sua realização positiva. |
| [CompletedC3ValveGreenNaturality.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/4de44de2341089a29665917ed48cd388c68a85e5/CarrySelfAdjointOperator/CompletedC3ValveGreenNaturality.lean) | `canonicalCompletedC3ValveGreenNaturality`: reconstrói o mesmo port, fonte Gamma e par escalar `(-F′,F)`. A igualdade das formas finais não é uma das conclusões. |
| [CompletedC3ValveCauchyNaturalityFrontier.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/4de44de2341089a29665917ed48cd388c68a85e5/CarrySelfAdjointOperator/CompletedC3ValveCauchyNaturalityFrontier.lean) | `CanonicalCompletedC3ValveBoundaryNaturalityFrontier`: compatibilidade das formas de bordo no mesmo estado, ainda uma proposição a demonstrar. |
| [CanonicalEnrichedBoundaryResidualIdentity.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/4de44de2341089a29665917ed48cd388c68a85e5/CarrySelfAdjointOperator/CanonicalEnrichedBoundaryResidualIdentity.lean) | `canonicalEnrichedScalarBoundary_eq_green_iff_explicitDefects_cancel`: conserva proveniência, cruzamentos e correções dos readouts na igualdade exata. |
| [CompletedC3CausalGreenGramSewing.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/4de44de2341089a29665917ed48cd388c68a85e5/CarrySelfAdjointOperator/CompletedC3CausalGreenGramSewing.lean) | `canonicalCompletedC3RawGammaGram_eq_causalAdjointSquare`: Gram positivo do estado causal completo, com retorno de bordo. Identificá-lo com os momentos exige outra igualdade. |
| [CompletedNativeCausalCoefficientMomentGate.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/4de44de2341089a29665917ed48cd388c68a85e5/CarrySelfAdjointOperator/CompletedNativeCausalCoefficientMomentGate.lean) | `HasPolarizedCoefficientVectorEquation` e `complexGreenWronskianMomentKernel_of_vectorCoefficientEquation`: interface sem exigir derivadas complexas de um estado radial. |
| [CompletedNativeRadialChiralMultiplier.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/4de44de2341089a29665917ed48cd388c68a85e5/CarrySelfAdjointOperator/CompletedNativeRadialChiralMultiplier.lean) | `CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive`: entrada alternativa suficiente com não degenerescência; a desigualdade em todas as combinações finitas ainda precisa ser demonstrada. |

Próxima tentativa concreta: construir `T` a partir do ledger completo,
incluindo bordo, normalização e termos cruzados; testar primeiro
`c(0,2) = c(1,1)` e a coluna `c(p,0)`, antes de tentar a prova em todas as ordens.
Uma definição de `T` que use a positividade dos próprios momentos como
premissa devolve a obrigação original e não a fecha.

## 4. Reprodução e validação

No servidor `llm`:

```bash
cd ~/carry-self-adjoint-operator
export PATH=/home/thlinux/.elan/bin:$PATH
lake build --wfail CarrySelfAdjointOperator.ProjectiveValveMomentFrontierAudit
bash scripts/audit.sh
lake env lean /tmp/carry-projective-moment-obligations.lean
```

O último comando é um **probe diagnóstico deliberadamente incompleto**, fora
dos fontes do projeto. Ele sai com código 1 para imprimir as duas metas e a
contradição. O módulo formal e sua auditoria compilam sem metas abertas.

- Build específico final: passou, 9.106 jobs, incluindo a realização ponderada
  e sua obstrução.
- As 30 declarações novas, junto da universalidade aritmética, usam somente `propext`, `Classical.choice` e
  `Quot.sound`.
- Auditoria completa final: passou com `kernel audit passed`, incluindo a
  biblioteca raiz, `Audit`, `BR2Audit` e `OrderAudit`.
- Auditoria estática e `git diff --check`: passaram; pins preservados.
- Log do build específico: `/tmp/carry-projective-moment-focused.log`.
- Log da auditoria completa: `/tmp/carry-projective-moment-full-audit.log`.
- Probe: `/tmp/carry-projective-moment-obligations.lean`.
- Metas impressas: `/tmp/carry-projective-moment-obligations.log`.

A identificação nativa permanece aberta. Esta tentativa fica separada em
branch, sem merge no `main`.

## 5. Probe completo preservado

Para reproduzir as metas mesmo após limpar `/tmp`, salvar o bloco abaixo em
`/tmp/carry-projective-moment-obligations.lean` e executar o último comando da
seção 4 na branch da tentativa.

```lean
import CarrySelfAdjointOperator.ProjectiveValveMomentFrontier

open CarrySelfAdjointOperator CarrySelfAdjointOperator.ProjectiveValve
open FiniteNativeCarryOperator.Camera

-- Diagnostic probe: deliberately leave the two mathematical obligations open.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : LinearMap.range nativeIncidenceProjectiveMap →ₗ[ℝ] E)
    (hT : Function.Injective T)
    {base radius : ℕ} (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    CompletedNativeRealHPCarrierCertificate
      (polarizedCoefficientParityJet (projectiveIncidenceRawJet T base radius)) := by
  apply realHPCarrierCertificate_of_projectiveMomentEquation T hT hbase hradius
  rw [projectiveIncidenceMomentEquation_iff_boundary_transport]
  constructor

-- Diagnostic probe: the current realization would need this false equality.
example : projectiveIncidenceCoefficient nativeProjectiveCoreToHilbert 3 1 0 2 =
    projectiveIncidenceCoefficient nativeProjectiveCoreToHilbert 3 1 1 1 := by
  rw [c3_rawCoefficient_zero_two, c3_rawCoefficient_one_one]
```


## 6. Incorporação do peso derivado e invariante por câmera

A observação de Motta foi incorporada à tentativa. A origem do peso já é
aritmética: representação posicional, classe saturada do incremento, contagem
uniforme e raiz quadrática não negativa da massa. A cadeia está em
[CarryGeometry.Universality](https://github.com/thiagomassensini/carry-geometry/blob/1f85b8c3ab5ded27a0782956e1ada0dd8a1b6fd4/CarryGeometry/Universality.lean),
no pin efetivamente consumido pelo projeto. `arithmeticCarryUniversality`
também foi compilado e incluído na auditoria desta tentativa.

O [WeightedTransform.lean](https://github.com/thiagomassensini/carry-geometry/blob/3a64ccebfa3849251b2d564432d693ed19a4b74b/CarryGeometry/WeightedTransform.lean)
consultado está no `main` mais recente do `carry-geometry`, em
`3a64ccebfa3849251b2d564432d693ed19a4b74b`. Esse arquivo ainda não integra o pin
`1f85b8c3ab5ded27a0782956e1ada0dd8a1b6fd4`. Os pins foram preservados.

Na fonte consultada constam:

- `weightedCameraTransform_intertwines`;
- `weightedCameraTransform_preserves_compressedEnergy`;
- `weightedCameraTransform_preserves_compressedBracket`;
- `weightedEmbeddingTransform_preserves_compressedEnergy`;
- `weightedEmbeddingRetract_transform`.

Esses transportes preservam a forma comprimida da janela, com reindexação ou
extensão por zero. Pela linearidade e polarização, a energia de todas as
combinações determina também seus produtos cruzados reais. Esta última frase
é a consequência matemática da definição linear e da identidade de energia;
não atribui ao arquivo um teorema adicional de identificação com os momentos.

### 6.1 A mesma amplitude já aparece no Green efetivamente usado

Em [ProjectiveValveCarryEnergyFrontier.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/agent/projective-valve-moment-frontier/CarrySelfAdjointOperator/ProjectiveValveCarryEnergyFrontier.lean), o Lean provou:

$$
q_b^k=\operatorname{carryAmplitude}(b,k),\qquad
(q_b^k)^2=\operatorname{carryMass}(b,k),\qquad
q_b=\frac1{\sqrt b}.
$$

O núcleo do Green causal efetivo é, portanto,

$$
\mathcal G_b(r)=r\,\operatorname{carryAmplitude}(b,r),\qquad
\mathcal G_b(r)^2=r^2\,\operatorname{carryMass}(b,r).
$$

Declarações:

- `canonicalBR2CarryAmplitudeRatio_eq_carryAmplitude`;
- `canonicalBR2CarryAmplitudeRatio_pow_eq_carryAmplitude`;
- `canonicalBR2CarryAmplitudeRatio_pow_sq_eq_carryMass`;
- `canonicalCarryGreenKernel_eq_depthAmplitude`;
- `canonicalCarryGreenKernel_sq_eq_depthMass`.

Aqui `r` é a distância vertical entre camadas da fibra, conforme
`CpCarryWeightedVerticalGreen.lean`. O índice de célula do bracket e a ordem de
um jet da função de altura são índices distintos. A passagem entre eles faz
parte da identidade a provar.

### 6.2 Energia completa, incluindo cruzamentos e bordo

`canonicalCarryTfvd_inner_eq_fourChannel` prova, para quaisquer estados
`x,y` do Hilbert vertical, no parâmetro derivado `q_b`:

$$
\langle x,y\rangle=
\langle G_qB_qx,G_qB_qy\rangle+
\langle G_qB_qx,R_q\tau_qy\rangle+
\langle R_q\tau_qx,G_qB_qy\rangle+
\langle R_q\tau_qx,R_q\tau_qy\rangle.
$$

A prova usa a reconstrução exata `G_q B_q + R_q τ_q = I`. Assim, a energia e os
cruzamentos são conservados para o mesmo estado reconstruído. Ainda falta
identificar essa forma, nos estados nativos apropriados, com o kernel de
`-F′/(2F)`.

### 6.3 Teste com o Green ponderado: resultado e alcance

`canonicalProjectiveCarryGreenMap` foi construído com o Green causal já
existente e o parâmetro derivado `q_b`, sem parâmetro de peso livre.
`canonicalProjectiveCarryGreenMap_injective` prova sua injetividade;
`projectiveIncidenceRawJet_canonicalCarryGreen` identifica seus vetores com as
respostas efetivas aos brackets.

O Lean provou em [ProjectiveValveCarryGreenObstruction.lean](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/agent/projective-valve-moment-frontier/CarrySelfAdjointOperator/ProjectiveValveCarryGreenObstruction.lean):

```lean
not_br2C3CausalResponse_coefficientEquation
not_canonicalProjectiveCarryGreenMomentEquation
```

O primeiro vale para todo `0 < q < 1`; o segundo especializa o resultado em
`q = 1 / sqrt 3`. A obstrução vale para a família transladada de fontes C3 e
suas respostas causais com sementes iniciais zero.

O mecanismo é exato: o Green ponderado comuta com translações unilaterais,
que preservam produtos internos. Portanto, os três vetores `u₀,u₁,u₂` têm a
mesma norma. A igualdade `inner u₀ u₂ = inner u₁ u₁` exigida pela recorrência
forçaria `norm (u₀-u₂) = 0`; isso contradiz a injetividade do transporte das
incidências distintas. O argumento não usa aproximações dos momentos.

O construtor condicional
`realHPCarrierCertificate_of_canonicalCarryGreenMomentEquation` explicita a
entrada que seria necessária; o teste acima refuta essa entrada para esta
família C3. Ele não constitui um certificado nativo.

**Alcance:** essa prova não identifica nem refuta o estado completado nativo,
seus jets próprios ou seus dados de bordo. Ela elimina duas escolhas
específicas da família, mesmo depois de inserir o peso canônico na segunda.
A geometria métrica derivada continua disponível para a construção correta.

### 6.4 Obrigação seguinte com a origem do peso já resolvida

Construir a família a partir do estado nativo dependente da altura, com as
normalizações, derivadas/limites e seu próprio retorno de bordo. Demonstrar
que a forma de quatro canais é o kernel `dslope(-F′/(2F))`, ou satisfaz as
metas A e B para os coeficientes nativos. Depois transportar a independência
para **essa** família de jets.

A identidade não pode ser substituída pela identificação entre ordem do jet
e simples translação de um bracket: ambas as realizações transladadas
examinadas acima falham no teste formal.
