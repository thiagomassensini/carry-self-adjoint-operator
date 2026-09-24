# Checkpoint — válvula projetiva, momentos nativos e gate Stieltjes/HP

**Data da consolidação:** 2026-09-23
**Natureza:** checkpoint documental; este arquivo não acrescenta um theorem de
positividade.
**Checkout no momento da consolidação:** branch
`codex/six-source-center-leg-bridge-2026-09-19`, `HEAD = 3fb0c42b2d7a1184c40ee98ac6d1c66c96373b7b`.
**Importante:** o worktree já continha mudanças alheias a esta auditoria; elas
não foram alteradas para produzir este documento.

**Complemento `primos`/CPFormal:** em 2026-09-23 também foram conferidos o
repositório `/home/thlinux/primos`, os PRs #34, #40, #42 e #43 e o pin
`CPFormal = 65d50f6db1208708e109982ba97e1d51d3039956` consumido pelo manifesto
Git deste projeto. As peças pertinentes e seus guardrails estão registrados na
seção 13.

## 1. Veredito executivo

Há um registro legítimo de que a **rota canônica foi fechada**. O significado
correto desse fechamento é:

\[
\boxed{
\text{certificado HP concreto}
\Longrightarrow
\text{Stieltjes all-order}
\Longrightarrow
\text{Hankel PosDef}
\Longrightarrow
\text{Jacobi}
\Longrightarrow
J_N^{-1/2}
\Longrightarrow
\text{completion}
\Longrightarrow
\text{maximal self-adjoint}.
}
\]

O downstream do certificado está formalizado. O que **não foi localizado**,
nem no GitHub nem na arqueologia local realizada nesta data, é a descarga
incondicional do certificado para a sequência concreta
`canonicalCompletedNativeLogDerivativeMoment`.

O alvo extensional que permanece é:

```lean
CanonicalCompletedNativeStieltjesPositivity
```

isto é,

\[
\boxed{
\forall N,\quad
\operatorname{hankelGram}(h,N)>0
\quad\land\quad
\operatorname{shiftedHankel}(h,N)>0,
\qquad
h=\texttt{canonicalCompletedNativeLogDerivativeMoment}.
}
\]

A teoria da válvula projetiva e o Green causal refinam muito a localização
desse gate:

\[
\boxed{
\text{o Green/readout já recupera exatamente os momentos nativos;}
}
\]

o que falta é provar que esse readout escalar assinado é realizado como o
**Gram positivo estrito** de um carrier Hilbertiano corretamente normalizado.

Não falta reconstruir o operador, refazer Jacobi ou provar autoadjunticidade
novamente.

## 2. Três significados diferentes de “fechou”

Estes três enunciados não devem mais ser misturados.

### 2.1. Fechamento escalar/formal — provado

A característica completada, sua log-derivada, a válvula projetiva, o readout
com cauda exata e os coeficientes escalares do Wronskian estão identificados
em toda ordem.

### 2.2. Fechamento downstream — provado sob certificado

Dado `CompletedNativeRealHPCarrierCertificate`, ou diretamente
`CanonicalCompletedNativeStieltjesPositivity`, a torre Hankel/Jacobi, o
operador de alturas, a completion e os resultados de autoadjunticidade estão
formalizados.

### 2.3. Fechamento métrico concreto — não localizado

Ainda não foi encontrado um theorem sem hipótese que transforme o readout
nativo concreto em uma representação de Gram positiva estrita dos dois
Hankels em toda ordem.

Em uma linha:

\[
\boxed{
\text{fechar a máquina}
\neq
\text{descarregar a última condição concreta que alimenta a máquina}.
}
\]

## 3. Definições que fixam o alvo

Em
[`CanonicalCompletedNativeStieltjesOperator.lean`](CarrySelfAdjointOperator/CanonicalCompletedNativeStieltjesOperator.lean),
o alvo é definido por:

```lean
def CanonicalCompletedNativeStieltjesPositivity : Prop :=
  ∀ N,
    (hankelGram canonicalCompletedNativeLogDerivativeMoment N).PosDef ∧
    (shiftedHankel canonicalCompletedNativeLogDerivativeMoment N).PosDef
```

Em
[`CompletedNativeHPGateAudit.lean`](CarrySelfAdjointOperator/CompletedNativeHPGateAudit.lean),
o certificado real do carrier contém três campos materiais:

```text
momentKernel
evenIndependent
oddIndependent
```

Interpretados geometricamente:

\[
h_{i+j}=\langle e_i,e_j\rangle,
\qquad
h_{i+j+1}=\langle o_i,o_j\rangle,
\]

com independência linear global das famílias par e ímpar. A identidade de
Gram dá semidefinição positiva; a independência promove para positividade
estrita em cada seção finita.

## 4. Registro histórico recuperado

### 4.1. PR #63 e a “rota canônica fechada”

O PR mergeado #63, **“Consolidar no README a rota canônica fechada”**, é a
origem documental legítima da lembrança de fechamento. O próprio README,
porém, preserva o guardrail: o constructor concreto do certificado é um
theorem real, mas possui inputs explícitos; antes de chamar o certificado
concreto de incondicional, é necessário localizar a prova de cada input.

Portanto, a leitura historicamente consistente do PR é:

\[
\texttt{certificate}
\Longrightarrow
\text{downstream completamente fechado},
\]

e não:

\[
\text{geometria concreta}
\Longrightarrow
\texttt{certificate}
\quad\text{sem hipótese}.
\]

### 4.2. Commits e PRs que usam “all-order” corretamente

- `6258013`, **“formalize all-order Hankel positivity from Gram data”**:
  prova positividade em toda ordem a partir de representação de Gram e
  independência.
- `a7d1b7b`, **“derive strict Hankel positivity from incidence transport”**:
  transporta um certificado BR2 mais incidência para `G_N,K_N > 0` para todo
  `N`; o certificado continua sendo entrada.
- `ede8024`, **“Formalize the BR2 center-leg chain to strict finite
  self-adjointness”**: fecha independência geométrica all-base e o downstream
  até `PosDef`; o PR correspondente registra que os certificados concretos de
  identificação ainda precisavam ser construídos.
- O branch/arquivo `UnconditionalC3HeightClosureReduction.lean` preserva em
  seu cabeçalho que não está fingindo que os certificados finais concretos já
  foram construídos; seu theorem principal recebe entradas equivalentes a
  `hrep`, `heven` e `hodd`.
- O PR #48 fecha câmera → mesmos jets → mesmos momentos → mesmos Hankels em
  toda ordem. As identidades não exigem positividade; os corolários
  operatoriais mantêm as hipóteses de positividade.
- O PR #52 prova uma positividade de baixa ordem via certificados theta.
- O PR #58 leva a redução até ordem 10, mas não afirma a positividade do gate
  seguinte (`det G3` no registro histórico); a desigualdade theta de ordem 10
  permanece uma obrigação.

Esses resultados são substanciais e corretos. “All-order” neles se refere ao
alcance do transporte ou da consequência após o certificado, não a uma prova
incondicional já existente do gate concreto.

### 4.3. Torre escalar corrigida não é carrier HP

`CompletedNativeCorrectedChiralClockTower.lean` prova uma torre escalar com
coeficientes, shift, primeira coluna e unicidade. O checkpoint histórico
[`docs/CHECKPOINT_AUTO_ADJUNTO.md`](docs/CHECKPOINT_AUTO_ADJUNTO.md) adverte que
`canonicalCompletedNativeCorrectedClockTowerCoefficient` não deve ser usado
como `rawJet`: ele fornece os coeficientes escalares corretos, mas não uma
realização Hilbertiana positiva nem um
`CompletedNativeRealHPCarrierCertificate`.

## 5. Resultado da arqueologia local de 2026-09-23

A busca local incluiu fontes, refs Git, branches, stash, reflog, objetos
inalcançáveis, histórico local do editor e artefatos compilados.

Resultado congelado nesta data:

- foram encontrados **12 constructors diretos compilados** de
  `CanonicalCompletedNativeStieltjesPositivity`; todos possuem hipóteses
  materiais explícitas, como certificado, não-degenerescência, dominância
  quiral, gate radial ou equivalentes;
- foram examinados **16 commits inalcançáveis** e **114 blobs
  inalcançáveis** no clone principal;
- um blob dangling continha uma definição local da forma
  `let hpos : CanonicalCompletedNativeStieltjesPositivity := ...`, mas o
  theorem ainda recebia `greenMomentJets`, `heven` e `hodd`;
- o stash localizado continha documentação/checkpoint que marcava a
  positividade superior como aberta;
- o histórico local do editor continha apenas cópias antigas de arquivos de
  auditoria, sem um constructor incondicional novo;
- foram inspecionados **859 arquivos `.olean`**;
- os `.olean` contêm positividade incondicional de Grams de outras famílias,
  por exemplo os Grams Taylor enriquecidos, mas a identificação com os
  Hankels canônicos ainda recebe `hcoeff`, `heven`, `hodd` ou hipótese
  equivalente;
- há positividade all-order para sequências auxiliares, como
  `threeFourSixCompactMoment`, mas também há theorem explícito separando seu
  momento de ordem zero do momento nativo;
- outros clones locais consultados não forneceram o theorem incondicional.

Conclusão da arqueologia local:

\[
\boxed{
\text{não foi encontrado um commit local perdido contendo a descarga final.}
}
\]

Este é um resultado de busca, não uma impossibilidade matemática. Um objeto
apagado e já coletado pelo Git não pode ser reconstruído por essa auditoria.

## 6. A teoria da válvula projetiva está realmente fechada

O arquivo
[`NativeMomentProjectiveValveBridge.lean`](CarrySelfAdjointOperator/NativeMomentProjectiveValveBridge.lean)
é o ponto de encontro literal entre a teoria da válvula e os momentos usados
pelo operador.

Defina:

\[
\widehat\Phi(v)=\frac{\Phi(v)}{\Phi(0)},
\qquad
Q(v)=\sum_{n\ge0}h_n v^n.
\]

Os theorems relevantes são:

- `derivative_completedNativeEvenFormalSeries`:
  \(\Phi'=-Q\Phi\);
- `derivative_normalizedCompletedNativeEvenFormalSeries`:
  \(\widehat\Phi'=-Q\widehat\Phi\);
- `normalizedCompletedNativeEvenFormalSeries_eq_valveMass_neg`:
  \(\widehat\Phi=\operatorname{Valve}(-Q)\);
- `projectiveValveMass_nativeMoments_eq_reciprocal`:
  \(\operatorname{Valve}(Q)=\widehat\Phi^{-1}\);
- `projectiveValveCurvature_nativeReciprocal_eq_moments`:
  \(\operatorname{curvature}(\widehat\Phi^{-1})=Q\);
- `isNativeMomentSequence_iff_valveMass_eq_nativeReciprocal`:
  uma sequência proposta é a sequência nativa se, e somente se, sua massa de
  válvula é a recíproca normalizada nativa;
- `projectiveGreenMass_eq_nativeReciprocal_iff`:
  igualdade das massas é equivalente à igualdade das curvaturas após o
  transporte projetivo.

Não há hipótese de positividade Hankel nessas identidades.

A infraestrutura anterior também está formalizada:

- reconstrução discreta por bordo + Green;
- válvula multiplicativa e unicidade do canal;
- mudança projetiva de coordenadas e sua inversa;
- cancelamento Green–jacobiano;
- existência e unicidade da massa normalizada;
- round-trips massa ↔ curvatura;
- isomorfismo entre soma de curvaturas e produto de massas;
- fluxo, órbitas, direções projetivas, spans e incidência;
- transporte injetivo das incidências nativas ao núcleo projetivo e ao
  Hilbert TFVD.

Essa teoria não é uma ramificação lateral: ela passa exatamente pelo
\(Q\) que alimenta a torre Hankel/Jacobi.

## 7. O readout completado chega à mesma massa

Em
[`C3ProjectiveHilbertReadoutKernel.lean`](CarrySelfAdjointOperator/C3ProjectiveHilbertReadoutKernel.lean):

- `completedProjectiveStateCharacteristic_eq` identifica o readout completo,
  incluindo cabeça, cauda, fator de câmera e completion, com a característica
  nativa;
- `iteratedDeriv_completedProjectiveStateCharacteristic` identifica todos os
  jets;
- `completedProjectiveStateEvenCoefficient_eq_native` identifica todos os
  coeficientes pares;
- `completedProjectiveStateReciprocalMass_eq_native` identifica a massa do
  readout com \(\widehat\Phi^{-1}\);
- `completedProjectiveStateReciprocalMass_eq_valveNativeMoments` prova:

\[
\boxed{
\texttt{completedProjectiveStateReciprocalMass}
=
\operatorname{Valve}(Q).
}
\]

Portanto existe uma cadeia que não coloca os momentos por definição:

\[
\text{readout geométrico completado}
\longrightarrow
\Phi
\longrightarrow
\widehat\Phi^{-1}
=
\operatorname{Valve}(Q).
\]

## 8. O Green causal conhece os momentos em toda bidegree

Em
[`CompletedNativeCausalGreenProvenance.lean`](CarrySelfAdjointOperator/CompletedNativeCausalGreenProvenance.lean),
estão provados:

- resposta causal + retorno de bordo recompõe o estado gradiente;
- o adjunto-quadrado correspondente reproduz a energia nativa;
- a métrica de retorno é autoadjunta e positiva;
- `canonicalCompletedNativeCarryGreenChiralResponse_oddCoefficient_eq_moment`;
- `canonicalCompletedNativeCarryGreenChiralResponse_succCoefficient_eq_polarizedMoment`.

O último theorem afirma, para todos `M p q`:

\[
\boxed{
W_M[p+q+1]
=
\operatorname{polarizedGreenMomentCoefficient}(h,p,q).
}
\]

Assim, a obrigação restante não é perguntar se o Green sabe quais são os
momentos. Ele sabe, em toda ordem e antes de Hankel/Jacobi.

O arquivo
[`CompletedNativeCausalGreenTraceTransport.lean`](CarrySelfAdjointOperator/CompletedNativeCausalGreenTraceTransport.lean)
registra explicitamente a distinção: o Wronskian/response quiral assinado
fornece o readout escalar exato; um único carrier positivo cujo Gram seja o
kernel canônico dos momentos é uma costura mais forte.

## 9. Por que a válvula não implica Stieltjes

Na teoria da válvula, “massa” significa uma série formal normalizada e
invertível, não uma medida positiva ou um funcional positivo.

`projectiveValveMass` é definido para toda série formal admissível. Portanto
existência, unicidade e invertibilidade da válvula não podem, sozinhas,
selecionar apenas sequências Stieltjes.

Teste abstrato: uma sequência com `m₀ = 1` e `m₁ = -1` possui sua massa formal
de válvula, mas sua Hankel deslocada de ordem um é `[-1]`, que não é positiva.

Logo:

\[
\boxed{
\text{massa formal correta}
\not\Rightarrow
\text{medida positiva}
\not\Rightarrow
\text{Hankel PosDef}.
}
\]

## 10. O kernel Hilbert positivo disponível não é o Gram nativo

O mesmo
[`C3ProjectiveHilbertReadoutKernel.lean`](CarrySelfAdjointOperator/C3ProjectiveHilbertReadoutKernel.lean)
prova que toda seção finita de `completedProjectiveHilbertKernel` é positiva
semidefinida. Porém também prova:

```lean
completedProjectiveHilbertKernel_zero_ne_nativeMoment
```

isto é, o valor central do kernel bruto não coincide com `h₀`.

Existem simultaneamente:

1. um kernel Hilbertiano positivo;
2. um readout escalar que recupera exatamente `Valve(Q)`;

mas ainda não existe um theorem incondicional identificando esse kernel
bruto com a polarização dos coeficientes de `Q`.

Positividade do espaço ambiente não é suficiente. É necessária a identidade
de Gram com a sequência correta e, para `PosDef`, independência estrita.

## 11. Endpoints condicionais mais claros

### 11.1. Rota do observável positivo

`completedNativeRealHPCarrierCertificate_of_positiveObservable_readoutMass`
recebe explicitamente:

```text
S simétrico
u
hcyclic : LinearIndependent (positiveObservableOrbit S u)
hmass   : Valve(positiveObservableMoment S u) = completed readout mass
```

e então produz `CompletedNativeRealHPCarrierCertificate`.

A válvula transforma a igualdade de sequências numa igualdade de massas, mas
não constrói por si o par concreto `(S,u)` nem prova `hcyclic`.

O constructor
`completedNativeRealHPCarrierCertificate_of_positiveObservable` apresenta a
mesma fronteira como vanishing de um defeito de convolução mais independência
cíclica.

### 11.2. Rota do center–leg readout

Em `CompletedNativeHPGateAudit.lean`, a proposição

```lean
HasCanonicalCompletedNativeTfvdGreenCenterLegReadout incidence jet
```

é exatamente a identidade:

\[
\operatorname{polarizedGreenMomentCoefficient}(h;i,j)
=
\langle \mathrm{jet}_i,\mathrm{jet}_j\rangle
\]

nos pares center–leg relevantes.

Dado esse readout e um transporte de incidência,
`completedNativeRealHPCarrierCertificate_of_centerLegReadout` produz o
certificado. A independência global das duas paridades vem do transporte já
formalizado.

Esta é a formulação geométrica mais concentrada da costura restante — mas ela
deve ser provada para um **carrier corrigido**. Alguns carriers literais já
foram refutados.

### 11.3. Rotas radiais/quirais

Também existem constructors a partir de contractividade radial, dominância
quiral estrita, no-leak, determinant lower bounds e gates equivalentes. Eles
são reduções válidas. Enquanto essas proposições entrarem como hipóteses, não
constituem uma descarga incondicional de Stieltjes; em vários casos o gate é
equivalente à própria positividade expandida.

## 12. No-go’s que devem ser preservados

### 12.1. Carrier C3 bruto

Em
[`ProjectiveValveMomentFrontier.lean`](CarrySelfAdjointOperator/ProjectiveValveMomentFrontier.lean):

\[
c(0,2)=0,
\qquad
c(1,1)=6.
\]

Esses dois coeficientes deveriam representar o mesmo `h₁`. Por isso estão
provados:

- `not_c3_rawMomentEquation` para qualquer sequência de momentos;
- `not_c3_rawGreenMomentKernel`;
- `not_c3_rawHPCarrierCertificate`.

### 12.2. Respostas zero-seed transladadas

Em
[`ProjectiveValveCarryGreenObstruction.lean`](CarrySelfAdjointOperator/ProjectiveValveCarryGreenObstruction.lean),
`not_canonicalProjectiveCarryGreenMomentEquation` prova que escolher o peso
canônico do carry não conserta a família C3 zero-seed transladada. A
invariância por translação é incompatível com a identidade de shift dos
momentos.

Em
[`NativeCausalCenterLegNoGoAudit.lean`](CarrySelfAdjointOperator/NativeCausalCenterLegNoGoAudit.lean),
`not_canonicalBR2CausalGreenResponse_centerLegReadout` refuta o center–leg
readout para esse jet causal zero-seed.

### 12.3. Jet BR2 projectivo literal após a torre de seis fontes

Em
[`CompletedNativeTfvdSixSourceCenterLegBridge.lean`](CarrySelfAdjointOperator/CompletedNativeTfvdSixSourceCenterLegBridge.lean):

- `nativeC3SeededClockTfvdSixSource_centerLegReadout_iff_defect_eq_zero`
  reduz a costura ao defeito entrywise explícito;
- `not_nativeC3SeededClockTfvdSixSource_centerLegReadout_projectiveHilbert`
  prova que o jet BR2 projectivo literal não satisfaz esse readout;
- o witness já aparece na amostra de ordem zero.

Consequência de engenharia:

\[
\boxed{
\text{não tentar “provar melhor” o readout para esses carriers crus;}
}
\]

a igualdade é falsa. Uma continuação válida precisa conservar o estado
completado, o retorno de bordo e a calibração métrica correta, ou construir
outro observável positivo.

## 13. Complemento auditado — peças relevantes do `primos`/CPFormal

### 13.1. Versão realmente consumida por este projeto

O `lake-manifest.json` registrado no `HEAD` deste repositório fixa:

```text
CPFormal
https://github.com/thiagomassensini/primos.git
65d50f6db1208708e109982ba97e1d51d3039956
```

Esse commit é posterior à release `v0.60.0` e contém a integração corrigida do
PR #43. Os módulos e theorems descritos abaixo não são apenas arqueologia de
branches: estão presentes no pin que o `carry-self-adjoint-operator` consome.

Durante esta conferência, o `origin` do clone `/home/thlinux/primos` foi
atualizado por fetch somente-leitura. O commit `65d50f6` continua ancestral do
`origin/main` e os módulos relevantes também estão presentes na árvore atual.

Links abaixo são fixados no commit consumido, para não depender do movimento
futuro de `main`.

### 13.2. TFVD significa reconstrução exata com bordo

No vocabulário histórico do `primos`, TFVD é literalmente **Teorema
Fundamental da Válvula Discreta**. Sua arquitetura é:

\[
\boxed{
I=\mathcal G\mathcal B+\mathsf R\operatorname{Tr}.
}
\]

O bracket/segunda diferença apaga duas coordenadas de bordo. O traço guarda
valor e inclinação iniciais, e o retorno repõe a parte afim que o Green do
bracket não enxerga. Portanto:

\[
\boxed{
\text{curvatura isolada não reconstrói o estado;}
\quad
\text{curvatura + bordo reconstrói.}
}
\]

No Hilbert vertical ponderado, isso está compilado como:

```lean
carryWeightedVerticalTfvd_identity
```

em
[`CpCarryWeightedVerticalTfvdIdentity.lean`](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpCarryWeightedVerticalTfvdIdentity.lean):

\[
G_qB_q+R_q\operatorname{Tr}_q=I,
\qquad 0<q<1.
\]

A forma multibase está em
[`CpUniversalCarryStructuralPersistence.lean`](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpUniversalCarryStructuralPersistence.lean):

```lean
baseCarryWeightedVerticalTfvd_identity
baseCarryAmplitudeRatio_eq_criticalAmplitude_one
```

Logo, para toda base material `b ≥ 2`, o peso do Green é a amplitude crítica
do primeiro nível e a mesma identidade de reconstrução vale. A estrutura não
é exclusiva de bases primas; `p : Nat.Primes` aparece depois como seleção de
observáveis Cp.

Essa peça reforça diretamente o diagnóstico do checkpoint principal: o
retorno de bordo não é decoração que possa ser descartada antes do Gram. Ele
é uma das duas componentes necessárias da inversa exata do bracket.

### 13.3. A porta TFVD finita é uma mudança invertível de coordenadas

Em
[`CpFiniteTfvdBridge.lean`](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpFiniteTfvdBridge.lean),
cada coordenada preserva o índice do bloco e os dois canais:

\[
\operatorname{through}=-\frac{L+R}{\kappa},
\qquad
\operatorname{bracket}=\frac{\omega(R-L)}{\kappa}.
\]

O theorem `tfvdDecode_encode` prova, para `κ,ω ≠ 0`:

\[
\boxed{
\operatorname{tfvdDecode}(\operatorname{tfvdEncode}(L,R))=(L,R).
}
\]

Portanto, a porta TFVD não substitui as duas arestas por um único escalar; ela
troca coordenadas sem apagar proveniência.

### 13.4. A estrutura simplética exige parear antes de sintetizar

Em
[`CpSeededTfvdSameSBoundary.lean`](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpSeededTfvdSameSBoundary.lean),
o wedge das arestas retornadas é exatamente o wedge dos canais TFVD:

```lean
sameSEdgeBoundaryWedge_decoded_eq_channelWedge
```

A forma preserva separadamente `visibleCell` e `dormantCell`, é alternada ao
trocar as pernas e zera no autopareamento.

Em
[`CpFinitePortWronskian.lean`](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpFinitePortWronskian.lean),
há um witness formal de que sintetizar primeiro e formar o Wronskiano depois
introduz interferências `m ≠ n`. O pareamento bloco a bloco, por outro lado,
produz a diagonal correta:

```lean
finiteTfvdCpGreenDiagonal_eq_finiteOrientedCpGreenFlux
```

Guardrail operacional:

\[
\boxed{
\text{parear TFVD/proveniência bloco a bloco primeiro; sintetizar depois.}
}
\]

Isso explica por que uma torre escalar ou um readout já sintetizado não pode
ser promovido automaticamente a carrier de Gram: os termos cruzados e as
coordenadas dormentes podem ter sido apagados pela compressão.

### 13.5. C2 entra na porta exatamente, mas ainda em nível finito algébrico

Em
[`CpConnectedC2TfvdPort.lean`](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpConnectedC2TfvdPort.lean),
o cumulante conectado é codificado nas quatro massas da porta enriquecida.
Após o retorno:

\[
\operatorname{visibleCell}=K_h,
\qquad
\operatorname{dormantCell}=0,
\]

e Richardson entre `h=1/2` e `h=1` recupera exatamente
`(1/2) ε_p ε_q`.

O próprio cabeçalho limita corretamente o alcance: essa é uma codificação
algébrica finita. Ela ainda não fornece um intertwiner de operadores nem a
especialização aritmética que faria um zero Genuine fechar a porta. Para o
checkpoint HP, ela confirma a genealogia C2 → cumulante → TFVD, mas não é
positividade Hankel.

### 13.6. Colagem TFVD–`G_pre` conserva a proveniência em atlas finito

Em
[`CpNativeGpreTfvdFiniteClosedRelation.lean`](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpNativeGpreTfvdFiniteClosedRelation.lean),
o bordo conjunto é:

\[
\mathbb C\times\mathbb C^S,
\]

onde a primeira coordenada é o bordo vertical TFVD e a segunda retém a
proveniência aritmética `G_pre`. A relação é fechada em cada atlas finito e as
duas projeções recuperam as relações TFVD e `G_pre` correspondentes.

Esse fechamento usa finitude dimensional. Ele não fornece automaticamente
uma cota uniforme, uma completion infinita ou um Gram dos momentos nativos.

### 13.7. Histórico auditado dos PRs #40, #42 e #43

A situação exata no GitHub, conferida em 2026-09-23, é:

| PR | Status | CI relevante | Alcance |
| --- | --- | --- | --- |
| #40, “Construct the Genuine-first finite G_pre tower collapse” | fechado, draft, não mergeado | `Build CPFormal`: **failure** | primeira construção explícita da fonte de torre a partir da proveniência |
| #42, “Certify explicit finite TFVD–G_pre tower moments” | fechado, draft, não mergeado | `Build CPFormal`: **success** | fatoração e momento TFVD/log-jet verdes, ainda com interface ativa problemática |
| #43, “Integrate explicit finite G_pre tower sources and publish v0.60.0” | **merged** | kernel e verificação da integração: **success** | integra a parte válida e repara a hipótese vacuosa |

Os drafts exigiam atividade na célula zero. O próprio kernel define a
coordenada nativa nessa célula como zero. O PR #43 não escondeu a contradição;
substituiu a família assumida por contextos canônicos explícitos:

\[
\boxed{
\operatorname{cell}=p(n+1),
\qquad
\operatorname{towerLevel}=n+1.
}
\]

Em
[`CpNativeGpreTfvdCommutatorTowerSource.lean`](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpNativeGpreTfvdCommutatorTowerSource.lean),
`nativeGpreCanonicalActiveCommutatorContext_active` prova que essas
coordenadas são realmente ativas.

Portanto não há um grande theorem verde abandonado apenas nos branches #40 ou
#42. A parte válida, com o defeito reparado, entrou no PR #43 e está no pin
consumido por este projeto.

### 13.8. A peça nova realmente importante: fonte construída antes do momento

Em
[`CpNativeGpreFiniteTowerCollapse.lean`](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpNativeGpreFiniteTowerCollapse.lean),
cada coordenada de proveniência é fatorada como:

\[
\text{kernel aritmético/canto/orientação/role}
\times
\text{perfil material da torre}.
\]

A fonte é construída no Hilbert da torre a partir da proveniência, antes do
readout. Depois se prova:

```lean
inner_nativeGpreTowerProfileVector_boundaryContextTowerSource
inner_nativeGpreTowerProfileVector_finiteBoundaryTowerSourceAt
inner_nativeGpreTowerProfileVector_finiteWeightedBoundaryTowerSourceAt
```

Assim, todo funcional real finito, inclusive ponderado, de uma fibra material
é um pareamento literal com uma fonte explicitamente extraída; a fonte não é
definida a partir do escalar-alvo.

Aplicando isso ao wedge refletido ordinário/log-jet, o theorem:

```lean
inner_nativeGpreTowerProfileVector_canonicalCpLogJetCommutatorPrefixTowerSource_eq_greenBulk
```

prova:

\[
\boxed{
\left\langle
\operatorname{towerProfile}(p,\tau),
\operatorname{prefixTowerSource}(p,\tau,M,s)
\right\rangle
=
\operatorname{finiteNativeGpreLogJetGreenBulkReadout}(p,M,s).
}
\]

Esse é um avanço de proveniência genuíno: existe um vetor construído antes da
leitura cujo pareamento produz o bulk Green finito.

### 13.9. Por que esse “tower moment” ainda não é o certificado HP

O vocábulo `moment` nessa camada não deve ser confundido com os momentos
Hankel `h_n` do `carry-self-adjoint-operator`.

O theorem anterior é:

- um pareamento entre **dois vetores em geral diferentes**, perfil e fonte;
- finito;
- especializado câmera a câmera por `p : Nat.Primes`;
- dependente de `p`, `τ`, `M` e `s` na fonte canônica;
- uma identidade para o bulk Green daquela câmera.

Ele não fornece, por si:

- um único vetor atlas-independente para todas as câmeras;
- uma órbita `S^n u` de um observável simétrico;
- as identidades `h_{i+j}=⟨e_i,e_j⟩` e
  `h_{i+j+1}=⟨o_i,o_j⟩`;
- independência das famílias correspondentes;
- positividade estrita dos Hankels canônicos.

Portanto:

\[
\boxed{
\text{fonte explícita antes do readout}
\quad\text{é relevante, mas}\quad
\text{não é ainda Gram/HP/Stieltjes}.
}
\]

O uso mais promissor dessa infraestrutura é como modelo de construção para o
carrier corrigido: extrair a fonte de dados TFVD/`G_pre` tipados, preservar os
dois canais e só depois provar a identidade com o readout nativo.

### 13.10. PR #34: conservação Bessel exata, mas a seta uniforme permanece

O PR #34, mergeado e verde, conecta reconstrução TFVD sem perda, observável
radial Green em cada cutoff e conservação Bessel/Pitágoras finita. Entre os
resultados estão:

```text
canonicalEnrichedPrimeCarryDefectProvenanceState_norm_sq_eq_finiteSeededTfvdBesselEnergy
seededTfvdFiniteBesselEnergiesBounded_iff_re_eq_half
```

O próprio PR preserva o guardrail: não prova automaticamente que um zero
Genuine produz a cota uniforme sobre todos os atlas. A obrigação restante é a
passagem de reconstruções finitas para uma única cota independente do atlas.

Essa rota é importante para a genealogia e para controle de energia, mas não
descarrega `CanonicalCompletedNativeStieltjesPositivity`.

### 13.11. Guardrail posterior: no-go do collapse same-edge bruto

O desenvolvimento posterior do `primos` chega ainda mais perto de uma fonte
global. Em
[`CpTfvdSameEdgeReflectedEnergyCollapse.lean`](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpTfvdSameEdgeReflectedEnergyCollapse.lean),
os pares ordinary/log-jet recuperam exatamente os endpoints e o gradiente
refletido. Disso é construído um único estado de energia, independente do
observável primo, lido corretamente pelo **perfil refletido** de cada câmera.

Mas
[`CpTfvdSameEdgeReflectedEnergyFixedTimeNoGo.lean`](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpTfvdSameEdgeReflectedEnergyFixedTimeNoGo.lean)
prova que esse estado bruto não pode ser diretamente o source de momento no
tempo nativo fixo `τ=1` no locus crítico:

```lean
isSeededTfvdGpreMomentCollapseAt_sameEdgeReflectedEnergy_not_of_critical
```

No locus crítico, o perfil refletido lê zero, enquanto o perfil nativo fixo lê
uma energia estritamente positiva `p⁻¹ E`. A igualdade requerida é falsa.

Por isso
[`CpTfvdSameEdgeCompletedPrecompressionCollapse.lean`](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpTfvdSameEdgeCompletedPrecompressionCollapse.lean)
mantém dois canais separados:

```text
visible fixed-time channel
residual reflected precompression-energy channel
```

e prova que os readouts podem zerar enquanto o estado residual permanece não
nulo.

Esse no-go é diretamente análogo aos no-go’s do carrier bruto no
`carry-self-adjoint-operator`: um estado positivo de energia e o readout
escalar correto podem coexistir sem que o primeiro seja o Gram/momento correto
do segundo. A correção precisa conter uma operação real de
transporte/aniquilação radial ou preservar os dois canais até a costura final;
não basta renomear a energia positiva como momento.

### 13.12. O que o `primos` muda na fronteira deste checkpoint

O `primos` **não muda o veredito** sobre o theorem Stieltjes incondicional. Ele
melhora a descrição do objeto que deveria alimentá-lo:

\[
\boxed{
\text{carry}
\to
\text{bracket}
\to
\text{TFVD}
\to
\text{Green + retorno de bordo}
\to
\text{wedge/readout com proveniência}
\to
\text{fonte de torre explícita}
\to
\text{costura métrica ainda necessária}.
}
\]

Regras reutilizáveis para a próxima construção:

1. não eliminar o retorno de bordo;
2. não sintetizar antes do pareamento bloco a bloco;
3. preservar `visible` e `dormant/residual` como canais distintos;
4. construir a fonte a partir da proveniência antes de ler o momento;
5. exigir um vetor/carrier comum quando a conclusão precisa ser global;
6. testar a troca entre perfil refletido e perfil de tempo fixo — ela já falha
   para o collapse bruto;
7. só chamar de HP quando houver Gram da sequência canônica e independência,
   não apenas um pareamento perfil–fonte ou uma identidade de energia.

## 14. Estado consolidado por camada

| Camada | Estado |
| --- | --- |
| TFVD/discrete Green | formalizada |
| Válvula multiplicativa/projetiva | formalizada, invertível e única |
| Curvatura ↔ massa normalizada | equivalência formal |
| Soma ↔ produto; grupo, fluxo e órbitas | formalizados |
| Geometria projetiva de spans/incidência | formalizada |
| Incidência nativa → núcleo projetivo/Hilbert | injetiva e fiel |
| Momentos nativos `Q` → `Valve(Q)=Φ̂⁻¹` | formalizado sem positividade |
| Readout completado → mesma massa | formalizado |
| Wronskian causal → momentos polarizados em toda bidegree | formalizado |
| Resposta causal + retorno de bordo | cadeia pré-Gram formalizada |
| TFVD ponderada/multibase `G B + R Tr = I` em CPFormal | formalizada e consumida pelo pin |
| Wedge TFVD bloco a bloco → fluxo Green diagonal | formalizado |
| Proveniência `G_pre` finita → fonte de torre explícita | formalizado |
| Fonte de torre Cp → bulk Green finito câmera a câmera | formalizado |
| Fonte comum atlas-independente → todos os momentos nativos | não fornecida por essa camada |
| Collapse same-edge bruto → momento em tempo fixo | refutado no locus crítico |
| Kernel Hilbert bruto | PosSemidef, mas não é o kernel nativo |
| Gram bruto C3 = Gram dos momentos | refutado |
| Zero-seed ponderado = Gram dos momentos | refutado |
| Jet BR2 literal de seis fontes = Gram dos momentos | refutado |
| Carrier positivo corrigido = Gram nativo | aberto/não localizado |
| `CanonicalCompletedNativeStieltjesPositivity` sem hipótese | não localizado |
| Hankel/Jacobi/altura/completion após certificado | formalizado |
| Maximal self-adjoint após certificado | formalizado |

## 15. Fronteira matemática atual

Há três formas honestas de avançar.

### A. Prova direta da sequência concreta

Provar diretamente:

```lean
theorem canonicalCompletedNativeStieltjesPositivity :
    CanonicalCompletedNativeStieltjesPositivity := by
  ...
```

sem receber um gate equivalente disfarçado.

### B. Carrier TFVD/Green corrigido

Construir um `jet` que retenha corretamente resposta causal, retorno de bordo,
normalização e termos cruzados, e provar:

```lean
HasCanonicalCompletedNativeTfvdGreenCenterLegReadout incidence jet
```

com o transporte de incidência já disponível. Isso entrega o certificado e,
depois, Stieltjes all-order.

Antes de uma prova geral, testar obrigatoriamente:

- a massa de ordem zero contra `h₀`;
- `c(0,2)=c(1,1)`;
- a primeira coluna completa;
- a identidade de shift;
- se o candidato evita os no-go’s de translação.

### C. Observável positivo concreto

Construir explicitamente `S` e `u`, provar simetria, independência cíclica e:

\[
\operatorname{Valve}(\operatorname{moments}(S,u))
=
\texttt{completedProjectiveStateReciprocalMass}.
\]

A igualdade de massas então identifica todos os momentos nativos; a
independência fornece a estrita positividade.

## 16. Frases seguras para documentação futura

Podemos afirmar:

- “A rota downstream do certificado HP está fechada.”
- “A válvula projetiva identifica exatamente os momentos nativos com a massa
  recíproca normalizada da característica.”
- “O readout completado produz a mesma massa da válvula.”
- “A resposta Wronskian causal lê os momentos polarizados em toda ordem.”
- “A incidência fornece independência par/ímpar em toda ordem para os
  transports apropriados.”
- “O CPFormal constrói fontes de torre finitas a partir da proveniência
  TFVD/`G_pre` antes do readout e recupera o bulk Green câmera a câmera.”
- “A promoção do readout escalar para um Gram positivo concreto permanece um
  gate material.”
- “Dado o certificado, a torre Jacobi, a completion e a autoadjunticidade
  maximal estão formalizadas.”

Não devemos afirmar, sem um novo theorem:

- “A massa da válvula é uma medida positiva.”
- “O kernel Hilbert bruto é o kernel dos momentos nativos.”
- “As identidades all-order entre câmeras provam Hankel PosDef.”
- “A torre escalar corrigida é um `rawJet` positivo.”
- “Resposta causal + bordo já produz automaticamente o certificado HP.”
- “O `tower moment` do `primos` já é o momento Hankel canônico.”
- “As fontes Cp câmera a câmera já formam um único vetor atlas-independente.”
- “O estado same-edge de energia bruto pode ser usado diretamente como source
  no tempo nativo fixo”; há um no-go formal no locus crítico.
- “`CanonicalCompletedNativeStieltjesPositivity` está provada sem hipótese.”
- “O carrier C3 bruto ou o zero-seed ponderado só precisam de uma prova mais
  forte”; ambos possuem no-go’s formais.

## 17. Critério de encerramento real

Esta pendência só deve ser marcada como fechada quando existir uma declaração
compilada, sem receber positividade ou um equivalente, que produza uma destas
saídas:

```lean
CanonicalCompletedNativeStieltjesPositivity
```

ou

```lean
CompletedNativeRealHPCarrierCertificate concreteJet
```

com todos os inputs concretos descarregados no grafo de dependências.

Uma equivalência, redução, capstone condicional ou theorem que apenas mova o
gate para dominância quiral, contractividade, no-leak, lower bound, `hrep`,
`heven`, `hodd`, `hmass`, `hcyclic` ou `hreadout` não satisfaz sozinho esse
critério.

## 18. Conclusão canônica a preservar

\[
\boxed{
\begin{array}{c}
\text{A válvula projetiva e o Green causal identificam exatamente}\\
\text{a massa, a curvatura e os coeficientes escalares nativos.}\\[4pt]
\text{A independência all-order e todo o downstream operatorial estão prontos.}\\[4pt]
\text{O gate restante é a realização positiva estrita, corretamente}\\
\text{normalizada, desses mesmos coeficientes concretos.}
\end{array}
}
\]

Esse é o ponto que explica simultaneamente por que a memória de “fechou” é
legítima e por que o theorem final incondicional ainda não apareceu na busca.

## 19. Avanço posterior do mesmo dia — rota B como correção métrica com canal de perda

Depois da consolidação acima, a rota **B — carrier TFVD/Green corrigido** foi
escolhida como a continuação principal. O primeiro avanço está em
[`CompletedNativeTfvdGreenCorrectedMetric.lean`](CarrySelfAdjointOperator/CompletedNativeTfvdGreenCorrectedMetric.lean).

### 19.1. A métrica BR2 literal de C3 foi calculada em toda ordem

O arquivo anterior
`CompletedNativeTfvdSixSourceBr2EnergyExcess.lean` continha as contas
explícitas dos primeiros blocos de tamanhos dois e três. A nova prova global

```lean
br2C3CameraBracketVerticalState_inner
```

estabelece, para quaisquer índices naturais `i,j`:

\[
\left\langle B_i,B_j\right\rangle
=
\begin{cases}
6,&i=j,\\
0,&i\ne j.
\end{cases}
\]

Portanto a família literal completa de brackets C3, raio um, é ortogonal e
tem energia constante `6`. Isso promove as contas finitas anteriores para as
identidades all-order compiladas:

\[
\boxed{
E_N^{\mathrm{even}}=6I-H_N,
\qquad
E_N^{\mathrm{odd}}=6I-K_N,
\qquad
E_N^{\mathrm{cross}}=0.
}
\]

Os nomes Lean são:

```text
nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_evenBlock_eq
nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_oddBlock_eq
nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_crossBlock_eq_zero
```

Aqui `H_N` e `K_N` são, respectivamente, os blocos Hankel nativo e Hankel
deslocado. Essa igualdade não afirma que `H_N` ou `K_N` são positivos; ela
fixa exatamente qual energia a correção deve retirar do carrier literal.

### 19.2. A correção correta precisa ser uma compressão, não uma expansão

A nova estrutura

```lean
CanonicalCompletedNativeTfvdGreenLosslessCorrection E Loss
```

parte do carrier TFVD/Green fiel já existente e fornece dois mapas reais
lineares:

```text
correctedMap : carrier TFVD → E
lossMap      : carrier TFVD → Loss
```

com:

1. `correctedMap` injetivo, para preservar a independência das incidências;
2. a identidade de Gram polarizada

\[
\langle x,y\rangle
=
\langle Cx,Cy\rangle
+
\langle Lx,Ly\rangle.
\]

Assim, o output corrigido `C` e o canal de perda `L` formam uma decomposição
pitagórica do estado TFVD original. O sinal não é arbitrário: o momento
nativo aparece depois de **subtrair** o excesso do Gram literal.

A proposição

```lean
RealizesSixSourceEnergyExcess
```

exige que o Gram do canal `lossMap`, aplicado aos brackets com sua proveniência
original, seja exatamente o excesso de seis fontes já construído:

\[
\langle LB_i,LB_j\rangle
=
\langle B_i,B_j\rangle-C_6(i,j).
\]

O lado direito conserva o ledger TFVD/`G_pre`, completion, canais ordinário e
log-jet e os resíduos já transportados. Ele não é uma fatorização de Hankel
introduzida depois do fato.

### 19.3. Essa costura entrega exatamente o certificado final

Foi provado:

```lean
sixSourceCenterLegCoefficient_eq_corrected_inner
toRealHPCarrierCertificate
toStieltjesPositivity
```

Isto é, se o canal geométrico de perda realizar o excesso explícito, então:

\[
C_6(i,j)=\langle CB_i,CB_j\rangle
\]

em toda bidegree. A injetividade de `C` transporta automaticamente a
independência all-order das incidências. A recorrência da torre de seis fontes
identifica `C_6` com os coeficientes polarizados nativos. Logo o mesmo objeto
produz, sem hipótese adicional de Hankel/Jacobi:

```text
CompletedNativeRealHPCarrierCertificate
CanonicalCompletedNativeStieltjesPositivity
```

Essa ainda é uma redução condicional: falta construir `lossMap` a partir dos
canais TFVD/Green concretos. A melhoria é que o gate deixou de ser a igualdade
abstrata “Gram corrigido = momento”. Agora ele tem direção, sinal, carrier de
origem, lei de conservação e residual de proveniência explicitamente fixados.

### 19.4. Calibração obrigatória no grau zero

Para C3, todo candidato que satisfizer a nova interface obedece aos theorems:

```lean
loss_even_zero_norm_sq_eq_six_sub_h0
corrected_even_zero_norm_sq_eq_h0
corrected_even_zero_norm_sq_lt_raw
loss_even_zero_ne_zero
```

ou seja:

\[
\boxed{
\|LB_0\|^2=6-h_0,
\qquad
\|CB_0\|^2=h_0,
\qquad
\|CB_0\|^2<\|B_0\|^2=6.
}
\]

Consequências para a próxima construção:

- uma isometria do carrier literal não pode funcionar;
- uma inclusão ortogonal que apenas adicione canais positivos não pode
  funcionar;
- o canal de perda não pode ser zero;
- a correção deve ser uma compressão genuína, mas injetiva nas incidências;
- o primeiro teste de qualquer candidato concreto é reproduzir exatamente
  `6 - h₀` no output de perda, antes de tentar a identidade em toda ordem.

### 19.5. Nova fronteira operacional

A tarefa material mais concentrada passa a ser:

\[
\boxed{
\text{construir, dos canais TFVD/Green/}G_{\mathrm{pre}}\text{ existentes,}
\quad L
\quad\text{tal que}\quad
\langle LB_i,LB_j\rangle=E(i,j),
}
\]

junto de seu complemento corrigido injetivo `C` e da identidade pitagórica.
Se essa construção for obtida, a passagem ao certificado HP e a Stieltjes
all-order já está compilada no novo módulo.

Há uma condição necessária que deve ser testada antes de investir numa
construção complicada. Como todo Gram de um canal de perda é positivo
semidefinido, a existência desse splitting implica, em toda ordem:

\[
\boxed{
6I-H_N\succeq0,
\qquad
6I-K_N\succeq0.
}
\]

Isso foi formalizado por:

```lean
energyExcess_hankelBlocks_posSemidef
six_sub_nativeHankelBlocks_posSemidef
```

Esse upper-frame bound é **mais forte** do que a positividade Stieltjes do
alvo. Portanto a rota de compressão lossless do carrier BR2 C3 de energia `6`
pode ser refutada por uma falha de `6I-H_N` ou `6I-K_N` sem que isso refute
outra realização positiva dos momentos. O próximo teste decisivo desta rota é
provar ou refutar precisamente esses dois bounds usando os dados
TFVD/Green/`G_pre`, antes de tentar construir `lossMap` em toda generalidade.

## 20. Continuação após a interrupção — o `lossMap` reencontra o Parseval das câmeras

A observação “identidade antes de estimativa” levou à estrutura histórica

\[
R^*R+B^*B=I
\]

da câmera finita. Ela foi formalizada como continuação direta da rota B em
[`CompletedNativeTfvdCameraParsevalLossChannel.lean`](CarrySelfAdjointOperator/CompletedNativeTfvdCameraParsevalLossChannel.lean).

### 20.1. O canal corrigido e o canal complementar não precisam ser inventados

A estrutura

```lean
CanonicalCompletedNativeTfvdCameraParsevalTransport C
```

recebe somente:

1. um transporte complexo-linear `U` do carrier vertical TFVD/Green para uma
   família finita de estados;
2. a positividade definida do Gram de linhas da câmera;
3. a conservação polarizada de pairing por `U`.

Depois disso, os dois outputs são literalmente os objetos históricos:

```text
visibleMap = finiteCanonicalCameraHilbertReadout C ∘ U
blindMap   = finiteCanonicalCameraBlindProjection C ∘ U
```

e o theorem `gramSplit` prova

\[
\langle Rx,Ry\rangle+\langle Bx,By\rangle=\langle x,y\rangle.
\]

Não há construção de um Gram alvo nem uma hipótese de PSD nessa identidade.

### 20.2. O defeito exato é somente a costura do coeficiente visível

Foi definido

\[
D_{\mathrm{vis}}(i,j)
=C_6(i,j)-\langle R U B_i,R U B_j\rangle.
\]

O theorem compilado

```lean
blind_inner_eq_energyExcess_add_visibleCoefficientDefect
```

prova exatamente

\[
\boxed{
\langle B U B_i,B U B_j\rangle
=E(i,j)+D_{\mathrm{vis}}(i,j).
}
\]

Como `E = rawGram - C₆`, isto é apenas Parseval rearranjado. Em particular:

```lean
realizesSixSourceVisibleCoefficient_iff_energyExcess
```

estabelece a equivalência literal

\[
\boxed{
C_6(i,j)=\langle R U B_i,R U B_j\rangle
\iff
E(i,j)=\langle B U B_i,B U B_j\rangle.
}

Portanto a identificação visível e a identificação do `lossMap` não são dois
gates independentes. São a mesma costura escrita nos dois lados da lei de
conservação.

### 20.3. Correção importante: não exigir injetividade global do readout

A interface inicial da seção 19 exigia que `correctedMap` fosse injetivo no
carrier inteiro. Isso é forte demais para uma projeção de câmera com canal
cego não trivial. O que o certificado HP usa de fato é apenas a independência
da família de incidências visíveis.

A nova condição é:

```lean
HasVisibleIncidenceTransport
```

isto é, a existência de um `BR2BracketIncidenceJetTransport` para o jet
visível. Com essa condição estritamente mais fraca, os theorems

```lean
toRealHPCarrierCertificate
toStieltjesPositivity
```

entregam o mesmo downstream. A câmera pode ter kernel fora do span relevante;
o que ela não pode fazer é colapsar as incidências que certificam os dois
blocos Hankel.

### 20.4. Um no-go novo: o transporte `U` não pode ser separável

Foi testada a inclusão mais simples:

\[
U(x)=a\otimes x,
\]

com um perfil externo fixo de câmeras. O theorem

```lean
not_realizesSixSourceVisibleCoefficient_of_rankOneSourceTransport
```

descarta essa possibilidade. A razão é estrutural:

- os brackets BR2 `B₀` e `B₂` são ortogonais;
- uma câmera real aplicada ao mesmo perfil externo conserva esse zero;
- o coeficiente visível desejado para esse par é `h₁`;
- `h₁ ≠ 0` já está provado incondicionalmente.

Logo o transporte correto precisa **misturar o índice vertical/BR2 com o
índice de câmera ou proveniência**. Não basta copiar o estado vertical para
várias câmeras com amplitudes fixas.

Esse diagnóstico combina com os no-gos já existentes para a resposta causal
translacional: um mecanismo estacionário preserva ortogonalidade demais e não
cria os cruzamentos Hankel requeridos.

## 21. A projeção ambiente de seis câmeras já é um splitting concreto — mas é outro carrier

A arqueologia da rota encontrou
[`CompletedNativeSixCameraAmbientEnergyTest.lean`](CarrySelfAdjointOperator/CompletedNativeSixCameraAmbientEnergyTest.lean).
Esse arquivo já contém, sobre o estado ambiente normalizado real, a
decomposição concreta

\[
\widehat A(z)=V_6(z)+H_6(z),
\qquad
\langle\widehat A(z),\widehat A(w)\rangle
=\langle V_6(z),V_6(w)\rangle+
 \langle H_6(z),H_6(w)\rangle.
\]

O complementar `H₆` não é um remainder abstrato: ele é exatamente o halo
coerente global `P_global - P₆`. Isso confirma fortemente a leitura conceitual
“energia desviada para o complemento invisível”.

### 21.1. Guardrail: esse total não é ainda o `6I` literal do BR2

O lado esquerdo acima é o Gram do carrier ambiente normalizado. O repo prova
na ordem zero:

\[
\|\widehat A(0)\|^2>h_0.
\]

Ele não identifica esse Gram com `6δᵢⱼ`, e não existe hoje um transporte
isométrico do jet BR2 completo para esse estado ambiente. Portanto não é
válido concluir

\[
\langle H_6(i),H_6(j)\rangle=6\delta_{ij}-h_{i+j}
\]

apenas a partir do Parseval ambiente. Faltam precisamente:

1. o transporte `Bᵢ ↦ Âᵢ` entre os carriers;
2. a conservação do Gram bruto `6δᵢⱼ` nesse transporte;
3. a identificação do output visível com `C₆(i,j)`.

### 21.2. O teste central foi reduzido a doze coeficientes reais

O novo arquivo
[`CompletedNativeSixCameraAmbientVisibleCoefficient.lean`](CarrySelfAdjointOperator/CompletedNativeSixCameraAmbientVisibleCoefficient.lean)
remove mais uma camada do candidato ambiente. Definindo as duas análises
brancas de seis coordenadas

\[
a(z),b(z)\in\mathbb R^6,
\]

foi provada a fórmula polarizada exata

\[
\boxed{
\langle V_6(z),V_6(w)\rangle
=a(z)\!\cdot\!a(w)+b(z)\!\cdot\!b(w)
+i\bigl(a(z)\!\cdot\!b(w)-b(z)\!\cdot\!a(w)\bigr).
}
\]

O theorem central é:

```lean
norm_sq_canonicalCompletedC3NormalizedAmbientSixCameraVisibleState_zero_eq_analysis
```

e fornece

\[
\boxed{
\|V_6(0)\|^2=\|a(0)\|_{\mathbb R^6}^2+
                 \|b(0)\|_{\mathbb R^6}^2.
}
\]

Consequentemente, o gate central desse candidato concreto agora é a igualdade
finita

\[
\boxed{
\|a(0)\|^2+\|b(0)\|^2=h_0,
}

formalizada por

```lean
canonicalCompletedC3SixCameraHorizontal_central_energy_eq_excess_iff_analysis
```

Ela ainda não foi provada nem refutada. Mas já não é uma pergunta sobre uma
norma implícita no carrier Naimark infinito: é uma conta explícita com as duas
quadraturas e seis coordenadas brancas históricas.

### 21.3. Próximo alvo mínimo atualizado

Há agora dois testes concretos, em ordem:

1. **sanity-check ambiente de grau zero:** calcular as doze coordenadas acima
   e decidir se sua soma de quadrados é `h₀`;
2. **se o teste passar:** construir o transporte não separável do jet BR2 para
   a realização de câmera/proveniência e provar

   \[
   C_6(i,j)=\langle R U B_i,R U B_j\rangle
   \quad\forall i,j.
   \]

O segundo passo fecha automaticamente o Gram cego como `EnergyExcess` e,
junto da fidelidade das incidências visíveis, ativa o certificado HP e
`CanonicalCompletedNativeStieltjesPositivity`. Se o primeiro passo falhar,
ele refuta somente a projeção ambiente histórica `P₆` como realização do
canal corrigido; não refuta a arquitetura Parseval nem outra escolha
geométrica de `U`/readout.

A auditoria dos novos theorems está em
[`CompletedNativeTfvdCameraParsevalLossChannelAudit.lean`](CarrySelfAdjointOperator/CompletedNativeTfvdCameraParsevalLossChannelAudit.lean).

## 22. Transporte Parseval restrito à incidência BR2 — interface mínima e auditoria da genealogia existente

Esta seção responde à pergunta se a isometria global de
`sourceTransport` era necessária. Ela **não é** necessária para o handoff HP.

O novo módulo é
[`CompletedNativeTfvdCameraParsevalIncidenceTransport.lean`](CarrySelfAdjointOperator/CompletedNativeTfvdCameraParsevalIncidenceTransport.lean).

### 22.1. A interface mínima tem como domínio o ledger de incidências

A estrutura nova

```lean
CanonicalCompletedNativeTfvdCameraParsevalIncidenceTransport C base radius
```

substitui o mapa global

\[
U:\operatorname{CarryVerticalL2}\to
  \operatorname{FiniteHilbertFamily}(\mathrm{state},\operatorname{CarryVerticalL2})
\]

por um mapa somente real-linear

\[
U_{\rm inc}:(\mathbb N\to_0\mathbb R)\to
  \operatorname{FiniteHilbertFamily}(\mathrm{state},\operatorname{CarryVerticalL2}).
\]

Ela pede apenas:

1. `rowGramPosDef`, a hipótese geométrica já exigida para a câmera finita;
2. para todo par de brackets da base e raio escolhidos,

   \[
   \langle U_{\rm inc}e_i,U_{\rm inc}e_j\rangle
   =\langle B_i,B_j\rangle.
   \]

Como o mapa é real-linear, a igualdade por pares fornece a igualdade de
pairings para todas as combinações reais finitas dessas incidências. Isso é
exatamente o span usado pelas provas de independência par/ímpar.

Não se pede:

- isometria fora do ledger BR2;
- uma extensão complexa do mapa para todo `CarryVerticalL2`;
- injetividade do readout visível no carrier inteiro;
- Hankel PSD, Stieltjes, HP ou fatorização dos momentos.

Os jets de fonte, visível e cego são definidos somente a partir dessas
incidências. O theorem

```lean
sourceParityJet_inner_eq_br2
```

é a costura métrica mínima, e `gramSplit` passa a provar diretamente

\[
\langle C_i,C_j\rangle+\langle L_i,L_j\rangle
=\langle B_i,B_j\rangle
\]

no jet BR2, sem fazer afirmação fora dele.

### 22.2. Todo candidato global anterior induz o novo candidato restrito

Para o tipo global anterior, foi construída a conversão

```lean
CanonicalCompletedNativeTfvdCameraParsevalIncidenceTransport.ofGlobal
```

por composição explícita:

\[
U_{\rm inc}=
U_{\rm global}\circ
\texttt{br2CameraBracketProjectiveHilbertMap}.
\]

Os theorems

```lean
ofGlobal_sourceParityJet_eq
ofGlobal_visibleParityJet_eq
ofGlobal_blindParityJet_eq
ofGlobal_hasVisibleIncidenceTransport
```

mostram que:

- os jets fonte, visível e cego são os mesmos nos índices BR2;
- a velha hipótese de fidelidade visível transfere sem nova condição;
- a interface nova é de fato um enfraquecimento, e não outra teoria
  incompatível.

Também foram refeitos no nível restrito, sem hipótese global, os handoffs:

```lean
gramSplit
blind_inner_eq_energyExcess_add_visibleCoefficientDefect
realizesSixSourceVisibleCoefficient_iff_energyExcess
toRealHPCarrierCertificate
toStieltjesPositivity
```

Assim, a proposição material restante é ainda somente

\[
\boxed{
C_6(i,j)=\langle R U_{\rm inc}e_i,R U_{\rm inc}e_j\rangle.
}
\]

Se ela for provada junto da incidência visível fiel, Parseval fornece o canal
cego como `EnergyExcess` e o downstream HP/Stieltjes é idêntico ao da rota
global.

### 22.3. Resultado da auditoria TFVD → recuperação → Hilbert projetivo

A cadeia já existente foi seguida sem introduzir um novo readout:

\[
\text{BR2 incidence}
\to
\texttt{br2CameraBracketTfvdAnalysisMap}
\to
\texttt{br2FiniteTfvdHilbertRecovery}.
\]

O novo theorem

```lean
br2FiniteTfvdRecoveredParityJet_eq_projective
```

mostra, em toda ordem, que essa composição retorna exatamente

\[
\texttt{br2CameraBracketProjectiveHilbertParityJet}.
\]

Ou seja, ela é uma realização/reconstrução fiel do **total BR2 cru**. Ela
não é ainda uma compressão de câmera e não fornece, por si só, um termo de
perda.

O packing fiel de seis câmeras em
`CompletedTfvdGreenAllOrderIntertwining.lean` preserva uma igualdade vetorial
das funções Green após packing e Naimark. Mas seus alvos são
`CarryGammaComplexCamera` e `CarryGammaComplexNaimark`, enquanto o Parseval
histórico usado nesta rota requer uma
`FiniteHilbertFamily state CarryVerticalL2`. Não foi encontrado um mapa
tipado existente que faça essa ponte e preserve o pairing BR2 no span de
incidências.

Não é lícito preencher essa lacuna identificando o packing fiel com uma
compatibilidade Green global: os no-gos já documentados para o anchor/Gram
de ordem zero continuam válidos.

### 22.4. O defeito da cadeia existente é calculado exatamente

O arquivo
[`CompletedNativeTfvdCameraIncidenceCandidateAudit.lean`](CarrySelfAdjointOperator/CompletedNativeTfvdCameraIncidenceCandidateAudit.lean)
define

\[
D_{\rm rec}(i,j)=C_6(i,j)-
 \langle T_{\rm rec}(i),T_{\rm rec}(j)\rangle,
\]

onde `T_rec` é precisamente a análise TFVD finita seguida da reconstrução.

Foram provadas as duas identificações estruturais:

```lean
br2FiniteTfvdRecoveredCoefficientDefect_eq_centerLegDefect
br2FiniteTfvdRecoveredCoefficientDefect_eq_neg_energyExcess
```

Logo esse não é um residual novo nem uma estimativa. É exatamente o defeito
de center-leg já conhecido, ou, na orientação da rota B,

\[
\boxed{D_{\rm rec}=-\operatorname{EnergyExcess}.}
\]

Isso localiza a falha da cadeia atual: ela ainda está antes da operação que
deve mover esse excesso para um canal complementar.

### 22.5. Teste mínimo: a cadeia recuperada falha antes de qualquer extensão all-order

Para C3, raio um, o theorem

```lean
br2FiniteTfvdRecoveredParityJet_lowDegree_rawGram
```

calcula os quatro pairings diagnósticos do total recuperado:

\[
\begin{array}{c|cccc}
(p,r) &(0,0)&(0,1)&(0,2)&(1,1)\\ \hline
\langle T_{\rm rec,p},T_{\rm rec,r}\rangle
&6&0&0&6.
\end{array}
\]

Por outro lado,

```lean
nativeC3SeededClockTfvdSixSourceCenterLegCoefficient_lowDegree_hankel
```

prova a identidade Hankel material

\[
C_6(0,2)=C_6(1,1)=h_1.
\]

O total recuperado falha nessa mesma comparação por

\[
\langle T_{\rm rec,0},T_{\rm rec,2}\rangle-
\langle T_{\rm rec,1},T_{\rm rec,1}\rangle=-6,
\]

formalizado por

```lean
br2FiniteTfvdRecoveredParityJet_firstHankelDefect_eq_neg_six
```

e, na orientação do defeito visível,

\[
D_{\rm rec}(0,2)-D_{\rm rec}(1,1)=6,
\]

formalizado por

```lean
br2FiniteTfvdRecoveredCoefficientDefect_firstHankelDefect_eq_six.
```

Portanto a composição TFVD/análise/reconstrução já existente está
formalmente descartada como `correctedMap` ou canal visível. Ela permanece
importante como origem fiel do total (6I), mas não é o `U` não separável
que cria o Gram Hankel.

### 22.6. Situação do candidato ambiente histórico

A busca desta rodada não encontrou fórmula adicional para as doze
coordenadas de
`canonicalCompletedC3NormalizedAmbientSixCameraFstAnalysis` e
`canonicalCompletedC3NormalizedAmbientSixCameraSndAnalysis` no centro. O
sanity-check ambiente continua honestamente reduzido a

\[
\|a(0)\|^2+\|b(0)\|^2=h_0.
\]

Não foi assumida nem inferida essa igualdade. Ela continua sendo teste de uma
realização ambiente específica, não substituto da costura BR2/TFVD/câmera.

### 22.7. Próximo seam mínimo, agora sem ambiguidade de interface

O objeto ainda ausente tem tipo conceitual:

\[
U_{\rm inc}:(\mathbb N\to_0\mathbb R)
\longrightarrow
\operatorname{FiniteHilbertFamily}(
  \mathrm{state},\operatorname{CarryVerticalL2}),
\]

e deve satisfazer simultaneamente:

1. preservação dos pairings de brackets no span BR2;
2. `BR2BracketIncidenceJetTransport` para o output visível;
3. a única igualdade material

   \[
   C_6(i,j)=\langle R U_{\rm inc}e_i,R U_{\rm inc}e_j\rangle.
   \]

O channel blind será então, automaticamente, o endereço geométrico de

\[
6\delta_{ij}-C_6(i,j).
\]

O primeiro lugar razoável para procurar esse `U_inc` não é mais a
reconstrução TFVD pura — ela foi eliminada pelo defeito `-6` — mas um mapa
que use juntamente as coordenadas de proveniência/retorno/residual ainda
retidas antes da síntese e antes do packing Green global.

A nova auditoria está em
[`CompletedNativeTfvdCameraParsevalIncidenceTransportAudit.lean`](CarrySelfAdjointOperator/CompletedNativeTfvdCameraParsevalIncidenceTransportAudit.lean).

## 23. Dilatação incidencial pré-recuperação — o total Parseval existe; a compressão visível ainda não

Esta seção registra a rodada seguinte à interface incidencial restrita. A
pergunta foi se a genealogia TFVD enriquecida já continha, **antes** de
`br2FiniteTfvdHilbertRecovery`, uma dilatação das incidências BR2 cujo total
fosse `6I` e cuja compressão six-camera fornecesse o primeiro cruzamento
Hankel.

O resultado é misto e é importante preservar as duas partes:

1. existe uma dilatação incidencial pré-recuperação com total exatamente
   isométrico ao BR2 e com os quatro canais Green-frame separados;
2. ela ainda não vem equipada com a compressão finita que seria o
   `correctedMap`, e tratá-la inteira como visível falha formalmente no
   primeiro teste Hankel.

O código da rodada está em
[`CompletedNativeTfvdPreRecoveryIncidenceAudit.lean`](CarrySelfAdjointOperator/CompletedNativeTfvdPreRecoveryIncidenceAudit.lean),
e a auditoria em
[`CompletedNativeTfvdPreRecoveryIncidenceAuditAxioms.lean`](CarrySelfAdjointOperator/CompletedNativeTfvdPreRecoveryIncidenceAuditAxioms.lean).

### 23.1. O primeiro carrier realmente incidencial e ainda enriquecido

O primeiro objeto da genealogia que recebe uma incidência BR2 arbitrária e
mantém as coordenadas TFVD antes de qualquer reconstrução é

```lean
NativeGpreFiniteTfvdAnalysisCarrier S
```

com a forma literal

\[
((\operatorname{CarryVerticalL2}\times(\mathbb C\times\mathbb C))
 \times
 (\operatorname{BoundaryValue}_S\times\operatorname{BoundaryFlux}_S)).
\]

Logo ele retém simultaneamente:

- o bracket TFVD;
- o trace TFVD;
- a proveniência `G_pre` de valor;
- a proveniência `G_pre` de fluxo/número.

A composição incidencial concreta é

\[
\text{BR2 ledger}
\xrightarrow{\text{causal Green response}}
\operatorname{CarryVerticalL2}
\xrightarrow{\text{nativeGpreFiniteTfvdAnalysis}}
\operatorname{NativeGpreFiniteTfvdAnalysisCarrier}(S).
\]

Ela foi nomeada

```lean
br2CausalTfvdPreRecoveryIncidenceMap
br2CausalTfvdPreRecoveryIncidenceState.
```

O theorem

```lean
br2CausalTfvdPreRecoveryIncidenceState_bracket_eq
```

mostra que a projeção de bracket desse estado enriquecido é exatamente o
bracket BR2 literal:

\[
\operatorname{bracketProjection}(A_{q,S}e_i)=B_i.
\]

Isto é anterior à recuperação TFVD:
`nativeGpreFiniteTfvdReconstruction` não aparece na definição nem na prova.

### 23.2. Onde ficam os objetos C3 de quatro traces e six-camera

Os objetos destacados na busca são reais e preservam a informação correta,
mas estão em outra entrada da genealogia:

```lean
CanonicalC3BracketTfvdCompletionState M
CanonicalC3FourTraceSixCameraSource
```

O primeiro recebe um parâmetro complexo `s`; o segundo recebe `z,w`. Eles
retêm head de valor, head log-jet, ambos os tails, port Green direto e
refletido. As projeções relevantes são:

```lean
separatedFourTraceProjection
greenPortProjection
sixCameraGreenCarrierProjection.
```

Os theorems

```lean
canonicalC3FourTraceSixCameraSource_separatedTrace_eq
canonicalC3FourTraceSixCameraSource_greenPort_eq_bracket
canonicalC3FourTraceSixCameraSource_symplecticCarrier_eq
canonicalC3FourTraceSixCameraVectorBridge
canonicalC3FourTraceSixCameraCompletedVectorBridge
```

confirmam que, para os estados canônicos parametrizados, os heads/tails e os
três vetores Naimark coexistem antes de qualquer Wronskiano escalar.

Mas eles **não** fornecem um mapa do ledger BR2, ou de
`NativeGpreFiniteTfvdAnalysisCarrier S`, para esses estados. A cadeia

```text
incidência BR2
  → análise TFVD enriquecida em S
  → ledger C3 ordinary/logJet/residual
  → port C3 de seis células
  → família finita de estados verticais
```

não está formalizada. Em particular,
`completedTfvdGreenLedgerC3Port` recebe um
`CompletedTfvdGreenLedger` semeado por `s`; ele não recebe a análise de uma
incidência BR2 arbitrária.

Esse é o primeiro seam de tipos concreto, e não uma ausência de estimativa.

### 23.3. Protótipo máximo já construível sem inventar a ponte

Da coordenada de bracket do estado enriquecido, é possível aplicar a análise
Parseval já existente do Green frame:

\[
W_{q,S}=
\operatorname{ParsevalGreenFrame}
\circ\operatorname{bracketProjection}
\circ\operatorname{TFVDAnalysis}_{q,S}
\circ\operatorname{CausalResponse}_{q}.
\]

Em Lean:

```lean
br2CausalTfvdParsevalGreenFrameIncidenceMap
br2CausalTfvdParsevalGreenFrameIncidenceState.
```

É uma aplicação real-linear do ledger de incidências para
`CanonicalCompletedGreenFrameCarrier`. O theorem

```lean
br2CausalTfvdParsevalGreenFrameIncidenceState_inner_eq_br2
```

prova a conservação total exata:

\[
\boxed{
\langle W_i,W_j\rangle=\langle B_i,B_j\rangle.
}
\]

Para C3/radius one, portanto,

\[
\langle W_0,W_0\rangle=6,
\qquad
\langle W_0,W_2\rangle=0,
\qquad
\langle W_1,W_1\rangle=6,
\]

formalizado por

```lean
br2CausalTfvdParsevalGreenFrameIncidenceState_lowDegree_total.
```

Esse é o lado total da hipótese de dilatação: a ortogonalidade BR2 sobrevive
em um carrier maior e genuinamente dividido.

### 23.4. A energia está em quatro canais, mas eles ainda não são a câmera finita da rota B

O carrier de chegada de `W` é a soma ortogonal dos canais

\[
\boxed{
\text{seed}\oplus\text{residual}\oplus\text{depth-one Green}\oplus\text{bulk Green}.
}
\]

O theorem

```lean
br2CausalTfvdParsevalGreenFrameIncidenceState_inner_eq_channelSum
```

decompõe o produto interno exatamente como a soma dos quatro produtos de
canais. Portanto este é de fato um endereço geométrico pré-síntese da
energia, e não uma estimativa de norma.

Contudo, este splitting **não é ainda** a decomposição histórica da câmera
finita

\[
\operatorname{FiniteHilbertFamily}(\mathrm{state},
  \operatorname{CarryVerticalL2})
\xrightarrow{R\oplus B}
\operatorname{FiniteHilbertFamily}(\mathrm{camera},
  \operatorname{CarryVerticalL2})
\oplus
\operatorname{FiniteHilbertFamily}(\mathrm{state},
  \operatorname{CarryVerticalL2}).
\]

Não existe neste ponto um `R` formalizado de
`CanonicalCompletedGreenFrameCarrier` para essa família finita. Assim não é
válido escolher arbitrariamente seed, residual, depth-one ou bulk como
`visible`; tampouco é válido identificar o packing C3/Naimark global com esse
readout sem um theorem de ponte.

### 23.5. No-go de baixa ordem para o total inteiro como visível

Para deixar explícito o que o protótipo **não** resolve, foi definido

\[
D_{\rm total}(i,j)=C_6(i,j)-\langle W_i,W_j\rangle.
\]

O theorem

```lean
br2CausalTfvdParsevalGreenFrameTotalCoefficientDefect_eq_neg_energyExcess
```

prova

\[
\boxed{D_{\rm total}=-\operatorname{EnergyExcess}.}
\]

É o mesmo defeito já observado para a recuperação TFVD crua. Isso é esperado:
o mapa `W` preserva deliberadamente o total BR2.

No primeiro teste Hankel:

```lean
br2CausalTfvdParsevalGreenFrameTotalCoefficientDefect_firstHankel_eq_six
```

\[
D_{\rm total}(0,2)-D_{\rm total}(1,1)=6.
\]

Portanto:

\[
\boxed{
\text{não promover }W\text{ como correctedMap ou visible channel.}
}
\]

Esse no-go não descarta a rota B. Ele identifica exatamente o que falta:
uma compressão não trivial dos canais retidos, não outra preservação do total.

### 23.6. Resposta da rodada e próximo seam mínimo

A resposta à pergunta desta rodada é:

\[
\boxed{
\begin{array}{l}
\text{Existe uma dilatação incidencial pré-recuperação com total }6I\\
\text{e canais ortogonais explícitos;}\\
\text{não existe ainda uma ponte formalizada que a comprima no readout}\\
\text{six-camera finito e produza }C_6(0,2)=C_6(1,1).
\end{array}}
}
\]

Não há, portanto, theorem nesta rodada do formato

```lean
inner_visible_br2_enriched_zero_two_eq_h1
```

e não se deve promover para all-order.

O próximo seam deve ser procurado com o tipo explícito

```lean
finiteTfvdSixCameraDilation :
  NativeGpreFiniteTfvdAnalysisCarrier S →ₗ[ℝ]
    FiniteHilbertFamily state CarryVerticalL2
```

ou, equivalentemente, como um mapa real-linear direto do ledger BR2 que
**fatora pela análise enriquecida** e usa de modo não trivial bracket, trace,
value-provenance e number-flux/proveniência. Para ser a ponte certa, ele deve
ter:

1. preservação do pairing BR2 no span incidencial;
2. uma aplicação do readout `finiteCanonicalCameraHilbertReadout` bem tipada;
3. a costura visível nos dois testes iniciais

   \[
   \langle RU_0,RU_2\rangle=C_6(0,2),
   \qquad
   \langle RU_1,RU_1\rangle=C_6(1,1);
   \]

4. nenhuma passagem por `br2FiniteTfvdHilbertRecovery` nem definição a
   partir de momentos/Hankel.

Somente depois disso `realizesSixSourceVisibleCoefficient_iff_energyExcess`
transformará o complemento blind histórico em

\[
6I-H.
\]

O resultado positivo desta rodada é que o lado ``6I`` já tem uma realização
pré-recuperação, incidencial e channel-separated. A lacuna restante não é
mais ``achar uma energia positiva'': é construir a **ponte de compressão
tipada** que transforme essa energia total nos canais visible/blind da câmera
finita.

## 24. Promoção six-source vetorial para six-camera — source roles, camera slots e o seam ainda aberto

### 24.1. O último dado vetorial six-source existe e é anterior ao readout escalar

O seeded clock não passa diretamente de um dado escalar a
`nativeC3SeededClockTfvdSixSourceCorrectedBoundary`. Seu dado imediatamente
anterior é

```lean
nativeC3SeededClockTfvdSixSourceAnalysis :
  CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S
```

isto é, seis valores de `NativeGpreFiniteTfvdAnalysisCarrier S`:


\[
\boxed{
(\mathrm{ordinary},\mathrm{logJet})
\times
(z,w,\operatorname{reflected}z).
}
\]

O novo módulo

```text
CompletedNativeTfvdSixSourceCameraPromotionAudit.lean
```

expõe esse produto por um tipo semântico explícito:

```lean
CanonicalC3SixSourceRole :=
  CanonicalC3SixSourceParameterRole × CanonicalC3SixSourceChannelRole
```

com os teoremas de ida e volta

```lean
canonicalC3SixSourceRoleAnalysisData_roleAnalysis
canonicalC3SixSourceRoleAnalysis_roleAnalysisData.
```

Assim ficou formalizado que nenhuma das seis análises foi contraída ou
reordenada apenas para tornar o dado conveniente.

O último objeto vetorial que entra **diretamente** no corrected boundary é o
par

```lean
canonicalC3SixSourceRecoveredGreenPorts :
  FiniteC3GreenPortCarrier (3 * M) ×
    FiniteC3GreenPortCarrier (3 * M).
```

Ele é obtido reconstruindo separadamente a fonte direta `w` e a fonte
refletida `z`. A igualdade literal

```lean
canonicalC3SixSourceRecoveredGreenPorts_correctedBoundary
```

diz apenas

\[
\operatorname{CorrectedBoundary}
=
\operatorname{greenForm}(\operatorname{directPort},
  \operatorname{reflectedPort}).
\]

Isso fixa um guardrail importante: `greenForm` é uma leitura
Green/simplética; ela **não** é, por si só, um Gram Hilbertiano positivo.

Também existe a crosswalk vetorial, anterior a qualquer momento:

```lean
nativeC3SeededClockTfvdSixSource_vectorCrosswalk
```

que identifica a reconstrução lossless das seis análises com a fonte
three-point do Green frame orientado. Ela preserva a fonte
ordinary/log-jet antes da leitura scalar, mas não fornece por si uma família
finita de `CarryVerticalL2`.

### 24.2. Os seis source roles não são os seis camera slots

Os slots históricos da câmera foram mantidos em outro tipo:

```lean
CanonicalC3SixCameraSlot := CanonicalC3SixCameraLeg × Fin 3
```

com `first` e `second` como as duas pernas geométricas. O label nativo é
proveniente da construção C3 já existente:

```lean
canonicalC3SixCameraSlotLabel :
  CanonicalC3SixCameraSlot → ℕ
```

e usa literalmente `firstC3CameraIndex` e `secondC3CameraIndex`, isto é, as
câmeras `2,\ldots,7`.

Portanto não foi criada nenhuma bijeção por posição entre

\[
(z,w,\operatorname{reflected}z)
\times(\mathrm{ordinary},\mathrm{logJet})
\]

e

\[
(\mathrm{first\ C3\ leg},\mathrm{second\ C3\ leg})
\times \operatorname{Fin}3.
\]

Uma promoção válida deve explicitar geometricamente como proveniência,
porta, retorno, reflexão e os dois canais verticais determinam os slots
externos. A coincidência de cardinalidade seis não é uma identificação.

### 24.3. O tail canal-a-canal da promoção já está disponível

Uma vez dada a promoção ausente

```lean
CanonicalC3SixSourceToCameraChannelAnalysis S :=
  CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S →ₗ[ℂ]
    (ℕ →₀ NativeGpreFiniteTfvdAnalysisCarrier S),
```

a parte seguinte já é inteiramente tipada e não usa
`cameraChannelSynthesis`:

\[
\begin{aligned}
&\operatorname{CanonicalC3AllCutoffMixedSourceTfvdAnalysisData}(S)\\
&\quad\xrightarrow{P}
  \mathbb N\to_0\operatorname{NativeGpreFiniteTfvdAnalysisCarrier}(S)\\
&\quad\xrightarrow{\texttt{cameraChannelTfvdReconstruction}}
  \mathbb N\to_0\operatorname{CarryVerticalL2}\\
&\quad\xrightarrow{\texttt{restrictCameraResolvedCarryVertical}}
  \operatorname{FiniteHilbertFamily}(
    \operatorname{CanonicalC3SixCameraSlot},
    \operatorname{CarryVerticalL2}).
\end{aligned}
\]

O mapa composto está formalizado como

```lean
canonicalC3SixSourceFiniteCameraFamilyOfPromotion.
```

Sua fórmula por slot,

```lean
canonicalC3SixSourceFiniteCameraFamilyOfPromotion_apply,
```

confirma que cada coordenada é reconstruída separadamente a partir da análise
promovida no seu label geométrico. Não há síntese precoce na construção.

### 24.4. Há dois arrows ausentes para a versão incidencial, não apenas um

Para obter os vetores `U_i` da rota B a partir da incidência BR2, a promoção
de source role para câmera não basta. A realização material six-source é
paramétrica em `(z,w)`, enquanto a Parseval restrita recebe o ledger real de
incidências. A auditoria isolou os dois arrows necessários:

```lean
J : (ℕ →₀ ℝ) →ₗ[ℝ]
  CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S

P : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S →ₗ[ℂ]
  (ℕ →₀ NativeGpreFiniteTfvdAnalysisCarrier S).
```

Em Lean eles são os tipos

```lean
BR2IncidenceToCanonicalC3SixSourceAnalysis S
CanonicalC3SixSourceToCameraChannelAnalysis S.
```

Com ambos, a composição real-linear já construída é

```lean
br2CanonicalC3SixSourceFiniteCameraIncidenceMap :
  (ℕ →₀ ℝ) →ₗ[ℝ]
    FiniteHilbertFamily CanonicalC3SixCameraSlot
      CanonicalCompletedTfvdGreenHilbertCarrier.
```

Ela é exatamente o tipo de entrada requerido por
`CanonicalCompletedNativeTfvdCameraParsevalIncidenceTransport`.

O primeiro arrow, `J`, é a lacuna adicional que fica invisível se se olha
apenas para o scalar six-source: a torre scalar cria os coeficientes por
readout e jatos, mas não fornece um jet **vetorial incidencial** nos seis
roles. O segundo, `P`, é a costura geométrica principal source-role para
camera-channel. Nenhum deles foi encontrado como instância existente.

### 24.5. O packing six-camera existente não preenche esse tipo

O mapa já formalizado

```lean
canonicalC3SixCameraSourceMap :
  FiniteC3GreenPortCarrier 3 → RealifiedCameraComplexification
```

é fiel e preserva o vetor de porta, mas seu alvo é
`RealifiedCameraComplexification`, não

```lean
FiniteHilbertFamily CanonicalC3SixCameraSlot CarryVerticalL2.
```

Além disso, o packing parte de um `FiniteC3GreenPortCarrier`, depois que as
fontes foram reconstruídas, e não de `CanonicalC3AllCutoffMixedSourceTfvdAnalysisData`.
Não foi encontrada ponte formalizada de `RealifiedCameraComplexification` para
`CameraResolvedCarryVertical`, nem uma ponte que forneça `J` ou `P` acima.

Isso explica por que não é válido declarar o packing Naimark histórico como
instância da Parseval finita da rota B apenas por ambos terem “seis câmeras”.

### 24.6. Teste de baixa ordem e no-go de um candidato próximo

Não há nesta rodada um candidato `U_i` bem tipado que seja simultaneamente:

1. uma imagem de incidências BR2;
2. uma família finita de `CarryVerticalL2` para a Parseval histórica; e
3. uma promoção dos seis roles que preserve direct/reflected,
   ordinary/log-jet e provenance.

Logo os testes

\[
\langle U_0,U_0\rangle=6,
\quad
\langle U_0,U_2\rangle=0,
\quad
\langle U_1,U_1\rangle=6,
\]

e os testes visible contra `C_6(0,2)` e `C_6(1,1)` ainda não podem ser
instanciados honestamente. Não houve promoção all-order.

Foi, porém, auditado o candidato vetorial próximo já existente: o carrier
orientado ordinary/log-jet/residual levado ao fixed concrete positive carrier.
Ele não é uma família six-camera da interface atual e já falha no seu primeiro
teste métrico central. Os teoremas

```lean
canonicalC3FixedPositiveCarrier_centralDefect_ne_zero
canonicalC3FixedPositiveCarrier_not_sixSourceSewing
```

registram, respectivamente,

\[
\operatorname{ConcretePositiveSewingDefect}(M,0,0)\ne0
\]

e a impossibilidade da sewing fixa. Esse é um no-go para essa métrica positiva
concreta, não para uma futura promoção `J` e `P` nem para a arquitetura Parseval.

### 24.7. Próximo seam mínimo e critério de continuação

O próximo trabalho não é um bound nem uma fatorização de `6I-H`. É construir
geometricamente `J` e `P` — ou um único mapa incidencial que fatora por ambos
os níveis — e demonstrar antes de qualquer all-order:

\[
\begin{aligned}
\langle U_i,U_j\rangle&=6\delta_{ij},\\
\langle R U_0,R U_2\rangle&=C_6(0,2),\\
\langle R U_1,R U_1\rangle&=C_6(1,1).
\end{aligned}
\]

Somente se esses testes passarem, a equivalência já existente

```lean
realizesSixSourceVisibleCoefficient_iff_energyExcess
```

identificará automaticamente o canal blind com `EnergyExcess`; então, e só
então, o handoff HP/Stieltjes poderá ser aplicado.

## 25. Kernel vetorial funcional six-source — a parte radial fecha por duas quadraturas, mas ainda não é o Gram visible

### 25.1. O último vetor anterior à `greenForm` foi localizado e formalizado em todo cutoff

O módulo novo

```text
CompletedNativeTfvdSixSourceSymplecticVectorKernel.lean
```

fecha a auditoria que faltava entre a análise TFVD six-source e a primeira
scalarização Green. Para qualquer dado separado

```lean
data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S
```

ele reconstrói, sem sintetizar os seis roles, os dois ports já existentes

```lean
canonicalC3SixSourceRecoveredGreenPorts :
  FiniteC3GreenPortCarrier (3 * M) ×
    FiniteC3GreenPortCarrier (3 * M).
```

Se esses ports são (x) (direto) e (y) (refletido), o estado vetorial
funcional novo é literalmente


\[
\boxed{
\mathcal V_M(z,w;\mathrm{data})
=
\bigl(
N_{3M}x,\;
N_{3M}y,\;
N_{3M}(i y)
\bigr),
}
\]

com alvo

```lean
CanonicalC3SixSourceSymplecticNaimarkVectorCarrier
  = CanonicalC3SixCameraSymplecticGreenCarrierHilbert.
```

Os três vetores são expostos pelas igualdades compiladas

```lean
canonicalC3SixSourceSymplecticNaimarkVector_direct
canonicalC3SixSourceSymplecticNaimarkVector_reflected
canonicalC3SixSourceSymplecticNaimarkVector_quarterTurnReflected.
```

Portanto o objeto anterior à `greenForm` não é hipotético: ele é uma família
vetorial honesta, dependente de ((z,w)), com direct, reflected e
quarter-turn ainda separados. Ele é construído exclusivamente da genealogia
TFVD/recovery/Green/Naimark; nenhum momento, Hankel, fatorização PSD ou lift
incidencial entra na definição.

### 25.2. Identidade funcional exata encontrada — e a sua natureza correta

As duas quadraturas reais são

\[
Q_0=\operatorname{realifiedGreenSkew}(N x,N y),
\qquad
Q_1=\operatorname{realifiedGreenSkew}(N x,N(i y)).
\]

O readout complexo é

\[
Q_0-iQ_1.
\]

O theorem novo

```lean
canonicalC3SixSourceSymplecticNaimarkReadout_eq_correctedBoundary
```

prova, para **todo** cutoff e todo dado six-source,

\[
\boxed{
\operatorname{CorrectedBoundary}_M(z,w;\mathrm{data})
=Q_0-iQ_1
=\operatorname{greenForm}(x,y).
}
\]

A especialização material é igualmente literal:

```lean
nativeC3SeededClockTfvdSixSourceSymplecticNaimarkReadout_eq_correctedBoundary
nativeC3SeededClockTfvdSixSourceSymplecticNaimarkReadout_eq_ledgerRadial.
```

Logo o **kernel radial corrected** já tem uma realização vetorial funcional
pré-momento e pré-jato. Isto é um PASS para a parte “identidade antes de
estimativa” da busca.

Mas a identidade é uma polarização **simplética**; ela não afirma

\[
Q_0-iQ_1=\langle V(z),V(w)\rangle.
\]

Cada (Q_k) usa `realifiedGreenSkew`, e não o produto interno positivo do
carrier Naimark. A realização localiza rigorosamente a scalarização, mas não
transforma por definição uma forma skew em Gram visible. Isso preserva o
guardrail central da rota B.

### 25.3. O último estado vetorial antes do `FinalReadout` é ainda maior

O momento/coeficiente six-source não é extraído somente do canal radial. A
fonte material normalizada usa o `FinalReadout`, e o ledger já existente o
mantém explicitamente como estado Hilbertiano

```lean
CanonicalCompletedC3AllCutoffKernelLedgerHilbert.
```

O novo nome material

```lean
nativeC3SeededClockTfvdSixSourceKernelLedgerVector M z w
```

é a família canônica desse estado. Suas coordenadas são

\[
\boxed{
(N x,\;N y,\;N(i y),\;
  \mathrm{structural},\;\mathrm{tail},\;\Xi,\;\mathrm{chart}).
}
\]

Portanto ele retém simultaneamente:

- as três coordenadas Naimark usadas pelas quadraturas Green;
- green provenance, off-diagonal e readout residual;
- tail completion;
- peso \(\Xi\) e archimedean chart.

Os teoremas novos

```lean
nativeC3SeededClockTfvdSixSourceKernelLedgerVector_radial_eq_symplecticNaimark
nativeC3SeededClockTfvdSixSourceKernelLedgerVector_final_eq_nativeFinalReadout
```

provam, respectivamente, que o canal radial é o readout do triple acima e
que somente depois de todos esses canais serem preservados o `FinalReadout`
material é tomado. A decomposição existente é literalmente

\[
\operatorname{FinalReadout}
=\Xi\bigl(
  \operatorname{radial}
 +\operatorname{structural}
 +\operatorname{tail}\bigr)
 +\operatorname{chart}.
\]

Consequência prática: uma tentativa de usar apenas o triple Naimark radial
como `correctedMap` para `C_6` seria prematura. Ela explicaria o corrected
boundary, mas não demonstraria ainda que o **kernel final normalizado** do
qual os coeficientes são extraídos seja o Gram visible.

O segundo theorem é uma igualdade do **readout scalar** nativo com o readout
do ledger canônico. Não se deve fortalecê-lo informalmente para uma nova
igualdade vetorial de um `data` six-source arbitrário com o ledger inteiro:
essa crosswalk completa ainda não foi construída. O que já é vetorial e
diretamente functorial em `data` é exatamente o triple Green/Naimark da
subseção anterior; para o ledger inteiro, a proveniência structural já é
conhecida no source canônico, mas a promoção full-data continua parte do seam.

### 25.4. O que existe para jatos — e o que ainda não comuta

Há duas cadeias distintas, agora claramente separadas.

Para a parte vetorial radial, existe a família

```lean
nativeC3SeededClockTfvdSixSourceOnePointSymplecticNaimarkVector :
  ℂ → CanonicalC3SixSourceSymplecticNaimarkVectorCarrier
```

na fatia (w=0). A biblioteca também já contém o lema real-linear geral

```lean
iteratedDeriv_continuousLinearEquiv_comp
```

que mostra que uma equivalência contínua real-linear comuta com todos os
jatos de uma família `ℝ → E`.

Para os coeficientes materiais, porém, a cadeia formalizada atualmente é
scalar e assinada:

```lean
nativeC3SeededClockTfvdSixSourceTowerCoefficient_eq_signedChiralDerivative
```

isto é,

\[
C_6(p,r)
=\frac{1}{(p+r+1)!}\partial^{p+r+1}
\left[
i\,\bigl(K_+(0,z)-K_-(0,z)\bigr)
\right]_{z=0}.
\]

Não foi encontrada uma prova que identifique esse jato scalar com o jato do
triple Naimark, nem uma regra de derivação vetorial para a família complexa
realificada que comute com o `FinalReadout` completo e produza vetores de
`CarryVerticalL2`. Em particular, ainda não se pode definir honestamente

\[
e_n\longmapsto \frac{1}{n!}\partial^n\mathcal V(0)
\]

como o lift incidencial de rota B: falta primeiro a promoção positiva e a
compatibilidade analítica de seus jatos. Não se construiu `J` por base nem se
promoveu all-order.

### 25.5. A Hilbertização chiral existente é informativa, mas não é o `P` procurado

Existe um bloco positivo genuíno, com os dois estados

```lean
canonicalCompletedC3NormalizedFullWronskianPositiveChiralState
canonicalCompletedC3NormalizedFullWronskianNegativeChiralState
```

e Gram de dois canais

```lean
canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel.
```

Todo sample finito desse bloco é PSD pelo theorem

```lean
canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel_posSemidef.
```

Contudo o scalar relevante é a assinatura

\[
\boxed{
i\bigl(\langle V_+(0),V_+(z)\rangle
-\langle V_-(0),V_-(z)\rangle\bigr),
}
\]

e não o Gram do bloco direto. Assim, essa doubled-Hilbert realization explica
de onde a forma assinada vem, mas não prova que ela seja uma compressão
positiva ou o readout visible da câmera.

Mais forte: a tentativa causal/coisométrica natural de transformar o
readout chiral positivo em readout de câmera já possui no-go formal:

```lean
not_canonicalCompletedC3CausalChiralReadoutKernelCompatibleAt_of_im_pos.
```

Ela exclui essa **Hilbertização causal fixa** no semiplano superior; não
exclui uma promoção incidencial TFVD/six-camera que preserve proveniência no
span BR2. Portanto o bloco chiral é diagnóstico, não uma instância de `P`.

### 25.6. Seam exato restante e status dos testes de baixa ordem

Para o canal radial, o tipo da seta faltante está agora explícito:

```lean
CanonicalC3SymplecticNaimarkToFiniteCameraFamily :=
  CanonicalC3SixSourceSymplecticNaimarkVectorCarrier →ₗ[ℝ]
    FiniteHilbertFamily CanonicalC3SixCameraSlot
      CanonicalCompletedTfvdGreenHilbertCarrier.
```

Ela teria de ser geométrica, não separável e provenance-aware. Em particular,
não pode esquecer direct/reflected/quarter-turn e não pode ser o embedding
rank-one já descartado. Para fechar a rota B, uma extensão dela também teria
de explicar como structural, tail, \(\Xi\) e chart entram antes da extração
dos jatos do `FinalReadout` — ou provar uma identidade que os transporte
para o mesmo visible kernel.

Nenhuma ponte formalizada foi encontrada de

```lean
RealifiedNaimarkComplexification
```

ou do triple/ledger acima para

```lean
FiniteHilbertFamily CanonicalC3SixCameraSlot CarryVerticalL2.
```

Consequentemente ainda não existe um candidato honesto de `U_0,U_1,U_2` que
possa ser entregue ao readout Parseval. Os testes

\[
\langle R U_0,R U_2\rangle=C_6(0,2),
\qquad
\langle R U_1,R U_1\rangle=C_6(1,1)
\]

**não foram forçados** nem promovidos para all-order. O próximo teste mínimo
continua exatamente esse, mas somente após uma seta bem tipada para a família
de câmera finita e uma costura funcional que chegue ao `FinalReadout`, não
apenas ao radial `CorrectedBoundary`.

### 25.7. Conclusão operacional desta rodada

O achado positivo é preciso:

\[
\boxed{
\text{six-source TFVD}
\to
\text{ports Green recuperados}
\to
\text{triple Naimark vetorial}
\to
\text{duas quadraturas skew}
\to
\text{CorrectedBoundary}.
}
\]

E, com todos os canais ainda presentes,

\[
\boxed{
\text{six-source TFVD no locus canônico}
\to
\text{kernel ledger vetorial}
\to
\text{FinalReadout scalar}
\to
\text{jatos/coefficient tower}.
}
\]

O que **não** foi encontrado é a seta positiva de compressão que substitua
as quadraturas/assinatura por um Gram Hilbertiano visible da câmera finita.
Assim a rota B avançou de “precisamos adivinhar um vetor” para um seam único e
concreto: construir (ou localizar) a promoção provenance-aware do vetor
Naimark/ledger para os slots `CarryVerticalL2`, com compatibilidade de kernel
e jatos. Enquanto isso não existir, `6I=H+\mathrm{blind\ Gram}` permanece
uma arquitetura formal pronta para receber a costura, não uma identidade
concreta já demonstrada.

## 26. Ponte característica multibase → espectro de altura — operador já existente, seam de readout exato

### 26.1. O downstream espectral não requer um novo operador de Potapov

O módulo integrado

```text
MixedReturnHeightSpectrumBridge.lean
```

confirma que a teoria já possui o operador correto para a leitura por alturas:
o reduced signed-height self-adjoint operator construído a partir de um

```lean
CompletedNativeRealHPCarrierCertificate jet.
```

Portanto uma futura característica multibase, mínima, Potapov ou Weyl **não**
deve criar uma segunda realização espectral. O seu único handoff para essa
parte da teoria é identificar o seu readout na reta real com a característica
canônica já usada pelo operador:

\[
F(t)=\texttt{completedNativeOperatorCharacteristic}(t).
\]

O guardrail condicional é importante: como todo o downstream HP/Jacobi, os
teoremas de espectro desta seção recebem um
`CompletedNativeRealHPCarrierCertificate`. Eles não descarregam por si a
positividade concreta all-order que continua sendo o gate principal deste
checkpoint. O que foi removido é a necessidade de um **novo operador** depois
que esse certificado existe.

### 26.2. Interface mínima e reutilizável

Foi formalizada a interface

```lean
IsExactCompletedNativeHeightReadout (readout : ℝ → ℂ) : Prop :=
  ∀ t : ℝ,
    readout t = completedNativeOperatorCharacteristic (t : ℂ).
```

Ela não menciona momentos, Hankel, HP, Potapov, uma extensão auto-adjunta nova
nem um zero numérico. Assim qualquer construção futura tem a obrigação
upstream única

\[
\boxed{
R(t)=F(t)\quad\text{para todo }t\in\mathbb R.
}
\]

e herda a rota espectral canônica sem duplicação.

O readout mixed-return já existente satisfaz essa interface em qualquer
cutoff de seis câmeras:

```lean
mixedReturnCompletedHeightCharacteristic_isExactReadout
```

isto é,

\[
\texttt{mixedReturnCompletedHeightCharacteristic}(\mathrm{cutoff},t)=F(t).
\]

### 26.3. Consequências espectrais já compiladas

Dado um certificado HP real e qualquer `readout` exato, o theorem genérico

```lean
CompletedNativeRealHPCarrierCertificate
  .exactReadout_zero_hasSignedHeightEigenvalue
```

prova

\[
\boxed{
R(t)=0
\Longrightarrow
t\in\sigma_p(H_{\mathrm{signed\ height}}).
}
\]

O autovalor é o próprio (t), visto em \(\mathbb C\). Não há nessa ponte uma
reparametrização por \(\log n\), por \(t^{-2}\), nem um fitting de alturas.

Para \(t\ne0\), o theorem correspondente fornece a roupa Jacobi do mesmo
evento:

```lean
CompletedNativeRealHPCarrierCertificate
  .exactReadout_zero_iff_jacobiEigenvalue_inv_sq
```

\[
\boxed{
R(t)=0
\Longleftrightarrow
(t^2)^{-1}\in\sigma_p(J).
}
\]

As duas versões concretas para o readout mixed-return são:

```lean
mixedReturnCompletedHeightCharacteristic_zero_hasSignedHeightEigenvalue
mixedReturnCompletedHeightCharacteristic_zero_iff_jacobiEigenvalue_inv_sq.
```

### 26.4. Relação com a rota B e próximo seam

Esta ponte não substitui a rota B Parseval/HP; ela organiza o seu downstream.
As duas obrigações permanecem claramente separadas:

\[
\begin{array}{rcl}
\text{rota B}&:&
\text{geometria six-source/câmera}
\to\text{certificate HP concreto},\\[1mm]
\text{ponte de alturas}&:&
\text{característica multibase }R
\to R|_{\mathbb R}=F
\to\text{espectro do operador já construído}.
\end{array}
\]

Assim, o seam novo de pesquisa não é “construir o operador de alturas”, mas

\[
\boxed{
\text{característica multibase física}
\xrightarrow{\ \text{readout exato}\ }
\texttt{completedNativeOperatorCharacteristic}.
}
\]

Se uma construção natural produzir primeiro

\[
R(t)=u(t)F(t),\qquad u(t)\ne0,
\]

ela não deve ser artificialmente forçada a uma igualdade literal. A interface
exata permanece a meta preferida, pois conserva mais estrutura; uma futura
interface secundária de equivalência de zeros pode tratar esse caso de
normalização não nula sem reconstruir o downstream espectral.

### 26.5. Auditoria e validação local

O módulo e seu audit foram compilados localmente em worktree isolado, sem PR
e sem modificar `main`:

```text
lake build CarrySelfAdjointOperator.MixedReturnHeightSpectrumBridge
lake env lean CarrySelfAdjointOperator/MixedReturnHeightSpectrumBridgeAudit.lean
```

Os cinco teoremas auditados dependem somente de

```text
propext, Classical.choice, Quot.sound.
```

O commit remoto original foi integrado sem conflitos; os três arquivos da
ponte são adicionais e não alteram a implementação existente do operador de
altura, do certificado HP ou da torre Jacobi.

## 27. Seam espectral mínimo: equivalência de zeros, não igualdade forçada

### 27.1. Resultado confirmado

O módulo novo

```text
MixedReturnHeightZeroEquivalenceBridge.lean
```

formaliza a interface estritamente mais fraca que a igualdade literal e que é
suficiente para o *handoff* espectral:

```lean
IsZeroEquivalentCompletedNativeHeightReadout
    {A : Type*} [Zero A] (readout : ℝ → A) : Prop :=
  ∀ t : ℝ,
    readout t = 0 ↔
      completedNativeOperatorCharacteristic (t : ℂ) = 0.
```

O codomínio não é fixado em `ℂ`. Isso é deliberado: antes da leitura
secular, a característica multibase física pode permanecer vetorial; e um
residual/Potapov pode permanecer matricial. Basta provar que o seu `= 0`
expressa a cegueira coletiva física e que esta ocorre exatamente nos zeros de

\[
F(t)=\texttt{completedNativeOperatorCharacteristic}(t).
\]

Não há scalarização arbitrária de roles multibase, nem novo operador, nessa
interface.

### 27.2. Construtor por gauge não nulo

Para o caso em que o objeto final já é escalar, os dois constructors

```lean
IsZeroEquivalentCompletedNativeHeightReadout.of_nonvanishing_scalar_factor
IsZeroEquivalentCompletedNativeHeightReadout.of_nonvanishing_scalar_factor_right
```

formalizam respectivamente

\[
R(t)=u(t)F(t),\ u(t)\ne0
\qquad\text{ou}\qquad
R(t)=F(t)u(t),\ u(t)\ne0.
\]

Assim a normalização estrutural de um secular reduzido, de um fator Potapov
ou de uma gauge de completion pode ser removida somente no nível de zeros,
desde que sua não-anulação seja realmente provada na reta real. O padrão já
existia concretamente em
`NativeCarrySpectralWeyl.Camera.CommonZeroSet`: um fator de câmera não nulo
produz o mesmo locus de zeros, enquanto multiplicidade local é tratada como
questão separada.

### 27.3. Transporte downstream — sem nova estrutura espectral

Dado o mesmo certificado já exigido pelo downstream,

```lean
certificate : CompletedNativeRealHPCarrierCertificate jet,
```

foram compilados:

```lean
certificate.zeroEquivalentReadout_zero_hasSignedHeightEigenvalue
certificate.zeroEquivalentReadout_zero_iff_jacobiEigenvalue_inv_sq
```

Logo, para qualquer codomínio com zero,

\[
R(t)=0
\Longrightarrow
t\in\sigma_p(H_{\mathrm{signed\ height}}),
\]

e, se \(t\ne0\),

\[
R(t)=0
\Longleftrightarrow
(t^2)^{-1}\in\sigma_p(J).
\]

As provas chamam diretamente os theorems canônicos já usados pela ponte
exata. A única operação nova é aplicar a direção apropriada da equivalência
de zeros. Portanto a rota é precisamente

\[
\boxed{
\text{característica multibase física}
\to\text{zero-equivalência com }F
\to\text{espectro signed-height já construído}.}
\]

### 27.4. Igualdade exata continua necessária em outro nível

`IsExactCompletedNativeHeightReadout` implica a interface nova, e o
`mixedReturnCompletedHeightCharacteristic` agora possui ambas. Porém não há
conversa: equivalência de zeros não transporta automaticamente derivadas,
coeficientes de Taylor, momentos, nem multiplicidades analíticas. Esta
distinção é material, pois `CompletedNativeAtomicMultiplicity.lean` usa a
ordem analítica local de `F` para calcular o resíduo/massa atômica Weyl.

Assim a recomendação de arquitetura é:

\[
\begin{array}{rcl}
\text{característica vetorial/matricial multibase}
&\to& \text{provar cegueira coletiva}\;\Longleftrightarrow\;F=0,\\
\text{secular escalar normalizado}
&\to& uF\ \text{com }u\ne0\quad\text{(se existir)},\\
\text{derivadas, jatos ou multiplicidade}
&\to& \text{voltar a exigir identidade literal/analítica.}
\end{array}
\]

### 27.5. Auditoria da arquitetura existente e próximo gate

Não foi localizada uma implementação Lean de realização mínima multibase ou
Potapov no repositório atual. Há, contudo, três peças que tornam a nova
interface não especulativa:

1. `MixedReturnNativeReadout.lean` já dá a igualdade literal do readout
   mixed-return com `F` em toda a reta real;
2. `CompletedNativeCameraUniversality.lean` normaliza qualquer câmera
   suportada por seu fator não nulo e a identifica literalmente com `F`,
   inclusive em todas as derivadas; e
3. `NativeCarrySpectralWeyl.Camera.CommonZeroSet` já prova o mecanismo
   abstrato concreto “fator não nulo \(\Rightarrow\) zeros comuns”, sem
   confundi-lo com multiplicidade.

Portanto o próximo seam da rota característica é único e anterior ao
downstream:

```text
característica física vetorial/matricial
  → prova de que zero = cegueira coletiva
  → IsZeroEquivalentCompletedNativeHeightReadout
  → signed-height/Jacobi já existentes.
```

Se a construção produzir um secular escalar, basta em vez disso uma
fatorização real-axis `R = u * F` mais `∀ t, u t ≠ 0`. Nenhuma parte desse
trabalho substitui ou descarrega a rota B:

```text
rota B: geometria six-source/câmera → certificado HP concreto;
rota característica: zeros físicos → espectro, condicionado ao certificado HP.
```

### 27.6. Validação local

Foram validados somente os módulos afetados, sem PR e sem Actions:

```text
lake build CarrySelfAdjointOperator.MixedReturnHeightZeroEquivalenceBridge
lake env lean CarrySelfAdjointOperator/MixedReturnHeightZeroEquivalenceBridgeAudit.lean
```

O audit lista para os sete itens novos somente:

```text
propext, Classical.choice, Quot.sound.
```

## 28. Cegueira coletiva multibase canônica → zero de `F`

### 28.1. Resultado fechado nesta rodada

O módulo

```text
CompletedNativeMultibaseCollectiveReadout.lean
```

fecha a versão mínima e já justificada no repositório da característica
multibase: uma família de coordenadas de câmera **completadas e normalizadas**

```lean
completedNativeCameraFamilyReadout camera cutoff time : ι → ℂ
```

cuja coordenada `i` é

```lean
normalizedCompletedNativeCameraCharacteristic (camera i) (cutoff i) time.
```

Para cada câmera suportada (`2 ≤ camera i`), Gate A é literalmente o theorem

```lean
completedNativeCameraFamilyReadout_apply_eq
```

e diz

\[
R_i(t)=F(t).
\]

Ou seja, depois da normalização já formalizada em
`CompletedNativeCameraUniversality.lean`, o caso `R_i=u_iF` ocorre com
\(u_i=1\). Não foi necessário introduzir outra fatorização nem uma hipótese
nova de não-anulação.

Para uma família não vazia, Gate B está compilado como

```lean
completedNativeCameraFamilyReadout_eq_zero_iff_nativeZero
```

e prova puramente por coordenadas

\[
\boxed{
(R_i(t))_{i\in\iota}=0
\Longleftrightarrow
F(t)=0.}
\]

No sentido \(\Rightarrow\), basta uma coordenada fornecida pela não-vacuidade;
no outro sentido, todas as coordenadas são zero. Nenhuma positividade, HP,
Weyl, dado numérico ou espectro participa dessa etapa.

### 28.2. Secular root-free finito

Se a família é finita, foi definido o defeito escalar canônico

```lean
completedNativeCameraFamilyRootFreeSecular camera cutoff time
  = 4 * ∑ i, Complex.normSq (R_i time).
```

O theorem

```lean
completedNativeCameraFamilyRootFreeSecular_eq_zero_iff
```

prova a identidade algébrica

\[
4\sum_i|R_i(t)|^2=0
\Longleftrightarrow
(R_i(t))_i=0.
\]

Assim, para uma família finita não vazia suportada,

\[
\boxed{
\texttt{completedNativeCameraFamilyRootFreeSecular}(t)=0
\Longleftrightarrow F(t)=0.}
\]

Isso realiza a forma `4 |Phi|²` para o **vetor canônico de coordenadas
completadas** e não usa uma estrutura Hilbertiana adicional. A positividade
aqui é somente a não-negatividade elementar de somas de `Complex.normSq`; não
é uma nova prova HP nem um argumento espectral.

### 28.3. Instância concreta das seis câmeras

O módulo especializa a construção para

```text
sixCamera : Fin 6 → ℕ = (2,3,4,5,6,7),
```

com cutoff independente em cada slot. Estão compilados:

```lean
completedNativeSixCameraCollectiveReadout_eq_zero_iff_nativeZero
completedNativeSixCameraRootFreeSecular_eq_zero_iff_nativeZero
completedNativeSixCameraCollectiveReadout_isZeroEquivalent
completedNativeSixCameraRootFreeSecular_isZeroEquivalent.
```

Portanto tanto a cegueira coletiva vetorial canônica quanto seu secular
root-free escalar entram diretamente em
`IsZeroEquivalentCompletedNativeHeightReadout`.

Dado o mesmo `CompletedNativeRealHPCarrierCertificate jet` já exigido pelo
downstream, os corolários reutilizam — sem reconstruí-los — o bridge da seção
27:

\[
\text{cegueira coletiva canônica em }t
\Longrightarrow
t\in\sigma_p(H_{\mathrm{signed\ height}}),
\]

e para \(t\ne0\),

\[
\text{cegueira coletiva canônica em }t
\Longleftrightarrow
(t^2)^{-1}\in\sigma_p(J).
\]

### 28.4. O que a auditoria encontrou — e o seam que continua aberto

Há no repositório infraestrutura finita genuína de Gram, whitening e
coisometria:

```text
NativeCarrySpectralWeyl.Finite.Gram
NativeCarrySpectralWeyl.Finite.Whitening
sixCameraInverseSqrt
sixCameraLogOperator.
```

Ela prova a identidade de whitening do Gram e a auto-adjunticidade dos
operadores de momento finitos. Porém **não** foi encontrado um objeto Lean que
seja a órbita empírica

\[
Q_Ne^{-itL_N}j_N,
\]

nem uma realização Potapov mínima `S_N(z)`, nem uma comparação formal entre
essa órbita e as coordenadas escalares completadas acima. O readout
`mixedReturnCompletedCameraReadout` também já existe, mas é uma combinação
escalar assinada de câmeras, não o vetor de cegueira coletiva.

Assim, a conclusão correta não é que o \(Q_N\) experimental já foi
formalizado. O que foi fechado é a rota canônica disponível hoje:

\[
\boxed{
\text{câmeras completadas normalizadas}
\to\text{cegueira coletiva}
\Longleftrightarrow F=0.}
\]

O seam mínimo restante para identificar a característica física laboratorial é
exatamente uma seta de comparação de zeros, finita e anterior a qualquer
limite:

```text
Phi_N(t) = Q_N exp(-it L_N) j_N
  = 0  ↔  completedNativeCameraFamilyReadout sixCamera cutoff t = 0.
```

Equivalentemente, se o objeto físico escolhido for um secular/defeito
reduzido, basta provar

```text
Delta_N(t) = 0
  ↔  completedNativeCameraFamilyRootFreeSecular sixCamera cutoff t = 0.
```

Somente depois dessa comparação a característica empírica pode usar a
zero-equivalência já compilada. A promoção de cutoff/\(N\to\infty\), inclusive
o possível colapso da versão whitened normalizada e a preferência pela versão
desnormalizada \(\chi_N=C_Ne^{-itL_N}\alpha_N\), permanece explicitamente
fora desta rodada.

### 28.5. Validação

Foram compilados somente os módulos novos/afetados:

```text
lake build CarrySelfAdjointOperator.CompletedNativeMultibaseCollectiveReadout
lake env lean CarrySelfAdjointOperator/CompletedNativeMultibaseCollectiveReadoutAudit.lean
```

O audit dos onze itens expostos lista somente:

```text
propext, Classical.choice, Quot.sound.
```

## 29. Seam físico finito: whitening preserva kernel; a cauda de completamento permanece

### 29.1. Resultado fechado nesta rodada

O módulo novo

```text
FinitePhysicalSixCameraWhiteningBridge.lean
```

separa formalmente as duas questões que não podem ser confundidas na
característica física finita.

Primeiro, Gate A é agora um fato de álgebra linear compilado. Para matrizes
arbitrárias sobre um corpo,

```lean
whitened_mulVec_eq_zero_iff_raw_mulVec_eq_zero_of_leftInverse
```

prova que, se `whiteningInv * whitening = 1`, então


\[
W(Cx)=0\Longleftrightarrow Cx=0.
\]

O resultado é deliberadamente complexo e não depende de positividade, de
tempo, do gerador logarítmico, de HP ou de espectro. Logo é aplicável à forma
física (Q_N=W_NC_N) assim que a realização concreta de (W_N) fornecer sua
inversa à esquerda.

Também foi compilada a especialização real já presente na biblioteca:

```lean
finiteCanonicalCameraReadout_mulVec_eq_zero_iff_raw_mulVec_eq_zero
```

Sob

```lean
(finiteCameraRowGram C).PosDef,
```

ela dá literalmente

\[
(CC^{\mathsf T})^{-1/2}Cx=0\Longleftrightarrow Cx=0.
\]

Assim a etapa de whitening não é uma estimativa, nem uma hipótese de
positividade Hankel: é uma identidade de núcleo.

### 29.2. Correspondência honesta dos objetos Lean

O inventário corrigiu algumas possíveis ambiguidades de notação.

| Notação do laboratório | Objeto Lean mais próximo | Estado |
|---|---|---|
| (C_N), matriz complexa literal das leituras | `NativeCarrySpectralWeyl.Limits.finiteCameraMatrix cutoff camera` | existe; para seis câmeras usar `camera = sixCamera` |
| versão real da mesma matriz de coeficientes | `finiteLiteralSixCameraMatrix cutoff` | existe e tem Gram de linhas literal |
| (W_N=(C_NC_N^*)^{-1/2}) finito | `positiveInverseSqrt (finiteCameraRowGram C)` no modelo real; `atlasSixCameraWhiteningMatrix cutoff` para o candidato com Gram finito normalizado | a definição existe; não há ainda prova global de `PosDef` do Gram literal finito nem bridge de complexificação que a instancie como o (W_N) físico |
| whitening `sixCameraInverseSqrt` | `sixCameraInverseSqrt` | é o inverse square root do **Gram periódico limite**, não deve ser identificado automaticamente com o (W_N) físico de cutoff |
| (L_N=\operatorname{diag}(\log(n+1))) | `CPFormal.Analytic.Cp.finiteRealSpectralGenerator N` | existe; `finiteRealSpectralEvolution N t` é sua evolução unitária |
| `sixCameraLogOperator` | `NativeCarrySpectralWeyl.Finite.sixCameraLogOperator` | é o primeiro momento whitened no espaço das seis câmeras; não é o diagonal espectral (L_N) no espaço de estados |
| (e^{-itL_N}\alpha_N) | `finiteRealSpectralStateVector N t` | existe e `finiteRealSpectralStateVector_eq_evolution_zero` prova exatamente a órbita a partir da semente crítica |
| (j_N=\alpha_N/\lvert\alpha_N\rvert) | nenhum objeto nomeado separado | a normalização não nula é inofensiva para zeros; `smul_finiteCameraPhysicalRawReadout_eq_zero_iff` formaliza isso |

Com isso foi definido o readout matricial genuinamente finito

```lean
finiteCameraPhysicalRawReadout cutoff camera time
  : index → ℂ
```

pela expressão

\[
 C_N\,\psi_N(t),\qquad
 \psi_N(t)=\texttt{finiteRealSpectralStateVector}\ N\ t.
\]

E, para qualquer whitening complexo explicitamente munido de inversa à
esquerda, foi definido

```lean
finiteCameraPhysicalWhitenedReadout whitening cutoff camera time.
```

O theorem

```lean
finiteCameraPhysicalWhitenedReadout_eq_zero_iff_raw_eq_zero
```

é Gate A aplicado à órbita; portanto o whitening não cria nem remove
cegueira coletiva.

### 29.3. O resultado que impede um handoff falso para `F`

O objeto canônico que entra em
`CompletedNativeMultibaseCollectiveReadout.lean` não é o head bruto de
cutoff. Por definição ele contém uma cauda analítica de células centrais
inteiras. Para uma câmera,

```lean
finiteCameraPhysicalRawHead camera cutoff time
finiteCameraPhysicalCompletionTail camera cutoff time
```

satisfazem a identidade literal compilada

```lean
finiteCameraPhysicalRawHead_add_completionTail_eq_completed
```

isto é,

\[
\boxed{
H_{b,N}(t)+T_{b,N}(t)
=\operatorname{completedNativeCharacteristic}(b,N,\operatorname{nativeLine}(t)).
}
\]

Em particular, se (F(t)=0), a universalidade completada fornece

\[
\boxed{H_{b,N}(t)=-T_{b,N}(t).}
\]

Isso está registrado como

```lean
finiteCameraPhysicalRawHead_eq_neg_completionTail_of_nativeZero
finiteSixCameraPhysicalRawHead_eq_neg_completionTail_of_nativeZero.
```

Consequentemente, no zero canônico,

\[
H_{b,N}(t)=0\Longleftrightarrow T_{b,N}(t)=0,
\]

e analogamente para o vetor das seis câmeras. Este é o resultado decisivo:
**a passagem do head finito bruto para a característica completada é aditiva,
e não um simples fator escalar não nulo.** Portanto não é legítimo concluir
que um (C_Ne^{-itL_N}j_N) puramente truncado tem o mesmo zero-set de `F`
apenas a partir da invariância de kernel sob whitening.

### 29.4. Seam mínimo restante

Há duas setas, de natureza diferente, ainda ausentes; a segunda é a
substancial.

```text
finiteCameraMatrix cutoff sixCamera
  * finiteRealSpectralStateVector (finiteFamilyWindow cutoff sixCamera) t
  ──(stencil expansion ainda não nomeada)──►
finiteBracketCharacteristic (sixCamera i) cutoff (nativeLine t)
  ──(+ whole-center completion tail)──►
completedNativeCharacteristic (sixCamera i) cutoff (nativeLine t)
  ──(normalização já formalizada)──► F(t).
```

A primeira é uma igualdade finita de expansão de matriz/stencil. Os dois
lados já usam literalmente os mesmos coeficientes `finiteCoefficientAt` e a
mesma órbita de Dirichlet, mas o repositório ainda não possui o theorem que
nomeia essa igualdade para `finiteCameraPhysicalRawReadout`.

A segunda não é uma lacuna cosmética: é o acréscimo da cauda analítica
inteira. Se o objeto físico final deve ser o readout completado, a rota limpa
é definir/adicionar esse canal de cauda antes do handoff. Se se insistir no
vetor puramente finito, é necessário provar a condição adicional

\[
\boxed{T_{6,N}(t)=0\quad\text{nos zeros de }F,}
\]

que não segue de whitening, da normalização de (j_N), nem da
universalidade das câmeras completadas. Não foi assumida nem alegada nesta
rodada.

Logo, o enunciado correto atualmente fechado é

\[
W_N C_N\psi_N(t)=0\Longleftrightarrow C_N\psi_N(t)=0
\]

para qualquer (W_N) com inversa à esquerda; o enunciado

\[
Q_Ne^{-itL_N}j_N=0\Longleftrightarrow F(t)=0
\]

continua condicionado exatamente à integração do ledger de cauda (e à
expansão matricial/stencil acima). Não se deve promover ainda para o bridge
espectral de altura o readout finito sem esse adapter de completamento.

### 29.5. Separação preservada e validação

Nada nesta rodada altera:

```text
rota B: six-source/câmera → certificado HP concreto;
rota característica canônica: câmeras completadas → F → espectro,
  condicionado ao certificado HP;
rota física finita: matriz/orbita/whitening → ainda requer completion-tail adapter.
```

Foram validados localmente, sem PR, push ou GitHub Actions:

```text
lake build CarrySelfAdjointOperator.FinitePhysicalSixCameraWhiteningBridge
lake env lean CarrySelfAdjointOperator/FinitePhysicalSixCameraWhiteningBridgeAudit.lean
```

O audit dos seis theorems expostos lista somente:

```text
propext, Classical.choice, Quot.sound.
```

## 30. Readout físico finito completado → `F` → signed-height

### 30.1. Gate A fechado: matriz literal = stencil finito

O módulo

```text
FinitePhysicalSixCameraWhiteningBridge.lean
```

agora contém o theorem de expansão que antes faltava nomear:

```lean
finiteCameraPhysicalRawReadout_apply_eq_finiteBracketCharacteristic
```

Para uma família finita de câmeras, uma linha `i` e uma janela comum
camera-completa, ele prova

\[
\boxed{
\bigl(\texttt{finiteCameraMatrix}\ N\ \texttt{camera}\bigr)
\,\texttt{finiteRealSpectralStateVector}\ N\ t\,(i)
=
\texttt{finiteBracketCharacteristic}
(\texttt{camera}\ i)\ N\ (\texttt{nativeLine}\ t).
}
\]

A prova é inteiramente finita:

1. `finiteRealSpectralStateVector` é reescrito coordenadamente como o valor
   de Dirichlet positivo em `nativeLine`;
2. a linha da matriz se expande pelos `finiteCoefficientAt`;
3. o suporte do stencil fica dentro de qualquer janela que contenha
   `finiteCameraWindow`; e
4. `evalDirichletStencil_finiteStencil` identifica a soma com o head de
   bracket.

Para o pacote histórico, a forma vetorial pronta é:

```lean
finiteSixCameraPhysicalRawReadout_eq_rawHead
```

e diz

\[
\boxed{
C_Ne^{-itL_N}\alpha_N
=H_{6,N}(t).}
\]

Aqui `finiteRealSpectralStateVector` é a órbita não normalizada
\(e^{-itL_N}\alpha_N\); a normalização não nula para (j_N) continua sendo
zero-invariante pelo theorem da seção 29.

### 30.2. Gate B/C fechado: soma literal com a cauda

A cauda não foi reinventada. O vetor existente é reaproveitado sob o nome

```lean
finiteSixCameraPhysicalCompletionTail cutoff time : Fin 6 → ℂ.
```

Sua coordenada `i` é literalmente

```lean
finiteCameraPhysicalCompletionTail (sixCamera i) cutoff time
```

isto é, a mesma soma de centros inteiros omitidos que já ocorria no ledger
escalar.

Foram definidos:

```lean
finiteSixCameraCompletedNativeReadout cutoff time
finiteSixCameraCompletedPhysicalReadout cutoff time
```

com os significados respectivos

\[
\mathcal C^{\mathrm{comp}}_{6,N}(t)_i
=\operatorname{completedNativeCharacteristic}
(b_i,N,\operatorname{nativeLine}(t)),
\]

e

\[
\widetilde C_N(t)
=C_Ne^{-itL_N}\alpha_N+T_{6,N}(t).
\]

A costura principal está compilada como

```lean
finiteSixCameraCompletedPhysicalReadout_eq_completedNativeReadout
```

e é uma igualdade vetorial literal:

\[
\boxed{
\widetilde C_N(t)=\mathcal C^{\mathrm{comp}}_{6,N}(t).
}
\]

Portanto a correção aditiva deixou de ser apenas uma interpretação do
checkpoint: ela está inserida no readout físico formalizado.

### 30.3. Relação com o readout coletivo canônico já existente

O objeto já existente

```lean
completedNativeSixCameraCollectiveReadout (fun _ => cutoff) time
```

não é literalmente igual a `finiteSixCameraCompletedPhysicalReadout`: ele
remove, coordenada a coordenada, os fatores de câmera não nulos e conserva o
fator comum de completion. A diferença é portanto de normalização de valores,
não de evento de cegueira.

O theorem compilado

```lean
finiteSixCameraCompletedPhysicalReadout_eq_zero_iff_collectiveReadout_eq_zero
```

prova:

\[
\widetilde C_N(t)=0
\Longleftrightarrow
\texttt{completedNativeSixCameraCollectiveReadout}(t)=0.
\]

Em seguida,

```lean
finiteSixCameraCompletedPhysicalReadout_eq_zero_iff_nativeZero
finiteSixCameraCompletedPhysicalReadout_isZeroEquivalent
```

fecham o handoff procurado:

\[
\boxed{
\widetilde C_N(t)=0
\Longleftrightarrow
\texttt{completedNativeOperatorCharacteristic}(t:\mathbb C)=0.
}
\]

Assim o objeto físico correto de cutoff finito é, formalmente,

```text
raw matrix orbit + whole-center completion tail,
```

e não o head matricial truncado por si só.

### 30.4. Gate D e downstream já existente

Para um whitening complexo explicitamente munido de inversa à esquerda,
foi definido

```lean
finiteSixCameraCompletedPhysicalWhitenedReadout whitening cutoff time
```

e os theorems

```lean
finiteSixCameraCompletedPhysicalWhitenedReadout_eq_zero_iff_completed_eq_zero
finiteSixCameraCompletedPhysicalWhitenedReadout_eq_zero_iff_nativeZero
finiteSixCameraCompletedPhysicalWhitenedReadout_isZeroEquivalent
```

provam:

\[
W_N\widetilde C_N(t)=0
\Longleftrightarrow
\widetilde C_N(t)=0
\Longleftrightarrow F(t)=0.
\]

O whitening vem **depois** do completamento. Não foi assumido que esse
`whitening` já seja o inverse square root canônico do Gram físico literal;
só é requerida a identidade de inversa à esquerda que já basta para
preservar kernels.

Sob o `CompletedNativeRealHPCarrierCertificate` que já era condição de todo
downstream, há agora corolários pequenos, sem novos operadores:

```lean
finiteSixCameraCompletedPhysicalReadout_zero_hasSignedHeightEigenvalue
finiteSixCameraCompletedPhysicalReadout_zero_iff_jacobiEigenvalue_inv_sq
finiteSixCameraCompletedPhysicalWhitenedReadout_zero_hasSignedHeightEigenvalue
finiteSixCameraCompletedPhysicalWhitenedReadout_zero_iff_jacobiEigenvalue_inv_sq.
```

Logo, para o objeto completado,

\[
\widetilde C_N(t)=0
\Longrightarrow t\in\sigma_p(H_{\mathrm{signed\ height}}),
\]

e, se (t\ne0),

\[
\widetilde C_N(t)=0
\Longleftrightarrow(t^2)^{-1}\in\sigma_p(J).
\]

As mesmas conclusões valem depois de qualquer whitening com inversa à
esquerda.

### 30.5. O que continua separado

Esta rodada fecha o handoff físico finito de zero-set. Ela não prova:

1. que o whitening físico concreto é literalmente
   \((C_NC_N^*)^{-1/2}\) para todo cutoff;
2. `PosDef` global do Gram literal finito ou sua ponte real--complexa;
3. igualdade de valores, derivadas, multiplicidades ou resíduos entre o
   readout físico completado e o readout canônico normalizado; ou
4. qualquer passagem (N\to\infty).

Essas lacunas não impedem a rota de zeros já fechada. Em particular, a
condição que antes faltava — adicionar o ledger de cauda antes de tentar
comparar com `F` — não é mais uma hipótese externa.

### 30.6. Validação

Foram validados localmente apenas os módulos envolvidos:

```text
lake env lean CarrySelfAdjointOperator/FinitePhysicalSixCameraWhiteningBridge.lean
lake build CarrySelfAdjointOperator.FinitePhysicalSixCameraWhiteningBridge
lake env lean CarrySelfAdjointOperator/FinitePhysicalSixCameraWhiteningBridgeAudit.lean
```

O audit dos treze theorems expostos lista somente:

```text
propext, Classical.choice, Quot.sound.
```

## 31. Estabilização exata do readout físico completado sob cutoff

### 31.1. Resultado fechado

O módulo

```text
CarrySelfAdjointOperator/FinitePhysicalSixCameraWhiteningBridge.lean
```

agora expõe

```lean
finiteSixCameraCompletedPhysicalReadout_cutoff_independent
```

e prova, para quaisquer `cutoff₁ cutoff₂ : ℕ` e `time : ℝ`, a igualdade
vetorial literal

\[
\boxed{
\widetilde C_{N_1}(t)=\widetilde C_{N_2}(t).
}
\]

A prova é extensão nas seis coordenadas seguida de

```lean
completedNativeCharacteristic_cutoff_independent
```

aplicado a cada `sixCamera i`. As duas premissas desse theorem já são
automáticas aqui: `two_le_sixCamera i` fornece a admissibilidade da câmera, e
`nativeLine time ∈ nativeScalarDomain` é descarregado por `simp` e
`norm_num`.

Portanto, nesta camada não há uma convergência a provar:

\[
\boxed{
H_N(t)+T_N(t)=\widetilde C(t)\qquad\text{para todo cutoff }N.
}
\]

O head truncado `H_N` e a tail `T_N` continuam individualmente dependentes do
cutoff. Apenas sua soma física completada estabiliza, e ela o faz
**exatamente**, não assintoticamente.

### 31.2. Compensação exata de cutoff

Foram formalizados tanto o enunciado por câmera como o pacote vetorial de
seis câmeras:

```lean
finiteCameraPhysicalRawHead_add_completionTail_cutoff_independent
finiteCameraPhysicalRawHead_sub_eq_completionTail_sub
finiteSixCameraPhysicalRawHead_sub_eq_completionTail_sub
```

Em particular,

\[
\boxed{
H_{N_2}(t)-H_{N_1}(t)=T_{N_1}(t)-T_{N_2}(t).
}
\]

Assim, elevar o cutoff não cria nem destrói informação no readout físico
completado: desloca exatamente uma parcela da tail para o head. A descrição
mais fiel é **exact cutoff compensation** (ou compensação exata de cutoff),
e não um contratermo introduzido por uma aproximação.

O theorem escalar já basta para qualquer família finita de câmeras
suportadas: basta tomar as coordenadas `head + tail` e aplicar
extensionalidade. Não foi criada outra API de família física apenas para
reempacotar essa consequência.

### 31.3. Representante cutoff-free, sem limite topológico

Foi definida a apresentação canônica

```lean
canonicalCompletedSixCameraPhysicalReadout
```

por `finiteSixCameraCompletedPhysicalReadout 0`. O cutoff `0` é usado somente
como representante seed-only da classe já provadamente independente de
cutoff; ele não é uma escolha geométrica adicional. O theorem

```lean
finiteSixCameraCompletedPhysicalReadout_eq_canonical
```

prova literalmente

\[
\widetilde C_N(t)=\widetilde C(t).
\]

Não se usam `Tendsto`, filtros, completude, `lim` ou uma construção de
Hilbert no infinito. A palavra “infinite” deve, portanto, ser evitada para
este objeto: o nome `canonicalCompleted...` registra corretamente que se
trata de uma apresentação cutoff-free por igualdade exata.

O `completedNativeSixCameraCollectiveReadout` anterior permanece útil, mas
não substitui esta nova definição: ele é o pacote de coordenadas **normalizadas**
e é zero-equivalente; o novo objeto preserva literalmente os valores físicos
não normalizados `raw head + whole-center tail`.

### 31.4. Zero-set e downstream reutilizados

Foram adicionados:

```lean
canonicalCompletedSixCameraPhysicalReadout_eq_zero_iff_nativeZero
canonicalCompletedSixCameraPhysicalReadout_isZeroEquivalent
canonicalCompletedSixCameraPhysicalReadout_zero_hasSignedHeightEigenvalue
canonicalCompletedSixCameraPhysicalReadout_zero_iff_jacobiEigenvalue_inv_sq
```

Sob o mesmo `CompletedNativeRealHPCarrierCertificate` já exigido pelo
downstream, conclui-se:

\[
\widetilde C(t)=0
\Longrightarrow t\in\sigma_p(H_{\mathrm{signed\ height}}),
\]

e, se `t ≠ 0`,

\[
\widetilde C(t)=0
\Longleftrightarrow(t^2)^{-1}\in\sigma_p(J).
\]

Nada de HP, Jacobi, Weyl ou do operador de altura foi reconstruído nesta
rodada; são somente corolários do bridge zero-equivalente já existente.

### 31.5. Whitening: o que é e o que não é independente de cutoff

O theorem novo

```lean
finiteSixCameraCompletedPhysicalWhitenedReadout_eq_zero_iff_canonical_eq_zero
```

explicita a distinção correta. Para cada whitening `W_N` que tenha sua
própria inversa à esquerda,

\[
W_N\widetilde C(t)=0
\Longleftrightarrow\widetilde C(t)=0
\Longleftrightarrow F(t)=0.
\]

Não foi provada — e não se deve inferir — a igualdade de valores

\[
W_{N_1}\widetilde C(t)=W_{N_2}\widetilde C(t),
\]

porque os whitenings concretos podem depender de `N`. A independência exata
de cutoff pertence ao readout físico completado **antes** do whitening; após
whitening, o que permanece fechado sem hipóteses extras é o zero-set.

### 31.6. Validação desta rodada

Foram verificados localmente os módulos diretamente afetados:

```text
lake env lean CarrySelfAdjointOperator/FinitePhysicalSixCameraWhiteningBridge.lean
lake build CarrySelfAdjointOperator.FinitePhysicalSixCameraWhiteningBridge
lake env lean CarrySelfAdjointOperator/FinitePhysicalSixCameraWhiteningBridgeAudit.lean
```

O audit foi estendido para a independência de cutoff, as duas identidades de
compensação, o representante canônico e os corolários espectrais. Ele continua
a reportar somente:

```text
propext, Classical.choice, Quot.sound.
```

## 32. Whitening físico finito concreto — Gram literal positivo, complexificação e handoff sem hipótese externa

### 32.1. O Gram literal correto foi localizado

O objeto novo

```lean
finitePhysicalSixCameraRowGram cutoff
```

é, por definição literal,

\[
G_N^\mathbb R
=
\texttt{finiteCameraRowGram}
  (\texttt{finiteLiteralSixCameraMatrix}\;N)
=C_N^\mathbb R(C_N^\mathbb R)^\mathsf T.
\]

Ele não é o `sixCameraGram` periódico e não foi identificado com o objeto
limite `sixCameraInverseSqrt`. A ponte de coordenadas já existente mostra que
as entradas são o Gram das linhas literais finitas; a nova prova trabalha
diretamente nesta matriz, sem importar uma positividade assintótica.

### 32.2. Positividade definida a partir de um minor estrutural uniforme

Foi provado:

```lean
finiteLiteralSixCameraMatrix_vecMul_injective
finitePhysicalSixCameraRowGram_posDef
```

para `1 ≤ cutoff`. A condição é mínima para esta realização: no cutoff `0` a
janela finita tem apenas três posições e, portanto, não pode conter um minor
de seis colunas que dê independência às seis linhas.

A prova não usa floating point, fitting, nem uma lista de certificados por
cutoff. Ela restringe todas as seis linhas às seis primeiras posições e mostra
exatamente dois regimes uniformes:

\[
\det M_1=880,
\qquad
\det M_N=960\quad(N\ge2).
\]

O primeiro é o template literal do cutoff `1`; o segundo é o mesmo minor no
regime em que cada entrada já coincide com o perfil periódico. Esses são
inteiros exatos verificados por `decide` no kernel; o argumento que passa do
minor à matriz completa é a injetividade da restrição, e daí

\[
\boxed{G_N^\mathbb R>0\qquad(N\ge1).}
\]

### 32.3. A raiz inversa positiva concreta e sua inversa à esquerda

Foram definidos:

```lean
finitePhysicalSixCameraRealWhitening
finitePhysicalSixCameraRealWhiteningInverse
finitePhysicalSixCameraRealWhitening_whitens
```

com

\[
W_N^\mathbb R=(G_N^\mathbb R)^{-1/2}
\]

na definição `positiveInverseSqrt` já existente. A positividade definida
anterior fornece `IsUnit` dessa raiz, e o theorem

```lean
finitePhysicalSixCameraRealWhiteningInverse_mul
```

fecha literalmente

\[
(W_N^\mathbb R)^{-1}W_N^\mathbb R=I.
\]

Além da invertibilidade requerida pelo bridge de kernel, o theorem
`finitePhysicalSixCameraRealWhitening_whitens` registra a normalização
canônica real completa:

\[
W_N^\mathbb R G_N^\mathbb R W_N^\mathbb R=I.
\]

### 32.4. Ponte real → complexa: o que foi provado, e o que não foi forçado

O repo já representa a matriz complexa literal como

```lean
finiteCameraMatrix cutoff sixCamera
```

e agora prova:

```lean
complexify_finiteLiteralSixCameraMatrix
complexify_finitePhysicalSixCameraRowGram
```

isto é,

\[
\operatorname{complexify}(C_N^\mathbb R)=C_N^\mathbb C,
\qquad
\operatorname{complexify}(G_N^\mathbb R)
=C_N^\mathbb C(C_N^\mathbb C)^\ast.
\]

O whitening usado pelo handoff físico é, portanto, definido honestamente por

\[
W_N=
\operatorname{complexify}\!\left((G_N^\mathbb R)^{-1/2}\right),
\]

e `finitePhysicalSixCameraWhiteningInverse_mul` constrói

\[
W_N^{-1}W_N=I.
\]

Não foi afirmada a igualdade mais forte

\[
W_N=(C_N^\mathbb C(C_N^\mathbb C)^\ast)^{-1/2}
\]

na álgebra funcional complexa do repo: essa exigiria uma ponte de
funcional calculus que não é necessária para o evento de cegueira. O que já
foi provado é precisamente a complexificação canônica do whitening real do
Gram literal e a sua invertibilidade sobre `ℂ`.

### 32.5. Handoff concreto sem `hleft` fornecido pelo usuário

Foi definido:

```lean
finitePhysicalSixCameraWhitenedCompletedReadout cutoff time
```

e formalizada a fórmula de laboratório como reescrita:

```lean
finitePhysicalSixCameraWhitenedCompletedReadout_eq_whitening_mulVec_raw_add_tail
```

ou seja,

\[
\widetilde\Phi_N(t)=
W_N\bigl(C_N\psi_N(t)+T_N(t)\bigr).
\]

Para todo `1 ≤ cutoff`, a hipótese abstrata `hleft` desaparece no theorem:

```lean
finitePhysicalSixCameraWhitenedCompletedReadout_eq_zero_iff_nativeZero
```

que prova

\[
\boxed{
\widetilde\Phi_N(t)=0
\iff
F(t)=0.
}
\]

Os corolários reutilizam, sem reconstrução, o bridge já existente:

```lean
finitePhysicalSixCameraWhitenedCompletedReadout_zero_hasSignedHeightEigenvalue
finitePhysicalSixCameraWhitenedCompletedReadout_zero_iff_jacobiEigenvalue_inv_sq
```

Assim, sob o mesmo `CompletedNativeRealHPCarrierCertificate`, cegueira física
concretamente whitened implica autovalor do signed-height; para `t ≠ 0`, é
equivalente ao autovalor Jacobi em `(t²)⁻¹`.

### 32.6. Dependência de cutoff preservada corretamente

O vetor não-whitened `canonicalCompletedSixCameraPhysicalReadout` continua
exatamente estabilizado em cutoff. Já `finitePhysicalSixCameraWhitening N`
pode variar com `N`; não foi provada igualdade entre whitenings de cutoffs
distintos, nem ela é necessária. O resultado concreto é, para cada cutoff
admissível,

\[
W_N\widetilde C(t)=0
\iff
\widetilde C(t)=0
\iff F(t)=0.
\]

Logo nenhuma promoção topológica `N\to\infty` é necessária para esta camada
de zero-set. A eventual identificação da raiz funcional complexa e qualquer
estudo de valores/multiplicidades permanecem proposições separadas.

### 32.7. Validação

Os módulos desta rodada são:

```text
CarrySelfAdjointOperator/FinitePhysicalSixCameraConcreteWhitening.lean
CarrySelfAdjointOperator/FinitePhysicalSixCameraConcreteWhiteningAudit.lean
```

Foram verificados localmente o módulo, seu target Lake e o audit. O audit
inclui o minor, a injetividade, `PosDef`, as duas inversas, a ponte de Gram
real→complexa, a equivalência concreta de zeros e os dois corolários
espectrais. Ele reporta somente:

```text
propext, Classical.choice, Quot.sound.
```

## 33. Canal físico completado analítico e auditoria da realização lossless

### 33.1. A extensão complexa correta já existe no ledger analítico

O canal físico completo não precisa esperar uma construção Potapov para ser
visto fora do eixo real.  O objeto escalar já usado pela completion,

```lean
completedNativeCharacteristic camera cutoff z
```

é, por definição, o head finito de stencil mais a série inteira dos centros
omitidos.  A nova embalagem vetorial em
`CompletedPhysicalSixCameraAnalyticReadout.lean` apenas preserva esse fato
para as seis câmeras, sem inventar uma órbita finita inexistente:

```lean
finiteSixCameraPhysicalRawHeadComplex
finiteSixCameraPhysicalCompletionTailComplex
finiteSixCameraCompletedPhysicalReadoutComplex
```

e prova literalmente:

```lean
finiteSixCameraPhysicalRawHeadComplex_add_completionTailComplex_eq_completed
```

isto é,

\[
\widetilde C_N(z)=H_N(z)+T_N(z).
\]

Em cada coordenada e no `bracketDomain`, a mesma função é a característica
de bracket já formalizada:

```lean
finiteSixCameraCompletedPhysicalReadoutComplex_apply_eq_bracketCharacteristic
finiteSixCameraCompletedPhysicalReadoutComplex_apply_differentiableOn
```

Assim a holomorfia já disponível para a característica de bracket foi
transportada formalmente, coordenada por coordenada, para o vetor completado.
Não foi necessário introduzir uma segunda teoria de continuação analítica.

Na linha nativa,

\[
\widetilde C_N(\operatorname{nativeLine}(t))
=\texttt{finiteSixCameraCompletedPhysicalReadout}\ N\ t,
\]

com theorem
`finiteSixCameraCompletedPhysicalReadoutComplex_nativeLine`.

Importante: o nome *raw head complex* designa a extensão do stencil.  A
igualdade com a órbita matricial física literal foi provada no repo na linha
real; este checkpoint não afirma uma realização matricial exponencial finita
para a tail em `z\in\mathbb C`.

### 33.2. Whitening constante e decomposição visível correta

O whitening literal finito construído na seção 32 não depende de `z`.  Foi
portanto definida a função vetorial complexa

```lean
finitePhysicalSixCameraWhitenedCompletedReadoutComplex cutoff z
```

e provado o ledger estrutural:

```lean
finitePhysicalSixCameraWhitenedCompletedReadoutComplex_eq_head_add_completion
```

ou seja,

\[
\boxed{
\widetilde\Phi_N(z)
=\Phi_N^{\rm head}(z)+W_NT_N(z).
}
\]

O segundo termo é uma contribuição **aditiva** de completion.  Não foi
absorvido em gauge multiplicativo e não foi declarado um estado oculto sem
proveniência.

Na linha real a extensão é exatamente o canal físico já fechado:

```lean
finitePhysicalSixCameraWhitenedCompletedReadoutComplex_nativeLine
finitePhysicalSixCameraWhitenedCompletedReadoutComplex_nativeLine_eq_zero_iff_nativeZero
```

Logo, para cada `1 ≤ cutoff`, continua válido

\[
\widetilde\Phi_N(\operatorname{nativeLine}(t))=0
\iff F(t)=0.
\]

### 33.3. Secular root-free do canal físico, sem alegação Potapov

Foi acrescentado o secular real de canal visível efetivo:

```lean
finitePhysicalSixCameraWhitenedCompletedRootFreeSecular cutoff time
```

com

\[
\Delta_N^{\rm phys}(t)
=4\sum_{i:\operatorname{Fin}6}
\left|\widetilde\Phi_N(t)_i\right|^2.
\]

Os theorems

```lean
finitePhysicalSixCameraWhitenedCompletedRootFreeSecular_eq_zero_iff
finitePhysicalSixCameraWhitenedCompletedRootFreeSecular_eq_zero_iff_nativeZero
finitePhysicalSixCameraWhitenedCompletedRootFreeSecular_isZeroEquivalent
```

provam, puramente por soma finita de quadrados,

\[
\boxed{\Delta_N^{\rm phys}(t)=0\iff F(t)=0.}
\]

Este é um secular root-free legítimo para o canal físico completado.  Ele
**não** é ainda identificado com determinante, minor ativo ou defeito de
round-trip de uma matriz Potapov; a igualdade com uma tal realização seria
um theorem novo, não uma convenção de nomenclatura.

Sob o `CompletedNativeRealHPCarrierCertificate` preexistente, os corolários
curtos

```lean
finitePhysicalSixCameraWhitenedCompletedRootFreeSecular_zero_hasSignedHeightEigenvalue
finitePhysicalSixCameraWhitenedCompletedRootFreeSecular_zero_iff_jacobiEigenvalue_inv_sq
```

também entregam o secular físico root-free ao mesmo signed-height/Jacobi
downstream, sem criar nenhuma estrutura espectral adicional.

### 33.4. Auditoria honesta: o que existe de lossless e o que não foi conectado

A busca por `Potapov`, `colligation`, `Q_hid`, `O_N`, `active block` e
`round trip` não encontrou implementação Lean da matriz laboratorial

\[
O_Ne^{izL_N}O_N^*,
\]

nem de seus blocos ativos/gauge.  As referências a Potapov em módulos de
readout são guardrails documentais sobre uma realização futura; não são uma
definição ou theorem que possa ser reutilizado.

O repo possui, sim, realizações conservativas genuínas, mas em outra
genealogia:

* `finiteEnrichedMovingCameraTfvdState` fornece exatamente o par finito
  visible/blind com Parseval, para uma família de estados
  `FiniteHilbertFamily state CarryVerticalL2`;
* `canonicalCompletedC3NaimarkState` e
  `canonicalCompletedC3SixCameraSource` vivem nos carriers C3
  TFVD/Green/Naimark completados;
* `CanonicalNaimarkStateReadout` fornece a coisometria abstrata
  `realifiedNaimarkAdjoint ∘ realifiedNaimarkPort = I`;
* `CompletedC3GenuineBracketGreenTransport` fornece um ledger separado de
  radial, off-diagonal, seam, provenance e prefixos Hilbertianos.

Mas nenhuma dessas cadeias contém theorem de tipo/valor que identifique

\[
\sum_{m\ge0}
\operatorname{centerBracketTerm}(b,z,m+N)
\]

com uma saída Green, boundary, return, blind ou Naimark.  O símbolo
`completion` em alguns ledgers C3 significa completion de prefixos
Hilbertianos; ele não é automaticamente a `finiteCameraPhysicalCompletionTail`
da característica física.

Há ainda dois guardrails formais já presentes:

* `FiniteEnrichedCameraNaimarkEscapeIntertwining.lean` explicita que falta
  uma ponte entre o projector finito de câmeras e o projector Naimark
  completado, sob o nome
  `NaimarkProjectorIntertwiningSeam`;
* `CompletedNativeAllCameraPortAmbientNoGo.lean` elimina o porto Naimark
  global histórico como canal de escape para o excesso ambiente.  Esse
  no-go não refuta a tail física, mas impede que aquele porto seja reciclado
  sem uma nova identificação.

### 33.5. O menor seam restante para uma realização conservativa

O próximo dado geométrico necessário não é outro secular nem uma nova prova
espectral.  É uma realização de porto para a tail analítica, com uma leitura
de seis câmeras compatível.  Conceitualmente, deve haver uma cadeia já
proveniente de Green/return/whole-center:

\[
z\longmapsto X^{\rm tail}_N(z)
\quad\xrightarrow{\;P_6\; }\quad
T_N(z)\in\mathbb C^6,
\]

e uma realização para o head no mesmo carrier, tal que a leitura de
`X^{head}_N(z)+X^{tail}_N(z)` seja `H_N(z)+T_N(z)`.  Só depois dessa seta
estar formalizada faz sentido perguntar se o carrier ampliado é conservativo
e construir uma coligação/characteristic matrix.

Em termos de tipos atuais, a ponte precisa relacionar a saída física

```lean
finiteSixCameraPhysicalCompletionTailComplex cutoff : ℂ → Fin 6 → ℂ
```

com uma saída finita de um carrier como
`RealifiedNaimarkComplexification` ou do par
`FiniteHilbertFamily _ CarryVerticalL2`; hoje não há mapa de leitura nem
theorem de igualdade que faça essa ligação.  Também não deve ser contornada
por um embedding separável/rank-one, pois essa arquitetura já é incompatível
com os no-gos da rota incidencial.

Portanto o status desta rodada é:

\[
\boxed{
\text{canal completado analítico e secular físico: FECHADOS};
\quad
\text{realização conservativa da tail: OPEN}.
}
\]

Não há justificativa atual para afirmar que a antiga realização
finito-dimensional do head implementa o canal completado, nem para promover
automaticamente seus setores gauge/bloco ativo à nova característica.

### 33.6. Validação

Foram adicionados e verificados localmente:

```text
CarrySelfAdjointOperator/CompletedPhysicalSixCameraAnalyticReadout.lean
CarrySelfAdjointOperator/CompletedPhysicalSixCameraAnalyticReadoutAudit.lean
```

Foram executados o `lake env lean` do módulo e do audit, e os dois targets
Lake correspondentes. O audit imprime somente:

```text
propext, Classical.choice, Quot.sound.
```

## 34. Diagnóstico: shift de cutoff da cauda versus shift Hankel (2026-09-24)

### 34.1. Veredito

Esta rodada **não** encontrou um intertwiner linear natural

\[
\mathcal M B_{\rm tail}=A\mathcal M
\]

entre a cauda de centros alinhados e o operador de multiplicação da torre
Hankel.  A razão não é uma lacuna de notação: os dois shifts agem em eixos
distintos, e a passagem concreta que produz os momentos contém uma
normalização não linear.

O diagrama correto atualmente é:

\[
\begin{array}{ccccc}
\text{centros alinhados / cutoff }N
&\xrightarrow{\;N\mapsto N+1\;}&
\text{centros alinhados / cutoff }N+1
\\[1mm]
\downarrow\;\text{head + tail, completion}
&&\downarrow\;\text{head + tail, completion}
\\[1mm]
F
&=&F
\\[1mm]
\downarrow\; -F'/(2F)
&&\downarrow\; -F'/(2F)
\\[1mm]
\text{jets / primeira coluna}
&\xrightarrow{\;p,q\text{ diagonal}\;}&
\text{torre }C_{p,q}.
\end{array}
\]

O primeiro shift é uma translação de **centros aritméticos**; o segundo é
multiplicação pela variável de momento / transporte de **ordem de jet**.
Eles só devem ser relacionados após o functor de completion e resposta
normalizada, não por identificação direta de índices.

### 34.2. Índices e shifts, sem identificação indevida

| índice | objeto | operação que ele enumera | shift literal |
|---|---|---|---|
| `m` | `centerBracketTerm b s m` | centro alinhado aritmético | remove/avança um centro da cauda |
| `N` | cutoff da câmera | início da cauda e tamanho do head | `N ↦ N+1` |
| `n` | `canonicalCompletedNativeLogDerivativeMoment n` | ordem da série/jato normalizado | `n ↦ n+1` corresponde à multiplicação por `y` no modelo Stieltjes condicional |
| `p,q` | torre polarizada `C_{p,q}` | duas ordens de jet | `C_{p,q+1}=C_{p+1,q}` |
| `i,j` | seção Hankel | índices de monômios em um prefixo | `G_{ij}=h_{i+j}`, `K_{ij}=h_{i+j+1}` |

A cauda literal é

\[
T_{b,N}(s)=\sum_{m\ge0}a_{b,N+m}(s),\qquad
a_{b,k}(s)=\texttt{centerBracketTerm}(b,s,k),
\]

e agora possui o theorem compilado

```lean
finiteCameraPhysicalCompletionTail_succ
```

que prova, para `2 ≤ camera`,

\[
\boxed{T_{b,N+1}(t)=T_{b,N}(t)-a_{b,N}(\operatorname{nativeLine}(t)).}
\]

Depois de qualquer vestimenta diagonal não nula, essa é a versão conjugada do
backward shift unilateral descrito nos laboratórios. Ela não é, por si, uma
lei de avanço de ordem de momento.

Do lado da torre, o theorem já existente e reexportado pelo diagnóstico é

```lean
canonicalCompletedNativeMomentTower_shift
```

isto é,

\[
\boxed{C_{p,q+1}=C_{p+1,q}.}
\]

É esta última identidade que dá `G_{i,j+1}=K_{ij}=G_{i+1,j}` após a separação
de paridade.

### 34.3. Álgebra finita de `G/K` formalizada

Foi adicionado o módulo independente

```text
CarrySelfAdjointOperator/FiniteHankelShiftBoundaryCorrection.lean
```

Ele trabalha numa seção não vazia de dimensão `N + 1` e define o shift de
elevação truncado `finiteHankelRaisingShift N`, orientação

\[
Se_j=e_{j+1}\quad(j<N),\qquad Se_N=0.
\]

Os theorems compilados mostram:

\[
K=GS+B,
\]

onde `B = finiteHankelShiftBoundaryCorrection` é nulo fora da coluna final e
sua coluna final é exatamente a coluna final de `K`.  Em convenção de seção
de dimensão `n`, isto é

\[
(K-GS)_{ij}=0\;(j<n-1),\qquad
(K-GS)_{i,n-1}=K_{i,n-1}=h_{i+n}.
\]

Sob a hipótese condicional `hG : G.PosDef`, o módulo define

\[
A=G^{-1}K,
\qquad
c=Ae_{n-1}=G^{-1}Ke_{n-1},
\]

e prova literalmente

\[
\boxed{A=S+c e_{n-1}^{\!*}},
\qquad
\boxed{GA=K},
\qquad
\boxed{A^{\mathsf T}G=K}.
\]

Os nomes Lean são:

```lean
shiftedHankel_eq_hankelGram_mul_finiteHankelRaisingShift_add_boundary
hankelGram_mul_finiteHankelGalerkinMultiplication
finiteHankelGalerkinMultiplication_transpose_mul_hankelGram
finiteHankelGalerkinMultiplication_eq_raisingShift_add_boundaryColumn
```

Também foi formalizada a identidade de whitening com a raiz positiva já usada
no repo:

\[
G^{1/2}AG^{-1/2}=G^{-1/2}KG^{-1/2},
\]

e a simetria do lado direito, nos theorems:

```lean
finiteHankelSqrt_mul_galerkin_mul_inverseSqrt_eq_whitened
finiteHankelWhitenedMultiplication_isSymm
```

A conservação
\(e^{-itA*}G e^{-itA}=G\) é o corolário matricial padrão de
\(A^{\mathsf T}G=GA\); ela foi verificada no laboratório abaixo, mas não foi
adicionada como uma nova API de exponencial matricial porque não é necessária
ao downstream Jacobi já existente.

**Guardrail:** esta construção é álgebra de compressão condicional em
`hG`. Ela não descarrega `CanonicalCompletedNativeStieltjesPositivity`, nem
substitui a torre Jacobi projectiva baseada no LDL canônico. A positividade
nativa all-order continua sendo o gate descrito nas seções anteriores.

Sob uma representação Stieltjes (hipótese, não fato novo deste checkpoint),
`A` é a compressão Galerkin de `p(y) ↦ y p(y)` em
\(\operatorname{span}\{1,y,\ldots,y^{n-1}\}\). A coluna de bordo é
precisamente o termo que sai do espaço, \(y\,y^{n-1}=y^n\).

### 34.4. Onde a linearidade falha

O repo fornece a genealogia concreta:

```text
bracket–TFVD Wronskian
→ canonicalC3BracketTfvdNormalizedResponse
→ Taylor coefficients
→ odd coefficients = canonicalCompletedNativeLogDerivativeMoment.
```

O theorem compilado

```lean
canonicalC3BracketTfvdResponseJet_odd_eq_moment
```

reexporta a identificação em toda ordem. Mas a resposta é

\[
R(F)=-\frac{F'}{2F},
\]

não um operador linear de `F`. Para qualquer escalar não nulo,
\(R(\lambda F)=R(F)\), enquanto um mapa linear não nulo teria
\(L(\lambda F)=\lambda L(F)\). Portanto não há uma promoção natural,
linear e homogênea da cauda/characterística crua diretamente para a sequência
de momentos. O primeiro ponto exato de falha da tentativa ingênua é a divisão
por `F` em `completedGreenNormalizedResponse`.

Antes disso, a cauda ainda não determina sequer a característica por um mapa
linear isolado: para um cutoff fixo, a característica completada é
`head_N + tail_N`, uma soma afim no termo de tail. Depois da completion, a
característica é cutoff-independent; os momentos também são
cutoff-independent. Assim, deslocar o cutoff é uma mudança de apresentação,
enquanto deslocar a ordem de momento é uma operação interna da série já
normalizada.

Os no-gos existentes reforçam essa separação: a realização causal BR2 falha a
primeira igualdade Hankel em `BR2CausalShiftDefect.lean`, e o clock material
de um bloco C3, embora satisfaça seu shift interno, possui energia de ordem
zero incompatível com o momento nativo sem uma calibração adicional
(`nativeBlockSeededData_zero_energy_ne_nativeMoment`).

### 34.5. Laboratório reproduzível

O script

```text
research/tail-hankel-shift-diagnosis-2026-09-24/tail_hankel_shift_lab.py
```

reimplementa a definição literal de `centerBracketTerm` e testou as câmeras
`2,3,4,5,6,7`, cutoffs `8,16,32,64` e tempos `0`, `1` e
`14.134725141734693790`, sem usar esse último número para construir qualquer
carrier. A forma finita exata do shift de tail teve resíduo máximo

\[
6.59\times10^{-83}
\]

em aritmética de 80 dígitos. A compensação finita head/tail foi testada com o
mesmo endpoint para os dois lados.

O mesmo script testa a álgebra universal `G/K` num modelo Stieltjes atômico
**declaradamente sintético**: para dimensões 2, 3 e 4, os resíduos de
`K - G*S - B`, `GA-K`, `AᵀG-K`, da identidade de whitening e da conservação
métrica exponenciada ficaram entre zero exato e aproximadamente
\(2\times10^{-78}\) em aritmética de 80 dígitos. Isso valida a forma da
álgebra; não é evidência de `PosDef` nativa concreta.

O relatório JSON reproduzível foi salvo em:

```text
research/tail-hankel-shift-diagnosis-2026-09-24/tail_hankel_shift_lab_report.json
```

### 34.6. Validação e axiomas

Foram acrescentados:

```text
CarrySelfAdjointOperator/TailCutoffMomentShiftDiagnosis.lean
CarrySelfAdjointOperator/FiniteHankelShiftBoundaryCorrection.lean
CarrySelfAdjointOperator/TailCutoffMomentShiftDiagnosisAudit.lean
```

e foi executado localmente:

```bash
lake build \
  CarrySelfAdjointOperator.TailCutoffMomentShiftDiagnosis \
  CarrySelfAdjointOperator.FiniteHankelShiftBoundaryCorrection \
  CarrySelfAdjointOperator.TailCutoffMomentShiftDiagnosisAudit
```

O audit dos nove theorems novos/imediatos imprimiu somente:

```text
propext, Classical.choice, Quot.sound.
```

Nenhum push, PR ou GitHub Action foi acionado nesta rodada.

## 35. Princípio do transporte completado pelo bordo (2026-09-24)

O diagnóstico anterior de que os shifts da cauda e de Hankel **não** são um
mesmo operador ganhou uma formulação positiva comum.  Eles são duas
instâncias orientadas de uma mesma álgebra de defeito de bordo, mas com papéis
distintos:

\[
\boxed{
U_{\rm cut}\text{ muda a representação e desaparece após síntese},
\qquad
S_{\rm mom}\text{ propaga ordem dentro do objeto sintetizado}.
}
\]

### 35.1. Forma de síntese

O novo módulo
`CarrySelfAdjointOperator/BoundaryCompletedTransport.lean` define, para
mapas lineares

\[
\beta:X\to P,
\qquad S:X\to X,
\qquad J:P\to Y,
\qquad R:X\to Y,
\]

o transporte e a síntese

\[
U(p,x)=(p+\beta x,Sx),
\qquad
\Sigma(p,x)=Jp+Rx.
\]

Ele prova literalmente a equivalência

\[
\boxed{
J\beta+RS=R
\iff
\Sigma U=\Sigma.
}
\]

Equivalentemente, o mesmo arquivo prova exatamente a escrita por defeito:

\[
\boxed{R(I-S)=J\beta.}
\]

Os theorems são:

```lean
boundarySynthesis_comp_boundaryCompletedTransport
isBoundaryCompletedSynthesis_of_synthesis_invariant
isBoundaryCompletedSynthesis_iff_synthesis_invariant
isBoundaryCompletedSynthesis_iff_readout_id_sub_interior_eq_port_boundary
```

Assim, a frase “o defeito de transportar o interior é o que emerge pelo
porto” ficou uma identidade formal, não apenas uma analogia.

### 35.2. Instância literal da tail

Para uma sequência somável `tail : ℕ → ℂ`, foram definidos

\[
S^*a=(a_{m+1})_{m\ge0},
\qquad
U_{\rm cut}(H,a)=(H+a_0,S^*a),
\qquad
\Sigma(H,a)=H+\sum_m a_m.
\]

O theorem

```lean
tailSynthesis_cutoffTransport
```

prova exatamente:

\[
\boxed{\Sigma U_{\rm cut}=\Sigma.}
\]

O domínio é explicitamente o de tails `Summable`; a soma não foi tratada
indevidamente como funcional Hilbertiano em \(\ell^2\).

Para a tail literal de `centerBracketTerm`, os theorems

```lean
finiteCameraPhysicalRawHead_succ_eq_add_centerBracketTerm
finiteCameraPhysicalCutoffLedger_succ
finiteCameraPhysicalCutoffLedger_synthesis_eq_completed
finiteCameraPhysicalCutoffLedger_synthesis_succ
```

mostram que o ledger físico real

\[
L_N=\left(H_N,\,(a_{N+m})_{m\ge0}\right)
\]

evolui exatamente por esse `U_cut`, e sua síntese é a característica nativa
completada.  Em particular, a independência de cutoff não é um limite:

\[
\boxed{
H_{N+1}+T_{N+1}=H_N+T_N.
}
\]

### 35.3. Forma métrica

O mesmo módulo formaliza, para matrizes compatíveis,

\[
K-GS=d\beta,
\qquad Gc=d,
\qquad A=S+c\beta,
\]

e prova:

\[
\boxed{GA=K.}
\]

Se \(G\) e \(K\) são simétricas, também prova:

\[
\boxed{A^{\mathsf T}G=K=GA.}
\]

Os nomes são:

```lean
gram_mul_boundaryCompletedMetricTransport
boundaryCompletedMetricTransport_transpose_mul_gram
```

A instanciação Hankel tem o espaço de bordo `Fin 1`, a coluna
\(c=G^{-1}Ke_{\rm last}\) e o funcional de última coordenada.  O theorem

```lean
finiteHankel_boundaryCompletedMetricTransport_eq_galerkin
```

identifica a construção abstrata literalmente com o Galerkin já formalizado:

\[
\boxed{A_N=S_N+c_Ne_{\rm last}^{\!*}=G_N^{-1}K_N.}
\]

### 35.4. Instância TFVD/Green: reconstrução estática, não shift de cutoff

A costura com TFVD foi agora testada diretamente e compilada em
`CarrySelfAdjointOperator/TfvdBoundaryCompletedTransport.lean`.

Para (0<q<1), o carrier vertical existente já fornece os quatro mapas

\[
\begin{aligned}
\operatorname{Tr}_q &: H_{\rm vert}\to\mathbb C^2,\\
B_q &: H_{\rm vert}\to H_{\rm vert},\\
R_q &: \mathbb C^2\to H_{\rm vert},\\
G_q &: H_{\rm vert}\to H_{\rm vert},
\end{aligned}
\]

com a identidade literal

\[
\boxed{
R_q\operatorname{Tr}_q+G_qB_q=I.
}
\]

O bracket interno é a segunda diferença vestida, com a coordenada inicial
reservada ao bordo:

\[
(B_qx)_{n+1}=q^{-1}x_{n+2}-2x_{n+1}+q x_n,
\qquad
\operatorname{Tr}_q x=(x_0,q^{-1}x_1-x_0).
\]

O novo adapter usa precisamente a API abstrata introduzida no capstone:

```lean
carryWeightedVerticalTfvdBoundaryAnalysis q
carryWeightedVerticalTfvdBoundarySynthesis q hq0 hq1
carryWeightedVerticalTfvd_isBoundaryReconstruction
carryWeightedVerticalTfvdBoundarySynthesis_comp_analysis
carryWeightedVerticalTfvdBoundaryAnalysis_injective
```

Em notação:

\[
\mathcal A_q(x)=(\operatorname{Tr}_qx,B_qx),
\qquad
\mathcal S_q(\tau,b)=R_q\tau+G_qb,
\]

e o theorem novo prova

\[
\boxed{\mathcal S_q\mathcal A_q=I.}
\]

Assim, `trace ⊕ bracket` é lossless no sentido correto: a análise é
injetiva.  Não foi afirmado o inverso em pares arbitrários
((\tau,b)): pares incompatíveis não devem ser promovidos a estados sem uma
condição de compatibilidade adicional.

Isto confirma a família estrutural “interior + porto”, mas também fixa a
distinção necessária:

\[
\boxed{
\begin{array}{rcl}
\Sigma U_{\rm cut}&=&\Sigma
\quad\text{(tail: mudança de representação)},\\[1mm]
\mathcal S_q\mathcal A_q&=&I
\quad\text{(TFVD: reconstrução estática)},\\[1mm]
G_NA_N&=&K_N
\quad\text{(Hankel: correção métrica de borda)}.
\end{array}}
\]

Portanto a TFVD **não** fornece, por si só, o entrelaçamento falso

\[
\mathcal M S^*_{\rm tail}=A_{\rm mom}\mathcal M.
\]

Ela mostra onde entra o transporte de segunda ordem: dentro de (B_q), não
como o avanço de cutoff (U_{\rm cut}).  O próximo seam genuíno, se for
necessário, é um diagrama bidimensional entre mudança de cutoff da
representação e extração de response/jets depois da síntese completa.

No nível finito de coeficientes, o theorem já existente e agora exposto como
adapter

```lean
finiteSlopeCoefficient_tfvdBoundaryReconstruction
```

prova que Green response mais boundary return é exatamente o prefixo
sintetizado.  Isto conecta a mesma reconstrução à cadeia de jets sem usar
momentos, PosDef, HP ou Stieltjes.

### 35.5. Guardrail renovado

O capstone não revoga o diagnóstico da seção 34:

\[
\boxed{
U_{\rm cut}\not\mapsto S_{\rm mom}\text{ por um intertwiner linear natural.}
}
\]

O correto é

\[
\mathcal M U_{\rm cut}=\mathcal M,
\qquad
\mathcal M=
\text{jets}\circ\text{normalized response}\circ\Sigma,
\]

enquanto o shift de momentos só começa depois de `\Sigma` e da normalização
não linear por \(F\).  A divisão em `completedGreenNormalizedResponse`
continua sendo o primeiro ponto onde uma ponte tail \(\to\) momentos deixa de
ser linear.

### 35.6. Validação e axiomas

Foram acrescentados:

```text
CarrySelfAdjointOperator/BoundaryCompletedTransport.lean
CarrySelfAdjointOperator/BoundaryCompletedTransportAudit.lean
```

e foi executado localmente:

```bash
lake build \
  CarrySelfAdjointOperator.BoundaryCompletedTransport \
  CarrySelfAdjointOperator.BoundaryCompletedTransportAudit
```

O audit dos nove theorems novos/imediatos imprimiu somente:

```text
propext, Classical.choice, Quot.sound.
```

Nenhum push, PR ou GitHub Action foi acionado nesta rodada.

### 35.7. Validação da costura TFVD

Foram acrescentados:

```text
CarrySelfAdjointOperator/TfvdBoundaryCompletedTransport.lean
CarrySelfAdjointOperator/TfvdBoundaryCompletedTransportAudit.lean
```

e executado localmente:

```bash
lake build \
  CarrySelfAdjointOperator.BoundaryCompletedTransport \
  CarrySelfAdjointOperator.TfvdBoundaryCompletedTransport \
  CarrySelfAdjointOperator.BoundaryCompletedTransportAudit \
  CarrySelfAdjointOperator.TfvdBoundaryCompletedTransportAudit
```

Os quatro theorems TFVD do adapter imprimem somente:

```text
propext, Classical.choice, Quot.sound.
```

Nenhum push, PR ou GitHub Action foi acionado nesta rodada.

### 35.8. Auditoria: Gram causal TFVD \(\neq\) automaticamente Gram Hankel

Foi auditada a hipótese de transportar a positividade da família causal TFVD
para os Hankels canônicos apenas por “primeira coluna + shift”.  A conclusão
é mais nítida do que uma simples falta de prova.

O arquivo `CompletedNativeCausalCoefficientGram.lean` já constrói, para cada
ordem finita \(N\), a família separada

```lean
canonicalFiniteNativeCausalGreenBoundaryJet hbase N :
  Fin N → FiniteWeightedSlopeGreenBoundaryCarrier
```

e prova:

```lean
canonicalFiniteNativeCausalGreenBoundaryJet_linearIndependent
canonicalFiniteNativeCausalGreenBoundaryGram_posDef
```

Logo existe uma Gram causal estritamente positiva, construída de
`Green response ⊕ boundary return`, sem hipótese de momentos.  Mas seus
índices são um prefixo `Fin N`; a árvore de theorems atual não contém uma
compatibilidade projetiva de suas Grams quando \(N\) muda, nem o theorema

\[
\langle\Psi_p,\Psi_0\rangle
=
\operatorname{oddMomentResponseCoefficient}(p+1),
\]

nem a lei de dois índices

\[
\langle\Psi_p,\Psi_{q+1}\rangle
=
\langle\Psi_{p+1},\Psi_q\rangle.
\]

Essas duas identidades são exatamente o conteúdo de

```lean
HasPolarizedCoefficientVectorEquation moments rawJet
```

para uma família all-order em carrier fixo.  Assim, a positividade causal é
um recurso upstream real, mas ainda não é a Gram \(G_N=(h_{i+j})\).

Dois atalhos naturais foram excluídos formalmente:

1. A família all-order em carrier fixo
   `canonicalCompletedNativeTfvdEnrichedTaylorRawJet` é independente nas duas
   paridades, mas falha já no coeficiente \((0,0)\):

   ```lean
   not_hasPolarizedCoefficientVectorEquation_enrichedTfvdTaylor
   ```

   Sua energia refletida mais energia log-jet é estritamente maior que
   \(h_0\); portanto não pode ser renomeada como a Gram nativa dos momentos.

2. A resposta causal BR2 C3 literal também não serve, mesmo permitindo
   retorno de bordo arbitrário de duas sementes:

   ```lean
   not_canonicalBR2CausalGreenResponse_centerLegReadout
   not_nonempty_canonicalBR2C3BoundaryResponse_momentCertificate
   ```

   A obstrução já ocorre na massa central: toda solução da fonte BR2 C3 tem
   norma grande demais para realizar \(h_0\) na métrica causal literal.

Existe ainda o raw jet Naimark all-order por diferença finita,
`canonicalCompletedTfvdGreenNaimarkRawJet k`, mas ele conserva o parâmetro
de passo \(k\).  O repo só registra a forma de um eventual limite all-order
em `IsCanonicalCompletedTfvdGreenRawJetLimit`; não há hoje uma família limite
construída e calibrada que descarregue a equação de Gram.

Portanto o próximo seam construtivo não é aplicar a Gram causal bruta aos
momentos.  É construir ou identificar uma família vetorial **completada**,
all-order e em carrier fixo, que preserve os portos TFVD/six-source e prove
diretamente:

\[
\boxed{
\texttt{HasPolarizedCoefficientVectorEquation}
\;\texttt{canonicalCompletedNativeLogDerivativeMoment}\;\Psi.
}
\]

Depois disso, a independência e a construção HP/Jacobi já existentes voltam
a ser puramente downstream.

Foi acrescentado o audit:

```text
CarrySelfAdjointOperator/TfvdCausalGramCalibrationAudit.lean
```

Nenhuma nova positividade, medida Stieltjes, HP, Jacobi ou realização
espectral foi introduzida nesta auditoria.
