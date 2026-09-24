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
