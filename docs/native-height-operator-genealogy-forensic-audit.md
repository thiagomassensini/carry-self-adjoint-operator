# Auditoria forense da genealogia do operador de alturas nativo

**Escopo.** Esta auditoria parte do commit
d1a3f8ca7a86f86bea2add879549f6c4fb9e6c3c, na branch
agent/native-height-operator-genealogy-forensic-audit. Ela é somente
documental: não muda definições de operadores, não tenta zerar
D_native, não constrói outro Green inverse e não adiciona teoremas de
positividade, Jacobi ou HP.

## Resultado

O resultado primário é **Outcome D — MULTIPLE GENEALOGIES**. Há mais de uma
construção chamada de autoadjunta, e as rotas foram ligadas por crosswalks
posteriores. Para a primeira construção de alturas que pode ser recuperada com
data, a classificação da completação é **Completion-C — NATIVE + CLASSICAL
DRESSING**:

\[
\text{câmera + cauda exata + quociente}
\;\longrightarrow\;
A_{\rm arch}N
\;\longrightarrow\;
\text{coeficientes pares}
\;\longrightarrow\;
h_n
\;\longrightarrow\;
(G_N,K_N)
\;\longrightarrow\;
J_N
\;\longrightarrow\;
T_N=J_N^{-1/2}.
\]

Isso não afirma que a completação clássica seja ilegítima. Afirma apenas que,
na evidência recuperável, ela entra como fator separado antes da extração dos
momentos. Não foi encontrado um commit Git dos scripts Python que permita
provar uma versão anterior sem esse fator.

## Limitação de proveniência dos scripts

Os arquivos em /home/thlinux/Downloads/Wayl são artefatos externos ao Git
deste repositório. A busca Git por completion_series, gamma_series e
hankel_pair não retorna commits, e git ls-files não lista esses scripts. O material anexado em
/home/thlinux/Downloads/geometria_do_carry_multibase.md também foi lido como
nota externa: suas seções sobre L, candidatos de energia, Green/Poisson e
limites confirmam a separação entre relógio, operadores auxiliares e a rota
de alturas, mas não constituem evidência Git nem prova Lean. O
arquivo jacobi.zip preserva timestamps internos e é a evidência mais antiga
recuperável, mas não fornece um hash Git. Portanto:

- “primeiro” abaixo significa **primeiro artefato recuperável**, não primeiro
  commit histórico absoluto;
- a data do arquivo é evidência de arquivo, não uma prova de autoria ou de
  ordem global;
- os commits Lean têm proveniência Git exata e são separados dos scripts.

## Primeiro artefato que constrói alturas

O arquivo mais antigo recuperável com a cadeia completa J_N,T_N é:

/home/thlinux/Downloads/Wayl/jacobi.zip, entrada
native_carry_height_moment_jacobi_operator_lab.py, timestamp interno
2026-08-17 13:02, SHA-256 da entrada
e82e9ff9efe98991f38f5dd50ace0a12a124253f8d6ec61355c1654541eaf929.

A entrada define:

1. completed_xi(s) por
   0.5*s*(s-1)*pi**(-s/2)*gamma(s/2)*zeta(s);
2. height_characteristic(z)=completed_xi(0.5+i z);
3. coeficientes por integrais discretas de Cauchy;
4. seleção dos coeficientes pares de uma característica even;
5. logarithmic_moments, divisão formal de -Phi'/Phi;
6. hankel_matrices, com (G_N)_{ij}=h_{i+j} e
   (K_N)_{ij}=h_{i+j+1};
7. jacobi_from_moments, Cholesky e
   J_N=L_N^{-1}K_NL_N^{-\mathsf T};
8. height_spectrum, com T_N=J_N^{-1/2}.

A função de referência mp.zetazero aparece somente depois de todos esses
objetos terem sido calculados. O JSON do laboratório marca
zero_heights_used_in_construction: false e root_finding_in_construction:
none. Isso é uma barreira de dependência, não uma prova de positividade
all-order.

As variantes native_autoadjunto.py e native_carry_r2_height_operator.py usam
a mesma ordem, mas com uma completion_series explícita antes dos momentos.
Nelas não há chamada a mp.zeta ou mp.zetazero; a série é montada com
polinômio, rotação de pi e série de Gamma.

## O que exatamente é completion_series

Na série em z, as linhas 263--286 de native_autoadjunto.py montam

\[
P(z)=-\frac14-z^2,
\qquad
A_{\rm arch}(z)=
\frac12 P(z)\,
\pi^{-1/4}e^{-\,i z\log(\pi)/2}
\Gamma\!\left(\frac14+\frac{i z}{2}\right).
\]

Os coeficientes -1/4 e -1 são os graus zero e dois de P; a
rotation_series implementa as potências de i, e gamma_series(1/4,1/2,...)
implementa a expansão de Gamma. A função closed_native_series faz, nessa
ordem:

\[
\texttt{finite}+\texttt{tail}
\;\longrightarrow\;
\frac{\texttt{finite}+\texttt{tail}}{\texttt{camera factor}}
\;\longrightarrow\;
A_{\rm arch}\,\texttt{common}.
\]

A forma Lean equivalente, introduzida no commit
7fe207aedddcca5bc51add04561a2880cd2fca3e, é:

\[
\texttt{nativeXiCompletionFactor}(z)
 =
 \frac12\,s(s-1)
 e^{-(s/2)\log\pi}\Gamma(s/2),
 \qquad s=\frac12+i z,
\]

e

\[
\texttt{completedNativeOperatorCharacteristic}(z)
 =
 \texttt{nativeXiCompletionFactor}(z)\,
 \texttt{nativeScalar}(s).
\]

O theorem Lean nativeXiCompletionFactor_mul_completedNativeCharacteristic é
uma ponte multiplicativa cruzada. Ele não deriva A_arch da energia
Green/TFVD.

Há uma separação anterior, sem esse fator, no commit
326f5f238b3a9fe31910f805f8a9f8fc901024ce:
completedNativeCharacteristic é literalmente

\[
\texttt{finiteBracketCharacteristic}
+
\sum_{\texttt{index}}\texttt{centerBracketTerm},
\]

e o theorem completedNativeCharacteristic_eq_factor_mul_nativeScalar
identifica essa soma com factor(camera,s)*nativeScalar(s). Essa é a completude
geométrica head--tail; ela é diferente do dressing arquimediano de
CompletedOperatorCharacteristic.lean.

A nota NATIVE_CARRY_CANONICAL_HEIGHT_WEYL_GATE_LOG.md chama a completação
xi de “canônica clássica, externa” e registra como tarefa aberta derivar o
termo arquimediano como retorno Green. Essa declaração é compatível com o
código: não há theorem anterior que produza o fator arquimediano a partir do
retorno TFVD.

## Linha do tempo Lean

| Data | Commit | Evidência | Papel causal |
|---|---|---|---|
| 2026-08-21 03:30 | a3d493f100421923e0db6adfa6b954ce01f0051e | NativeLogEvolution.lean, LogarithmicMomentHankel.lean | fixa L e_n=log(n+1)e_n e a infraestrutura de momentos; ainda não é T_N |
| 2026-08-21 04:10 | c73ea47cbf33693890533ecfe9ac0dbfb4b83fac | FiniteJacobiTransport.lean | J_N=B_N K_N B_N^T, congruência e positividade condicional |
| 2026-08-21 04:23 | de9ec64cf3af0b9420421b1509ae2015c8882fb3 | FiniteHeightOperator.lean | T_N=J_N^{-1/2} por cálculo funcional Hermitiano |
| 2026-08-21 04:50 | 326f5f238b3a9fe31910f805f8a9f8fc901024ce | CompletedNativeCharacteristic.lean | head + cauda exata e quociente pelo fator de câmera |
| 2026-08-21 05:42 | 779eb2d860c622aad2d229b3b267d8858a0991f4 | CanonicalFiniteHeight.lean | construtor canônico finito, ainda parametrizado por momentos/Gram |
| 2026-08-21 06:09 | 7fe207aedddcca5bc51add04561a2880cd2fca3e | CompletedOperatorCharacteristic.lean | introduz A_arch e F=A_arch N |
| 2026-08-21 06:18 | dba780a78f8b44d768f340583a98dcb726b115e4 | identificação do scalar | crosswalk posterior com zeta; não é entrada necessária ao script sem mp.zeta |
| 2026-08-21 23:12--2026-08-22 00:20 | 108a12b, e518550, 6f00328 | torres projetivas | compatibilidade principal/LDL, downstream de momentos |
| 2026-08-22 00:28 | a5ed3a346485cfd7017774c84809ad2f5360b7d3 | GreenJetSignedHeightIntertwiner.lean | intertwiner de Green-jets posterior |
| 2026-08-24 16:53 | 1d9c631d5915fdd4c26a4f3f7dedd63d75b2a3cd | traces de câmeras com TFVD | entrada tardia do crosswalk TFVD |
| 2026-08-24 22:55 | e80bb49e1670073490127527fc0ba982e41e5e8e | CompletedNativeWeylMoments.lean, CompletedNativeGreenWeylHeight.lean | momentos completed concretos e certificado Green condicional |
| 2026-08-25 15:57 | 9d96bafc663c43d1725b0d19d79acf0b9313ff79 | CompletedNativeJacobiCyclicReadout.lean | leitura cíclica da Jacobi no Green core |
| 2026-08-28 07:49 | 02fc6ab003486141719d552776c2a9bd1085bc16 | Stieltjes operator gate | operador positivo global condicional |
| 2026-09-01 15:26 | 17bfb5a5db5d71e32f258bb7452f33e9f32d35ee | signed-generator Gram | readout Herglotz posterior e condicional |
| 2026-09-12 | ec1bc2b, e21ad6a, d98567, d1a3f8c | branches de trace/dressing | crosswalks recentes; não são a origem do J_N/T_N |

A ordem Git mostra que o construtor genérico de T_N existia antes do
characteristic concrete Xi, mas recebe uma sequência de momentos arbitrária.
Isso não constitui uma versão histórica “pure native”; a primeira realização
concreta recuperável com J_N,T_N é a série do arquivo de 17 de agosto.

## Inventário dos objetos autoadjuntos

A tabela usa “mesmo objeto?” somente quando há uma declaração de igualdade ou
equivalência; sem isso, a relação é marcada como desconhecida.

| Família | Declaração/artefato | Espaço e entrada | Saída/status | Relação |
|---|---|---|---|---|
| relógio nativo | nativeLogGenerator | NativeLogHilbert=InfiniteRealSpectralHilbert=ell²(N,C); multiplicação por log(n+1) | maximal, self-adjoint | primitivo; não é T_N |
| relógio finito | finiteRealSpectralSelfAdjointGenerator (CPFormal) | EuclideanSpace C (Fin N); diagonal log(n+1) | finite self-adjoint | truncamento do relógio, não height |
| transporte de relógio | H_clock=VLV* | apenas nas notas; nenhum VLV* literal encontrado | conceitual/sem theorem atual | não identificável automaticamente com qualquer Jacobi |
| compressões de câmera | vários módulos C3/camera | espaços de porta/frames e mapas de câmera | operadores auxiliares | família; sem um objeto único |
| Jacobi de profundidade | scripts e bridge C2 | C2/Meixner; dados de profundidade | auxiliar | distinta da Jacobi de alturas |
| Jacobi mixed-mode | scripts de modos 3--4--6 | setor misto | auxiliar | nenhuma equivalência com J_height encontrada |
| Jacobi de alturas | finiteJacobiSection, canonicalFiniteJacobiSection | Matrix (Fin N) (Fin N) R; momentos e whitening | simétrica/PosDef sob hipóteses | downstream de h_n |
| operador de alturas finito | finiteHeightOperator, nativeFiniteHeightOperator, canonicalFiniteHeightOperator | mesma matriz; cálculo funcional y↦y^{-1/2} | simétrico/self-adjoint em dimensão finita | T_N=J_N^{-1/2} |
| operador assinado finito | canonicalSignedFiniteHeightOperator | doubling/paridade | simétrico; bloco T_N⊕(-T_N) | extensão assinada de T_N |
| torre Jacobi | canonicalJacobiTowerLimitMatrix e módulos de torre | matriz infinita/entradas finitas | exact principal compatibility sob dados de positividade | downstream de Hankel |
| Jacobi Green global | canonicalCompletedNativeStieltjesJacobiEnergyOperator, J=B*B | LinearPMap/fecho | self-adjoint condicional a Gram/independência | não provado igual ao relógio |
| signed height Green global | closedGreenJetReciprocalSignedHeightOperator e versão reduced | carrier de Green-jets | maximal real self-adjoint sob os gates | crosswalk posterior |
| complexificação | complexifiedClosedGreenJetReciprocalSignedHeightOperator | complexificação do carrier real | self-adjoint complexo | variante, não nova origem |
| pencil/factor limit | scripts native_carry_height_spectral_pencil_lab.py e ...factor_selfadjoint_limit_lab.py | artefatos de laboratório | rota paralela/condicional; nenhum único capstone atual identificado | não se presume equivalente |

Assim, há **13 entradas semânticas** na tabela (algumas são variantes da mesma
família); elas não formam 13 classes de equivalência. Em particular,
nativeLogGenerator, H_clock, J_height, T_height e o signed Green operator têm
tipos, espaços ou hipóteses diferentes.

## A cadeia causal sustentada pelo código

~~~text
CARRY
  |
  +-- native logarithmic generator L = diag(log(n+1))
  |       |
  |       +-- native orbit / camera primitives
  |               |
  |               +-- finite camera head + exact analytic tail
  |                       |
  |                       +-- camera quotient -> common scalar N
  |                               |
  |                               +-- (historical height route) A_arch * N
  |                               |       |
  |                               |       +-- F, even Phi, h_n
  |                               |               |
  |                               |               +-- G_N, K_N
  |                               |                       |
  |                               |                       +-- whitening -> J_N -> T_N
  |                               |
  |                               +-- (later/parallel geometric route)
  |                                       TFVD / Green / boundary crosswalk
  |                                       |
  |                                       +-- conditional Green moment certificate
  |
  +-- later comparisons:
          signed HP, Stieltjes, Gamma trace, D_native
~~~

A seta tracejada conceitual “TFVD/Green -> h_n” não é marcada como fechada:
o código atual exige exatamente esse crosswalk como hipótese.

## Mapa de setas histórico → Lean

| Seta histórica | Contraparte atual | Status |
|---|---|---|
| carry state -> log orbit | nativeRealSpectralState_eq_logOrbit_zero, nativeFiniteRealSpectralState_eq_logEvolution_zero | CLOSED EXISTING |
| log orbit -> L | nativeLogGenerator, nativeLogGenerator_basisVector_log, CPFormal generator | CLOSED EXISTING |
| finite camera -> head | finiteBracketCharacteristic, módulos Camera; correspondência exata com o script não tem theorem único | CONDITIONAL/CROSSWALK |
| head -> cauda | completedNativeCharacteristic, complete_head_add_complete_center_tail | CLOSED FORMAL |
| head + cauda -> common scalar | completedNativeCharacteristic_eq_factor_mul_nativeScalar | CLOSED FORMAL, divisão evitada |
| common scalar -> A_arch N | nativeXiCompletionFactor, completedNativeOperatorCharacteristic | CLASSICAL IDENTITY/DEFINITION |
| completion -> Phi even | completedNativeEvenCharacteristicCoefficient, CompletedNativeRealWeylMoments | FORMAL LEAN, depende do characteristic dressed |
| Phi -> h_n | canonicalCompletedNativeLogDerivativeMoment, canonicalCompletedNativeLogDerivativeMoment_eq | CLOSED FORMAL |
| h_n -> G_N,K_N | hankelGram, shiftedHankel | CLOSED FORMAL |
| G_N -> whitening | canonicalHankelWhitening, canonicalLDLInverseFactor_whitens | CLOSED FORMAL sob G_N>0 |
| whitening + K_N -> J_N | canonicalFiniteJacobiSection, finiteJacobiTransport | CLOSED FORMAL |
| J_N -> T_N | finiteHeightOperator, canonicalFiniteHeightOperator | CLOSED FORMAL sob PosDef |
| J_N -> torre | CanonicalProjectiveJacobiTower, ExactProjectiveMatrixTower | CLOSED/CONDITIONAL conforme positividade all-order |
| T_N -> signed | SignedFiniteHeightOperator | CLOSED FORMAL finite |
| Green/TFVD -> mesmo h_n | CompletedNativeGreenWeylHeightCertificate e HasCanonicalCompletedNativeGreenMomentJets | CONDITIONAL; seam ainda explícito |
| Green jets -> operador global | CurrentInfiniteHeightStatus, canonicalCompletedNativeHeightOperator_adjoint_eq_of_greenMomentJets | CONDITIONAL |
| operador global -> zeros | nenhum theorem incondicional; status registra gate separado | OPEN |

## Green, TFVD e a origem do primeiro J_N

O primeiro script datado com J_N,T_N não importa Green nem TFVD como
biblioteca: ele opera sobre a série xi/completion, Cauchy coefficients e
divisão formal. As notas de cronologia dizem que carry -> TFVD -> Green ->
Weyl foi a ordem conceitual da descoberta, mas também registram que os textos
fonte iniciais foram absorvidos em OLD/ e que os laboratórios atuais
preservam peças finitas. Portanto a afirmação historicamente segura é:

- Green/TFVD é uma **interpretação geométrica posterior ou paralela** da
  origem nativa, não uma entrada verificável do primeiro script J_N/T_N;
- a primeira entrada concreta de Green no Lean height package é o commit
  e80bb49e, que constrói um certificado **condicional**;
- o próprio CurrentInfiniteHeightStatus.lean diz que a identificação dos
  jets TFVD concretos com o kernel Green canônico ainda é necessária.

Não há base para usar Green para justificar retroativamente que a primeira
linha Python já tinha uma fatoração positiva nativa.

## Torre projetiva

Os scripts e os módulos Lean distinguem duas afirmações:

1. a identidade de matrizes principais J_N=P_NJ_{N+1}P_N*, que é algébrica
   depois que as seções e as whitenings canônicas existem;
2. a existência de uma torre positiva all-order, que exige
   positividade/independência não fornecida pelo cálculo de um único cutoff.

ExactProjectiveMatrixTower.lean e CanonicalProjectiveJacobiTower.lean
formalizam a primeira camada sob os dados apropriados. Nenhuma dessas provas
usa zeros, Green ou TFVD. A identidade cíclica
< x_0,J_N^k x_0 >= h_k aparece no Lean no Green-core
(greenJetJacobiCoreCyclicMoment_eq) e é condicionada à representação de
momentos Green; ela não é prova de que o primeiro script tenha obtido J_N de
um x_0 geométrico independente de h.

## Origem computacional versus fundação matemática

**Origem computacional:** os scripts recebem amostras da característica,
calculam séries/Cauchy, dividem formalmente séries e usam Cholesky/eigsy.
mp.zetazero é uma comparação posterior no laboratório principal; não é input
da construção.

**Fundação matemática alegada:** para chamar esses objetos de operador nativo
de alturas, ainda são necessárias as identidades de camera/head/tail,
a identificação do scalar comum, a legitimidade do dressing escolhido, a
positividade all-order de G_N,K_N, e a realização Green/TFVD positiva.
O Lean tem as primeiras pontes algébricas e as construções condicionais, mas
não transforma automaticamente a origem computacional em uma prova de todos
esses gates.

## Inversões de dependência detectadas

1. **Não é inversão:** canonicalFiniteHeightOperator declara explicitamente
   que recebe momentos, Gram e independência. Ele é um construtor downstream,
   não uma prova de que os momentos vêm do carry.
2. **Crosswalk posterior:** CompletedNativeGreenWeylHeight constrói um
   certificado a partir de HasCanonicalCompletedNativeGreenMomentJets; o
   certificado não prova essa hipótese.
3. **Crosswalk posterior:** CompletedNativeSignedGeneratorHerglotzGram usa o
   certificado para o readout Herglotz; não funda a sequência.
4. **Risco de inversão narrativa:** o comentário de NativeLogEvolution chama
   L de origem operatorial da construção, mas L é o relógio log(n+1), não T_N.
5. **Risco de inversão:** nativeXiCompletionFactor é usado para definir o
   characteristic que alimenta os momentos; o theorem disponível é
   multiplicativo e não deriva o fator da energia Green.
6. **Risco de equivalência excessiva:** os módulos
   CompletedNativeJacobiCyclicReadout, Stieltjes e Green signed-height
   fornecem leituras ou operadores posteriores; nenhum theorem os identifica
   literalmente com nativeLogGenerator.
7. **Sem circularidade lógica local:** as branches recentes mantêm os
   mismatch/realization como estruturas condicionais; o problema seria
   apresentar essas condições como teoremas incondicionais.

## Branches recentes

As branches recentes são crosswalks posteriores e não necessárias para
construir o primeiro J_N/T_N:

- ec1bc2b4..., NativeBoundaryArchimedeanDressingSeparation.lean: separa
  F=A N e a correção de Green.
- e21ad6a1..., PureNativeBoundaryGreenSewing.lean: define o mismatch nativo
  puro.
- d98567fd..., NativeSourceLocusGreenCompatibility.lean: restringe o mismatch
  à source locus.
- d1a3f8ca..., NativeGreenInverseTraceSewing.lean: cria uma realization de
  trace nativa **condicional**; a própria documentação diz que a identificação
  vertical -> scalar continua sendo gate.

Elas devem permanecer como crosswalks/experimentos. Não apagar, mover ou
reclassificar esses arquivos nesta branch.

## Positividade finita versus global

Os scripts registram G_N>0 e K_N>0 em ordens testadas por aritmética de alta
precisão. Isso é evidência numérica. No Lean:

- finiteJacobiSection_posSemidef_of_shiftedGram e
  canonicalGreenJetHankelGramPosDef são teoremas condicionais;
- PosDef exige representação de Gram e independência;
- CurrentInfiniteHeightStatus deixa explícito que a identificação TFVD
  concreta e a positividade/globalização continuam gates separados.

Logo nenhuma positividade global ou HP/RH deve ser atribuída à primeira
execução Python.

## Árvore causal auditada

~~~text
CARRY
  |
  +-- native logarithmic generator L = diag(log(n+1))
  |       |
  |       +-- native orbit / camera primitives
  |               |
  |               +-- finite camera head + exact analytic tail
  |                       |
  |                       +-- camera quotient -> common scalar N
  |                               |
  |                               +-- (historical height route) A_arch * N
  |                               |       |
  |                               |       +-- F, even Phi, h_n
  |                               |               |
  |                               |               +-- G_N, K_N
  |                               |                       |
  |                               |                       +-- whitening -> J_N -> T_N
  |                               |
  |                               +-- (later/parallel geometric route)
  |                                       TFVD / Green / boundary crosswalk
  |                                       |
  |                                       +-- conditional Green moment certificate
  |
  +-- later comparisons:
          signed HP, Stieltjes, Gamma trace, D_native
~~~

A seta tracejada conceitual “TFVD/Green -> h_n” não é marcada como fechada:
o código atual exige exatamente esse crosswalk como hipótese.

## Respostas obrigatórias

1. **Primeiro arquivo recuperável que constrói J_height:**
   native_carry_height_moment_jacobi_operator_lab.py na entrada do
   jacobi.zip, timestamp interno 2026-08-17 13:02. No Git Lean, o primeiro
   construtor genérico é FiniteJacobiTransport.lean, commit c73ea47...
2. **Primeiro arquivo que constrói T_height=J^{-1/2}:**
   o mesmo laboratório Python para o artefato computacional; no Lean,
   FiniteHeightOperator.lean, commit de9ec64...
3. **Commit dessa construção:** os scripts não têm commit Git recuperável.
   Para os construtores Lean: c73ea47... para J, de9ec64... para T; o
   construtor canônico é 779eb2d...
4. **Recebe zeros como input?** Não. O laboratório principal consulta
   mp.zetazero apenas depois; o JSON marca
   zero_heights_used_in_construction: false.
5. **Usa root finding?** Não; o próprio laboratório marca
   root_finding_in_construction: none.
6. **mp.zeta participa da construção original?** No laboratório completed_xi,
   sim, como avaliação da característica. Nas variantes native_autoadjunto.py
   e native_carry_r2_height_operator.py, não há chamada a mp.zeta; há a
   série explícita de completion.
7. **mp.zetazero antes ou depois?** Depois de momentos, Hankels, Jacobi e
   alturas terem sido construídos.
8. **completion_series já existia na primeira construção?** A cópia mais
   antiga recuperável usa completed_xi diretamente; as variantes com
   completion_series são arquivos posteriores sem histórico Git. Não é
   possível provar a presença no primeiro commit absoluto.
9. **Fórmula exata:** A_arch(z)=1/2(-1/4-z²)
   pi^{-1/4} exp(-i z log(pi)/2) Gamma(1/4+i z/2), equivalente ao
   nativeXiCompletionFactor Lean.
10. **Commit que introduziu completion_series:** nenhum commit Git
    recuperável; os scripts estão fora do índice. O primeiro commit Lean do
    fator nomeado é 7fe207...
11. **Versão anterior sem completion?** Há completedNativeCharacteristic
    head+tail sem o fator arquimediano (commit 326f5f...), mas não foi
    encontrada uma versão concreta J/T que use somente esse scalar.
12. **Theorem que deriva a completion da geometria?** Nenhum theorem anterior
    foi encontrado. O cross-multiplied bridge de 7fe207... apenas relaciona
    os fatores.
13. **Primeira interpretação xi:** no laboratório
    native_carry_height_moment_jacobi_operator_lab.py (timestamp 2026-08-17)
    e, no Lean, em CompletedOperatorCharacteristic.lean, commit 7fe207...
14. **Primeiro nativeXiCompletionFactor:** 7fe207..., 2026-08-21 06:09:59.
15. **Diferença entre H_clock=VLV* e T_height:** H_clock é um
    transporte/compressão do gerador diagonal log(n+1), com espectro de
    logaritmos; T_height é a função J_N^{-1/2} da Jacobi obtida de h_n, com
    espectro de alturas recíprocas. Não há igualdade ou equivalência unitária
    provada.
16. **Quantos autoadjuntos distintos?** A auditoria encontrou 13 entradas
    semânticas na tabela, agrupadas em relógio nativo, relógio finito,
    compressões de câmera, Jacobis auxiliares, Jacobi/height finitos, signed
    finite, torre, Stieltjes/Green global, recíprocos signed, complexificação
    e pencils/factors arquivados. Não são 13 objetos todos equivalentes.
17. **Jacobis distintas:** pelo menos Jacobi de profundidade C2/Meixner,
    Jacobis de câmera, mixed-mode 3--4--6, Jacobi de alturas J_N, torre
    projetiva J_N, Jacobi Green global e matrizes de pencil/factor de
    laboratório.
18. **Qual é a Jacobi de alturas?** canonicalFiniteJacobiSection /
    finiteJacobiSection alimentada por (G_N,K_N), no script pela Cholesky e
    no Lean pela whitening LDL canônica.
19. **Quando Green entrou?** Na narrativa das notas, antes de Weyl; na
    evidência de código do height package, o módulo Green/Weyl concreto
    aparece em e80bb49... (2026-08-24 22:55), depois dos construtores
    finitos.
20. **Quando TFVD entrou?** A ponte de traces TFVD aparece em 1d9c631...
    (2026-08-24 16:53) e é consumida pelo pacote Green/Weyl posterior.
21. **A primeira construção de heights dependia de Green?** Não há essa
    dependência no script de 17 de agosto; ele usa série/completion, Cauchy e
    momentos. A dependência Green é uma interpretação/crosswalk posterior.
22. **Dependia de TFVD?** Não no script recuperável; a justificativa
    geométrica TFVD permanece posterior/condicional no Lean.
23. **Status de J_N=P_NJ_{N+1}P_N*:** identidade algébrica exata nos
    módulos de torre quando as seções/whitening existem; a torre positiva
    all-order continua condicional. Não depende de zeros, Green ou TFVD.
24. **Cadeia causal histórica real:** para a implementação recuperável:
    câmera/head + cauda exata -> quociente -> completion clássica -> Phi
    even -> h -> G/K -> whitening -> J -> T. A cronologia conceitual das
    notas também contém carry -> TFVD -> Green, mas ela não é a cadeia de
    imports do primeiro script.
25. **Parte puramente nativa:** L, órbita logarítmica, head/cauda
    geométricos, quociente pelo fator de câmera e a infraestrutura formal de
    momentos; o scalar N é o ponto comum antes do dressing.
26. **Parte classical dressing:** multiplicação por A_arch, ou a função
    nativeXiCompletionFactor, antes dos coeficientes/momentos da rota
    histórica concreta.
27. **Branches recentes:** as quatro branches de dressing/trace listadas
    acima são crosswalks posteriores; devem ficar fora da genealogia causal
    original do J/T.
28. **Dependências invertidas:** tratar nativeLogGenerator como T_height;
    tratar o certificado Green como prova de seus próprios
    HasCanonical...; tratar a definição Xi como consequência já provada da
    energia Green; identificar signed/Stieltjes/HP globais com o relógio
    log(n+1). O código não sustenta essas leituras.
29. **Ordem para futura refatoração Lean:** (i) manter o módulo do relógio
    nativo; (ii) separar geometricamente completedNativeCharacteristic de
    CompletedOperatorCharacteristic; (iii) nomear explicitamente o dressing
    clássico; (iv) manter h,G,K,J,T como camada downstream; (v) adicionar
    somente depois o crosswalk Green/TFVD HasCanonicalCompletedNativeGreenMomentJets;
    (vi) aplicar Stieltjes, signed HP e resultados globais sob suas hipóteses
    nomeadas.
30. **D_native é fundacional?** Não. É um crosswalk posterior entre duas
    projeções de trace; não participa da construção histórica de J/T.
31. **Outcome:** **D — MULTIPLE GENEALOGIES**, com subresultado Completion-C
    para a rota concreta de alturas.
32. **Branch:** agent/native-height-operator-genealogy-forensic-audit.
33. **Commit:** c660840f3957c3a55a44d759ecc0d5db6415c093.
34. **Push:** concluído em origin/agent/native-height-operator-genealogy-forensic-audit.
35. **Build/audits:** foram executados após adicionar os artefatos; nenhum
    arquivo Lean foi alterado e os resultados estão no JSON.
36. **Axiomas:** não foram adicionadas declarações Lean, portanto não há novos
    capstones/axiomas. Os theorems existentes são os auditados pelo
    CarrySelfAdjointOperator.Audit; esta branch não adiciona sorry, admit ou
    axioma.
37. **Próximo passo recomendado:** antes de qualquer refatoração matemática,
    escolher explicitamente se o projeto quer (a) documentar J/T como operador
    de momentos com dressing clássico, ou (b) provar o crosswalk independente
    Green/TFVD. O próximo theorem mínimo para (b) continua sendo
    HasCanonicalCompletedNativeGreenMomentJets para os jets concretos; não
    implementar esse theorem nesta branch.

## Arquivos e commits consultados

### Artefatos externos

- /home/thlinux/Downloads/Wayl/jacobi.zip (SHA-256
  29111e72a3cb6faddb05d38ac2d222210ff5323eb1ea7978ad5c65ebe39c2b25);
- native_carry_height_moment_jacobi_operator_lab.py,
  native_autoadjunto.py, native_carry_r2_height_operator.py;
- NATIVE_CARRY_HEIGHT_MOMENT_JACOBI_OPERATOR_LOG.md;
- MEMORIA_DERIVACAO_OPERADOR_AUTOADJUNTO_GENUINE.md;
- NATIVE_CARRY_CANONICAL_HEIGHT_WEYL_GATE_LOG.md;
- TFVD_DEFECT_JETS_GREEN_POSITIVE_CARRY_OPERATOR_AUDIT.md;
- CARRY_GEOMETRY_TFVD_GREEN_WEYL_CAUSAL_CHRONOLOGY.md;
- IDENTIDADE_PROJETIVA_EXATA_LIMITE_OPERADOR_ALTURAS.md.
- /home/thlinux/Downloads/geometria_do_carry_multibase.md (anexo externo,
  SHA-256 19f72b50363ac2a25ebe5d4d24f0e53ca67b8cfc84af102300906e1c66347845).

### Fontes Git/Lean

- a3d493f100421923e0db6adfa6b954ce01f0051e,
  c73ea47cbf33693890533ecfe9ac0dbfb4b83fac,
  de9ec64cf3af0b9420421b1509ae2015c8882fb3,
  326f5f238b3a9fe31910f805f8a9f8fc901024ce,
  779eb2d860c622aad2d229b3b267d8858a0991f4,
  7fe207aedddcca5bc51add04561a2880cd2fca3e,
  dba780a78f8b44d768f340583a98dcb726b115e4,
  108a12b114baae7874bfbac74b9fe23b645c5223,
  e518550c3d58b655823e012f44e59699ed7cd8d2,
  6f00328a71c23da4b9ffe1b901e3cc5dc79d7142,
  a5ed3a346485cfd7017774c84809ad2f5360b7d3,
  e80bb49e1670073490127527fc0ba982e41e5e8e,
  9d96bafc663c43d1725b0d19d79acf0b9313ff79,
  02fc6ab003486141719d552776c2a9bd1085bc16,
  17bfb5a5db5d71e32f258bb7452f33e9f32d35ee,
  ec1bc2b4ce9ccac3bf8be7d82909470d6b4ec162,
  e21ad6a176507369fee67127c6c5801fbd77bf6e,
  d98567fd5768866ba0455473f026eb1f9866bbeb,
  d1a3f8ca7a86f86bea2add879549f6c4fb9e6c3c.

## Validação

Esta documentação não contém código executável. Os comandos de validação
foram executados antes do commit: lake build, os dois audits Lean,
bash scripts/audit.sh, git diff --check e
python3 -m json.tool audit/native-height-operator-genealogy.json. O resultado
está registrado no objeto validation do JSON.
