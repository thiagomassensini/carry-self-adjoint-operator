# CHECKPOINT AUTO-ADJUNTO

# CURRENT STATE

Atualizado em: 2026-09-14 (auditoria ReturnMetric antes de novo carrier)

Branch: `agent/next-natural-native-gate`

HEAD REAL CONFIRMADO: `3681881a542e976a968fbdc7a50b0d0d0b0facce`
Comando de confirmação: `git rev-parse HEAD` no checkout remoto.

Status remoto: somente `.lake` não rastreado; preservado intencionalmente.

## Prioridade atual — auditar ReturnMetric antes de criar carrier

A nova rota deve testar primeiro a hipótese histórica de que o node trace e o
Green trace só coincidem depois do whitening pela métrica de retorno nativa.
A comparação deve ser feita após a colagem global das incidências pelo mesmo
rótulo n, não câmera a câmera.

Tabela obrigatória a preencher após a auditoria:
objeto antigo | objeto Lean atual | theorem de transporte | métrica usada

Alvos: return metric/endpoint metric, whitening G^(-1/2), node trace ↔ Green
trace, Parseval isometry, Naimark dilation e global incidence/fibre gluing.
Não criar novo carrier nem promover FourTraceSymplecticBridge a isometria
euclidiana antes de localizar essa cadeia. A classificação Gamma–TFVD continua
D para o balance e D2 para o Gamma literal até que ReturnMetric prove uma
ponte bilinear diferente.

## Expansão literal do sewing

Lado A já expandido até a mesma fonte Naimark:

```text
canonicalNativeBoundaryReadout
→ canonicalNativeBoundarySourceState
→ canonicalNativeBoundarySourceState_eq_gamma
→ canonicalNativeBoundaryReadout_eq_gammaBoundaryReadout
→ canonicalNativeBoundaryReadout_eq_separation_mul_gammaKernel
```

Teoremas: `NativeBoundaryReadoutHPIntertwining.lean`; todas essas setas são
igualdades exatas, sob as hipóteses de domínio e `im ≠ 0`. A última forma é a
Gram Gamma/Cauchy; ela ainda não é o Wronskiano escalar.

Lado B já expandido até o readout escalar completado:

```text
completedGreenWronskian
→ completedNativeOperatorCharacteristic
  + completedNativeOperatorBoundaryCompanion
→ boundary companion = -deriv characteristic
→ canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime
→ Green/TFVD structural channels
```

Teoremas: `CompletedC3CoisometricWronskianEnergyGate.lean`,
`CompletedC3FNegFPrimeMixedKernel.lean` e
`CompletedNativeCausalGreenProvenance.lean`. A decomposição escalar mantém
`greenProvenance`, `offDiagonal`, `readoutResidual`, `tailCompletion` e
`archimedeanChart`; o tail isolado já é exato.

Primeira divergência confirmada: os dois lados usam a mesma fonte/estado
estruturado, mas aplicam readouts de bordo diferentes. O residual canônico é
`canonicalCompletedC3RawGammaWronskianDefect`, já decomposto como
`sameStructuredGreenForm - scalar/native Green form` e como
`gammaNativeMismatch - archimedeanTransportCorrection`.

Theorem mínimo ainda faltante: uma identidade bilinear upstream para o
readout corrigido que elimine esse residual, ou uma única identidade concreta
de fonte/companion que o decomponha até um termo geométrico único. Não usar
balance, sewing, Gram, zeros ou Jacobi como hipótese.

## Classificação Gamma–TFVD

D para o balance Gamma–TFVD: a fatoração energética é uma identidade
geométrica global no domínio (`Balance = Im z * (E_TFVD - E_Gamma)`), mas o
zero do balance não é uma identidade global nem foi obtido no zero-locus.
Para o carrier Gamma literal há ainda D2: o sewing bilinear é formalmente
falso perto do centro. Para o carrier corrigido/enriquecido, a costura exige
também o defeito Gamma–Wronskian; portanto o theorem mínimo de fonte/readout
continua aberto.

Não é Caso B: no zero característico, a energia coisométrica/Wronskiana é
estritamente positiva fora do eixo real. Há uma equivalência de isotropia com
`Im z = 0` quando a condição de fechamento nativo já fornece o zero, mas usá-la
para provar o fechamento seria circular (alerta de Caso C, não um certificado).

## Theorem decisivo encontrado

Nome: `canonicalCompletedC3GammaCorrectionBalance_eq_energyDifference`;
arquivo: `CompletedC3CompressedGammaGramCorrection.lean`;
statement:

```lean
canonicalCompletedC3GammaCorrectionBalance z hz hzHalf =
  z.im * (‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 -
    ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2)
```

Complementos decisivos: `...Balance_eq_zero_iff_energy`,
`canonicalCompletedC3BoundaryGreenSewing_iff_rawDefect_zero` e
`canonicalCompletedC3NormalizedPolarizedGammaKernel_eq_dslope_iff_rawWronskian`.
Nenhum deles prova o zero do balance ou do defeito.

Theorem decisivo de projeção/sewing: `canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_gammaCorrectionBalance` em `CompletedC3CoisometricWronskianProjectionGate.lean`:

```lean
boundaryReadout = completedGreenWronskian ↔
  rawGammaWronskianDefect z z hz hz +
    Complex.I * (((2 * Balance z hz hzHalf : ℝ) : ℂ)) = 0
```

Assim, `Balance = 0` reduz a costura a `rawGammaWronskianDefect = 0`; ele não
substitui a ponte bilinear.

No-go decisivo para a versão Gamma literal:

Nome: `canonicalC3RawDefect_counterexamples_arbitrarily_close`;
arquivo: `C3GammaCameraTraceObstruction.lean`;
statement resumido:

```lean
∀ ε > 0, ∃ t, 0 < t ∧ t < ε ∧ t < 1/2 ∧
  operatorHeightParameter (I * t) ∈ genuineCriticalStrip ∧
  completedNativeOperatorCharacteristic (I * t) ≠ 0 ∧
  ∀ hz, (I * t).im ≠ 0 →
    canonicalCompletedC3RawGammaWronskianDefect
      (I * t) (I * t) hz hz ≠ 0
```

Com os teoremas exatos
`canonicalNativeBoundaryReadoutDefect_eq_rawGammaWronskianDefect` e
`canonicalNativeBoundaryCompletedReadoutSewing_iff_defect_zero`, isso refuta
o sewing global do `canonicalNativeBoundaryReadout` com o Wronskiano
completado. A refutação é pré-Hankel e não usa zeros, RH ou `characteristic = 0`.

## Gargalo atual exato

Provar, usando a realização corrigida fonte → retorno → Naimark já existente,
a igualdade bilinear do readout Gamma/TFVD corrigido com o Green escalar
`(F,-F')`, mantendo os dois cross terms e o termo de correção. A identidade
diagonal de energia sozinha não é suficiente para o kernel de duas variáveis.

Auditoria literal do seam: a fonte, o resolvente e o estado Naimark são os
mesmos nos dois lados. A primeira divergência ocorre apenas no readout de
bordo do mesmo `canonicalCompletedC3StructuredOnePointState`: o lado Gamma
projeta `greenPort` pela fonte de seis câmeras/Cauchy, enquanto o lado escalar
projeta `completedTraceAt` no par orientado `(Psi,F)=(-F',F)`. Portanto ainda
não há igualdade de costura; há um residual de projeção estruturado.

Resíduos exatos já localizados:

```text
canonicalCompletedC3RawGammaWronskianDefect
  = sameStructuredGreenForm - scalar/native Green form
  = gammaNativeMismatch - archimedeanTransportCorrection
```

Os nomes são `canonicalCompletedC3RawGammaWronskianDefect_eq_sameStructuredGreenForm_sub`,
`canonicalCompletedC3RawGammaWronskianDefect_eq_gammaNativeMismatch_sub_archimedeanTransportCorrection`
e `canonicalCompletedC3NativeSourceLocusProjectionMismatch_eq_pureNative`.
Na rota de fatorização TFVD, o mesmo seam aparece como os canais explícitos
`greenProvenance`, `offDiagonal`, `readoutResidual`, `tailCompletion` e
`archimedeanChart`, sem theorem de anulação. O tail escalar já é exato; não é
o gargalo.

## Expansão estrutural — carrier completo e primeira igualdade genuinamente nova

`CompletedC3FullWronskianOperatorCarrier.lean` não é uma prova do sewing
Gamma: ele constrói um carrier de traço completo com operador limitado
skew (`canonicalCompletedC3FullWronskianOperator`), e prova que o readout
escalar `(F,-F')` é exatamente sua forma simplética. Em particular,
`completedGreenWronskian_eq_normalizedFullOperatorInner` e
`canonicalCompletedC3NormalizedFullWronskianOperatorKernel_eq_completed`
expõem o Lado B como produto interno com o operador Wronskiano completo.

`CompletedC3GammaFullWronskianOperatorBridge.lean` apenas reescreve o mesmo
fato no domínio TFVD e dá:

```text
raw Gamma defect
= Gamma boundary readout
  - full-Wronskian-operator inner product.
```

Os teoremas `..._eq_fullOperatorInner_iff` e
`..._eq_sub_fullOperatorInner` são reduções exatas do seam; não são uma
identificação, e o no-go `...GammaBoundary_ne_fullOperatorInner_of_characteristicZero`
confirma que o Gamma literal não pode ser promovido a esse carrier.

`CompletedC3FourTraceSymplecticBridge.lean` fornece a ponte vetorial concreta:
o mesmo `CanonicalC3FourTraceSixCameraSource` tem `greenPort`,
`symplecticCarrier` e os traços `(F,-F')` coordenalmente compatíveis. O
teorema `canonicalC3FourTraceSixCameraSource_greenReadout_eq_greenForm`
identifica o readout de seis câmeras com uma forma de Green finita, mas não
prova que a projeção Gamma preserve a forma simplética do carrier completo.

Assim, a primeira divergência fica mais precisa:

```text
mesmo source/state estruturado
→ Gamma: greenPort / seis câmeras / Cauchy readout
→ escalar: completedTraceAt / (F,-F') / full symplectic readout
```

O theorem mínimo não é mais uma comparação vaga de Gram. É uma destas duas
setas equivalentes:

```lean
-- forma bilinear corrigida
gammaCorrectedGreenForm z w = fullWronskianOperatorInner z w

-- ou transporte vetorial que a implica
∃ U : ... →ₗᵢ[ℂ] ..., ∀ z, U (correctedGammaState z) = fullWronskianState z
```

Para o Gamma literal, a segunda seta é falsa pelo no-go acima. A busca deve
continuar por um estado/readout corrigido que preserve os canais estruturais;
não se deve zerar `structural defect`, descartar cross terms, nem usar a
estrutura `CanonicalCompletedC3WronskianResolventRealization` como prova,
pois ela recebe justamente a igualdade de readout como campo.

## Carrier corrigido encontrado — sewing escalar sem apagar o ledger

A rota corrigida já tem uma realização geométrica concreta, mas ela não é o
Gamma positivo isolado:

- CanonicalC3SymplecticNaimarkBridge.lean prova que o packing de seis
  câmeras e sua promoção Naimark preservam exatamente a forma Green real
  (a parte real de greenForm) e são injetivos. Isso é uma identidade
  vetorial/geométrica global da porta; não é ainda a igualdade com o
  Wronskiano escalar.
- CompletedC3BracketTfvdGreenFactorization.lean prova
  canonicalC3BracketTfvdMixedCorrectedBoundary_eq_greenReadout e a
  fatorização do Wronskiano em greenProvenance, offDiagonal,
  readoutResidual, tailCompletion e archimedeanChart. A passagem
  GlobalGreenReadout_tendsto_wronskian_iff reduz a costura a
  Tendsto (canonicalC3FiniteMixedHeightStructuralDefect ...) (nhds 0);
  não zera esse canal genericamente.
- CompletedC3RecoveredEnrichedWronskianCarrier.lean constrói o carrier
  enriquecido que retém radial, canal estrutural, tail, peso xi e chart.
  canonicalCompletedC3RecoveredAllCutoffLedgerState_readout_tendsto_wronskian
  e ..._readout_tendsto_fullOperatorInner dão a realização escalar
  concreta do Wronskiano/operador completo; a energia do estado permanece
  positiva mesmo quando o readout escalar tende a zero num zero.
- CompletedC3EnrichedChiralReadoutTransformation.lean e
  CompletedC3CoisometricCameraChiralTransformation.lean têm no-go para
  uma fatoração linear global do bloco coisométrico Gamma através da
  polarização positiva do Wronskiano. A obstrução é um modo Naimark direto
  invisível ao trace, portanto o transporte só pode ser procurado no
  subespaço causal dos estados canônicos, não no carrier ambiente irrestrito.

Logo, a seta verdadeira já fechada é:

text:
fonte/TFVD
→ porta Naimark symplectic corrigida
→ carrier enriquecido (radial + structural + tail + xi + chart)
→ readout Green completo
→ Wronskiano do operador completo.

A seta que permanece é precisamente a identificação desse readout corrigido
com o readout Gamma positivo no subespaço causal. Para o Gamma literal ela é
falsa (D2). O menor statement não circular a procurar é, portanto, uma
preservação bilinear restrita aos estados canônicos, com a forma existente:

lean:
theorem canonicalCompletedC3CausalCorrectedReadout_eq_fullOperatorInner
    {z w : Complex}
    (hz : z.im != 0) (hw : w.im != 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    correctedCausalReadout z w hzStrip hwStrip =
      inner Complex
        (canonicalCompletedC3NormalizedFullWronskianOperatorState 0 z)
        (canonicalCompletedC3FullWronskianOperator
          (canonicalCompletedC3NormalizedFullWronskianOperatorState 0 w))

A declaração acima é o único gate ainda não realizado: correctedCausalReadout
deve ser a leitura bilinear do carrier enriquecido já existente, não uma nova
métrica positiva nem um campo de uma estrutura de realização. O teorema
canonicalCompletedC3RecoveredAllCutoffLedgerState_readout_tendsto_fullOperatorInner
já prova o lado direito para o readout de limite; falta apenas uma definição/
identificação de correctedCausalReadout com o estado Gamma corrigido no
subespaço causal.

## Próxima ação mínima

Auditar os módulos atuais de ReturnMetric, frame/Gram/Parseval, Naimark e
incidence gluing, sempre na família global indexada pelo mesmo n. Expandir a
cadeia node trace → Green trace → return-metric whitening → Parseval/Naimark
e preencher a tabela acima com declarações reais. Só depois decidir se ela
fecha o residual Gamma–Wronskian ou se deixa um gate bilinear explícito.

## Retomada

"O HEAD atual confirmado é `90971844358a2aa23ae98889a9deed841043aa57`.
A classificação é D para o balance: sua fatoração energética é global, mas
seu zero/sewing ainda exige o defeito Gamma–Wronskian. O carrier Gamma literal
é D2 por contraexemplos formais arbitrariamente próximos do centro. No zero
característico, a energia coisométrica é positiva fora do eixo real; portanto
não há rota B pelo zero do balance. Continue pelo response/readout corrigido,
sem promover balance zero a identidade nem deduzi-lo de characteristic = 0."

## Descoberta registrada nesta retomada — seam causal center-leg

A cadeia causal já existente prova a proveniência escalar: fonte nativa →
resposta Green causal → retorno de bordo → traço Hilbert, além do transporte
injetivo de incidência. Em particular,
`canonicalCompletedNativeCarryGreenChiralResponse_succCoefficient_eq_polarizedMoment`
identifica os coeficientes escalares com
`polarizedGreenMomentCoefficient` antes de Hankel/Jacobi.

Isso ainda não é a identidade de produto interno exigida por
`HasCanonicalCompletedNativeTfvdGreenCenterLegReadout`. O carrier causal
zero-seed bruto é unilateralmente traduzido e satisfaz o no-go formal
`not_br2C3CausalResponse_coefficientEquation`; seu primeiro defeito de métrica
é explicitamente `-6`. Logo o próximo objeto não pode ser essa família bruta:
deve ser o response/readout corrigido, com a correção de bordo/center-leg e os
canais de defeito preservados. O seam restante é, portanto, uma igualdade
bilinear de center-leg para o carrier corrigido, não uma nova comparação de
Gram nem uma prova do zero do balance.

## Descoberta formal — center-leg do jet causal bruto é impossível

Foi compilado o theorem
`not_canonicalBR2CausalGreenResponse_centerLegReadout` em
`NativeCausalCenterLegNoGoAudit.lean`:

```lean
theorem not_canonicalBR2CausalGreenResponse_centerLegReadout
    (incidence : BR2CameraIncidence) :
    ¬ HasCanonicalCompletedNativeTfvdGreenCenterLegReadout incidence
      (canonicalBR2CameraBracketCausalGreenResponseParityJet 3 1)
```

A prova usa `Nat.even_or_odd'` para mostrar que o jet intercalado cobre toda a
família causal, transforma o readout center-leg em
`IsPolarizedGreenCoefficientEquation` e aplica
`not_br2C3CausalResponse_coefficientEquation`. O fato de o center-leg ser
off-diagonal para todos os pares não repara a obstrução: a família bruta é uma
família de translações unilaterais. Isso classifica esse candidato como no-go
de carrier, não como um simples buraco de diagonalização.

Consequência operacional: a próxima seta deve usar o response/readout
corrigido (boundary return, completion ou canal de defeito) e provar o
center-leg nesse novo carrier. O theorem acima não refuta a realização
corrigida; ele impede apenas reutilizar o jet causal zero-seed sem correção.

## Descoberta formal — balance global, sewing não reduzido ao balance

`CompletedC3CoisometricWronskianProjectionGate.lean` expõe a forma exata:

```lean
canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_gammaCorrectionBalance
```

Ela diz que a costura diagonal é equivalente a
`rawGammaWronskianDefect + I * (2 * GammaCorrectionBalance) = 0`.
Portanto a igualdade de energia é uma identidade geométrica global de
fatorização, mas sua anulação não é global e não basta para a costura. Se o
balance for fornecido como zero, o residual exato que ainda precisa ser
provado é `canonicalCompletedC3RawGammaWronskianDefect = 0`.

O lado corrigido também está classificado: `canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_polarizedMoment`
prova o readout escalar dos momentos antes de Hankel/Jacobi, mas não fornece
o produto interno do carrier. E
`canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance_pos_of_characteristicZero`
prova positividade estrita no zero característico fora do eixo real. A
equivalência de isotropia com `z.im = 0` sob `NativeCarryLogWaveBoundaryCloses`
é uma consequência condicional e não pode ser usada para fabricar o zero.

Foi formalizado e compilado em `GammaBalanceSewingResidualAudit.lean`:

```lean
theorem canonicalCompletedC3CoisometricSewing_iff_rawDefect_of_gammaBalance_zero
    (z : ℂ) (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hbalance : canonicalCompletedC3GammaCorrectionBalance z hz hzStrip.1 = 0) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout
          z z hzStrip.1 hzStrip.1 =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z ↔
      canonicalCompletedC3RawGammaWronskianDefect z z hz hz = 0
```

O nome completo do readout no arquivo é
`canonicalCompletedC3CoisometricCompressedBoundaryReadout`. Esse é o menor
corolário formal que impede usar o balance como substituto do sewing.

## Auditoria estrutural registrada antes de continuar

- `NativeBoundaryReadoutHPIntertwining.lean`: a cadeia
  `canonicalNativeBoundaryReadout → canonicalNativeBoundarySourceState →
  canonicalCompletedC3TfvdCameraSource → canonicalCompletedC3TfvdResolventDomainVector`
  é exata; a unicidade leva ao estado Gamma/Naimark e ao `gammaBoundaryReadout`.
- `CompletedC3BoundaryRelationSewingBridge.lean`: o sewing é equivalente ao
  `canonicalCompletedC3RawGammaWronskianDefect = 0`; não é consequência do
  balance diagonal.
- `CompletedC3BracketTfvdGreenFactorization.lean`: o Wronskiano completado
  fatoriza através do Green TFVD com todos os canais, e a convergência do
  readout global ao Wronskiano é equivalente ao defeito estrutural misto
  tender a zero.
- `NativeBoundaryArchimedeanDressingSeparation.lean`: a correção
  arquimediana é uma contribuição explícita pela regra do produto; não deve
  ser apagada ao comparar os dois readouts.
- `NativeSourceLocusGreenCompatibility.lean` e
  `CompletedC3SameStructuredBoundaryState.lean`: Gamma e escalar são duas
  projeções do mesmo estado; a compatibilidade é exatamente o residual de
  igualdade entre as formas Green dessas projeções.
- `CompletedC3AllOrderGammaWronskianLimitGate.lean`: a diferença finita se
  separa em dinâmica-estática, defeito estrutural e tail; o tail já tende a
  zero, restando a compatibilidade do carrier/readout.

Conclusão provisória antes do contraexemplo explícito: a evidência apontava
para D, isto é, um theorem bilinear upstream concreto. O resultado foi depois
refinado para D2 no carrier Gamma literal pelo witness formal abaixo; para o
carrier corrigido/enriquecido ainda permanece D. Não usar `Characteristic = 0`,
`BoundaryGreenSewing`, HP ou Gram como hipótese para provar o theorem correto.

### Atualização após o no-go do centro

A conclusão acima foi refinada por `C3GammaCameraTraceObstruction.lean`:
`canonicalC3RawDefect_counterexamples_arbitrarily_close` fornece, para todo
`ε > 0`, um ponto diagonal off-axis Genuine dentro de `ε` do centro, com
`completedNativeOperatorCharacteristic ≠ 0` e defeito Gamma–Wronskian não
nulo. Logo o alvo literal

```lean
∀ z w hz hw,
  canonicalNativeBoundaryReadout z w hz hw =
    completedGreenWronskian
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion w z
```

é falso para o carrier Gamma atual. O defeito não é um simples termo ainda
não estimado: ele tem testemunho formal de não-anulação. A rota correta é
conservar o Gamma como projeção positiva e usar o carrier enriquecido com a
correção/ledger para o readout escalar; a identidade a provar muda de
“Gamma sozinho = Wronskian” para uma igualdade do readout corrigido, com os
cross terms explícitos.

Próxima ação mínima: depois de registrar a negação do sewing Gamma literal,
auditar o center-leg readout do jet causal/TFVD e só então expandir as definições de
`CanonicalCompletedC3FNegFPrimeMixedChannels` e dos canais
`greenProvenance/offDiagonal/readoutResidual/tailCompletion/archimedeanChart`,
identificando se há uma igualdade de fonte já existente que os combine ou
qual único cross-term ainda falta. O alvo literal Gamma não deve mais ser
tratado como uma identidade possível.

Alteração deste checkpoint: somente documentação; nenhum arquivo Lean de
produção alterado. `.lake` não rastreado preservado.

### Formalização do no-go literal

Foi compilado, sem `sorry`, o arquivo
`CarrySelfAdjointOperator/NativeBoundaryReadoutGammaNoGoAudit.lean`, com o
theorem:

```lean
not_canonicalNativeBoundaryCompletedReadoutSewing_of_cameraFive_counterexample :
  ¬ CanonicalNativeBoundaryCompletedReadoutSewing
```

A prova usa apenas o contraexemplo diagonal já kernel-checked e a igualdade
exata entre `canonicalNativeBoundaryReadoutDefect` e
`canonicalCompletedC3RawGammaWronskianDefect`. A checagem direta foi:

```text
lake env lean CarrySelfAdjointOperator/NativeBoundaryReadoutGammaNoGoAudit.lean
```

com exit code `0`. O arquivo de auditoria ainda não foi incluído no agregador
principal; a prova é independente e rastreável no branch.

### Separação do carrier corrigido

`CompletedC3EnrichedSymplecticNoLeakBridge.lean` e
`CompletedC3RecoveredEnrichedWronskianCarrier.lean` já provam um fato
verdadeiro e mais fraco: o `finalReadout` do ledger enriquecido, mantendo
radial + structural + tail + xi + archimedean, é exatamente o Wronskiano
completado em cada cutoff. Isso é uma identidade escalar de readout, não uma
representação `inner state(z) state(w)` e não fornece positividade por si só.

O carrier positivo concreto correspondente também tem um no-go formal:
`not_hasCompletedNativeRealAxisNormalizedGreenKernel_concreteC3_of_defect`
em `CompletedC3ConcretePositiveSewingClosure.lean`, derivado do defeito
central `canonicalCompletedC3ConcretePositiveSewingDefect_zero_zero_ne_zero`.
Logo não é válido promover o ledger escalar a Gram positivo sem uma métrica ou
transporte adicional.

O menor seam natural restante já está tipado em
`CompletedNativeHPGateAudit.lean`:

```lean
def HasCanonicalCompletedNativeTfvdGreenCenterLegReadout
    (incidence : BR2CameraIncidence)
    (jet : (ℕ ⊕ ℕ) → CanonicalCompletedTfvdGreenHilbertCarrier) : Prop :=
  ∀ i j, incidence.centerCoordinate i ≠ incidence.legCoordinate j →
    polarizedGreenMomentCoefficient
      canonicalCompletedNativeLogDerivativeMoment
      (parityJetNumber i) (parityJetNumber j) =
      inner ℂ (jet i) (jet j)
```

Com `BR2BracketIncidenceJetTransport`, esse theorem já fecha o certificado
HP via `completedNativeRealHPCarrierCertificate_of_centerLegReadout`; o
capstone pré-Gram é
`canonicalC2Geometry_causal_response_height_of_centerLegReadout` em
`NaturalNativeSourceValveGreenProvenance.lean`. Portanto o alvo correto para
continuar é provar esse readout no jet causal, não ressuscitar o sewing Gamma
literal nem usar o `finalReadout` escalar como Gram.

Branch: `agent/next-natural-native-gate`
HEAD: `e0d3d09` (`Record native carrier seam checkpoint`)
Data: 2026-09-14

## Meta global

Remover a hipótese geométrica restante e instanciar nativamente
`CompletedNativeRealHPCarrierCertificate` pela cadeia carry → bracket/TFVD →
Green → carrier Hilbertiano correto → momentos canônicos → Jacobi/altura,
sem zeros, fitting, RH ou certificado assumido.

## Estado confirmado

- `CompletedNativeGeometryHeightProvenance.lean`: a cadeia
  `nativeGeometry_to_finiteHeight_chain_of_greenMomentKernel_and_incidenceTransport`
  já consome `IsGreenWronskianMomentKernelGramRepresentation` e o transporte
  incidencial; a independência par/ímpar já existe.
- `NaturalNativeOperatorShiftCapstone.lean`: a equação de coeficientes do
  response Green e o shift estão fechados antes de Gram.
- `CompletedNativeReturnMetricReadoutCrosswalk.lean`: a métrica
  `I + poisson† ∘L poisson` é positiva, auto-adjunta e possui identidade
  polarizada de retorno; ainda recebe a escolha do readout/canal.
- `CompletedNativeTfvdGreenMomentGramBridge.lean`: o defeito exato entre o
  Gram do jet Green e o kernel de momentos está nomeado como
  `canonicalCompletedNativeGreenMomentGramDefect`; a equivalência com o
  transporte Green está formalizada, mas o defeito não é zero em geral.
- `CompletedNativeCorrectedClockBoundaryGate.lean`: o transporte corrigido
  de primeira coluna, `HasCorrectedNativeChiralBoundaryTransport`, implica a
  equação de coeficientes, o kernel de momentos e o certificado HP.
- PR #57 (`agent/corrected-native-chiral-clock-tower`) está confirmado como
  **OPEN**, não mergeado em `main`; deve ser auditado antes de depender dele.

## Hipóteses ainda abertas

- Realizar geometricamente, no mesmo carrier, o Gram
  `polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment`.
- Provar o readout corrigido/valvulado ou a costura de bordo que fornece a
  primeira coluna sem assumir o transporte chiral.
- Se a rota radial for usada, provar simultaneamente a boundary intertwining e
  a strictness uniforme; elas não estão fechadas incondicionalmente.

## No-goes já provados

- O carrier C3 concreto padrão `ordinary ⊕ logJet ⊕ real residual` falha no
  defeito central `(0,0)`; não deve ser ressuscitado nem reescalado.
- A métrica de retorno genérica é positiva, mas seu kernel central é energia
  Green estritamente maior que `h₀`; portanto não é o carrier de momentos.
- O kernel projectivo bruto tem massa diagonal ≥ 1 e não coincide com `h₀`.
- A resposta BR2 causal literal tem massa mínima incompatível com `h₀`.
- Coeficientes corretos da torre quiral não são, sozinhos, uma realização
  Hilbertiana positiva.

## O que NÃO precisa ser refeito

- Não reconstruir Hankel, Jacobi, resolvente, equivalência zero↔autovalor ou
  independência par/ímpar já formalizada.
- Não usar tabela de zeros, scan em `t`, fitting, RH ou positividade assumida.
- Não confundir energia positiva pré-Hankel com igualdade de momentos.

## Alterações feitas nesta sessão

- arquivo: `docs/CHECKPOINT_AUTO_ADJUNTO.md`
- theorem: interface de retomada; nenhum theorem Lean novo ainda.
- motivo: registrar o estado obrigatório antes da arqueologia do PR #57 e
  preservar o gargalo como uma única folha verificável.

## Builds/audits executados

- comando: `ssh llm 'cd /tmp/carry-corrected-native-20260913 && git status ...'`
- resultado: branch limpa além do `.lake` não rastreado; HEAD `e0d3d09`.
- comando: `gh pr view 57 --json number,state,mergedAt,headRefName,baseRefName,title`
- resultado: PR #57 OPEN, base `main`, head
  `agent/corrected-native-chiral-clock-tower`, `mergedAt = null`.

## Gargalo atual EXATO

Provar, para um jet `jet` construído diretamente do carrier Green/TFVD/valva
corrigido,

```lean
IsGreenWronskianMomentKernelGramRepresentation
  canonicalCompletedNativeLogDerivativeMoment jet
```

sem usar `CompletedNativeRealHPCarrierCertificate`, `K`, `J` ou uma métrica
positiva escolhida retroativamente.

## Próxima ação mínima

Auditar o HEAD do PR #57 e comparar seus teoremas de torre corrigida com
`CompletedNativeCorrectedClockBoundaryGate.lean`, identificando se já existe
uma seta não usada para o carrier Hilbertiano; se não existir, registrar o
menor residual de primeira coluna que ainda impede essa seta.

## Retomada

"AO RETOMAR, LEIA ESTE CHECKPOINT PRIMEIRO E CONTINUE DAQUI.
NÃO REPITA INVESTIGAÇÕES MARCADAS COMO FECHADAS OU NO-GO."

## Checkpoint — 2026-09-14 — classificação formal do balance Gamma–TFVD

### Meta global

Determinar se a igualdade de energia Gamma–TFVD é uma identidade geométrica
upstream ou uma condição de sewing/confinamento, sem apagar os canais de
correção e sem usar o balance zero para provar a própria linha crítica.

### Estado confirmado

- Em `CompletedC3CompressedGammaGramCorrection.lean`, a identidade global
  verdadeira é

  ```lean
  canonicalCompletedC3GammaCorrectionBalance z hz hzHalf =
    z.im * (‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 -
      ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2)
  ```

  (`canonicalCompletedC3GammaCorrectionBalance_eq_energyDifference`). Ela é
  uma decomposição geométrica exata, não uma prova de que o lado esquerdo é
  zero.
- Para `z.im ≠ 0`,
  `canonicalCompletedC3GammaCorrectionBalance_eq_zero_iff_energy` prova
  exatamente que `Balance = 0` equivale à igualdade das duas energias. A
  versão totalmente geométrica
  `canonicalCompletedC3GammaCorrectionBalance_eq_zero_iff_gradientEnergy`
  substitui a energia ambiente pela energia do gradiente TFVD/carry.
- A fatoração vetorial é exata e completa:
  `canonicalCompletedC3AmbientResponseState_eq_gamma_add_correction` e
  `canonicalCompletedC3AmbientResponseKernel_eq_gamma_add_threeCorrections`
  mantêm Gamma–correção, correção–Gamma e Gram da correção. Não há theorem
  autorizando descartar qualquer desses canais.
- O carrier Gamma/Naimark é positivo antes do sewing:
  `canonicalCompletedC3PolarizedGammaKernel_posSemidef` e
  `canonicalCompletedC3NormalizedPolarizedGammaKernel_posSemidef`. A sua
  fronteira satisfaz exatamente
  `canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel`, isto é,
  `boundary = (w - conj z) * Gram`.
- O módulo `NativeBoundaryReadoutHPIntertwining.lean` prova a parte upstream
  genuína: fonte nativa, equação de defeito, right-inverse de Green e
  identificação do estado resolvido com o estado Gamma. Também prova que o
  readout nativo é o readout Gamma e que seu defeito é exatamente
  `canonicalCompletedC3RawGammaWronskianDefect`. Ele declara explicitamente
  que não prova a costura escalar.
- A ponte de relação de bordo em
  `CompletedC3BoundaryRelationSewingBridge.lean` é literal:

  ```lean
  CanonicalCompletedC3BoundaryGreenSewing ↔
    ∀ z w hz hw, canonicalCompletedC3RawGammaWronskianDefect z w hz hw = 0
  ```

  (`canonicalCompletedC3BoundaryGreenSewing_iff_rawDefect_zero`). A forma
  Green Gamma é a forma do estado seis-câmeras; a outra forma é a forma
  escalar do par `(boundary companion, characteristic) = (-F', F)`.
- `CanonicalCompletedC3GammaDslopeGram.lean` e
  `CanonicalCompletedC3NormalizedGammaSewing.lean` fecham a consequência,
  não a premissa: o Gram Gamma normalizado coincide com `dslope` exatamente
  quando o readout de bordo coincide com o Wronskiano. O theorem decisivo é
  `canonicalCompletedC3NormalizedPolarizedGammaKernel_eq_dslope_iff_rawWronskian`.
- A auditoria coisométrica fornece um teste contra a interpretação
  “zero característico implica balance”: em
  `CompletedC3CoisometricWronskianEnergyGate.lean`,
  `canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance_ne_zero_of_characteristicZero`
  prova que a balance de energia da realização coisométrica é não nula em um
  zero fora do eixo, e a versão
  `..._pos_of_characteristicZero` dá sinal estritamente positivo no
  semiplano superior. Isso não é uma prova sobre o balance Gamma corrigido em
  si, mas impede promover o locus de zeros a uma regra geral de sewing.
- Não foi encontrado theorem que prove globalmente
  `canonicalCompletedC3GammaCorrectionBalance = 0`, nem theorem que prove
  `completedNativeOperatorCharacteristic z = 0` ⇒ esse balance zero, nem
  equivalência do balance com `Re(s) = 1/2`.

### Classificação Gamma–TFVD

**D — falta exatamente um theorem bilinear upstream.**

Mais precisamente: existe uma identidade geométrica global para a
decomposição do balance, mas a igualdade de energias e o sewing não são
identidades globais já provadas. Também não há base formal para classificá-los
como uma consequência do zero-locus; e tratá-los como equivalentes à linha
crítica seria circular.

### Hipóteses ainda abertas

- Identificar a combinação corrigida de fonte, retorno, projeção e canais de
  escape cujo readout é o Green escalar completo. O carrier final pode não ser
  Gamma isolado; a expansão correta deve preservar os três canais de correção.
- Provar a igualdade bilinear no mesmo carrier, antes de momentos/Hankel/Jacobi.
- Só depois transportar para `HasPolarizedCoefficientVectorEquation` ou para
  `HasCompletedNativeRealAxisNormalizedGreenKernel`, usar a independência de
  incidência e instanciar o certificado HP.

### Theorem bilinear mínimo que falta

Sem criar uma nova abstração, o statement mínimo é a seguinte igualdade
pointwise; sua quantificação sobre todos os pares é exatamente o
`CanonicalCompletedC3BoundaryGreenSewing` já existente:

```lean
theorem canonicalCompletedC3GammaBoundaryState_greenForm_eq_scalarBoundaryPair
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    greenForm (𝕜 := ℂ)
        (canonicalCompletedC3GammaBoundaryState z hz)
        (canonicalCompletedC3GammaBoundaryState w hw) =
      greenForm (𝕜 := ℂ)
        (canonicalCompletedC3ScalarBoundaryPair z)
        (canonicalCompletedC3ScalarBoundaryPair w) := by
  -- prova geométrica fonte → retorno → readout corrigido ainda ausente
  sorry
```

Equivalentemente, usando somente objetos já definidos, falta provar:

```lean
theorem canonicalNativeBoundaryReadout_eq_completedWronskian
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalNativeBoundaryReadout z w hz hw =
      completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion w z := by
  sorry
```

O `sorry` acima é apenas a marca do seam ausente neste registro; nenhum
`sorry` foi introduzido no repositório. A segunda forma é equivalente à
primeira pelo theorem
`canonicalNativeBoundaryCompletedReadoutSewing_iff_boundaryGreenSewing`.

### Corolários já disponíveis quando o theorem bilinear for fornecido

- `CanonicalCompletedC3BoundaryGreenSewing.rawWronskian` obtém a identidade
  Wronskiana sem nova álgebra.
- `CanonicalCompletedC3BoundaryGreenSewing.normalizedGammaKernel_eq_dslope`
  obtém o kernel positivo normalizado e, portanto, a interface de momentos.
- A partir de um `rawJet` que realize essa identidade e do transporte de
  incidência já formalizado, os teoremas existentes de
  `HasPolarizedCoefficientVectorEquation`, Gram Green, Jacobi e resolvente
  constroem o `CompletedNativeRealHPCarrierCertificate`; essa parte não deve
  ser reconstruída.

### No-goes

- Não classificar `Balance = 0` como identidade global só porque a fórmula de
  `Balance_eq_energyDifference` é global.
- Não classificar como zero-locus sem um theorem explícito; no caso
  coisométrico análogo, o balance é estritamente não nulo em um zero
  característico.
- Não chamar a equivalência com `Re(s) = 1/2` sem prova; isso seria usar a
  conclusão como hipótese de sewing.
- Não substituir a igualdade bilinear por positividade do Gram Gamma, nem
  remover os cross terms da expansão ambiente.
- Não zerar genericamente o defeito estrutural das seis câmeras; a cauda
  tende a zero, mas o canal estrutural carrega o deslocamento crítico.

### O que não precisa refazer

- A identidade vetorial `ambient = Gamma + correction` e a expansão dos três
  canais.
- A fonte nativa, o right-inverse Green, a positividade dos Grams Gamma e a
  forma Green da relação de bordo.
- A identidade exata de cauda e toda a cadeia downstream
  `momentKernel → Hankel → whitening → Jacobi → operador`.

### Alterações feitas nesta sessão

- Atualização do bloco `# CURRENT STATE` para a classificação D.
- Registro da auditoria dos módulos Gamma/correção, fonte–Naimark, sewing e
  Gram normalizado.
- Nenhum Lean de produção foi alterado e nenhum `sorry` foi adicionado.

### Builds/audits executados

- Branch/HEAD remoto confirmado antes da auditoria: `agent/next-natural-native-gate`,
  `df12260f618decccacad3d47b490e9833682ac5b`; status somente `.lake` não
  rastreado.
- Auditoria somente leitura de `CompletedC3CompressedGammaGramCorrection.lean`,
  `NativeBoundaryReadoutHPIntertwining.lean`,
  `CompletedC3BoundaryRelationSewingBridge.lean`,
  `PureNativeBoundaryGreenSewing.lean`,
  `CanonicalCompletedC3GammaDslopeGram.lean`,
  `CompletedC3AllOrderSymplecticGammaLimit.lean`,
  `CompletedC3NormalizedAllOrderSymplecticGamma.lean` e módulos de energia
  coisométrica/defeito causal diretamente relacionados.
- Nenhuma compilação nova foi necessária; o build completo anterior permanece
  `9515 jobs`, exit code `0`.

### Gargalo atual EXATO

Não falta uma identidade de energia diagonal. Falta provar que o readout
bilinear do carrier corrigido fonte–retorno–Naimark é exatamente a forma Green
do par escalar `(−F', F)`, isto é, que o raw Gamma–Wronskian defect é zero no
carrier correto. Essa é a única seta que liga a geometria positiva ao
`dslope`/momentKernel; o balance diagonal é apenas um diagnóstico dessa
diferença.

### Próxima ação mínima

Não tentar `Balance = 0`. Auditar a definição concreta do readout corrigido e
provar primeiro o theorem pointwise `canonicalNativeBoundaryReadout_eq_completedWronskian`
ou, se ele for forte demais, identificar o menor residual bilinear entre os
dois lados. Depois de qualquer descoberta, fazer `CHECKPOINT → COMMIT →
CONTINUE`.

### Retomada

"A classificação é D. A decomposição de energia Gamma–TFVD é global; a
igualdade de energia/sewing ainda é um gate bilinear upstream. Continue pela
combinação de canais corrigidos e pelo readout fonte–retorno, mantendo o
defeito estrutural e sem promover zero de característica a sewing."

## Checkpoint — 2026-09-14 — no-go estrito do carrier ambiente source-matched

### Meta global

Fechar a confinamento nativo pela cadeia geométrica carry → câmeras/TFVD →
projeção/valva → Green/Wronskiano → carrier positivo → operador de alturas,
sem definir o carrier nativo a partir de Hankel, Jacobi ou de uma proxy positiva.
O alvo downstream continua sendo instanciar
`CompletedNativeRealHPCarrierCertificate` e consumir a cadeia Hankel/Jacobi já
formalizada.

### Estado confirmado

- O branch remoto é `agent/next-natural-native-gate`, em `98279a2`, com o único
  item não rastreado conhecido sendo `.lake`; ele foi preservado.
- A correção geométrica de Naimark/projeção e a decomposição
  `ambient = Gamma + correction` estão formalizadas em
  `CompletedC3CompressedGammaGramCorrection.lean`, incluindo projeção dos
  portos, ortogonalidade da fuga e a identificação do termo de escape.
- A identidade geométrica fonte → retorno → Hilbert/Green está formalizada em
  `NativeBoundaryReadoutHPIntertwining.lean`; ela produz o produto interno dos
  estados Naimark antes de qualquer Hankel, mas ainda não costura esse produto
  interno ao readout escalar canônico.
- O carrier ambiente/coisométrico é positivamente semidefinido e possui a
  identidade de Green exata. A auditoria em
  `CompletedC3AmbientRadialTiltSamplePositivity.lean` também mostra que o
  defeito radial normalizado, ponderado pelo fator de separação, tende a zero
  para cada entrada finita. Isso fecha uma aproximação radial, não a igualdade
  finita/global de readout.
- O arquivo `CompletedNativeAmbientCentralCurvatureDecision.lean` fecha agora
  o diagnóstico de ordem zero: o carrier ambiente source-matched bruto não é o
  carrier canônico de momentos. O teorema
  `canonicalCompletedC3NormalizedAmbientResponseState_zero_norm_sq_gt_moment_zero`
  prova estritamente

  ```text
  canonicalCompletedNativeLogDerivativeMoment 0 <
    ‖canonicalCompletedC3NormalizedAmbientResponseState 0 _‖².
  ```

  A prova vem da curvatura vertical ponderada pela característica, que fica
  abaixo de `1/16`, enquanto a energia do gradiente Green não ponderado fica
  acima de `1/16`. Portanto o mismatch não é numérico nem uma escolha de
  normalização arbitrária.

### Hipóteses ainda abertas

- Construir o readout/node-return corrigido que remove a componente ambiente
  extra sem reescalar o carrier por uma constante escolhida a posteriori.
- Provar a primeira coluna correta (em particular o valor `h₀`) para esse
  carrier corrigido e, depois, a igualdade polarizada de duas variáveis com o
  kernel nativo `dslope`/Green.
- Em termos dos gates existentes, fornecer uma instância concreta de
  `CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining` ou do ledger
  equivalente `CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak`, mas
  somente depois de calibrar o readout correto.
- Alternativamente, construir diretamente uma instância concreta de
  `HasDivisionFreeGreenRepresentation` ou provar
  `CanonicalCompletedC3BoundaryGreenSewing` no carrier corrigido.

### No-goes

- `canonicalCompletedC3NormalizedAmbientResponseState` não pode ser
  identificado com o momento canônico por igualdade literal: há o teorema
  `norm_sq_canonicalCompletedC3NormalizedAmbientResponseState_zero_ne_moment_zero`
  e a desigualdade estrita acima.
- Não basta usar a tendência radial ponderada a zero para concluir igualdade
  de matriz em cutoff finito ou costura global; a separação pode mascarar um
  mismatch de primeira coluna.
- Não corrigir o carrier com um fator escalar para forçar `h₀`, não substituir
  o defeito por uma Gram positiva abstrata e não usar `K`, `J`, Cholesky ou
  Hankel na definição do vetor nativo.
- O no-go é do carrier ambiente/source-matched bruto, não da geometria nativa
  nem do mecanismo de projeção/valva; a rota correta passa pelo
  `node-return/readout` corrigido.

### O que não precisa refazer

- Não refazer a identidade exata de cauda: ela já está formalizada e não é o
  seam atual.
- Não refazer a positividade do carrier Gamma/coisométrico, a decomposição de
  Naimark, nem a cadeia downstream Hankel → whitening → Jacobi → operador.
- Não reabrir a tentativa de uma câmera isolada: a rota estrutural relevante é
  a família de seis câmeras e sua projeção/correção global.

### Alterações feitas nesta sessão

- Nenhum arquivo Lean de produção foi alterado.
- Foi feita auditoria somente leitura do corpo dos teoremas de decisão central
  e deste checkpoint append-only.
- Este novo registro preserva explicitamente o no-go de primeira coluna e
  redireciona a busca para o readout corrigido, sem introduzir hipótese nova.

### Builds/audits executados

- Confirmado no remoto: `HEAD=98279a2`, branch
  `agent/next-natural-native-gate`; `.lake` permanece não rastreado.
- Inspecionado o corpo de `CompletedNativeAmbientCentralCurvatureDecision.lean`.
- Confirmados os teoremas
  `completedNativeAmbientCentralCurvatureDefect_neg`,
  `completedNativeVerticalModulusEnergy_secondDerivative_zero_ne_four_gradientEnergy`,
  `norm_sq_canonicalCompletedC3NormalizedAmbientResponseState_zero_ne_moment_zero`
  e
  `canonicalCompletedC3NormalizedAmbientResponseState_zero_norm_sq_gt_moment_zero`.
- Nenhum novo `lake build` foi necessário: a auditoria leu teoremas já
  presentes no branch cujo build completo anterior passou em `9515 jobs`.

### Gargalo atual EXATO

O carrier ambiente source-matched já é geométrico e positivo, mas carrega uma
energia central estritamente maior que `h₀`. O único seam agora é identificar a
componente que deve ser removida pelo readout/node-return corrigido — ou provar
que o carrier corrigido, e não o ambiente bruto, satisfaz a igualdade
polarizada Green–`dslope` com a primeira coluna calibrada.

### Próxima ação mínima

Inspecionar os módulos de calibração causal/central e de node-return já
existentes (`CompletedC3KernelMetricCalibration.lean`,
`C3GammaCameraTraceObstruction.lean` e os módulos de retorno nativo) para
localizar a definição concreta do readout corrigido e testar primeiro a
igualdade de ordem zero. Se a calibração também falhar, registrar o residual
exato em vez de ajustar constantes.

### Retomada

"AO RETOMAR, LEIA ESTE CHECKPOINT PRIMEIRO. O carrier ambiente bruto é um
carrier positivo real, mas tem `h₀` errado por desigualdade estrita. Continue
somente pela identificação do readout/node-return corrigido; não tente fechar
por Gram, por escala ou pela cauda já resolvida."

---

## Checkpoint 2026-09-14 — carrier nativo four-corner e residual exato

Branch: `agent/next-natural-native-gate`
HEAD confirmado antes deste registro: `232b77a` (`Record vector pre-Gram seam`)
Data: 2026-09-14

### Meta global

Fechar a proveniência nativa do operador de alturas pela cadeia geométrica
carry → câmeras/TFVD → Green/valva → carrier Hilbertiano positivo →
momento/Hankel/Jacobi, sem inserir o operador ou a positividade como hipótese
externa.

### Estado confirmado

- O carrier positivo nativo mais próximo já existe antes de Hankel/Jacobi:
  `nativeGpreFourCorner` e seus prefixos de Taylor/enriched Taylor em
  `CompletedC3FourCornerTaylorGram.lean`.
- `nativeGpreFourCornerTaylorPrefix_eq_inner` identifica literalmente esse
  prefixo com um produto interno de quatro cantos; as torres de Gram são
  positivas quando a independência correspondente é fornecida.
- A costura entre esse carrier e o Wronskiano completado já está reduzida a
  uma igualdade com residual nomeado:
  `canonicalCompletedC3RawMixedWronskian_eq_nativeFourCorner_add_totalDefect`
  e
  `canonicalNativePolarizedTfvdGreenMomentKernelDefect_eq_wronskian_sub_nativeFourCorner`.
- O teorema
  `canonicalNativePolarizedTfvdGreenMomentKernel_eq_nativeFourCorner_iff_defect_limit_zero`
  confirma que o four-corner vira exatamente o kernel Green/momento somente
  quando o limite do residual de sewing é zero.
- `CompletedNativeCorrectedMaterialAtlas.lean` melhora o readout radial,
  prime/log-jet e mantém o slot refletido oculto, mas não elimina por si só o
  residual nem fornece o transporte material de relógio.
- A resposta causal/return e o transporte de incidência existem como objetos
  nativos reais (`BR2CausalGreenResponseTransport.lean`), mas ainda não há
  igualdade entre o Gram dessa resposta e o kernel polarizado canônico.
- A torre corrigida do PR #57 continua sendo uma especificação exata de
  coeficientes, não uma realização positiva de Hilbert; portanto o PR não é
  dependência suficiente para fechar o gate.

### Hipóteses ainda abertas

- Provar que o residual material/total de four-corner tende a zero na
  normalização correta, ou construir uma valva/defeito corrigido cujo carrier
  já satisfaça essa costura exatamente.
- Alternativamente, produzir diretamente um `rawJet` nativo que satisfaça
  `HasPolarizedCoefficientVectorEquation` e cujo carrier seja o mesmo da
  independência incidencial.
- Depois disso, reutilizar o teorema pre-Gram
  `canonicalC2Geometry_height_chain_of_coefficientEquation_and_incidenceTransport`;
  a cadeia downstream de Hankel/Jacobi/altura não precisa ser reconstruída.

### No-goes já provados/reforçados

- O `nativeGpreFourCorner` positivo não pode ser identificado com o Green
  completado sem zerar o residual nomeado; positividade do four-corner não
  prova a costura.
- O enriched Taylor rawJet falha o teste de primeira coluna/baixo grau para
  `HasPolarizedCoefficientVectorEquation`; não usar essa família como ponte.
- O transporte do Green normalizado projetivo/BR2 específico falha já no
  ancoramento de ordem zero; isso é no-go dessa identificação, não de todo
  carrier corrigido.
- A torre escalar corrigida e a resposta causal incidencial não podem ser
  coladas por reinterpretacão como Gram positivo sem uma realização vetorial
  independente.

### O que NÃO precisa ser refeito

- Não reconstruir Gram → Hankel → whitening/Cholesky → Jacobi → operador.
- Não usar `K` ou `J` para definir o `rawJet` nativo.
- Não repetir as auditorias fechadas de `nativeGpre`, resposta causal/return,
  PR #57 ou dos no-goes de Taylor/BR2; retomar apenas pelo residual exato.

### Alterações feitas nesta sessão

- Apenas este checkpoint foi atualizado; nenhum Lean de produção foi alterado.
- O estado remoto segue em `232b77a`, com `.lake` não rastreado preservado.

### Builds/audits executados

- Status remoto confirmado: branch limpo salvo `.lake` não rastreado, HEAD
  `232b77a`.
- Auditoria estrutural dos módulos `CompletedC3FourCornerTaylorGram`,
  `CompletedNativePolarizedSameEdgeGreenGramBridge`,
  `CompletedNativeCorrectedMaterialAtlas` e
  `BR2CausalGreenResponseTransport`.
- Build anterior confirmado: `lake build`, `9515 jobs`, sucesso.

### Gargalo atual EXATO

O único seam atual é o residual de sewing/transport que mede a diferença entre
o Wronskiano Green completado e o carrier positivo four-corner nativo. Em
símbolos, falta provar o limite zero de
`canonicalNativePolarizedTfvdGreenMomentKernelDefect` (ou uma igualdade
equivalente no carrier corrigido); sem isso não existe ainda um `rawJet`
positivo nativo com `HasPolarizedCoefficientVectorEquation`.

### Próxima ação mínima

Ler `CompletedC3PolarizedCameraCrossResidual.lean` e localizar a forma
estrutural mínima do residual (primeira coluna, radial/prime-log ou termo de
defeito) que poderia ser anulada pela operação corrigida de
transporte/anulação, sem voltar para Hankel/Jacobi.

### Retomada

"AO RETOMAR, LEIA ESTE CHECKPOINT PRIMEIRO E CONTINUE DO RESIDUAL FOUR-CORNER.
NÃO REPITA AS AUDITORIAS FECHADAS; PROCURE SOMENTE A ANULAÇÃO/TRANSPORTE QUE
TORNA O CARRIER POSITIVO IGUAL AO GREEN COMPLETADO."

---

## Checkpoint 2026-09-14 — seis câmeras, canal estrutural e carrier Gamma

Branch: `agent/next-natural-native-gate`
HEAD no início deste checkpoint: `b8de70c` (`Record native four-corner residual audit`)
Data: 2026-09-14

### Meta global

Seguir a construção geométrica real: incidência/câmeras → TFVD/valva →
Naimark/simetria → carrier positivo nativo → identidade Green e momentos,
sem transformar o Gram ou o operador em definição retroativa.

### Estado confirmado

- O candidato de uma câmera e quatro canais é um no-go estrutural, não apenas
  uma falha de prova: em parâmetros iguais, o segundo canal converge para
  `-((3 : ℝ) ^ criticalDisplacement * infiniteReflectedGradientPairing)`,
  que é não nulo no Genuine critical strip.
- A realização correta é simultânea em seis câmeras (`2,...,7`). O módulo
  prova a igualdade exata da família completa de traces com o TFVD ponderado e
  a reconstrução symplectic/Naimark:
  `canonicalC3SixCameraSymplecticComplexReadout_eq_greenForm`.
- O readout Green das seis câmeras já é a mesma forma Green intrínseca do
  port C3; não é preciso eliminar câmeras individualmente.
- A decomposição exata do objeto completo é:

  ```text
  completed raw Wronskian
    = six-camera Green readout
      + structural defect
      + tail-completion defect.
  ```

  Isso está em `canonicalCompletedC3RawHeightMixedWronskian_eq_sixCameraGreen_add_channels`.
- A identidade de cauda já está fechada: `canonicalC3MixedHeightTailCompletionDefect_tendsto_zero`.
  Logo a cauda não é o gate atual.
- O defeito estrutural também já tem limite exato:
  `canonicalC3FiniteMixedHeightStructuralDefect_tendsto`, igual a
  `raw Wronskian - completed radial Green`. Em um Genuine zero ele tende ao
  negativo do canal radial e só tende a zero se a parte real for `1/2`.
- Portanto não devemos tentar provar que o defeito estrutural desaparece
  genericamente. Ele é precisamente o sinal geométrico que carrega a
  confinabilidade; zerá-lo fora da linha crítica seria pedir a conclusão.
- Existe um carrier positivo genuíno anterior a Hankel/Jacobi: o estado
  `canonicalCompletedC3AllOrderSymplecticGammaState` e seu kernel Gram
  `canonicalCompletedC3AllOrderSymplecticGammaKernel`. O Lean prova
  `canonicalCompletedC3AllOrderSymplecticGammaKernel_posSemidef` e a identidade
  de bordo `(w - conj z) * GammaKernel`.
- A normalização pelo trace bruto também é uma Gram positiva:
  `canonicalCompletedC3NormalizedAllOrderSymplecticGammaKernel_eq_inner` e
  `..._posSemidef`. A igualdade desse Gram com o Wronskiano normalizado é
  equivalente ao gate de sewing, não uma consequência automática da
  positividade.
- Há uma identidade ainda mais nativa, sem passar pelo Gram dos momentos:
  `canonicalNativeBoundarySource_green_identity_package`. Ela dá o defeito
  de Green ambiente como `(w - conj z)` vezes o produto interno de duas
  imagens Naimark da fonte nativa resolvida, e prova simultaneamente a
  equação de fonte e o right-inverse Green.

### Hipóteses ainda abertas

- O carrier Gamma/Naimark positivo precisa ser ligado ao readout escalar
  canônico da teoria (ou ao `polarizedGreenMomentCoefficient`) por uma
  identidade de transporte de dois parâmetros. A positividade do carrier,
  isoladamente, não fornece essa identificação.
- A hipótese global nomeada
  `CanonicalCompletedC3BoundaryGreenSewing` ainda não tem construtor nativo;
  ela é exatamente a igualdade entre o Green da fonte Gamma e o Green do par
  escalar TFVD, ou equivalentemente o zero do `canonicalCompletedC3RawGammaWronskianDefect`.
- Depois de uma prova dessa identidade de origem/readout, os teoremas
  `canonicalC2Geometry_native_normalizedRadialDslopeSampleMatrix_posSemidef_of_boundaryGreenSewing`
  e `canonicalC2Geometry_nativeNormalizedRadialGammaJet_inner_tendsto_of_boundaryGreenSewing`
  já transportam positividade e o coeficiente de momentos antes de Hankel.

### No-goes já provados/reforçados

- Não exigir que cada câmera isolada seja o carrier global; o no-go do segundo
  canal mostra que isso destrói a leitura correta.
- Não anular o defeito estrutural como se fosse erro de cauda. A cauda tende a
  zero, mas o estrutural tende ao radial negativo em um Genuine zero.
- Não identificar o Gram positivo Gamma com o Wronskiano normalizado sem
  provar `CanonicalCompletedC3BoundaryGreenSewing`.
- A igualdade Green seis-câmeras é uma igualdade de readout bilinear; ainda
  não é, sozinha, a equação de coeficientes do jet de momentos.

### O que NÃO precisa ser refeito

- Não reabrir o four-corner, a identidade de cauda ou o no-go de uma câmera.
- Não reconstruir Hankel/Cholesky/Jacobi.
- Não tentar fazer a prova por `Gram` bruto das linhas de câmera.

### Alterações feitas nesta sessão

- Checkpoint anterior foi salvo e publicado em `b8de70c`.
- Nenhum arquivo Lean de produção foi alterado.
- `.lake` não rastreado foi preservado.

### Builds/audits executados

- Auditoria de `CompletedC3PolarizedCameraCrossResidual.lean`:
  seis-câmeras, no-go da câmera única, decomposição estrutural e readout.
- Auditoria de `CompletedC3AllOrderSymplecticGammaLimit.lean`:
  carrier Gamma positivo, kernel Gram e identidade de bordo.
- Auditoria de `CompletedC3NormalizedAllOrderSymplecticGamma.lean`:
  normalização, positividade e equivalência com o gate de sewing.
- Auditoria de `NativeBoundaryReadoutHPIntertwining.lean`:
  identidade Green ambiente nativa sem hipótese de sewing escalar.
- Build global anterior confirmado: `lake build`, `9515 jobs`, sucesso.

### Gargalo atual EXATO

O seam não é mais “zerar a cauda” nem “provar que a câmera funciona”. É
identificar o readout escalar TFVD/Genuine com o carrier Gamma/Naimark nativo
na forma de uma igualdade de duas variáveis. Formalmente, falta construir
`CanonicalCompletedC3BoundaryGreenSewing` ou um teorema equivalente de
`HasPolarizedCoefficientVectorEquation` para o carrier resolvido. O defeito
estrutural deve permanecer como canal de confinamento, não ser apagado.

### Próxima ação mínima

Auditar `NativeBoundaryReadoutHPIntertwining.lean` e
`CompletedC3CompressedGammaGramCorrection.lean` para ver se a identidade
ambiente fonte→Naimark→Green já contém a operação corrigida que produz o
readout escalar, ou se resta exatamente um termo de correção Gamma–TFVD.

### Retomada

"AO RETOMAR, LEIA ESTE CHECKPOINT PRIMEIRO. A ROTA CORRETA É SEIS CÂMERAS +
NAIMARK + CARRIER GAMMA POSITIVO. NÃO TENTE ZERAR O DEFEITO ESTRUTURAL; PROCURE
SOMENTE A IDENTIFICAÇÃO DE READOUT QUE AINDA LIGA O CARRIER À TEORIA DOS
MOMENTOS."

---

## Checkpoint 2026-09-14 — projeção Naimark corrigida e gate radial de no-leak

Branch: `agent/next-natural-native-gate`
HEAD no início deste checkpoint: `c88e8ba` (`Record six-camera native carrier seam`)
Data: 2026-09-14

### Meta global

Formalizar a operação que remove o artefato de coordenadas das câmeras pela
projeção ortogonal do carrier nativo, mantendo o Green/TFVD como origem do
operador e só depois extraindo os momentos e a altura.

### Estado confirmado

- `CompletedC3CompressedGammaGramCorrection.lean` contém a decomposição vetorial
  exata do response ambiente:

  ```text
  ambient response = Gamma response + TFVD-resolved correction.
  ```

  A correção é dividida em diferença interna do porto e o oposto do escape
  Gamma.
- `canonicalCompletedC3AmbientPortProjection` é uma projeção idempotente,
  fixa os vetores promovidos pelo porto, comuta com a ação escalar realificada,
  e o complemento tem compressão de câmera zero.
- O escape Gamma é ortogonal ao componente projetado; o leak logarítmico é
  exatamente `z • GammaEscape`. Isso formaliza a “válvula” de ortogonalização
  antes de qualquer Hankel/Jacobi.
- `NativeBoundaryReadoutHPIntertwining.lean` prova, sem a costura escalar,
  que a fonte nativa satisfaz o Green right-inverse e que o defeito Green
  ambiente é `(w - conj z)` vezes o produto interno de duas imagens Naimark da
  fonte resolvida. Esta é a identidade geométrica forte disponível.
- `CompletedC3CoisometricBoundaryWronskian.lean` fornece a mesma identidade
  de forma canônica para o source coisométrico e separa explicitamente porto e
  leak; `CompletedC3CoisometricAmbientStrictPositivity.lean` prova
  independência/positividade do carrier ambiente.
- A rota radial anterior a Hankel está completamente explicitada em
  `CompletedNativeRadialTiltSamplePositivity.lean`:
  `CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining` equivale ao
  `CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak`; esse no-leak implica
  a flatness de todos os coeficientes do jet Gamma e, com o limite positivo,
  identifica cada produto interno com
  `polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment`.
- A positividade estrita requer ainda
  `CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound`; a positividade
  semidefinida do Gram Gamma não substitui esse gate de não-colapso.
- A auditoria `NaturalNativeGeometryOperatorAudit.lean` confirma a genealogia:
  a projeção/Green é pré-Hankel; o operador finito só aparece depois do no-leak
  radial e da não-degenerescência incidencial.

### Hipóteses ainda abertas

- Provar o no-leak radial efetivo (`CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak`),
  ou equivalentemente a identificação assintótica do Green boundary readout
  com o `dslope` nos stencils radiais.
- Provar a lower bound uniforme dos determinantes radiais, ou obter a mesma
  não-degenerescência pelo transporte de incidência nativa já existente.
- Não confundir a identidade Green ambiente (já exata) com a costura escalar
  `CanonicalCompletedC3BoundaryGreenSewing`; a segunda ainda é mais forte.

### No-goes já provados/reforçados

- A projeção positiva/ambiente não identifica automaticamente o kernel `dslope`.
- A correção vetorial e a ortogonalidade do escape não autorizam descartar o
  leak; o termo é explícito e reaparece no gate de no-leak.
- PSD de seções finitas e convergência entrada a entrada não implicam a lower
  bound uniforme necessária para positividade estrita.
- Não usar a costura escalar global quando a rota radial local já permite
  formular o seam mínimo.

### O que NÃO precisa ser refeito

- Não reconstruir a projeção Naimark, a decomposição Gamma+correção ou o Green
  ambiente: todos já estão compilados.
- Não tentar provar novamente a identidade de cauda nem o operador downstream.
- Não voltar ao Gram bruto das linhas de câmera.

### Alterações feitas nesta sessão

- Checkpoint anterior publicado em `c88e8ba`.
- Apenas este checkpoint foi atualizado; nenhum arquivo Lean de produção foi
  alterado.
- `.lake` não rastreado permanece preservado.

### Builds/audits executados

- Auditoria de `CompletedC3CompressedGammaGramCorrection.lean`:
  correção de fonte, projeção idempotente, escape/leak e ortogonalidade.
- Auditoria de `NativeBoundaryReadoutHPIntertwining.lean` e
  `CompletedC3CoisometricBoundaryWronskian.lean`:
  identidade Green ambiente/coisométrica exata.
- Auditoria de `CompletedNativeRadialTiltSamplePositivity.lean` e
  `NaturalNativeGeometryOperatorAudit.lean`:
  equivalência no-leak ↔ seam de momentos e gate de determinante.
- Build global anterior confirmado: `lake build`, `9515 jobs`, sucesso.

### Gargalo atual EXATO

O próximo gate mínimo não é “construir um Gram” nem “provar a cauda”: é
mostrar que, depois da projeção/correção nativa, o leak da ledger Gamma some no
germ radial para cada par de ordens, e obter a não-colapso uniforme que torna a
positividade estrita. Formalmente, o alvo é
`CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak` mais
`CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound` (ou uma prova
equivalente via incidência), mantendo o carrier Naimark como objeto de origem.

### Próxima ação mínima

Localizar no módulo da ledger a expressão exata do no-leak radial e testar se a
projeção/correção já provou cada termo do seu limite; se faltar, registrar o
primeiro termo residual (ordem zero) e não tentar concluir a torre inteira.

### Retomada

"AO RETOMAR, LEIA ESTE CHECKPOINT PRIMEIRO. A OPERAÇÃO NATURAL JÁ É A
PROJEÇÃO NAIMARK + CORREÇÃO TFVD. PROCURE SOMENTE O PRIMEIRO TERMO DO
NO-LEAK RADIAL E A NÃO-COLAPSO; NÃO REFAÇA O CARRIER OU O OPERADOR."

## Checkpoint de seam — identidade vetorial antes do Gram

Branch: `agent/next-natural-native-gate`
HEAD: `9502416` (`Record chiral positivity gate`)
Data: 2026-09-14

### Estado confirmado

- A interface mais próxima da genealogia natural é
  `HasPolarizedCoefficientVectorEquation moments rawJet`: ela afirma que o
  produto interno do `rawJet` satisfaz diretamente a equação Green polarizada
  (primeira coluna + shift), antes de qualquer Hankel, Cholesky ou Jacobi.
- `complexGreenWronskianMomentKernel_of_vectorCoefficientEquation` transforma
  essa lei vetorial no kernel par/ímpar; combinada com
  `BR2BracketIncidenceJetTransport`, a
  `canonicalC2Geometry_height_chain_of_coefficientEquation_and_incidenceTransport`
  constrói o certificado HP e retorna o operador simétrico. Este é o caminho
  formal que respeita a ordem `geometria → Green/shift → positividade → altura`.
- A ponte escalar correspondente já está fechada:
  `canonicalC2Geometry_nativeWronskianResponse_coefficientEquation_before_gram`
  e a identidade exata de cauda fornecem a resposta/shift, mas ainda não
  fornecem um `rawJet` com essa mesma lei de produto interno.
- O carrier causal Green/retorno tem transporte incidencial real e é positivo
  em cada cutoff, mas seus Grams são apenas pré-Hankel; o arquivo
  `CompletedNativeCausalGreenTraceTransport.lean` explicitamente mantém o
  readout Wronskiano assinado separado do carrier de momentos.
- O candidato normalizado `canonicalCompletedNativeGreenForwardDifferenceLimitParityJet`
  já possui `..._momentKernel`, mas o transporte vetorial para o BR2 incidencial
  não pode ser obtido por identificação ingênua: o componente par zero exige
  a âncora impossível entre o estado Green normalizado na origem e o estado
  BR2. Isso está provado em
  `CompletedNativeCameraTfvdGreenFrameDefectCrosswalk.lean` e
  `BR2GreenFrameDslopeLimitBridge.lean`.
- O `rawJet` enriquecido de Taylor ordinário + log também não serve: há um
  no-go de baixa ordem para `HasPolarizedCoefficientVectorEquation` em
  `CompletedNativeTfvdEnrichedLowOrderMomentTest.lean`.

### Hipóteses ainda abertas

- Construir ou identificar um `rawJet` nativo corrigido que simultaneamente:
  1. venha do carrier causal/TFVD/valva já existente;
  2. satisfaça a equação vetorial Green polarizada; e
  3. admita o `BR2BracketIncidenceJetTransport` já formalizado.
- Alternativamente, provar a costura division-free/Gamma que fornece o mesmo
  `momentKernel` no carrier correto; não basta transportar o estado Green
  normalizado para o BR2 bruto.

### No-goes reforçados

- Não usar `canonicalCompletedNativeGreenFrameDslopeJet` como se fosse o jet
  incidencial: sua igualdade ao BR2 é equivalente ao defeito vetorial zero e
  falha já em `(Sum.inl 0)` para todo estado com kernel normalizado.
- Não usar `canonicalCompletedNativeTfvdEnrichedTaylorRawJet`: o defeito de
  ordem baixa impede a equação vetorial.
- Não usar a torre `canonicalCompletedNativeCorrectedClockTowerCoefficient`
  como `rawJet`: ela fornece coeficientes escalares corretos, mas não uma
  realização Hilbertiana positiva.

### O que NÃO precisa ser refeito

- Não rederivar o shift, a identidade de cauda, o transporte incidencial
  abstrato, o teorema do kernel Green ou a construção downstream do operador.
- Não voltar ao Gram bruto das câmeras; o seam correto é a lei vetorial
  `HasPolarizedCoefficientVectorEquation`.

### Alterações feitas nesta sessão

- Registro da interface vetorial pré-Gram e da separação entre o carrier causal
  positivo, o readout Wronskiano assinado e o jet incidencial.
- Nenhum Lean de produção alterado.

### Builds/audits executados

- Auditoria de `CompletedNativeCausalCoefficientMomentGate.lean`,
  `CompletedNativeCorrectedGeometryHeightProvenance.lean`,
  `NaturalNativeOperatorShiftCapstone.lean`,
  `CompletedNativeCausalGreenTraceTransport.lean`,
  `BR2GreenFrameDslopeLimitBridge.lean`,
  `CompletedNativeCameraTfvdGreenFrameDefectCrosswalk.lean` e
  `CompletedNativeTfvdEnrichedLowOrderMomentTest.lean`.
- O build completo continua confirmado no checkpoint anterior: `9515 jobs`,
  exit code `0`.

### Gargalo atual EXATO

O menor elo não é mais “provar um Gram”: é fornecer um `rawJet` geométrico
correto com `HasPolarizedCoefficientVectorEquation` e transportá-lo
injetivamente a partir das incidências nativas. As duas realizações concretas
mais próximas já auditadas falham em pontos distintos: o Green-frame normalizado
falha na âncora BR2 de ordem zero; o Taylor enriquecido falha no Gram de baixa
ordem.

### Próxima ação mínima

Auditar a construção `nativeGpreFourCorner`/causal Green + retorno para saber
se ela contém um `rawJet` corrigido com a lei vetorial de primeira coluna e
shift. Se não contiver, registrar a igualdade mínima de primeira coluna que
falta, sem converter a torre escalar corrigida em carrier por definição.

### Retomada

"AO RETOMAR, LEIA ESTE CHECKPOINT PRIMEIRO E CONTINUE DAQUI.
NÃO REPITA INVESTIGAÇÕES MARCADAS COMO FECHADAS OU NO-GO."

## Checkpoint de descoberta — polarização quiral não é ainda o carrier de momentos

Branch: `agent/next-natural-native-gate`
HEAD: `b58e8de` (`Record Green carrier route audit`)
Data: 2026-09-14

### Estado confirmado

- `CompletedC3FullWronskianPolarization.lean` prova que a rotação quarteada
  do Wronskiano completo é uma involução hermitiana; as polarizações positiva e
  negativa são ortogonais e o bloco de dois canais é um Gram Hilbertiano
  positivo.
- `CompletedNativeChiralBlockMomentProbe.lean` prova, para qualquer ordem,
  que o coeficiente que contém os momentos canônicos é o readout assinado:
  `positiveKernel - negativeKernel`. Em particular,
  `canonicalCompletedC3ChiralBlockSignature_succ_eq_polarizedMoment` dá
  diretamente `polarizedGreenMomentCoefficient`.
- Logo a identidade disponível é estruturalmente
  `signed response = Gram(positive channel) - Gram(negative channel)`;
  positividade do bloco diagonal não implica positividade do readout assinado.
- `CompletedC3CausalChiralBoundaryRelation.lean` confirma a mesma leitura em
  forma de bordo: a forma canônica é indefinida (energia de câmera menos
  energia quiral), a isotropia é equivalente à costura diagonal ainda aberta,
  e em um zero característico hipotético a forma fica estritamente positiva,
  portanto o datum não é isotrópico.

### Hipóteses ainda abertas

- Provar uma dominância/compensação nativa que transforme a assinatura quiral
  no kernel Green positivo correto, ou fornecer diretamente o carrier
  `division-free Green`/`Gamma boundary sewing`.
- A rota de um canal isolado é positiva, mas ainda não há teorema de que seu
  kernel tenha os momentos canônicos; escolher um canal e descartar o outro
  mudaria o objeto.

### No-goes já provados/reforçados

- Não usar o Gram dos dois canais como se fosse o kernel assinado: ele é PSD,
  enquanto os momentos vêm da diferença dos blocos.
- Não deduzir a costura de bordo a partir de isotropia; a formalização mostra
  que isotropia é precisamente a hipótese/igualdade que falta.
- Não usar o Wronskiano completo como carrier positivo: ele é uma forma
  quarteada/indefinida, embora sua decomposição em dois Grams positivos seja
  exata.

### O que NÃO precisa ser refeito

- A prova do bloco positivo, a ortogonalidade quiral e os coeficientes
  `h₀`, `h₁` e gerais já estão compilados.
- A cadeia downstream de momentos → Jacobi → altura permanece intocada.

### Alterações feitas nesta sessão

- Registro desta separação entre bloco PSD e assinatura que gera momentos.
- Nenhuma alteração em Lean de produção.

### Builds/audits executados

- Auditoria textual de `CompletedC3FullWronskianPolarization.lean`,
  `CompletedNativeChiralBlockMomentProbe.lean` e
  `CompletedC3CausalChiralBoundaryRelation.lean`.

### Gargalo atual EXATO

A ponte positiva nativa ainda precisa provar que o readout assinado
`K₊(w,z) - K₋(w,z)` é o mesmo kernel de Green normalizado que representa o
  produto interno do jet incidencial. Sem essa igualdade, o bloco quiral é
  apenas evidência pré-Hankel e não uma instância de
  `IsGreenWronskianMomentKernelGramRepresentation`.

### Próxima ação mínima

Buscar no repositório uma hipótese já formalizada de dominância, compensação,
defeito complementar ou positividade do readout assinado; se ela não existir,
comparar explicitamente sua primeira coluna com `h₀` antes de qualquer tentativa
de transporte de todas as ordens.

### Retomada

"AO RETOMAR, LEIA ESTE CHECKPOINT PRIMEIRO E CONTINUE DAQUI.
NÃO REPITA INVESTIGAÇÕES MARCADAS COMO FECHADAS OU NO-GO."

## Checkpoint de descoberta — PR #57 não mergeado e torre apenas de coeficientes

Branch: `agent/next-natural-native-gate`
HEAD: `36f430a`
Data: 2026-09-14

### Estado confirmado

- `gh pr view 57` mostra `OPEN`, `mergedAt = null`, base `main` e head
  `agent/corrected-native-chiral-clock-tower`.
- O head remoto do PR foi auditado nos commits `d3a7e9d` e `e66d467`.
- `CompletedNativeCorrectedChiralClockTower.lean` define
  `canonicalCompletedNativeCorrectedClockTowerCoefficient p q` como
  `polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment p q`.
- O PR prova a primeira coluna corrigida, a equação de coeficientes, o shift e
  a unicidade da torre; ele não constrói uma norma/energia positiva nem prova
  `CompletedNativeRealHPCarrierCertificate`.

### Consequência

A torre corrigida é uma especificação canônica de coeficientes, não a
realização Hilbertiana final. Usá-la diretamente como Gram seria circular para
a missão atual. Não mergear o PR como se ele removesse o gate geométrico.

### Próxima ação mínima atualizada

Auditar as interfaces de `PositiveObservableNativeMomentBridge`,
`CompletedNativeReturnMetricReadoutCrosswalk` e
`CompletedNativeTfvdGreenMomentGramBridge` para encontrar a menor igualdade
upstream que transforma um carrier geométrico já existente no
`momentKernel`, mantendo o residual explícito se essa igualdade não estiver
provada.

## Checkpoint de estrutura — build completo e duas rotas equivalentes de entrada

Branch: `agent/next-natural-native-gate`
HEAD: `3edf447` (`Record corrected clock tower audit`)
Data: 2026-09-14

### Estado confirmado

- `lake build` no checkout remoto `/tmp/carry-corrected-native-20260913`
  terminou com sucesso: `9515 jobs`, exit code `0`.
- A torre corrigida do PR #57 continua sendo apenas uma especificação de
  coeficientes; ela não fecha um carrier positivo.
- Há duas formas já formalizadas de consumir a mesma costura upstream:
  1. `HasDivisionFreeGreenRepresentation` + continuidade produz
     `HasCompletedNativeRealAxisNormalizedGreenKernel` por
     `hasCanonicalCompletedNativeRealAxisNormalizedGreenKernel_of_divisionFreeGreen`;
     depois entram o jet Green, o kernel de momentos, o transporte incidencial
     e a cadeia de altura existente.
  2. O estado Gamma polarizado é positivo; se a costura de bordo
     `CanonicalCompletedC3BoundaryGreenSewing` for provada, seu kernel
     normalizado coincide com o `dslope` e pode alimentar a rota radial/HP.
- `CompletedC3GreenFrameStructuralReadoutBridge.lean` já identifica o
  readout escalar orientado com o produto interno do estado Parseval nativo,
  condicionado ao kernel Green normalizado. Portanto a passagem escalar →
  carrier está escrita; falta fornecer o kernel Green normalizado sem assumir
  a conclusão.
- `CompletedC3GammaDslopeGram.lean` prova positividade semidefinida do kernel
  Gamma e a equivalência exata entre sua identificação com `dslope` e a
  igualdade do readout de bordo.
- `CompletedC3BoundaryRelationSewing.lean`,
  `PureNativeBoundaryGreenSewing.lean` e
  `NativeBoundaryReadoutHPIntertwining.lean` reduzem essa igualdade ao
  residual nomeado de mismatch Gamma–Green nativo; nenhuma prova de que o
  residual é zero foi encontrada.
- O carrier do Wronskiano completo é exato como produto interno de um operador
  normalizado (`completedGreenWronskian_eq_normalizedFullOperatorInner`), mas
  não é um substituto positivo do carrier de momentos. O teorema
  `canonicalCompletedC3GammaBoundary_ne_fullOperatorInner_of_characteristicZero`
  mostra que identificar esses dois readouts globalmente seria uma afirmação
  adicional forte, não uma simplificação legítima.

### Hipóteses ainda abertas

- Fornecer uma realização concreta de
  `HasDivisionFreeGreenRepresentation` no carrier nativo correto, ou provar
  diretamente a costura `CanonicalCompletedC3BoundaryGreenSewing`.
- Em forma mínima, para um jet genuinamente construído por Green/TFVD/valva,
  provar:

  ```lean
  IsGreenWronskianMomentKernelGramRepresentation
    canonicalCompletedNativeLogDerivativeMoment jet
  ```

- Não há atualmente um estado concreto no código que satisfaz a hipótese
  division-free ou a costura de bordo; os teoremas downstream são condicionais
  a uma dessas entradas.

### No-goes reforçados

- A identidade algébrica da torre corrigida não pode ser reinterpretada como
  positividade: isso reutilizaria o kernel-alvo como se fosse Gram.
- A positividade do estado Gamma e a exatidão do Wronskiano completo, tomadas
  separadamente, não provam a mesma igualdade; o primeiro é positivo mas exige
  a costura, e o segundo é indefinido para o papel de momento.
- Não substituir o residual Gamma–Green por uma proxy positiva nem ajustar a
  constante para forçar o valor `h₀`.

### O que NÃO precisa ser refeito

- Não reconstruir a cadeia Hankel → whitening/Cholesky → Jacobi → operador de
  alturas.
- Não reauditar o build inteiro salvo após alteração de código; o build atual
  está confirmado em `9515 jobs`.
- Não tratar o PR #57 como dependência mergeada nem repetir a busca por uma
  prova de costura que já foi reduzida aos resíduos nomeados.

### Alterações feitas nesta sessão

- Atualização deste checkpoint com a auditoria estrutural das rotas
  division-free/Gamma e com o resultado do build completo.
- Nenhum arquivo Lean de produção foi alterado; nenhuma hipótese nova foi
  introduzida.

### Builds/audits executados

- `lake build`: sucesso, `9515 jobs`, exit code `0`.
- Auditoria de `CompletedNativeHPGateAudit.lean`,
  `NaturalNativeOperatorShiftCapstone.lean`,
  `CompletedC3GreenFrameStructuralReadoutBridge.lean`,
  `CanonicalCompletedC3GammaDslopeGram.lean`,
  `CompletedC3BoundaryRelationSewing.lean`,
  `CompletedC3ValveGreenNaturality.lean` e
  `CompletedC3GammaFullWronskianOperatorBridge.lean`.

### Gargalo atual EXATO

O único elo upstream ainda não materializado é a igualdade geométrica que
transforma o Green/TFVD/valva nativo em um kernel positivo normalizado com o
readout escalar canônico: equivalentemente, uma prova concreta de
`HasDivisionFreeGreenRepresentation` ou de
`CanonicalCompletedC3BoundaryGreenSewing`, suficiente para instanciar o
`momentKernel` no mesmo carrier que já possui a independência incidencial.

### Próxima ação mínima

Inspecionar a polarização quiral positiva e a relação causal de bordo para
verificar se elas constroem esse carrier positivo sem usar `K`, `J`, Hankel ou
os coeficientes da torre como definição. Se falhar, registrar o menor
residual de primeira coluna/costura, não fabricar uma igualdade.

### Retomada

"AO RETOMAR, LEIA ESTE CHECKPOINT PRIMEIRO E CONTINUE DAQUI.
NÃO REPITA INVESTIGAÇÕES MARCADAS COMO FECHADAS OU NO-GO."
