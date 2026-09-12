# Native boundary readout / HP crosswalk

## Provenance

- Repositório: `thiagomassensini/carry-self-adjoint-operator`
- Base observada: `535ddcf9eb3cd5f48e062f3918dfe9c11b0962ff`
- Branch de trabalho: `agent/native-cyclic-realization-hp-intertwining-next`
- Branch solicitada: `agent/native-cyclic-realization-hp-intertwining` (já existia como tentativa anterior e foi preservada)
- Commit produzido: registrado no histórico Git desta branch

A branch anterior não foi apagada nem reescrita. Ela contém a auditoria da fonte não amortecida e o diagnóstico de que essa fonte tem massa harmônica, portanto não é um vetor de `NativeLogHilbert`. A continuação aqui trata a fonte como dado de contorno/resolvente, que é a realização suportada pelo código atual.

## Escopo corrigido

A arqueologia em `/home/thlinux/Downloads/Wayl/` confirma a ordem causal

```text
native carry operator
  -> completed characteristic
  -> logarithmic response
  -> canonical moments
  -> Hankel/whitening/Jacobi/HP
```

Esta rodada não introduz um `Y_native` ou um vetor cíclico amortecido anterior aos momentos. Em vez disso, registra a realização nativa que o pin já possui: a fonte TFVD é resolvida no domínio maximal do multiplicador logarítmico e a compatibilidade escalar é deixada como um defeito de contorno explícito.

## Inventário

| objeto | estado |
|---|---|
| `nativeLogGenerator` e auto-adjunticidade | CLOSED EXISTING |
| órbita nativa não amortecida em `NativeLogHilbert` | OBSTRUCTED para a fonte bruta: massa harmônica |
| `canonicalCompletedC3TfvdCameraSource` | CLOSED EXISTING |
| `canonicalCompletedC3TfvdResolventDomainVector` | CLOSED EXISTING |
| equação de defeito do resolvente TFVD | CLOSED THIS BRANCH (wrapper) |
| right inverse Green do estado TFVD | CLOSED THIS BRANCH (wrapper) |
| identificação do estado com `carryGammaIntoDomain` | CLOSED THIS BRANCH (wrapper) |
| mapas de contorno das duas relações Gamma | CLOSED THIS BRANCH (wrapper) |
| readout boundary nativo de dois pontos | CLOSED THIS BRANCH |
| readout nativo = readout Gamma | CLOSED THIS BRANCH |
| separação espectral × kernel Gamma | CLOSED THIS BRANCH |
| Gram Hilbertiano ambient antes da scalarização | CLOSED EXISTING, especializado nesta branch |
| sewing escalar com o Wronskiano completed | OPEN/CONDITIONAL |
| kernel Gamma normalizado = `dslope` | CONDITIONAL pelo sewing existente |
| `h_n` como momentos de um operador positivo preexistente | OPEN; não exigido nesta branch |
| certificado HP incondicional | OPEN; depende do sewing/Gram nativo |

## Fonte e domínio

As definições novas são apenas aliases e wrappers das primitivas existentes:

```lean
canonicalNativeBoundarySourceState z hz
  := canonicalCompletedC3TfvdResolventDomainVector z hz

canonicalNativeBoundarySource z
  := canonicalCompletedC3TfvdCameraSource z

canonicalNativeBoundarySourceRelationPair z hz
  := (canonicalCompletedC3GammaSourceRelationFst z hz,
      canonicalCompletedC3GammaSourceRelationSnd z hz)
```

Os tipos exatos são:

```text
canonicalNativeBoundarySourceState z hz : RealifiedLogarithmicDomain
canonicalNativeBoundarySource z            : RealifiedCameraComplexification
canonicalNativeBoundarySourceRelationPair z hz
  : carrySourceRelation × carrySourceRelation
```

O estado é um resultado de `logarithmicResolventIntoDomain`; a fonte bruta não é afirmada como membro de `NativeLogHilbert`. A equação de defeito exportada nesta branch é

```lean
realifiedNaimarkScalar z
    (realifiedLogarithmicDomainEmbedding (canonicalNativeBoundarySourceState z hz))
  = realifiedLogarithmicMultiplication (canonicalNativeBoundarySourceState z hz)
      + realifiedNaimarkPort (canonicalNativeBoundarySource z)
```

A conversão da fonte TFVD para a fonte C3 canônica usa explicitamente
`canonicalCompletedC3TfvdCameraSource_eq_canonicalSource`; não há cast nem identificação por `rfl` entre construções diferentes.

## Right inverse e traços

Foram empacotados os teoremas existentes
`canonicalCompletedC3TfvdResolventDomainVector_greenRightInverse` e
`canonicalCompletedC3TfvdResolventDomainVector_eq_gamma`. Assim, o estado nativo é um right inverse de
`z - realifiedLogarithmicMultiplication` para a fonte C3 e coincide, por unicidade do resolvente, com o estado Gamma no domínio maximal.

As duas componentes de
`canonicalNativeBoundarySourceRelationPair` recebem os mapas de Weyl já provados:
`canonicalCompletedC3GammaSourceRelationFst_weylBoundaryMap` e
`canonicalCompletedC3GammaSourceRelationSnd_weylBoundaryMap`. Esta branch não constrói uma nova relação de contorno.

## Readout de dois pontos e residual

O readout não colapsado é

```lean
canonicalNativeBoundaryReadout z w hz hw :=
  canonicalCompletedC3CandidateResolventBoundaryReadout z w
    (canonicalNativeBoundarySourceState z hz)
    (canonicalNativeBoundarySourceState w hw)
```

Ele satisfaz, incondicionalmente,

```lean
canonicalNativeBoundaryReadout z w hz hw
  = canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw

canonicalNativeBoundaryReadout z w hz hw
  = (w - conj z) * canonicalCompletedC3PolarizedGammaKernel z w hz hw

canonicalNativeBoundaryReadout z w hz hw
  = canonicalCompletedC3BracketCauchyBoundaryReadout z w hz hw
```

O numerador division-free e o defeito são mantidos como objetos separados:

```lean
canonicalNativeBoundaryReadoutDefect z w hz hw
  := canonicalNativeBoundaryReadout z w hz hw
       - completedGreenWronskian
           completedNativeOperatorCharacteristic
           completedNativeOperatorBoundaryCompanion w z
```

O crosswalk exato é

```lean
canonicalNativeBoundaryReadoutDefect_eq_rawGammaWronskianDefect
```

e também

```lean
canonicalNativeBoundaryReadoutDefect_eq_boundaryGreenForm_sub
```

Portanto o único residual escalar não foi eliminado: ele é exatamente o
`canonicalCompletedC3RawGammaWronskianDefect`, equivalentemente a diferença entre a forma Green da fonte Gamma e a forma Green do par escalar completed. A equivalência pública é:

```lean
CanonicalNativeBoundaryCompletedReadoutSewing ↔
  ∀ z w hz hw, canonicalNativeBoundaryReadoutDefect z w hz hw = 0
```

```lean
CanonicalNativeBoundaryCompletedReadoutSewing ↔
  CanonicalCompletedC3BoundaryGreenSewing
```

A igualdade normalizada com o `canonicalCompletedNativePolarizedDslopeKernel` permanece explicitamente condicional em
`canonicalNativeBoundaryCompletedReadoutSewing.normalizedGammaKernel_eq_dslope`.

## Parte Hilbertiana que já fecha

Antes da costura escalar, a realização ambient existente fornece

```lean
canonicalCompletedC3AmbientDefectBoundaryReadout z w u v
  = (w - conj z) *
      inner ℂ
        (canonicalCompletedC3GammaNaimarkView
          (realifiedLogarithmicDomainEmbedding u))
        (canonicalCompletedC3GammaNaimarkView
          (realifiedLogarithmicDomainEmbedding v))
```

A branch especializa isso para os dois estados TFVD resolvidos em
`canonicalNativeBoundarySource_ambientGreenDefect_eq_separation_mul_gram`.

O teorema empacotado
`canonicalNativeBoundarySource_green_identity_package` reúne os dois right inverses e essa fatoração de Gram. Ele demonstra positividade do pedaço Hilbertiano por ser Gram, mas não afirma que o readout escalar Gamma é o Wronskian completed.

## O que não foi usado

- nenhuma escolha de `sixCamera` como fundamento do argumento;
- nenhum limite de atlas, cutoff ou câmera;
- nenhuma igualdade `inverse(compression) = compression(inverse)`;
- nenhum `Y_native` inventado a partir de momentos/Jacobi;
- nenhum dos carriers refutados (`ordinary + log`, ambient scalar, Taylor complexo, return metric ordinary);
- nenhum `Gpre`, TFVD collapse, Möbius, Jacobi, Hankel, zero, zeta, RH ou fitting numérico;
- nenhuma hipótese `Genuine`/zero nova;
- nenhuma constante recalibrada.

O nome `canonicalCompletedC3SixCameraSource` aparece internamente porque é a implementação atual da fonte C3 canônica, mas os novos teoremas não expõem índice de câmera nem tomam limite de atlas. A branch anterior continua preservada para o diagnóstico da fonte harmônica.

## Respostas do gate

1. **endpoint/source nativo:** `canonicalCompletedC3TfvdCameraSource` (igual à fonte C3 canônica) e o estado resolvido `canonicalCompletedC3TfvdResolventDomainVector`.
2. **bulk:** não foi criada uma nova decomposição; o bulk é o estado `RealifiedLogarithmicDomain` e seu embedding `realifiedLogarithmicDomainEmbedding`. O `realifiedLogarithmicMultiplication` é o operador bulk no defeito.
3. **Poisson:** a realização Gamma existente é `carryGammaIntoDomain`; sua unicidade identifica o estado TFVD. Não há um novo mapa Poisson nesta branch.
4. **`Eᴴ returnMetric E = I`:** não foi usado; a rota desta branch é boundary/resolvente TFVD, não a return metric.
5. **genericidade:** os wrappers são para a fonte C3 canônica atual; não há parâmetro de câmera no novo readout.
6. **desaparecimento da câmera:** não há câmera no tipo do readout ou do defeito; a implementação existente da fonte C3 ainda contém o packing canônico interno e não foi substituída por uma alegação de universalidade.
7. **kernel construído:** readout Gamma não colapsado e, no nível ambient, o defeito boundary com fatoração de Gram.
8. **fatoração:** `canonicalCompletedC3AmbientDefectBoundaryReadout_eq_kernel`, especializado pelo novo teorema.
9. **PSD:** o componente Gram Hilbertiano é PSD incondicional; a identificação com o dslope não é.
10. **readout comprimido:** `canonicalNativeBoundaryReadout`.
11. **numerador:** o próprio readout division-free e o defeito `canonicalNativeBoundaryReadoutDefect`; o defeito coincide com `canonicalCompletedC3RawGammaWronskianDefect`.
12. **Wronskiano completed:** não coincide incondicionalmente; a diferença é o residual acima.
13. **momento zero:** não foi provado nesta branch.
14. **defeito exato:** `canonicalNativeBoundaryReadoutDefect = canonicalCompletedC3RawGammaWronskianDefect`.
15. **kernel = dslope:** somente sob `CanonicalNativeBoundaryCompletedReadoutSewing`.
16. **identidade residual única:** diferença das duas formas Green, ou raw Gamma–Wronskian defect.
17. **return metric / `carryTfvdTraceMetric`:** relação não estabelecida; ambas permanecem separadas.
18. **constantes:** nenhuma ajustada.
19. **sixCamera como fundamento:** não.
20. **limites:** nenhum.
21. **no-go estático:** respeitado; o residual não foi apagado.
22. **novo `HasCompletedNativeRealAxisNormalizedGreenKernel`:** não construído, pois faltaria zerar o residual escalar.
23. **Hankel PosDef:** não ficou incondicional nesta branch; as APIs existentes continuam condicionais ao certificado de Gram.
24. **operador autoadjunto:** não ficou incondicionalmente novo nesta branch.
25. **outcome:** **C** — a fonte boundary/defect e a identidade de Gram Hilbertiana são fechadas; a compatibilidade escalar com o Wronskiano completed fica isolada num residual nomeado.
26. **próximo theorem mínimo:** construir, para a mesma fonte TFVD e sem novo carrier ajustado, um trace-glue que prove `CanonicalNativeBoundaryCompletedReadoutSewing`, ou equivalentemente `canonicalCompletedC3RawGammaWronskianDefect = 0`; depois reutilizar o crosswalk dslope → momentos → HP já existente.

## Axiomas e validação

Os teoremas novos foram escritos apenas como wrappers, reescritas e fatorações de teoremas existentes. A auditoria `#print axioms` deve permanecer nos axiomas permitidos (`propext`, `Classical.choice`, `Quot.sound`); nenhum `sorry`, `admit` ou axioma de projeto é introduzido.

O build e as auditorias são executados no commit final desta branch e registrados no relatório da rodada.
