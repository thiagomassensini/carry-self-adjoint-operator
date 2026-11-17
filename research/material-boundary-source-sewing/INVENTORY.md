# Inventário da costura física e relacional

Levantamento ao vivo no host `llm`, nesta rodada. Os quatro arquivos `inventory-*.lean` verificam os tipos e registram `#print axioms` das declarações indicadas. Os logs comprimidos e as versões efetivamente consultadas estão em `evidence/`. Não se usa um resultado positivo de um dos espaços como prova do sinal em outro.

## Versões

| Repositório consultado | HEAD / estado |
|---|---|
| carry-self-adjoint-operator | base `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`, main; dois arquivos C2OddTfvdTransport preexistentes não rastreados e preservados |
| native-carry-spectral-weyl | `871217099a069083791738578b2e44005b31986e`, branch `agent/relational-divisibility-gram`, limpo; PR #15 OPEN, não integrado |
| green-frame-theorem | checkout `/home/thlinux/green-frame-theorem-limit`, `12445c08087fa0c5fc5b2350f3455e09bc6b8b42`, main limpo |
| geometry-of-numbers | `da58f044c1c75bd828951bfb41614a6e7b8b465e`, branch `agent/seventh-even-centered-source`, limpo |

Esses são checkouts de pesquisa, não novos pins do operador. Os pacotes efetivamente consumidos permanecem: NativeCarrySpectralWeyl `298d83c9351e308a5213b9f5ac32e44087f98a9f`, GreenFrame `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`, geometria `d7cc54f5c485320f1fada33118e9e6101488819a`, CPFormal `65d50f6db1208708e109982ba97e1d51d3039956`, NativeCarryC3Crosswalk `150cfc7fb08da96bf8117f15869cc2b819d593c2`. Os caminhos reais, incluindo symlinks dos caches compartilhados, estão em `provenance.json`. Nenhum pin foi alterado. O checkout GreenFrame consultado não tinha oleans locais; sua auditoria Lean usa o cache efetivamente consumido pelo operador. Os cinco módulos originais examinados são idênticos byte a byte entre o checkout e esse pin, conforme `green-source-comparison.json`; a diferença de versões acrescenta somente VariableNormSigma e sua exposição/auditoria, sem mudar esses objetos. Não se anuncia um rebuild do checkout GreenFrame mais novo.

## native-carry-spectral-weyl e PR #15 separado

- **PASS existente:** `Infinite.finiteGramMatrix_quadratic_eq_sum_sq`, em `Infinite/GramKernel.lean`, realiza a forma quadrática do núcleo multibase como soma de quadrados de combinações de perfis por nível e resíduo, dividida pelo período. Os índices são câmeras, não posições materiais nem ordens de derivada.
- **PASS existente:** `finiteGramMatrix_posDef` prova positividade estrita das restrições principais, distinguindo inclusive C2/C4 no caso da mesma inclinação. `gramForm_pos` vale para coeficientes de suporte finito não nulos sobre `CameraIndex`.
- **PASS existente:** `Infinite.cameraEmbedding_inner`, em `Infinite/CameraCompletion.lean`, preserva exatamente `gramForm` na própria completação Hilbert. Não identifica esse Gram com a energia quiral assinada.
- **PASS no PR #15 ainda OPEN:** `Finite.Relational.divisibility_inner`, `gramKernel_relational` e `inner_naimarkCameraVector_relational`, em `Finite/RelationalDivisibilityGram.lean`, identificam o núcleo estático original com a realização por `1/lcm(d,e)`, com os coeficientes C2 e antipodais. O módulo foi verificado separadamente no checkout desse PR; ele não foi incorporado aos pins nem importado como uma nova hipótese do operador.
- **NO-GO existente, escopo específico:** `secondDifference_c5_not_in_sixCamera_span` separa os resíduos 1 e 13 do período 420 e refuta a invariância daquele span de seis perfis pela segunda diferença simétrica unitária. Gram estático positivo não fornece entrelaçamento dinâmico dos projetores.
- O script do PR #15 que testava C=B+E e massa quadrática do bordo 12 para cutoffs 1…100 foi lido como experiência inteira finita. A nova identidade vetorial desta rodada é universal em câmera/cutoff; não se anuncia aqui um novo teorema universal da massa 12.

## green-frame-theorem

- **PASS existente:** `Concrete.carryCameraWeight_finsum_eq_one`, em `Concrete/Arithmetic/PositionalDepth.lean`, soma literalmente as câmeras naturais para cada n>1. Câmera é representação da mesma geometria; o lema não autoriza escolher outra energia.
- **PASS existente:** `concreteAnalysisOperator` é o operador original `((semente,residual,G1),G≥2)` em `ConcreteSplitOperators.lean`. `seedResidualAnalysis` guarda a amostra em 1 e `residualAnalysis`; `concreteAnalysisOperator_norm_sq_eq_seedResidual_add_green` recompõe o Green completo antes da estimativa.
- **PASS existente:** `concreteAnalysisOperator_norm_sq_bounds` dá limites 1/2 e 1+greenBesselConstant na métrica original. Não declara que o Gram bruto seja identidade.
- **PASS existente:** `frameOperator_strictlyPositive` é um teorema sobre T†T com um certificado explícito `ComplexFrameBounds T`. Isso não instancia o pareamento da fonte quiral.

## geometry-of-numbers

- **PASS existente:** `C2GlobalGreenBridge.c2GlobalRestrictedGreenGram_strictlyPositive` refere-se ao Gram do Green bruto restrito à entrada C2 isométrica. O teorema de bounds conserva 1/2 e 1+greenBesselConstant; nenhuma isometria bruta G=I é inferida.
- **PASS existente:** `completeVerticalObservabilityGram_posDef`, em `CompleteVerticalObservationGram.lean`, deriva o Gram positivo da independência da própria família de observação completa, para 0<eta<1. Não é uma Hankel de momentos.
- **NO-GO existente:** `c2IsometricIncidenceSynthesis_not_parityMomentGram`, em `VerticalIncidenceGramObstruction.lean`, e `c2RealIncidenceJet_not_parityMomentGram`, em `RealTfvdCenterLegMomentSeam.lean`, refutam a identificação da incidência nua reconstruída e de suas imagens isométricas com uma Hankel: os pares (0,2) e (1,1) exigiriam o mesmo momento igual a zero e a um. Não refutam um readout completado diferente.

## carry-self-adjoint-operator

- **PASS existente:** `MaterialCameraJets.materialCameraSynthesis_jet_pairing`, em `FiniteMultibaseMaterialJetTower.lean`, conserva todos os pares ordenados de câmeras e a ordem total do relógio logarítmico material. `materialCameraPairing_zero_eq_periodicGram_add_residue` mantém o resíduo de cutoff no Gram literal, sem apagá-lo no limite finito.
- **PASS existente:** `cameraMaterialJet_eq_seed_add_radiusSum`, em `FiniteMultibaseMaterialBracketTransport.lean`, é uma igualdade de vetores com a semente, todos os centros e raios naturais, inclusive o antipodal. C2 usa sua identidade separada de núcleo/profundidade.
- **PASS existente:** `nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource` e `_energy_eq_storage`, em `CompletedNativeChiralJetStorageTransport.lean`, identificam as duas pernas da síntese original e seu balanço assinado com o storage, com fator dois. Não inferem seu sinal.
- **PASS existente reutilizado:** `PhysicalSewing.originalMaterialCompletedSource`, `NativePhysicalEndpointEncoder`, `NativePhysicalFiniteSewing` e `NativePhysicalMaterialProducer` já produzem a fonte a partir dos átomos materiais positivos. O polinômio é construído do estêncil; o encoder deriva esse polinômio e recupera as duas pernas originais. Esses mapas não são definidos por uma Gram-alvo.
- **PASS existente reutilizado:** `NativePhysicalCameraCrossings` conserva os quatro setores e caudas; `NativeCompletedFiniteGreenResidual` e `NativePhysicalGreenResolvent` mantêm o numerador residual analítico e os traços no mesmo carrier Lp. Os novos canais Green/residual são estes operadores físicos; não são identificados automaticamente com o operador positivo global do GreenFrame.
- **CONDICIONAL / OPEN:** `NaimarkProjectorIntertwiningSeam`, em `FiniteEnrichedCameraNaimarkEscapeIntertwining.lean`, pede os dois quadrados J R=U* E e E V=U J. As consequências para projetor e escape estão provadas; a definição não fornece E/J físicos nem uma instanciação desses quadrados.
- **OPEN:** `canonicalCompletedNativeGreenMomentGramDefect`, em `CompletedNativeTfvdGreenMomentGramBridge.lean`, compara o kernel de momentos com o Gram Taylor do ledger completado. A equivalência de sua anulação com a representação e a identidade condicional com o residual de diferenças finitas não provam sua anulação. Não foram usadas para presumir positividade nesta rodada.

O incremento escolhido foi a alternativa explícita do objetivo: uma identidade universal dos bordos no mesmo carrier material, transportada à fonte original com todos os cruzamentos. O enunciado novo, suas testemunhas e os gates que continuam abertos estão no `REPORT.md`.
