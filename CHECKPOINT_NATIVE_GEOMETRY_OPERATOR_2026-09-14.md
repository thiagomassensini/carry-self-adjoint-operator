# Checkpoint — geometria nativa até o operador de alturas

## O que foi fechado

O caminho formalizado agora pode ser lido na direção causal da construção:

`C2/carry -> bracket e TFVD -> cauda exata -> válvula/Green -> resposta causal + retorno de bordo -> energia nativa -> lei de bordo/shift -> Jacobi finita -> operador de alturas simétrico`.

O novo módulo `CarrySelfAdjointOperator/NaturalNativeGeometryOperatorAudit.lean`
adiciona a composição
`canonicalC2Geometry_native_sameGeometry_energy_to_height_operator_of_radialHerglotz`.
Ela começa na positividade Herglotz/Pick da válvula radial completada e na
não-degenerescência de incidência, constrói a dominância quiral estrita e
invoca o capstone fonte-direção.  A hipótese de entrada não é Gram, Cholesky,
Jacobi nem espectro ajustado.

## O que o capstone expõe antes do operador

- o readout de bracket/TFVD;
- a identidade exata de cauda sobre todos os centros;
- a soma resposta Green + retorno de bordo, que recompõe o estado gradiente;
- a identidade de energia como quadrado adjunto do readout nativo;
- a equação polarizada de coeficientes e a lei de primeira coluna/shift;
- somente depois disso, a seção de Jacobi e `nativeGeometryFiniteHeightOperator`.

## Gate que permanece honesto

O módulo não afirma que a positividade Herglotz de todas as ordens já foi
provada pela geometria. Ele identifica precisamente esse enunciado como o
gate material restante, junto da não-degenerescência nativa já isolada. A
equivalência formal usada é:

`radial chiral multiplier contractive <-> radial Herglotz/Pick positive`.

O resultado de duas pontas (`N = 2`) continua sendo apenas validação de baixa
ordem; não é promovido a positividade em todas as ordens.

## No-go preservado

O carrier bruto de câmera/projetivo e o jet Taylor complexo não são usados:
há resíduos exatos de ordem zero/primeira coluna e de translação. O carrier
correto conserva resposta causal e retorno de bordo no espaço Hilbert; a
normalização final é aplicada ao readout completado, não ao Gram bruto das
linhas da câmera.

## Checkpoint adicional — rotação Green antes de Hankel

Foi compilado no Lean o seam operatorial que faltava para tornar explícita a
interpretação geométrica da autoadjunção:

- `inner_canonicalCompletedC3RadialSymplecticRotation_left` prova que a
  rotação radial nativa é skew-adjunta;
- `inner_canonicalCompletedC3GlobalGreenOperator_left` prova o mesmo para o
  carrier global, que mantém separados o bloco radial resposta/retorno e o
  bloco archimedean/chart;
- `canonicalC2Geometry_native_globalGreenOperator_quarterTurn` prova
  simultaneamente a simetria da rotação `-iT` no produto interno e
  `(-iT)^2 = I`.

Portanto a primeira autoadjunção que nasce da geometria é a involução
Hermitiana obtida da rotação simplética do Green. Ela aparece antes de
momentos, Hankel, Cholesky ou Jacobi. O operador de alturas finito continua
sendo a compressão positiva downstream dessa cadeia, não essa rotação
skew-adjunta em si.

Também foi compilado o capstone
`canonicalC2Geometry_native_green_operator_to_height`: sob o transporte
material corrigido da primeira coluna e o transporte injetivo de incidência,
ele expõe juntos a lei de coeficientes Green polarizados, a
`HasPolarizedCoefficientVectorEquation` do jet material e a existência da
seção de alturas finita simétrica.

## Fronteira exata após este avanço

Não falta uma igualdade algébrica entre o Green e o operador. Essa parte agora
é exata no carrier operatorial. O único input material não descarregado é
`HasCorrectedNativeChiralBoundaryTransport` (equivalentemente,
`HasSameEdgeGreenToClockBoundaryTransport`): a igualdade vetor/coeficiente da
primeira coluna do atlas de relógio com o readout Green corrigido. A identidade
de cauda já está fechada e não é a obstrução. O transporte de incidência já
fornece a não-degenerescência; o gate restante é calibrar essa primeira coluna
sem substituir o carrier por um proxy positivo.

Verificação: módulo isolado e `lake build` completo passaram; os três novos
teoremas reportam apenas `[propext, Classical.choice, Quot.sound]`.

## Checkpoint adicional — seam radial direto até o operador

Foi adicionada e compilada a ponte
`canonicalC2Geometry_native_radial_boundary_to_height` em
`CarrySelfAdjointOperator/NaturalNativeGeometryOperatorAudit.lean`.

Ela começa no objeto geométrico correto, sem atlas finita:

`CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining`

e usa a equivalência já formalizada com
`CanonicalCompletedC3AsymptoticRadialGammaLedgerNoLeak`. Em seguida consome
o limite de não-colapso
`CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound` e instancia o
capstone `canonicalC2Geometry_native_source_valve_green_to_height_of_radialLedger`.

O resultado reúne, numa única conclusão source-direction:

- a identidade exata de cauda;
- a completion do readout da valva;
- a equação de coeficientes do Green polarizado;
- a positividade nativa de Stieltjes;
- a seção Jacobi/Hankel correspondente;
- a simetria do operador finito de alturas.

Isso fecha formalmente o seam radial como rota geométrica para o operador,
mas ainda preserva as duas premissas materiais no tipo. Não foi alegado que o
seam radial ou o limite uniforme já estejam provados incondicionalmente. O
atlas finita continua excluído pelo no-go de calibração; a rota correta agora
é o carrier Green/valva contínuo.

## Checkpoint adicional — nota C2/Mangoldt/Möbius/Green/Birman–Schwinger

Foi lida a nota
`/home/thlinux/Downloads/NOTA_CANONICA_C2_MANGOLDT_MOBIUS_GREEN_BIRMAN_SCHWINGER_2026-09-14.md`
(5439 linhas; SHA-256
`feed6f63195fa276486bb401186ba736b95af01c8af5c3b955c745b217e69de5`).
Ela ajuda a proveniência, mas não deve ser usada como prova externa dos gates
abertos: a própria nota distingue identidades algébricas, resultados
importados, numerics e estados infinitos ainda abertos.

### Conclusão que entra diretamente na rota nativa

O relógio `log n` não é um parâmetro escolhido depois. Ele é reconstruído
pelas incidências primas:

`sum_p v_p(n) * log p = log n`.

Isso já aparece no Lean atual como
`primeDepthLogLedger_eq_log`. Além disso, os teoremas
`finitePrimeDepthGeneratedLogSlopePrefixState_eq_completedTfvdLogJetPrefix`
e `finitePrimeDepthGeneratedC3HilbertPrefixState_eq_completedTfvd` mostram
que a apresentação por profundidades primas não cria outro carrier: ela é
exatamente o prefixo log/TFVD nativo já usado pelo Green.

Portanto a cadeia de proveniência fica mais precisa:

`C2 center/core -> prime-depth ledger -> native log slope -> completed TFVD
Hilbert prefix -> causal response + boundary return -> global Green quarter-turn
-> radial seam -> Stieltjes/Jacobi -> height operator`.

O arquivo `C2FiberDepthLogTransport.lean` acrescenta a distinção geométrica
importante: o log do centro é `depth * log 2 + prime-core ledger`, enquanto o
log da perna possui um defeito explícito de coordenada. Isso explica por que
o carrier centrado/Green pode ser invariável enquanto uma câmera individual
retém artefato de perna.

### O que a camada Möbius/Green realmente acrescenta

A nota dá uma fatoração aritmética paralela do defeito do atlas ímpar:

`Möbius(log-clock) = prime-power transport - positive connected dressing`.

O dressing é uma energia Hardy de caudas Möbius, com núcleo primo e
coercividade no setor composto em cada atlas finito. Isso é uma boa leitura
para a energia do complemento/defeito depois da ortogonalização, mas não é
automaticamente o mesmo objeto que `canonicalCompletedC3RadialGammaEvenGram`
ou que a Jacobi de alturas. A identificação entre esses dois carriers ainda
precisaria de um theorem de transporte; não foi inventada aqui.

O resultado Birman--Schwinger `lambda = 1` da nota é apenas uma reformulação
finita. A existência de um estado limite e a compactação Hardy uniforme
continuam abertas. Também foi preservado o no-go contra usar o autovalor
finite-section mais próximo de `1` como seletor de ramo.

### Consequência para os gates atuais

O material confirma que a cauda exata e o relógio aritmético já estão do lado
certo da prova. Ele não descarrega, por si só,
`CanonicalCompletedC3AsymptoticRadialTiltBoundaryIntertwining` nem o
`CanonicalCompletedC3RadialGammaUniformDeterminantLowerBound`.

Há, contudo, um certificado Lean intermediário relevante:
`canonicalFiniteNativeCausalGreenBoundaryGram_posDef`. Ele prova positividade
finita do carrier real de resposta causal + retorno de bordo usando apenas a
transformação TFVD nativa e independência dos jets, sem momento, espectro ou
proxy. O que ainda falta para virar o gate radial é a passagem uniforme desse
carrier finito ao limite radial e a identificação do readout com o seam
Gamma/valva.

## Checkpoint adicional — retorno positivo, no-go do carrier bruto e próximo seam

Este checkpoint registra a auditoria do seam seguinte sem apagar os
residuais anteriores.

### O que está fechado

O módulo
`CarrySelfAdjointOperator/CompletedNativeReturnMetricReadoutCrosswalk.lean`
formaliza a métrica de retorno

`clmReturnMetric = I + poisson† ∘L poisson`,

com a decomposição Parseval entre o setor externo e o bulk. Estão provados a
auto-adjunção, a positividade, a identidade de readout e a isometria do
retorno. Portanto existe uma realização nativa positiva antes de Hankel/Jacobi.

Também está fechada, antes de Gram, a equação escalar
`canonicalC2Geometry_nativeWronskianResponse_coefficientEquation_before_gram`
e a correspondente identidade de bordo/shift. Esta é a rota causal correta:
Green/TFVD/valva produzem o response e o deslocamento; o Gram só vem depois.

### O que foi descartado como carrier final

A métrica de retorno genérica não pode ser identificada com o momento
canônico. Os teoremas
`canonicalNativeReturnMetricCentralKernel_eq_gradient_energy`,
`canonicalNativeReturnMetricCentralDefect_pos`,
`canonicalNativeReturnMetricCentralKernel_gt_nativeMoment` e
`canonicalNativeReturnMetricCentralKernel_ne_nativeMoment` mostram que o
kernel central dessa métrica é energia Green de gradiente estritamente maior
que `h₀`. Logo ela é um carrier positivo válido, mas não é o carrier de
momentos; não se deve corrigir isso por uma constante.

O mesmo alerta vale para o kernel projectivo bruto, que satisfaz
`one_le_completedProjectiveHilbertKernel_diagonal` e
`completedProjectiveHilbertKernel_zero_ne_nativeMoment`, e para a resposta
BR2 causal literal: `br2C3SourceSolution_norm_ge_two_fifths` e
`canonicalBR2C3CausalResponseWithBoundary_nativeMassDefect_gt` dão o no-go de
massa no primeiro coeficiente. Esses objetos não devem ser usados como
substitutos positivos do carrier nativo corrigido.

### O que a positividade já fornece

O carrier four-corner/enriched-Taylor (`nativeGpreFourCorner` e suas versões
enriquecidas) e o carrier causal com retorno de bordo possuem Gram positivo e
independência finita. Isso é evidência nativa pré-Hankel real, mas ainda não
prova a igualdade com `h_{i+j}` e `h_{i+j+1}`.

O transporte de incidência também já está disponível na família
`canonicalBR2CameraBracketCausalGreenResponseIncidenceJetTransport`; portanto
o lado da independência não é o gargalo atual. O alvo tipado continua sendo a
hipótese de
`nativeGeometry_to_finiteHeight_chain_of_greenMomentKernel_and_incidenceTransport`:

`IsGreenWronskianMomentKernelGramRepresentation
  canonicalCompletedNativeLogDerivativeMoment jet`.

### Gate restante e regra de preservação

O que falta é a identificação do readout/energia corrigido da valva com o
kernel Green polarizado, não uma nova prova de positividade. Os residuais que
devem continuar nomeados são
`canonicalCompletedNativeGreenMomentGramDefect`,
`canonicalNativePolarizedTfvdGreenMomentKernelDefect` e
`canonicalCompletedC3NativeSourceLocusProjectionMismatch`, conforme o carrier
escolhido. A rota de fechamento é provar o transporte chiral/corrigido
(`HasCorrectedNativeChiralBoundaryTransport` ou a costura
`CanonicalCompletedC3BoundaryGreenSewing`) ou, na rota radial, as hipóteses
explícitas de boundary e strictness. Só depois disso se instancia o certificado
de momentos, a independência incidencial, Stieltjes/Jacobi e o operador de
alturas.

Regra deste checkpoint: manter a ordem

`native geometry -> Green/TFVD/valva -> response/shift -> carrier corrigido
positivo -> kernel de momentos -> incidência -> Jacobi -> altura`,

sem definir o carrier nativo a partir de `K`, `J` ou de uma fatoração positiva
genérica.
