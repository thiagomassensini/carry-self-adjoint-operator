# Enriched moving-camera / completed Naimark crosswalk

Base formal da rodada: 90bae45f623298ad80dfaf68f3f0e1aabc1f06e0.

A branch foi criada sem alterar as definicoes upstream. Este documento separa os
carriers e os cutoffs; nao identifica indices naturais com significados
diferentes.

## Inventario de tipos

| objeto | dominio/codominio | indice de camera | indice de estado/profundidade | cutoff | metrica |
|---|---|---|---|---|---|
| finiteLiteralCameraMatrix C | Matrix camera state R | linha camera | coluna state | cutoff dos coeficientes da camera | produto matricial real |
| finiteCanonicalCameraReadout C | Matrix camera state R | linha camera | coluna state | mesmo cutoff da matriz | inverse square root do row Gram |
| finiteCanonicalCameraBlindProjection C | Matrix state state R | indireto via C | state | mesmo cutoff | complemento de R^T R |
| CameraFinsupp | CameraIndex ->₀ R | label supported camera | - | bound de labels | gramForm |
| CameraHilbert | completion de CameraFinsupp | label supported camera | - | completion global | inner product intrinseco Gram |
| NaimarkSpace | Lp KolmogorovSpace 2 positiveLebesgueMeasure | intervalos de camera | coordenada L2 | nenhum cutoff | L2 |
| CarryVerticalL2 | l2(N,R2)/complexificado | - | sample vertical | prefixo TFVD | inner product vertical |
| FiniteHilbertFamily camera H | PiLp 2 (fun _ => H) | indice externo | valor H intacto | finito | produto PiLp |
| canonicalCompletedC3HilbertState | carrier C3/TFVD completed | - | coordenadas Green/TFVD | prefixo | carrier completed |
| canonicalCompletedTfvdGreenPortState | FiniteC3GreenPortCarrier 3 | cameras packed no port | coordenadas do port | cutoff C3 | Green port |
| canonicalCompletedTfvdGreenCameraState | CarryGammaComplexCamera | seis cameras packed | quadraturas | completed | camera complexificada |
| canonicalCompletedTfvdGreenNaimarkState | CarryGammaComplexNaimark | realizacao Naimark | quadraturas | completed | Naimark complexificado |
| canonicalCompletedTfvdGreenAllCutoffNaimarkState | RealifiedNaimarkComplexification | packing C3 | coordenadas Naimark | cutoff all-C3 | carrier global fixo |

O cutoff da camera, o prefixo TFVD, o cutoff C3 e o bound da completion de
cameras permanecem parametros diferentes. Nenhuma igualdade entre eles e
usada.

## Tres completions

### Camera Gram completion

CameraFinsupp, CameraHilbert, cameraEmbedding, finiteCameraInclusion e
dense_iUnion_range_finiteCameraInclusion ja constituem a completion
intrinseca do Gram all-bases. A inclusao finita preserva exatamente
gramForm; a uniao das imagens e densa.

### TFVD/Gpre projective completion

Os objetos nativeGpreTfvdProjectiveAnalysis,
nativeGpreTfvdProjectiveReconstruction,
nativeGpreTfvdProjectiveAnalysis_hasLeftInverse,
nativeGpreTfvdProjectiveAnalysis_injective e
nativeGpreTfvdProjectiveAnalysis_range_isClosed vivem em outro carrier.
As compatibilidades nativeGpreTfvdProjectiveAnalysis_finiteWeightedState_tendsto
e nativeGpreTfvdProjectiveAnalysis_completedState_compatible nao sao
identificacoes com CameraHilbert.

### C3/TFVD/Green/Naimark completion

canonicalCompletedTfvdGreenAllCutoffNaimarkState_tendsto fornece convergencia
em um carrier Naimark global fixo. Ela reutiliza a igualdade com o port
Green finite e nao e uma convergencia da matriz whitened finita.

## Resultados fechados nesta rodada

O novo modulo
CarrySelfAdjointOperator/EnrichedMovingCameraCompletedNaimarkCrosswalk.lean
define:

    finiteEnrichedMovingCameraTfvdState C X

com componentes

    (finiteCanonicalCameraHilbertReadout C X,
     finiteHilbertMatrixSynthesis
       (finiteCanonicalCameraBlindProjection C) X)

no tipo

    FiniteHilbertFamily camera CarryVerticalL2
      x FiniteHilbertFamily state CarryVerticalL2.

As provas novas sao wrappers tipados das APIs existentes:

- finiteEnrichedMovingCameraTfvdState_parseval: o pairing visivel mais o
- finiteEnrichedMovingCameraTfvdState_reconstruct: a sintese whitened mais o setor blind recompõem vetorialmente X, usando a identidade de projeção existente; a prova não identifica esse par finito com um carrier completed.
  pairing blind e exatamente o pairing do estado completo;
- finiteEnrichedMovingCameraTfvdState_raw_gram: a sintese literal raw
  induz a forma com finiteCameraRowGram;
- finiteEnrichedMovingCameraTfvdState_raw_single_channel: em dois canais
  externos, o pairing e finiteCameraRowGram C i j * inner x y;
- finiteEnrichedMovingCameraTfvdState_whitened_synthesis_isometry: a
  sintese V=C^T G^{-1/2} e isometrica quando o row Gram e PosDef;
- finiteEnrichedMovingCameraTfvdState_whitened_roundtrip: R V = I no carrier
  de familias H-valued;
- finiteEnrichedMovingCameraTfvdState_internal_map_commutes: qualquer mapa
  linear interno sobre CarryVerticalL2 comuta com o lift matricial externo.

O resultado de Naimark concreto e vetorial, ja existente e exposto com nomes
da rodada, e:

    canonicalCompletedC3NaimarkState_camera_roundtrip
    canonicalCompletedC3State_camera_readout_roundtrip

Eles sao consequencias de realifiedNaimarkAdjoint_canonicalCompletedC3NaimarkState
e canonicalCompletedC3GlobalCameraReadout_eq_source. Portanto a realizacao
C3 completed que e literalmente um realifiedNaimarkPort retorna exatamente
canonicalCompletedC3SixCameraSource.

Tambem foi exposta como corolario a convergencia ja provada:

    canonicalCompletedTfvdGreenAllCutoffNaimarkState_fixed_carrier_tendsto

Nao foi criada uma nova completion.

## Estado raw e whitening

O theorem de canal unico mostra precisamente onde o overlap raw aparece:
G_ij * inner(x,y). Assim, a decomposicao algebrica visible/blind nao e
declarada como ortogonalidade dos eixos raw. A ortogonalidade/isometria
disponivel e a dos modos produzidos pela sintese whitened
finiteCanonicalCameraHilbertSynthesis, sob a hipotese explicita
(finiteCameraRowGram C).PosDef.

O repositorio nao fornece nesta rodada um certificado incondicional de PosDef
para todo finiteLiteralCameraMatrix cutoff camera; por isso a hipotese nao foi
escondida nem inferida do limite sixCameraGram_posDef.

## Roundtrip Naimark e limite completed

O roundtrip concrete C3 fecha o canal camera de uma realizacao que ja esta no
range do port Naimark:

    realifiedNaimarkAdjoint
      (canonicalCompletedC3NaimarkState z)
    =
    canonicalCompletedC3SixCameraSource z.

A convergencia all-cutoff de TFVD/Green/Naimark tambem fecha em
RealifiedNaimarkComplexification, via
canonicalCompletedTfvdGreenAllCutoffNaimarkState_tendsto.

Nao ha no pin um theorem que identifique diretamente
canonicalCompletedTfvdGreenNaimarkState (carrier Gamma complexo) com o estado
realificado all-cutoff nem que aplique canonicalCameraStateReadout a ele sem
um mapa adicional. Essa diferenca de carrier foi mantida.

## Seam residual unico

O resultado minimo que ainda falta para a familia movel completa e um mapa
canonico, compativel entre cutoffs,

    finiteHilbertMatrixSynthesis
      (finiteCanonicalCameraBlindProjection C_M)
      X_M
        -> completed/projective provenance carrier

junto com um embedding para o carrier fixo que seja compativel com as
mudancas de Gram G_M^{-1/2}. Nenhuma API existente prova esse intertwiner
W_(M -> N), nem identifica o setor blind finito com Gpre, residual Green ou
provenance projective.

Em particular:

- o setor visible finito tem a descricao whitened e o roundtrip Naimark para
  estados que ja sao ports;
- o estado TFVD/Green completed tem convergencia forte em um carrier Naimark
  fixo;
- o blind/provenance moving state ainda nao tem um mapa tipado e
  cutoff-compatible para esse carrier.

Isso e uma obstrucao de transporte/cross-carrier, nao uma falha de Parseval e
nao pode ser resolvido por reescala, troca de fase ou remocao de coordenadas.

## Next Moving-State Gate

1. **CameraHilbert e a completion necessaria das cameras?** Sim, para o Gram
   all-bases intrinseco; nao substitui os carriers TFVD/Gpre ou C3.
2. **Qual objeto representa o limite coordinate-free de R_M?** O candidato
   existente e o adjunto realifiedNaimarkAdjoint no carrier Naimark, enquanto
   a restricao finita e finiteCameraInclusion; falta o theorem que identifica
   os whitenings finitos com essa restricao.
3. **canonicalCameraStateReadout recupera o completed camera state?** Sim,
   quando a realizacao e realifiedNaimarkPort o q; o C3 concreto satisfaz
   isso por canonicalCompletedC3NaimarkState_eq_realifiedNaimarkPort.
4. **Realizacao Naimark concreta:** c3SixCameraNaimarkRealization para o
   estado C3 e finiteC3SymplecticNaimarkRealization para os prefixos
   all-cutoff.
5. **Visible fechado?** Para o C3 em range do port, sim; para uma familia
   whitened movel arbitraria, a algebra finita esta fechada, mas falta a
   identificacao com o limite CameraHilbert.
6. **Blind fechado?** Parseval finite esta fechado; o transporte do blind
   para proveniencia completed nao esta.
7. **B_M corresponde a Gpre/residual/ambos?** Nenhuma identificacao foi
   provada.
8. **Mapa finite blind -> projective provenance?** Nao encontrado.
9. **Familia (R_M X_M,B_M X_M) em carrier fixo?** Ainda nao; o par finito foi
   construido, mas seu segundo componente muda de carrier e o whitening
   depende de G_M.
10. **Existe W_M_to_N?** Nenhum mapa canonico existente foi encontrado.
11. **Por que nao?** Inclusoes de cameras preservam o Gram intrinseco, mas
   finiteCanonicalCameraReadout C_M usa o inverse square root de cada row
   Gram finito; nao ha compatibilidade provada entre esses dois objetos.
12. **Strong convergence TFVD ajuda?** Sim, para o estado Naimark/Green
   all-cutoff ja existente; nao fornece o blind embedding.
13. **Compatibilidade Gpre ajuda?** Sim, apenas dentro do carrier Gpre; falta
   o envio do blind finite.
14. **Atlas all-bases do green-frame ajuda?** Fornece uma isometria alternativa
   para o core camera, mas nenhum theorem o identifica com B_M X_M.
15. **Unico theorem minimo seguinte:** um intertwiner cutoff-compatible para
   o setor blind/provenance (incluindo o embedding no carrier fixed).
16. **Distancia ate moment Gram/HP:** depois desse intertwiner, ainda seria
   necessario comparar a metrica do estado completo com o moment/HP carrier;
   esta rodada nao afirma qualquer igualdade de camera Gram com Hankel.

## Axiomas

O audit novo imprime os teoremas principais. O build reporta apenas o conjunto
padrao ja aceito pelo projeto:

    propext
    Classical.choice
    Quot.sound

Nenhum sorry, admit ou axioma novo foi adicionado.
