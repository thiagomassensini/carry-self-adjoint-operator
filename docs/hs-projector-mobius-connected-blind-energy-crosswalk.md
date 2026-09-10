# HS/projector e Möbius connected: crosswalk de energia cega

Base desta rodada: `8009a3f074dd88ad2b647040bc40796e9cccf462`.
Branch: `agent/hs-projector-mobius-connected-blind-energy-crosswalk`.

Esta rodada mantém três níveis separados: (i) o Gram finito das câmeras, (ii) o
carrier de estados TFVD-valued e (iii) os carriers completed/Naimark. O módulo
novo fecha a álgebra finita do projetor e da energia rank-one; ele não afirma
um limite Naimark para a parte cega.

## Inventário das construções e dos índices

| objeto | domínio/codomain | índice | cutoff/métrica |
|---|---|---|---|
| `finiteLiteralCameraMatrix cutoff camera` | `Matrix camera state ℝ` | linha = câmera, coluna = estado do stencil | cutoff literal da câmera |
| `finiteCameraRowGram C` | `Matrix camera camera ℝ` | somente câmeras | `C Cᵀ` |
| `finiteCanonicalCameraReadout C` | `camera → state` | câmera/estado | `G⁻¹ᐟ² C`, se `G.PosDef` |
| `finiteCanonicalCameraSynthesis C` | `state → camera` | estado/câmera | `Cᵀ G⁻¹ᐟ²` |
| `finiteCanonicalCameraProjection C` | `Matrix state state ℝ` | estado | `V R` |
| `finiteCanonicalCameraBlindProjection C` | `Matrix state state ℝ` | estado | `I - V R` |
| `FiniteHilbertFamily camera H` | `PiLp 2 (fun _ => H)` | câmera externa | produto `ℓ²` finito |
| `finiteCanonicalCameraHilbertSynthesis C` | famílias camera-valued → state-valued | câmera externa; `H` interno | lift matricial, sem identificar índices |
| `CameraHilbert` | completion de `CameraFinsupp` | câmera Spectral-Weyl | Gram de `cameraVector` |
| `positiveInverseSqrt G` | matriz finita real | câmeras | CFC, sem continuidade matricial disponível |

O `cutoff` do Gram não é identificado com o cutoff do prefixo TFVD. O índice
externo de câmera também não é identificado com a coordenada vertical interna.

## Parte I: inverse square root

O novo teorema
`atlasNormalizedFiniteSixCameraRowGram_posSemidef` prova
que o Gram normalizado é `PosSemidef` para todo cutoff, incluindo cutoff zero.
A prova usa `finiteCameraRowGram = C Cᵀ` e a positividade do escalar
`(cutoff : ℝ)⁻¹` quando o cutoff é não nulo.

`atlasSixCameraPositiveInverseSqrt_continuousAt` prova a parte que é
disponível no pin: a inversão matricial é contínua em `CFC.sqrt sixCameraGram`.
Ela usa a positividade estrita de `sixCameraGram`, a unidade do determinante e
`continuousAt_matrix_inv`.

`atlasSixCameraWhiteningMatrix_tendsto_of_sqrt_tendsto` reduz o limite do
whitening ao único enunciado restante:

```
Tendsto (fun M => CFC.sqrt (atlasNormalizedFiniteSixCameraRowGram M))
  atTop (nhds (CFC.sqrt sixCameraGram))
```

Não foi declarado um `atlasSixCameraWhiteningMatrix_tendsto` incondicional.
`CFC.continuousOn_sqrt` no pin exige `NonUnitalNormedRing`/`CompleteSpace` para
o tipo da matriz, e `Matrix (Fin 6) (Fin 6) ℝ` não possui essa instância. Criar
uma norma matricial ou um cálculo funcional novo seria uma alteração de
infraestrutura, não uma consequência do código atual.

Como consequência, também permanece condicional
`atlasSixCameraWhitenedHilbertEmbedding_inner_tendsto_of_sqrt_tendsto`.
Quando a hipótese de raiz estiver disponível, ele combina o whitening existente
com `positiveInverseSqrt_whitens` e entrega o pairing limite euclidiano.

**Status:** o limite foi reduzido a uma continuidade precisa; não há alegação
incondicional.

## Parte II: projetor e energia Hilbert--Schmidt finita

`rankOneMatrix x` é a matriz `Matrix.vecMulVec x x`. Foram provados:

* `rankOneMatrix_transpose`;
* `rankOneMatrix_mul_self`, isto é,
  `Q_x² = (x ⬝ᵥ x) • Q_x`;
* `rankOneMatrix_mul_self_of_dotProduct_eq_one`, a versão idempotente para
  estado unitário.

Definimos as escalarizações finitas reais

```
projectorVisibleEnergy P x := trace (P * rankOneMatrix x)
projectorBlindEnergy P x   := trace ((1 - P) * rankOneMatrix x)
```

A identidade
`trace_projection_rankOne_eq_norm_sq` vale para qualquer matriz simétrica e
idempotente. Dela seguem:

```
projectorVisibleEnergy_eq_norm_sq
projectorBlindEnergy_eq_norm_sq
```

com as formas quadráticas `‖P x‖²` e `‖(1-P)x‖²` (escritas como dot products).
A linearidade do traço dá
`projector_energies_add_eq_norm_sq`, sem introduzir uma métrica adicional.

Para uma câmera finita com `finiteCameraRowGram C).PosDef`, foram especializados:

```
finiteCanonicalCameraVisibleEnergy_eq_readout_norm_sq
finiteCanonicalCameraBlindEnergy_eq_blind_norm_sq
finiteCanonicalCameraVisibleBlindEnergy_add_eq_state_norm_sq
```

O primeiro usa `finiteCanonicalCameraProjection_eq_transpose_mul`,
`finiteCanonicalCameraReadout_mul_transpose` e a coisometria existente. O
segundo usa exatamente `finiteCanonicalCameraBlindProjection`; não elimina o
setor cego. O terceiro é a forma escalar da identidade
`finiteCanonicalEnrichedCamera_parseval`.

A álgebra H-valued já existente em
`MultibaseTfvdCameraGramHilbertTransport` foi reutilizada sem duplicação:
`finiteHilbertMatrixSynthesis_inner_gram`,
`finiteCameraHilbertRawSynthesis_inner`,
`finiteCanonicalCameraHilbertSynthesis_isometry`,
`finiteCanonicalCameraHilbertReadout_synthesis`,
`finiteCanonicalEnrichedCameraHilbert_parseval` e
`finiteHilbertMatrixSynthesis_map_linearMap_commutes`. Esta rodada não precisou
introduzir tensor products nem uma classe geral de operadores trace-class.

### Relação com a rota HS histórica

A formulação histórica `G = C C*`, `C₀ = G⁻¹ᐟ² C`,
`P = C₀* C₀` é exatamente a álgebra finita acima após a especialização real
(`*` vira transposta). A matriz rank-one é usada somente em dimensão finita;
nenhuma afirmação sobre `Xi`, Pick/Herglotz ou um operador HS infinito foi
adicionada.

## Parte III: inventário Möbius/connected

O repositório atual não possui um módulo de `Möbius connected tail` com o
carrier de funções de cauda e a Gram integral descritos nas notas. O que está
pinado e foi auditado é:

| afirmação | API encontrada | status |
|---|---|---|
| inversão aritmética Möbius/log-derivative | `CPFormal.Analytic.CpNativeCarryMobiusLogDerivativeGuardrail`: `integerLog_mul_moebius_eq_primePowerSignal`, `primePowerSignal_mul_zeta_eq_integerLog` e roundtrips associados | Lean no grafo atual |
| cumulante connected C2 em entradas coprimas | `CPFormal.Analytic.CpNativeGpreConnectedC2Guard.nativeGpreJordanPairConnectedCumulant_eq_zero_of_coprime` e `..._distinct_primes` | Lean no grafo atual |
| impossibilidade de readout linear de um produto connected | `...CpNativeGpreConnectedC2Guard.no_linear_pair_readout_realizes_connected_product` | Lean no grafo atual |
| lift Jordan/Möbius divisor-resolvido | `CpNativeGpreTowerLift`, `CpNativeGpreTowerNorm` e teoremas de somas de divisores listados na referência da teoria | Lean no grafo atual, mas é uma torre material/Gpre distinta |
| célula/log-jet connected C2 | `CpC2DirichletJetGpre`, `CpC2LogJetGpreLift` | Lean no grafo atual, com normalizações e defeitos próprios |
| Gram positivo de caudas connected, kernel exatamente setor primo, Hardy-tail integral | notas `MOBIUS_LOG_CLOCK_CONNECTED_DRESSING_THEOREM.md` e `MOBIUS_WAVELET_ANCHORED_LOCALIZATION_GATE.md` | auditoria matemática/histórica; não é theorem importado aqui |
| precisão Brownian/log-Green tridiagonal | `MOBIUS_CONNECTED_BIRMAN_SCHWINGER_GATE.md` | nota matemática; nenhuma API Lean correspondente foi encontrada |

As notas históricas marcam como fechadas a conjugação Smith/Möbius, o transporte
para potências primas, a positividade do connected dressing e a descrição por
tails. Isso não foi promovido a theorem nesta branch: o pin atual fornece os
guardrails aritméticos e os lifts Gpre, mas não o carrier integral
`⊕_d L²([0,∞), φ(d)du)` nem sua identificação com o Gram connected.
Também não foi adicionada dependência ao repositório histórico Atlas Energy.

Não foi criado `FiniteConnectedTailCarrier`: fazê-lo exigiria primeiro fixar no
pin a definição de `f_r`, a medida/totiente e o crosswalk de coordenadas nativas.

## Blind camera, Naimark escape e connected dressing

As três formas permanecem semanticamente separadas:

```
B_M = I - V_M R_M                 (complemento do readout de câmera finita)
B_∞ = I - U U*                    (escape Naimark completed)
C_conn                             (forma Möbius connected das notas)
```

Os novos teoremas dão uma energia finita para `B_M` e uma decomposição exata
visible + blind. Eles não fornecem um mapa `ker R_M → ker U*`, uma convergência
da energia cega, nem uma igualdade/decomposição com `C_conn`. A energia `rho`
do Atlas Energy também não foi identificada com `projectorBlindEnergy`: ela é
transversal ao clock/tangente, portanto remove em geral uma direção diferente.

## Axiomas e validação

Os teoremas do módulo e do audit reportam somente
`propext`, `Classical.choice` e `Quot.sound` em `#print axioms`.
Não há `sorry`, `admit` ou axioma novo.

## Next Lossless Moment Gate

1. A continuidade matricial de `positiveInverseSqrt` foi reduzida à continuidade
   de `CFC.sqrt`; a versão incondicional está aberta.
2. `atlasNormalizedFiniteSixCameraRowGram` converge para `sixCameraGram`; o
   whitening converge condicionalmente à raiz.
3. `J_M` (o embedding whitened da rodada Atlas) tem pairing exato e é
   assintoticamente isométrico sob essa hipótese; não incondicionalmente.
4. A energia visible finita foi escrita como `Tr(P Q_x)`.
5. A energia blind finita foi escrita como `Tr((I-P) Q_x)`.
6. Ambas são normas quadradas e somam a energia total.
7. A identidade finita usada é o pairing de traço rank-one; não foi construída
   uma conjugação HS geral.
8. O transporte Green/Naimark não foi instanciado para o limite cego.
9. A convergência da energia cega para a energia de escape permanece aberta.
10. Um mapa vetorial `ker R_M → ker U*` ainda não é necessário para a identidade
    finita, mas continua ausente para um limite vetorial.
11. A aritmética Möbius/log e alguns lifts Gpre/C2 já estão no Lean atual.
12. Não foi construído o carrier connected-tail positivo.
13. Logo sua norma ainda não foi identificada com `C_conn`.
14. A forma por tails nativos está somente nas notas históricas.
15. `C_conn` não foi identificado com a energia cega de câmera.
16. Não há residual positivo formal comum aos dois objetos.
17. Não há theorem de convergência de energia cega nesta branch.
18. A precisão Brownian/log-Green não está formalizada no pin atual.
19. Há uma energia positiva canônica no nível finito (projetores e Parseval), mas
    não um carrier lossless completed para o setor cego.
20. Antes de comparar um Gram com `h_n`, o theorem mínimo é um crosswalk
    métrico/limitante que envie a família de estados completados para um
    carrier fixo e identifique o pairing; a continuidade de `CFC.sqrt` é o
    primeiro subgate técnico dessa rota.
