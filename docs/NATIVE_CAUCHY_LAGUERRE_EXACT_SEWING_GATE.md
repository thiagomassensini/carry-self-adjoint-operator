# Gram Cauchy, pairing assinado e stencil completado — lote 1

Data: 2026-10-12. Host: `ssh llm`, `/home/thlinux/carry-self-adjoint-operator`.
Base: `b3bb99f83018781c6ca7296b50705dfcd6e6f1bd`. Os dois arquivos C2OddTfvdTransport
não rastreados preexistentes foram preservados e não integram este PR.

## Dicionário de tipos

| Papel | Tipo/índice efetivo | Distinção |
|---|---|---|
| endereço material n | ℕ; cortes em `FiniteRealSpectralHilbert N` | `log(n+1)` pertence ao relógio material |
| coeficiente TFVD j | ℕ → ℂ ou suporte finito | a identificação física com o endereço radial é uma obrigação própria |
| nó radial j | ℕ; `Fin M` no prefixo Cauchy | `completedNativeChiralCauchyFeature j` |
| malha k | ℕ | escala `sqrt(k+1)` do estado radial |
| distância d | ℕ | a telescopia também inclui d=0 |
| ordem Laguerre r | ℕ; `Fin (R+1)` | R é a maior ordem conservada |
| câmera b | ℕ, com condições originais de admissibilidade | outro Gram: `m_bc min(ell_b,ell_c)` |
| cutoff material M | ℕ | não determina R nem a malha |
| parâmetro vertical q | ℝ com `0<q<1` nas reconstruções existentes | não é o quociente quiral χ |
| passo h | ℂ, passo radial original | não é um relógio material |

## Resultados novos e alcance

`NativeCauchyLaguerreExactGram.lean` trabalha com `rho=(2j+1)/(2j+3)` e
`feature=2 rho^r/(2j+3)`, provando sua igualdade com as fórmulas originais.

* `feature_polynomial_moment`: soma binomial finita exata; não afirma uma integral.
* `cauchyMatrix_eq_gram`, `cauchyMatrix_posDef`: Gram do Lp original e positividade
  definida, por injetividade da síntese incidente já certificada.
* `exact_gram_head_tail`: `H=Vᴴ V+D H D`, para todo M,R, inclusive M=0.
* `head_posSemidef`, `tail_posSemidef`: positividade geométrica de cada parcela.
* `tail_entry_tendsto_zero`, `head_entry_tendsto_cauchy`: limites em índices fixos;
  nenhuma uniformidade em M crescente.

`NativeCauchyLaguerreSignedPairing.lean` reutiliza literalmente
`ChiralReturn.radialIncidentSynthesis`, `radialReturnedSynthesis` e
`canonicalCompletedNativeProjectiveChiralForm`.

* `incident_inner_eq_matrixPairing`: transporte até o pairing físico existente.
* `original_signed_pairing_head_tail`: duas entradas independentes, primeira
  entrada conjugada, fator `(k+1)/2` e diferença de duas caudas DHD.
* `returnedCoefficients` aplica somente o quociente original. A amplitude já
  incorporada em `nativeSourceChiralJetInput` não é reaplicada.

`NativeCompletedAllDistanceStencil.lean` reutiliza o estado original
`canonicalCompletedNativeRadialProjectiveChiralState` e a regra já certificada
`FirstEdgeSewing.radialProjectiveEdge_eq_threeChannels`.

* `edge_telescope`: telescopia em qualquer grupo abeliano.
* `completed_stencil_all_distance`: segunda diferença completada, para todo p,d,
  com os três canais e as duas pernas antes de qualquer pairing.
* `completed_stencil_linear_transport`: transporte por qualquer mapa linear já
  tipado; não fabrica um mapa físico material/radial.

## Validação

Lean: `leanprover/lean4:v4.32.0`. Pins inalterados e HEADs instalados conferidos:
Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, Weyl
`298d83c9351e308a5213b9f5ac32e44087f98a9f`, CPFormal
`65d50f6db1208708e109982ba97e1d51d3039956`. Nenhum AGENTS.md encontrado na árvore
do projeto ou diretamente em `/home/thlinux`.

Comandos executados no host, com `PATH=/home/thlinux/.elan/bin:$PATH`:

```sh
lake env lean CarrySelfAdjointOperator/NativeCauchyLaguerreExactGram.lean
lake env lean CarrySelfAdjointOperator/NativeCauchyLaguerreSignedPairing.lean
lake env lean CarrySelfAdjointOperator/NativeCompletedAllDistanceStencil.lean
lake build --wfail CarrySelfAdjointOperator.NativeCauchyLaguerreExactGramAudit
lake build --wfail CarrySelfAdjointOperator.NativeCauchyLaguerreSignedPairingAudit
lake build --wfail CarrySelfAdjointOperator.NativeCompletedAllDistanceStencilAudit
lake build --wfail
```

Os módulos Audit contêm `#print axioms` de todas as novas declarações públicas:
somente os axiomas padrão `propext`, `Classical.choice`, `Quot.sound` (ou subconjuntos).
Nenhum `sorry`, `admit`, `sorryAx` ou novo axioma. Logs brutos ficam em
`.lake/cauchy-laguerre-audit/` no host; o build completo passou com exit 0 (10109 jobs). O CI é registrado
separadamente no PR e no relatório all-order.

O script recebido `testar_gate_allorder.py` foi extraído do ap-14 e executado no llm:
7144 canários exatos PASS, incluindo dimensões 2,4,6,8, cortes 0,1,3,7 e distâncias
1,2,3 nas duas pernas. Os coeficientes de amplitude/quociente são sintéticos;
estes testes não certificam sinal físico. A certificação universal vem dos teoremas.

## Obrigações abertas

`OPEN_LAGUERRE_COMPLETENESS`: ainda não há neste lote família Laguerre no Lp,
ortonormalidade integral ou prova de densidade/sobrejetividade. Nenhuma equivalência
unitária foi declarada.

`OPEN_TYPED_PHYSICAL_SEWING`: falta um mapa independente dos coeficientes slope
de `finiteWeightedSlopeGreenResponse_add_boundaryReturn`, com seed e traços, para
os inputs radiais da fonte completada. Igualdade da cardinalidade de dois `Fin N`
não é esse mapa. `NativeCauchyPorts.geometricSeededPort_constant_no_go` e o defeito
literal `constantSeed_input_first_coordinate_defect_ne_zero` já expõem a perda do
seed no candidato baseado somente no gradiente.

`OPEN_ALL_ORDER_SIGNED_POSITIVITY`: nenhuma conclusão de positividade da diferença
quiral. A cauda geométrica, o residual analítico e o retorno TFVD são canais distintos.

PR para revisão, sem merge automático. `main` permanece no commit base.
