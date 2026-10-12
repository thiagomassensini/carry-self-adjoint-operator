# Carry / Cauchy–Laguerre–Green: relatório de formalização

Data: 2026-10-12. Execução: `ssh llm`, `/home/thlinux/carry-self-adjoint-operator`.
Instrução principal: `PROMPT_CODEX_CAUCHY_LAGUERRE_GREEN_2026-10-12.md` fornecido pelo
usuário. A pesquisa consolidada é especificação/registro experimental, não prova Lean.
Lidos integralmente núcleo 1–14, ap-08/ap-09, ap-29/ap-30; fontes primárias correntes
prevalecem sobre as transcrições históricas.

## Resultado

59 teoremas públicos novos, 26 definições públicas e 7 módulos de auditoria.
Todas essas 85 declarações públicas receberam `#print axioms`: somente
`propext`, `Classical.choice`, `Quot.sound`, ou subconjuntos desses axiomas padrão.
Também há um lema privado de normalização do somando do avanço.

Nenhum novo axioma, `sorry`, `admit`, `sorryAx`, repin ou ajuste de métrica.
Os resultados são finitos ou somas convergentes de features explicitamente indicadas.
Não há teorema de equivalência unitária Laguerre, positividade assinada all-order
ou costura física material–radial–multibase.

## Proveniência de entrada

* HEAD/base local e remoto: `b3bb99f83018781c6ca7296b50705dfcd6e6f1bd`, branch main.
* Lean/Lake: `leanprover/lean4:v4.32.0`; Lake `5.0.0-src+8c9756b`.
* Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
* Weyl: `298d83c9351e308a5213b9f5ac32e44087f98a9f`.
* CPFormal: `65d50f6db1208708e109982ba97e1d51d3039956`.
* Todos os demais HEADs de `.lake/packages` conferidos contra o manifest, sem alteração.
* Nenhum AGENTS.md encontrado no projeto ou diretamente em `/home/thlinux`.
* Dois arquivos C2OddTfvdTransport não rastreados preexistentes preservados byte a byte;
  SHA-256 fonte `5bfe06e8d15432c4d6cab6719dc22a0376019243f3e896329ea9ab9dd7458cb0`,
  audit `b6f05d0241058885da362b5cb20d3968d704a667da3ffc443714a69f3564623c`.
* Nenhuma worktree criada/removida. As quatro worktrees preexistentes foram mantidas.

O dicionário de tipos e índices consta em
`docs/NATIVE_CAUCHY_LAGUERRE_EXACT_SEWING_GATE.md`: endereço material, coeficiente
TFVD, nó radial, malha k, distância d, ordem r, câmera b, cutoffs M/R, q real e h
complexo têm papéis distintos. Igualdade de cardinalidade não certifica um mapa físico.

## Tabela por gate

| Gate | Status efetivo | Certificado / menor obrigação restante |
|---|---|---|
| A | EXISTING_LEAN + PASS_LEAN parcial | Gram físico original, H=VᴴV+DHD, H positivo definido, cabeça/cauda PSD, momento polinomial e limite em índices fixos. Overlap integral Laguerre ainda OPEN. |
| B | PASS_LEAN | Pairing original com duas entradas, primeira conjugada, fator (k+1)/2, quociente original e duas caudas assinadas. Nenhuma afirmação de sinal da diferença. |
| C | EXISTING_LEAN + PASS_LEAN | Regra de três canais reutilizada; stencil completado para todo p,d, incluindo d=0, em ambas as pernas antes do readout. |
| D | PASS_LEAN parcial + OPEN | Matriz binomial simétrica e soma convergente A f(j)=f(j+1). Sua realização integral universal, ortonormalidade/completude e equivalência unitária continuam OPEN. |
| E | PASS_LEAN parcial + NO_GO | Linha Jacobi truncada com ordem omitida; canário -2/3; H₂L₂≠L₂H₂. Derivada analítica, domínio maximal do log e A=exp(J) ainda OPEN. |
| F | EXISTING_LEAN + PASS_LEAN parcial | Bulk finito literal, seed e dois traços distintos na válvula. Numerador Green vetorial transportado na fonte completada. Inversos/resolventes na torre Laguerre e cotas funcionais ainda OPEN. |
| G | PASS_LEAN em suporte finito; regularidade explícita para nulidade | C S=M_u C+E e válvula corrigida nos representantes originais; adapter exato ao Lp. Resíduo com pernas iguais e pairing nulo na seção regular; quatro setores cruzados conservados. Extensão infinita e transporte por U_Lag ainda OPEN. |
| H | PASS_LEAN parcial + PASS_NUMERIC_ONLY | Álgebra geral de compressão e fatoração PSD da fuga sob projeção/auto-adjunção explícitas; R=0 certificado no Lp físico. Fórmula universal integral de A² e aplicação à torre completa ainda OPEN. |
| limites | CONDITIONAL / OPEN | Cota de operador π(k+1)θ² ainda sem prova Lean nova; escolha cofinal condicionada a amplitude/quociente e ordem fixa de jet. Sem uniformidade irrestrita em M ou ordem crescente. |
| I | OPEN_TYPED_PHYSICAL_SEWING + NO_GO de candidatos | Falta o dicionário independente material/radial/multibase. Dois candidatos concretos falham racionalmente; isto não é uma impossibilidade de toda a teoria. |

## Teoremas e commits efetivamente certificados

Namespace A/B/D/E/H: `CarrySelfAdjointOperator.NativeLaguerre`.
Namespace C: `CarrySelfAdjointOperator.FirstEdgeSewing`.
Namespace F/G: `CarrySelfAdjointOperator.NativeCauchyPorts`.

| Commit de prova | Módulo em CarrySelfAdjointOperator/ | Principais declarações públicas |
|---|---|---|
| `19092ed` | NativeCompletedAllDistanceStencil.lean | `edge_telescope`, `completed_stencil_all_distance`, `completed_stencil_linear_transport` |
| `eda3951` | NativeCauchyLaguerreExactGram.lean | `feature_polynomial_moment`, `cauchyMatrix_eq_gram`, `cauchyMatrix_posDef`, `exact_gram_head_tail`, `head_posSemidef`, `tail_posSemidef`, `head_entry_tendsto_cauchy` |
| `b0947e7` | NativeCauchyLaguerreSignedPairing.lean | `head_matrixPairing`, `matrixPairing_head_tail`, `incident_inner_eq_matrixPairing`, `original_signed_pairing_head_tail` |
| `7e04520` | NativeLaguerreAdvanceMatrix.lean | `advanceEntry_symmetric`, `advanceEntry_nonneg`, `hasSum_advance_feature`, `tsum_advance_feature` |
| `dcbcdc5` | NativeLaguerreClockDefect.lean | `fullJacobiRow_eq_derivativeFormula`, `finite_clock_defect_entry`, `finite_clock_defect_seed`, `material_clock_commutator_entry`, `material_clock_does_not_commute` |
| `55c4a19` | NativeLaguerreFiniteCompression.lean | `compression_square`, `compression_polynomial`, `compression_scaled_polynomial`, `compressionLeakage_eq_gram`, `compressionLeakage_posSemidef`, `inner_intervalMonomialLp`, canários `compression_R0_*` |
| `daa89be` | NativeCompletedFiniteGreenResidual.lean | `finiteTfvdBulk_succ`, `finiteCoefficientValve_two_traces`, `completedFiniteSynthesis_shift`, `completedFiniteSynthesis_valve`, `completedFiniteGreen_corrected_numerator`, `completedFiniteSynthesis_to_original`, `completedFiniteResidual_to_original_channels`, `regular_finiteResidual_signed_pairing_zero`, `completed_residual_four_sectors` |

Commits de exportação/documentação dos lotes 1 e 2: `db1ac48`, `5706c5d`.
Exportação/documentação do lote 3: `713ce2b`; a revisão final do relatório
registra URLs e o CI observado sem alterar fontes Lean.
As declarações completas e respectivas linhas constam no arquivo JSON de auditoria
entregue junto ao relatório; os módulos `*Audit.lean` são os checks reproduzíveis.

## Precisões matemáticas do lote F/G

O input tem tipo `ℕ →₀ ℂ`, antes da amplitude. `completedFiniteSynthesis` é somente
a soma finita dos estados `NativeCauchyPorts.completedContinuousPair` preexistentes,
que já contêm amplitude original, quociente original e escala `sqrt(k+1)`.
`completedFiniteSynthesis_to_original` leva a soma ao estado físico
`canonicalCompletedNativeRadialProjectiveChiralState` no Lp original.

A convenção deste lote é de coeficientes zero-based. O mapa que exclui a posição
material zero exige tradução própria com seed adicional; não foi identificado
com esta convenção. O bulk satisfaz b0=0 e b_(j+1)=q⁻¹x_(j+2)-2x_(j+1)+qx_j. Os traços são
t0=x0 e t1=q⁻¹x1-x0. A identidade da válvula guarda t0 e t1-t0 nas duas posições
seed, além do bulk deslocado. A reconstrução corrigida é o numerador exato:
conserva E b, E x, E Sx e o avanço de E x. Não se postula o inverso de um operador.

`normalized_chiral_gap` é deduzido das definições reais da normalização e das
coordenadas HB, com F(z)≠0 e coordenada positiva≠0 explicitamente declarados.
Isso prova a igualdade das duas pernas do residual em cada par de nós regular,
e depois nas somas de suporte finito. B(E x,E y)=0 sob essas condições.
`completed_residual_four_sectors` conserva B(Cx,Ey) e B(Ex,Cy); eles não são anulados.

## Validação reproduzível e resultados

Todos os comandos foram executados no llm, no diretório do repositório, com
`PATH=/home/thlinux/.elan/bin:$PATH` (o SSH não interativo omite `.elan/bin`).

```sh
lake env lean CarrySelfAdjointOperator/<cada um dos 7 módulos novos>.lean
lake build --wfail CarrySelfAdjointOperator.<cada módulo Audit>
lake build --wfail
```

Todos os módulos passaram em execução isolada e nos targets. Builds completos:
lote 1 exit 0, 10109 jobs; lote 2 exit 0, 10112 jobs; lote 3 exit 0, 10113 jobs.
Os jobs incluem alvos/cache de dependências; não significam que todos foram recompilados.
`git diff --check` passou; busca de admitidos/axiomas nas novas fontes sem ocorrências.
Os logs de build/axiomas originais estão em `.lake/cauchy-laguerre-audit/` no host.

| Teste executado | Resultado e alcance |
|---|---|
| ap-14 `testar_gate_allorder.py` | 7144 canários racionais, exit 0: momentos, Grams/caudas, pairing, stencils e crosses multibase. |
| ap-29 `verificar_ponte_green_laguerre.py` | 1613 canários racionais, exit 0: avanço, quadrado, ortogonalidade finita, Jacobi, fuga, válvula e Green completado. |
| `scripts/check_native_laguerre_physical_sewing_canaries.py` | diagnóstico racional independente a partir do período 420, preservando todos os crosses; exit 0. |

Dimensões 2,4,6,8, cortes 0,1,3,7, distâncias 1,2,3 e ambas as pernas cobertas.
Amplitudes/quocientes dos pacotes são sintéticos. As 8757 checagens dos dois pacotes
nunca são promovidas a provas Lean de integral, limite ou sinal físico.

O canário R=0 foi também provado independentemente no Lp físico: A00=1/2,
(A²)00=1/3, E00=1/12. Com q=1/2, a válvula verdadeira é 7/6, a substituição
ingênua dá 9/8 e a diferença é 1/24. Os teoremas de PSD aqui dizem respeito
à fuga geométrica e ao Gram, não à forma quiral assinada.

## OPEN_TYPED_PHYSICAL_SEWING: tipos, falhas e próximo lema

Tipos encontrados no HEAD:

* `finiteWeightedSlopeGreenResponse_add_boundaryReturn` toma `coeff : Fin N → ℂ`
  e reconstrói `finiteSlopeCoefficientState coeff : CarryVerticalL2`, por Green e
  retorno ponderados. Seu domínio é o espaço de coeficientes slope.
* `sourceCoordinateInput n k` toma `FiniteRealSpectralHilbert (2*n)` e produz
  outro elemento desse mesmo tipo por `nativeSourceChiralJetInput`.
* `sourceCoordinatePair n k` toma esse input e produz
  `CanonicalCompletedNativeProjectiveChiralCarrier`, ou seja duas cópias do Lp
  Cauchy original, através das sínteses incidente/retornada.
* A nova síntese finita toma `ℕ →₀ ℂ`, antes da amplitude, e chega ao mesmo carrier
  por representantes contínuos. Ela não escolhe o endereço material dos coeficientes.
* O Weyl Naimark usa um carrier adicional com perfis/câmeras e Gram
  `min(ell_b,ell_c)m_bc`; não é a norma radial Cauchy.

Falta um mapa independente dos dados materiais reconstruídos, conservando
seed, dois traços, câmeras/endereço, amplitude e quociente, para o input radial
da fonte original. Falta provar a comutatividade desse transporte com a síntese
e com o pairing de dois inputs. Não se pressupõe esse mapa por nomes semelhantes.

Menores obstruções mantidas:

* `NativeCauchyPorts.geometricSeededPort_constant_no_go` e
  `constantSeed_input_first_coordinate_defect_ne_zero` já certificados: o gradiente
  de input constante perde o seed e não recupera o primeiro port literal.
* Perfil C2 em cada átomo nas posições 1,2,3: valores [1,0,1], transformando
  1-2u+u² em 1+u². Perfil C4: [1,2,1], dando 1-4u+u².
* Replicação literal do stencil inteiro: 2K00-3K01=59/54≠0.
* Perfil aplicado átomo a átomo: 2K00-3K01=-157/54≠0.

Os dois últimos resultados são canários racionais reexecutados, sem certificado
Lean novo. Refutam a igualdade por uma única escala nesses candidatos, não todos
os transportes enriquecidos. O próximo lema físico é derivar uma coluna radial
normalizada a partir de ports/seed/traços/completion independentes e comparar
duas colunas com o Gram original, antes de reivindicar costura ou sinal.

Próximos lemas analíticos: construir λ_r no Lp; provar integral dos overlaps e
ortonormalidade; provar densidade da família. Só depois construir U_Lag como
equivalência unitária, transportar o domínio maximal do log e os resolventes Green.

## PRs e CI

* [PR #70](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/70):
  A–C, base main, HEAD `db1ac4805b76b59495f74927092c9fc2e7055872`.
* [PR #71](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/71):
  avanço/relógio/compressão, base PR #70, HEAD
  `5706c5dc501447086b7a8cc06dc0521b6de82c35`.
* [PR #72](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/72):
  Green finito/residual e este relatório, base PR #71; commit de exportação
  auditado `713ce2bf7a37fc0456a84eb6b3afc19ba2b3c412`.

CI observado nos três commits de exportação dos PRs #70/#71/#72:
`startup_failure`, zero jobs. Runs de PR 38282396010 / 38283373250 /
38284065002, respectivamente. Isso é CI externo inconclusivo, não um resultado
de compilação Lean. O comprovante local registra o HEAD final publicado e o
CI observado após a revisão apenas documental deste relatório.

Nenhum merge automático. `main` local/remoto não recebeu estes commits, conforme
o prompt principal. As branches publicadas permanecem disponíveis para revisão.
