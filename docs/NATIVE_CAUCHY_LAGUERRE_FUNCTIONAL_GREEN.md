# Realização funcional Cauchy–Laguerre, relógio e Green

Data: 12/10/2026. Execução e certificação no servidor `llm`, por SSH, no repositório `/home/thlinux/carry-self-adjoint-operator`.

A rodada certificou **79 teoremas novos, 25 definições públicas e 2 instâncias**. Todas as 106 declarações têm auditoria `#print axioms`. O resultado central é funcional: avanço radial, relógio geométrico maximal auto-adjunto, inverso Green e compressões físicas foram construídos no Hilbert original. A completude Laguerre continua aberta.

## Entrada, proveniência e dependências

HEAD inicial após atualização por fast-forward: `9f801d4abb45e246a8d020d2b3af4f763b3d743c`, com os PRs #70, #71 e #72 já integrados. Eles foram reutilizados: Gram e features do #70; avanço por série e álgebra de compressão do #71; válvula, dois traços, síntese completada e resíduos do #72.

O prompt funcional `PROMPT_CODEX_LAGUERRE_FUNCIONAL_GREEN_2026-10-12.md` foi a instrução principal explicitamente adotada pelo usuário. A pesquisa consolidada foi usada como contexto matemático. Nenhuma afirmação da pesquisa foi promovida a teorema sem corpo de prova.

Lean `leanprover/lean4:v4.32.0`; Lake `5.0.0-src+8c9756b`. Os 16 pins abaixo foram conferidos contra os HEADs efetivos dos pacotes antes e depois do trabalho. Nenhuma dependência, métrica ou constante física foi ajustada.

| Pacote | Pin e HEAD efetivo |
|---|---|
| `geometry-of-numbers` | `d7cc54f5c485320f1fada33118e9e6101488819a` |
| `NativeCarryC3Crosswalk` | `150cfc7fb08da96bf8117f15869cc2b819d593c2` |
| `mathlib` | `81a5d257c8e410db227a6665ed08f64fea08e997` |
| `CarryGeometry` | `1f85b8c3ab5ded27a0782956e1ada0dd8a1b6fd4` |
| `NativeCarrySpectralWeyl` | `298d83c9351e308a5213b9f5ac32e44087f98a9f` |
| `CPFormal` | `65d50f6db1208708e109982ba97e1d51d3039956` |
| `plausible` | `e12c1910fe855cbfc38803cd4e55543906d5fa62` |
| `LeanSearchClient` | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` |
| `importGraph` | `7e9612bf0b9ee66db3cb5b9988a35afc706f5a12` |
| `proofwidgets` | `6e311e2a844da9b2cc3971187df2fe0066947b93` |
| `aesop` | `a7dbf0c63b694e47f425f3dcddbc0e178bb432d3` |
| `Qq` | `38d591e778f100aec9762bb582f9c7f55f50e9dc` |
| `batteries` | `023ce7d62a0531e22a5331e20b587817a80d49ff` |
| `FiniteNativeCarryOperator` | `00e9d6beb17226545abf5ddf90bbfede6c7146b0` |
| `GreenFrame` | `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa` |
| `Cli` | `88679d088c9720c27ebdf2ba4dafe17341747f94` |

Os arquivos não rastreados `C2OddTfvdTransport.lean` e `C2OddTfvdTransportAudit.lean` permaneceram intactos. SHA256, respectivamente: `5bfe06e8d15432c4d6cab6719dc22a0376019243f3e896329ea9ab9dd7458cb0` e `b6f05d0241058885da362b5cb20d3968d704a667da3ffc443714a69f3564623c`. Não foram criados novos worktrees nem repositório público.

## Dicionário de tipos

| Objeto | Construção efetivamente usada |
|---|---|
| `H` | `CanonicalCompletedNativeChiralCauchyCarrier`, isto é, `Lp ℂ 2 volume` sobre `unitInterval` |
| `λ_r` | `laguerreMode r`, classe mensurável `L_r(-log u)` em H; não uma função contínua no intervalo fechado |
| `φ_(k,j)` | `completedNativeRadialChiralCauchyState k j`, com meia-densidade `sqrt(u) u^j` e amplitude `sqrt(k+1)` |
| `M_u` | `physicalRadialAdvance : H →L[ℂ] H`, multiplicação pelo u original |
| `T` | `geometricLogClock : H →ₗ.[ℂ] H`, multiplicação maximal por `log u` |
| domínio de T | `geometricClockDomain = {h : H | MemLp ((log u) h) 2 volume}` |
| `R_q` | `physicalGreenResolvent`, multiplicação por `(1-q u)^(-1)`; `0 ≤ q < 1` |
| `G_q` | `physicalGreenOperator = q M_u R_q²`, no H original |
| duas pernas | `CanonicalCompletedNativeProjectiveChiralCarrier = H × H`, canais retidos separadamente |
| fonte completada | `physicalCompletedFiniteSource k x`, literalmente a combinação `Finsupp` dos estados completados originais |
| resíduo | `physicalCompletedFiniteResidual k x`, literalmente a combinação dos resíduos analíticos originais |
| `q` e `χ_(k,j)` | q TFVD é real; χ é o quociente Hermite–Biehler complexo, variável com o endereço; não são identificados |
| `P_R` | `laguerreFiniteProjection R`, projeção ortogonal sobre o span de `λ_0,…,λ_R`; sua construção não assume ortonormalidade all-order |

A densidade do domínio do relógio é uma prova independente. Ela não implica densidade do span Laguerre.

## Teoremas certificados e limites por gate

| Gate | Resultado desta rodada | O que continua OPEN |
|---|---|---|
| F1 | PASS para todos os momentos, construção de todos os modos e overlaps físicos em toda ordem; ortonormalidade nas ordens 0–2 | Ortonormalidade all-order |
| F2 | OPEN_LAGUERRE_COMPLETENESS | Densidade do span Laguerre, sobrejetividade e equivalência unitária global com ℓ² |
| F3 | PASS para operador físico limitado, auto-adjunto, positivo, `0 ≤ M_u ≤ I`, shift exato e soma funcional de momentos em toda ordem | Redução universal da matriz integral à fórmula binomial; a fórmula fechada foi provada nas ordens 0–2 |
| F4 | PASS para domínio maximal denso, auto-adjunção, fechamento, domínio de todos os modos e estados nativos; Jacobi 0–2 | Jacobi all-order e OPEN_FUNCTIONAL_CALCULUS; transporte entre câmeras além da identidade mensurável de escala |
| F5 | PASS para inversos, cota de norma, Green físico e reconstrução da fonte completada de suporte finito com dois traços e todos os resíduos | Extensão a dados infinitos sob hipóteses de convergência e regularidade; tradução por uma unitária Laguerre ainda inexistente |
| F6 | PASS para todos os cortes R: projeção física, vazamento positivo, válvula comprimida e entrada exterior | Fórmula racional fechada all-order de `M_u²` nas coordenadas Laguerre |
| F7 | PASS para duas entradas independentes e quatro setores após a reconstrução completa | Cota de cauda com constante π, limites co-finais uniformes, OPEN_TYPED_MATERIAL_RADIAL_MULTIBASE_SEWING e OPEN_ALL_ORDER_SIGNED_POSITIVITY |

Não houve novo NO_GO nesta rodada. Os defeitos multibase `59/54` e `-157/54` são registros anteriores do anexo, com convenções distintas; não foram reclassificados como impossibilidade geral nem como novos teoremas Lean.

- **F1 — [integral_logarithmic_moment](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeLaguerreLogMoments.lean#L43):** Para todo n natural e a > -1, prova a integral verdadeira `∫₀¹ u^a (-log u)^n = n!/(a+1)^(n+1)` e sua integrabilidade, por mudança de variável e Gamma.
- **F1 — [laguerreMode_first_three_orthonormal](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeLaguerreLpModes.lean#L83):** Ortonormalidade funcional das ordens 0, 1 e 2, no H original.
- **F1 — [laguerreMode_feature](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeLaguerreLpModes.lean#L130):** Para todo r,j, o overlap com a meia-densidade é a feature já certificada no #70. A amplitude física é mantida exatamente uma vez por [laguerreMode_radial_state](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeLaguerreLpModes.lean#L150).
- **F3 — [physicalRadialAdvance_feature](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeIntervalMultiplier.lean#L74):** Avança a coluna física por um endereço. [physicalRadialAdvance_isSelfAdjoint](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeIntervalMultiplier.lean#L167), [physicalRadialAdvance_norm_le_one](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeIntervalMultiplier.lean#L172), [physicalRadialAdvance_isPositive](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeIntervalMultiplier.lean#L180) e [physicalRadialAdvance_complement_isPositive](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeIntervalMultiplier.lean#L186) certificam as propriedades do operador original.
- **F3 — [physicalRadialAdvance_matrix_moment_sum](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeIntervalMultiplier.lean#L216):** Identifica todas as entradas funcionais como somas finitas exatas de momentos Gamma. [physicalRadialAdvance_first_three_matrix](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeIntervalMultiplier.lean#L233) certifica a forma binomial no bloco 0–2. A identidade fechada universal exige ainda uma prova combinatória; não foi inferida de entradas finitas.
- **F4 — [geometricLogClock_adjoint_eq](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeGeometricLogClock.lean#L219):** Identifica o adjunto com o operador maximal original, usando o regularizador M_u e o multiplicador contínuo u log u. Daí [geometricLogClock_isSelfAdjoint](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeGeometricLogClock.lean#L224) e [geometricLogClock_isClosed](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeGeometricLogClock.lean#L228). Não depende de completude Laguerre.
- **F4 — [laguerreMode_mem_geometricClockDomain](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeGeometricLogClock.lean#L244):** Todos os modos pertencem ao domínio. [completedNativeRadialChiralCauchyState_mem_geometricClockDomain](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeGeometricLogClock.lean#L334) conserva os estados nativos com amplitude; [geometricLogClock_laguerre_expansion](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeGeometricLogClock.lean#L264) dá a ação exata no núcleo em toda ordem.
- **F4 — [geometricLogClock_first_three_Jacobi](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeGeometricLogClock.lean#L292):** Linhas Jacobi 0–2 como igualdades de vetores. [geometricClock_exp_canary](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeGeometricLogClock.lean#L301) prova `exp(log u)=u` a.e.; não é declarado um teorema de cálculo funcional de operadores. [weyl_literal_log_coordinate_shift](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativeGeometricLogClock.lean#L341) mantém a constante literal 1 e log ell do Weyl.
- **F5 — [physicalGreenResolvent_left_inverse](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativePhysicalGreenResolvent.lean#L40):** Inverso esquerdo de I-qM_u; [physicalGreenResolvent_right_inverse](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativePhysicalGreenResolvent.lean#L53) prova o direito e [physicalGreenResolvent_norm_le](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativePhysicalGreenResolvent.lean#L65) a norma ≤ (1-q)^(-1). Os inversos existem no H inteiro para 0 ≤ q < 1.
- **F5 — [physicalGreenOperator_as_multiplier](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativePhysicalGreenResolvent.lean#L98):** Realiza q u/(1-q u)². [physicalGreenOperator_isPositive](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativePhysicalGreenResolvent.lean#L105) e [physicalGreenOperator_isSelfAdjoint](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativePhysicalGreenResolvent.lean#L119) pertencem ao operador Green no H original, sem implicação de positividade da forma assinada.
- **F5 — [physicalCompletedFiniteGreen_reconstruct](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativePhysicalGreenResolvent.lean#L201):** Para 0 < q < 1 e toda entrada Finsupp x, reconstrói o vetor completado original nas duas pernas. Reutiliza o numerador do #72 e o adaptador [continuousPairToSource_physical_advance](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativePhysicalGreenResolvent.lean#L136).
- **F6 — [physicalFiniteLeakage_eq_gram](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativePhysicalLaguerreCompression.lean#L49):** Para todo R, identifica E_R com B*B; [physicalFiniteLeakage_isPositive](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativePhysicalLaguerreCompression.lean#L68) prova positividade. Não pressupõe uma equivalência unitária global.
- **F6 — [physicalFinite_scaled_valve_compression](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativePhysicalLaguerreCompression.lean#L116):** Comprime a válvula inteira q^(-1)(I-qM_u)², com q ≠ 0, e conserva q E_R. [physicalFinite_valve_outside_input](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativePhysicalLaguerreCompression.lean#L126) retém explicitamente `P_R D_q (I-P_R) h` para toda entrada original h.
- **F7 — [physicalCompletedFiniteGreen_signed_pairing](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativePhysicalGreenResolvent.lean#L221):** Duas entradas independentes são reconstruídas antes do pairing original; a primeira é conjugada pela convenção do inner product.
- **F7 — [physicalCompletedFiniteGreen_four_sectors](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/94dabb94163e70dade825fc30b5b3e178ba92f16/CarrySelfAdjointOperator/NativePhysicalGreenResolvent.lean#L234):** Mantém principal–principal, principal–resíduo, resíduo–principal e resíduo–resíduo depois do inverso. Resíduo com autopairing nulo não apaga cruzamentos.

A fonte continua sendo a síntese completada original, com amplitude normalizada e quociente HB nativos. O numerador retém bulk, seed, `t₀`, `t₁`, `E b`, `E x`, `M_u E x` e `E Sx`. Nenhuma amplitude completada é invertida sem hipótese de regularidade. Não se aplica a positividade de M_u ou G_q à diferença assinada dos canais.

A cota de cauda não foi substituída por `D H D ≤ θ² H`. A identidade de cauda do #70 permanece válida; falta a prova formal da cota de operador de Hilbert `‖H_M‖ ≤ π` e das hipóteses uniformes de amplitude/quociente para limites co-finais. Isso é uma obrigação de prova aberta, não uma refutação matemática.

## Commits, PRs e validação

| Bloco | PR | Commits de implementação | Merge em main |
|---|---|---|---|
| F1 | [#73](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/73) | [`9e98933`](https://github.com/thiagomassensini/carry-self-adjoint-operator/commit/9e989338943cce9d918df687104d71377002a329) | [`ed58af5`](https://github.com/thiagomassensini/carry-self-adjoint-operator/commit/ed58af5b39df24d36358216284a380aeb47cc8c7) |
| F3 / F6 inicial | [#74](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/74) | [`1a8b7c8`](https://github.com/thiagomassensini/carry-self-adjoint-operator/commit/1a8b7c86a156f4c106c641a48030ef279e179616), [`8a9a342`](https://github.com/thiagomassensini/carry-self-adjoint-operator/commit/8a9a342b9c5b61175d56019b0dda13b7ee4089c6) | [`2002f30`](https://github.com/thiagomassensini/carry-self-adjoint-operator/commit/2002f3058927952d2e5249b66c99277783291949) |
| F4 | [#75](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/75) | [`4aaf4b4`](https://github.com/thiagomassensini/carry-self-adjoint-operator/commit/4aaf4b419dff3446f09fdf4d792dce888710ca5d) | [`a668b28`](https://github.com/thiagomassensini/carry-self-adjoint-operator/commit/a668b28b5cf52b0c4992e367de2de73ced1d3a07) |
| F5 / F7 | [#76](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/76) | [`0d1f281`](https://github.com/thiagomassensini/carry-self-adjoint-operator/commit/0d1f281e7775c5154141da1f308c47984c56c132), [`f335ff9`](https://github.com/thiagomassensini/carry-self-adjoint-operator/commit/f335ff9fef8ffbdff978c961a8c8024918770931) | [`d93ced6`](https://github.com/thiagomassensini/carry-self-adjoint-operator/commit/d93ced61f1a9bb4cd5b056e109885c48b9022eef) |
| F6 todo R / relatório | [#77](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/77) | [`94dabb9`](https://github.com/thiagomassensini/carry-self-adjoint-operator/commit/94dabb94163e70dade825fc30b5b3e178ba92f16) | Merge após a validação local e deste relatório |

Cada branch começou da main atualizada. Os merges #73–#76 foram seguidos por novo build completo da main antes do próximo PR. A API anterior do corte de três modos foi mantida como especialização R=2; seus resultados não foram repetidos como se fossem novidades independentes.

Comandos executados, sempre no llm e com o toolchain pinado:

```bash
PATH=/home/thlinux/.elan/bin:$PATH lake env lean CarrySelfAdjointOperator/<Modulo>.lean
PATH=/home/thlinux/.elan/bin:$PATH lake build CarrySelfAdjointOperator.<Modulo>Audit --wfail
PATH=/home/thlinux/.elan/bin:$PATH lake build --wfail
```

Na revisão final, as cinco auditorias foram construídas juntas e seus nomes comparados ao inventário das 106 declarações públicas. Resultado: **106/106**, sem `sorryAx` ou axiomas adicionais; somente `propext`, `Classical.choice`, `Quot.sound`. O inventário separa 79 teoremas, 25 definições e 2 instâncias. Declarações reproduzidas de dependências nos logs não são contadas como resultados novos.

Builds completos aprovados: F1 10115 jobs; F3 10116; F6 inicial 10117; F4 10118; F5/F7 e F6 em todo R 10119. Os módulos também passaram isoladamente. Não foram usados experimentos numéricos como prova nesta rodada.

Logs locais: `.lake/laguerre-functional-audit/`, incluindo `final-axioms.log`, `final-build.log`, `certified-declarations.json`, `pins.json` e `ci-status.json`.

O CI externo está bloqueado por pagamento, conforme informado pelo usuário. Foram inspecionadas execuções com `startup_failure` e `jobs=[]`, por exemplo [38290535010](https://github.com/thiagomassensini/carry-self-adjoint-operator/actions/runs/38290535010), [38291730918](https://github.com/thiagomassensini/carry-self-adjoint-operator/actions/runs/38291730918), [38292324024](https://github.com/thiagomassensini/carry-self-adjoint-operator/actions/runs/38292324024) e [38293182210](https://github.com/thiagomassensini/carry-self-adjoint-operator/actions/runs/38293182210). Zero jobs é inconclusivo: o certificado matemático apresentado é o Lean local no llm. Os merges foram autorizados expressamente nesse cenário.

## Próximas obrigações de prova

A próxima ponte analítica é provar a ortonormalidade all-order e a densidade Laguerre, em vez de presumir uma unitária. A matriz física já tem fórmula exata por momentos; falta reduzir essa soma ao binomial para quaisquer r,s. O relógio maximal é auto-adjunto, mas ainda faltam a recorrência Jacobi em toda ordem e uma passagem tipada ao cálculo funcional de exp.

Para as fronteiras físicas, faltam a cota de cauda π com controle uniforme de amplitudes/quotientes e o dicionário independente material–radial multibase. A positividade da forma assinada em toda ordem permanece uma questão separada. Nenhuma dessas etapas foi declarada concluída por Gram positivo, canário finito ou auto-adjunção do multiplicador radial.

## Atualização: Costura Finita Vetorial e Observável

A continuação de 12/10/2026 parte de `91b1c52372d74db8956607183766c042e204a796`, depois do PR #77. O gate de entrada finita no lift Cauchy de posições positivas recebeu um encoder independente por derivadas iteradas do polinômio material em u=1. `physicalEndpointJetInput_nativeSourceInput` prova U(Ev)=A*v por Taylor, sem usar uma inversa de U e sem exigir regularidade de A.

`originalMaterial_wholeSource_capstone` identifica o SourceJet, o lift literal do stencil material e q*R_q² aplicado a `physicalGreenBulkBoundary + physicalGreenResidualNumerator`, no mesmo par Lp original. `originalMaterial_observable_capstone` acrescenta a rota independente do estado TFVD completado e o critério fiel para qualquer segundo port candidato. Os coeficientes são extraídos do polinômio do `FormalStencil`; seed, centros e raios não são definidos pela resposta desejada.

O fechamento é FINITO nesse lift prescrito. As aplicações centro–pernas valem em qualquer distância; a câmera C2 alinhada mantém centros 4m, e as câmeras naturais mantêm os raios e seeds originais. A carta ambiente conserva os dois ports e reconstrói o par inteiro, inclusive o canal diagonal dos resíduos. A ação da completação nos jets foi derivada por diferenças progressivas. `CanonicalC3BracketTfvdCompletionState` continua sendo o domínio do produtor, com transport, valueTail e logJetTail.

O capstone de entrada/Green só exige 0<q<1. A interpretação regular da carta e a rota TFVD exigem F≠0, E+≠0 e cada parâmetro de altura na `genuineCriticalStrip`; 2*N<k+1 é uma condição suficiente para a strip na grade ORIGINAL. Os quocientes Xi, chart, valor TFVD e cabeça usam denominadores não nulos explícitos. Não se afirma essa regularidade para todo corte e todo k.

`mixedPhysicalProbes_faithful`, `mixedPhysicalProbes_decode` e `mixedPhysicalProbes_diagnostic` conservam o vetor do defeito antes do diagnóstico. `laguerreFirstMoments_injective` é de dimensão arbitrária. `mixedPhysicalProbes_headTail` e `twoPort_camera_defect_fourHeadTails` conservam as caudas e todos os pares de câmeras, com duas entradas independentes. As features finitas não foram identificadas com a projeção física P_R.

Continuam abertas a ortonormalidade e completude Laguerre em toda ordem, a isometria multibase universal, o entrelaçador Weyl→Cauchy, o suporte infinito, as cotas uniformes de cauda, o cálculo funcional completo e a positividade física assinada global. O mismatch Gamma/native de `NativeSourceLocusGreenCompatibility` e `NativeGreenInverseTraceSewing` não foi anulado. A TFVD de diferenças dos coeficientes radiais e o estado TFVD enriquecido da série continuam objetos distintos.

O inventário e o relatório específico estão em `audit/physical-finite-sewing-registry.json` e `docs/PHYSICAL_FINITE_OBSERVABLE_SEWING.md`. No llm, 11 módulos e suas auditorias passaram com `--wfail`; as 154 declarações públicas (115 teoremas e 39 definições) receberam `#check`, `#print axioms` e auditoria transitiva de tipos/corpos. O build raiz passou com 10.130 jobs e `scripts/audit.sh` terminou com `kernel audit passed`. Apenas os axiomas padrão `propext`, `Classical.choice` e `Quot.sound` aparecem; nenhum axioma adicional ou obrigação admitida foi introduzido. Logs e comandos efetivos estão registrados no relatório específico e no pacote de entrega.
