# Dicionário físico Cauchy–Laguerre e transporte do passo

Data: 2026-10-13. Base: `46f98fe3a37ce21bb7015af15285be5b061b5031` (PR #82).
Host de execução: `llm`. Toolchain: Lean `v4.32.0`.

## Resultado e domínio

Foi recuperada a worktree `carry-cauchy-laguerre-isometry`, criada pela execução interrompida. Os arquivos `NativeCauchyLaguerreColumns.lean` e `NativeCauchyLaguerreIsometry.lean` estavam salvos. O primeiro já compilava; o segundo ainda tinha erros na aplicação de `Finsupp.range_linearCombination` e na resolução da instância de completude do fecho. A retomada corrigiu esses pontos e completou o dicionário e suas aplicações.

O carrier físico permanece `Lp ℂ 2 volume` no intervalo unitário. O domínio é

$$
\mathcal H_{\rm phys}=\overline{\operatorname{span}\{\psi_j:j\in\mathbb N\}},
\qquad \psi_j(u)=\sqrt u\,u^j.
$$

`physicalCauchyClosure` é um submódulo fechado desse carrier, com sua norma induzida. A construção mantém literalmente

$$
\rho_j=\frac{2j+1}{2j+3},\qquad
f_r(j)=\frac{2\rho_j^r}{2j+3},\qquad
v_j=(f_r(j))_{r\ge0}\in\ell^2(\mathbb N;\mathbb C).
$$

`feature_product_hasSum` usa o limite de cabeça + cauda já certificado, após demonstrar somabilidade geométrica. `inner_laguerreColumn` e `laguerreColumn_physicalGram` identificam o Gram exato. Para dois suportes finitos independentes, `laguerreColumnSynthesis_inner` preserva todos os cruzamentos ordenados.

`LinearMap.extendOfNorm` estende a síntese das colunas ao fecho físico a partir da igualdade de normas no núcleo denso. A entrada é produzida pela síntese física original, sem uma inversa ou normalização Parseval. Não há novos pesos nem mudança de métrica.

Os certificados centrais são

$$
\mathcal U:\mathcal H_{\rm phys}\longrightarrow\ell^2(\mathbb N;\mathbb C),
\qquad \mathcal U\psi_j=v_j,
\qquad (\mathcal Ux)_r=\langle L_r(-\log u),x\rangle.
$$

Nomes: `cauchyLaguerreIsometry`, `cauchyLaguerreIsometry_feature`, `cauchyLaguerreIsometry_coordinate`, `cauchyLaguerreIsometry_inner`, `cauchyLaguerreIsometry_range_isClosed`.

Não se afirma que esse fecho é todo L² ou que o range é todo ℓ². Completude Laguerre em todo L² permanece uma obrigação separada.

## Inventário aplicado de infraestrutura existente

| Resultado anterior | Tipos e hipóteses efetivos | Aplicação nesta construção |
| --- | --- | --- |
| `inner_completedNativeChiralCauchyFeature` | Duas meias densidades no L² físico | `laguerreColumn_physicalGram` conserva o Gram literal. |
| `cauchy_head_tail_orders`, `exact_gram_head_tail`, `head_entry_tendsto_cauchy` | Índices naturais, corte arbitrário, Gram Cauchy | Determinam a soma infinita de produtos das features; nenhuma cauda é ajustada. |
| `laguerreMode_feature` | Todo `r,j`; modo funcional no mesmo L² | A igualdade de coordenadas é estendida por continuidade a todo o fecho. |
| `laguerreMode_radial_state` | Amplitude física `sqrt(k+1)` | `cauchyLaguerreIsometry_radial` mantém essa amplitude exatamente uma vez. |
| `radialIncidentSynthesis_injective` | Qualquer dimensão finita e profundidade natural | `physicalFiniteSynthesis_injective` reutiliza a especialização `k=0`, para certificar a obstrução da cabeça curta. |
| `carryVerticalL2BackwardShift n` | `ℓ²(ℕ,ℂ) →L[ℂ] ℓ²(ℕ,ℂ)`; remove `n` coordenadas | `backwardShift_laguerreColumn` identifica a ação diagonal das colunas originais. |
| `carryVerticalL2BackwardShiftLinear_norm_le` | Contração em todo o alvo ℓ² | Fornece a cota para estender o passo diagonal físico ao fecho. |
| `l2CoordinateMaskCLM`, idempotência e autoadjunção | Predicado decidível de coordenadas em ℓ² | `laguerreHead R` mantém exatamente `0,…,R`, usando a projeção existente. |
| `l2CoordinateMask_tendsto`, energia residual | Cada coordenada eventualmente mantida; vetor fixo | `laguerreHead_tendsto` e `laguerreHead_residual_energy_tendsto_zero` especializam a hipótese com `r≤R`. |
| `chiral_pairing_balance_isometry` | Uma isometria complexa comum e quatro vetores independentes | `cauchyLaguerre_originalSource_chiral_balance` aplica o teorema à fonte original tipada no fecho. |
| PR #82: pernas e soma polarizada da fonte conjunta | Strip regular para a decomposição; coordenadas HB não nulas para as pernas | `cauchyLaguerre_originalSource_legs` e `cauchyLaguerre_source_polarized_product_sum` preservam hipóteses, denominadores e parâmetros originais. |
| Ledgers Γ/material e contraexemplos de colisão | Dois argumentos espectrais independentes, partes imaginárias não nulas | `laguerreMaterialLedger_eq_mismatch` e a família de contraexemplos mantêm o defeito refutado. |
| `ConditionalParsevalLimit` | `AdmissibleInfinitePartition`, `State`, `ConcreteAnalysisSpace` | As fontes atuais contêm `extendedFiniteInverseSqrt_tendsto` e `concreteEmbeddedCanonicalAnalysis_tendsto`; a antiga hipótese está descarregada. Esse carrier não é identificado com o Cauchy físico. |
| `strong_comp_tendsto` | Convergência forte dos fatores e cota uniforme do fator esquerdo | API disponível; a estabilidade do passo foi obtida diretamente da série quadrática do shift existente. |
| `GreenParsevalMaterialLogOperator` local | Estado material Green, range Parseval e gerador material | API de outro carrier/relógio. Não é usada para definir ou renormalizar as features Cauchy. |

Pins preservados: CPFormal `65d50f6db1208708e109982ba97e1d51d3039956`; GreenFrame `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`; geometry-of-numbers `d7cc54f5c485320f1fada33118e9e6101488819a`; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
SHA-256 do manifest: `822866313e377adcb9c6249680ed67ceb47682af1bb0cd3cc5203554786bcfeb`.

## Passo físico, Hardy e estabilidade

`physicalShiftSynthesis n` aplica `rho j ^ n` às meias densidades originais. Sua extensão `physicalCauchyShift n` satisfaz

$$
\mathcal U S_n=B_n\mathcal U,\qquad
S_n\psi_j=\rho_j^n\psi_j,\qquad
S_{n+m}=S_nS_m,\qquad S_n=S_1^n,\qquad\|S_n\|\le1.
$$

`backwardShift_preserves_physicalRange` prova a invariância do range fechado sem supor sobrejetividade. O passo é construído no núcleo físico e depois completado; a inversa da isometria não define a entrada.

`integral_physicalHalfDensity` calcula diretamente a integral das meias densidades. `hardyStep_physicalHalfDensity`, `hardyStep_physicalFiniteFunction` e `physicalCauchyShift_one_hardy_core` certificam, inclusive como igualdade a.e. no L² para cada síntese finita,

$$
S_1\psi_j(u)=\psi_j(u)-\frac1u\int_0^u\psi_j(v)\,dv
=\rho_j\psi_j(u).
$$

A fórmula no endpoint é compatível com o representante contínuo original. Os coeficientes finitos podem já conter quaisquer amplitudes físicas: a identidade é linear e não as renormaliza.

`backwardShift_tendsto_zero` reutiliza a contração/série ℓ² do alvo; `physicalCauchyShift_tendsto_zero` transporta a estabilidade forte por `𝒰`.

## Lift com cauda física e obstrução da cabeça curta

`physicalHeadTailIsometry R` toma valores no produto Hilbertiano `WithLp 2 (ℓ² × PhysicalCauchySpace)`:

$$
x\longmapsto(P_R\mathcal Ux,\;S_{R+1}x).
$$

O segundo componente continua sendo um vetor físico. Aqui `P_R` é a máscara de coordenadas no alvo ℓ²; a identificação com a projeção no L² de `NativePhysicalLaguerreCompression` exigiria uma prova própria. Para entradas independentes,

$$
\langle x,y\rangle=
\langle P_R\mathcal Ux,P_R\mathcal Uy\rangle+
\langle S_{R+1}x,S_{R+1}y\rangle.
$$

`physicalHeadTail_refinement` mantém a cabeça anterior e evolui sua cauda pelo mesmo semigrupo. `shortHead_full_physical_tail` usa rank/finrank e a injetividade física anterior: se `R+1<m`, existe um vetor físico não nulo sintetizado por `m` coeficientes com cabeça zero e com toda a norma na cauda física.

Consequentemente, `physicalCauchyShift_tail_opNorm_eq_one` prova

$$
\|S_{R+1}\|=1\quad\text{para todo }R,
$$

apesar de `S_n x→0` para todo vetor fixo. Não há convergência a zero em norma de operador nem controle uniforme de fontes com dimensão crescente decorrente apenas desse limite forte.

## Fonte conjunta, cruzamentos e ledgers

Há provas de pertinência ao fecho para `sourceValue`, `sourceCompanion`, `nativeDressedCompanion`, `completionCompanion`, a perna incidente e a retornada. Elas seguem das sínteses finitas físicas e não exigem novas hipóteses de positividade.

Os wrappers `physicalSourceValue`, `physicalSourceCompanion`, `physicalNativeCompanion`, `physicalCompletionCompanion`, `physicalOriginalIncident`, `physicalOriginalReturned` mantêm os vetores originais por definição; apenas certificam seu domínio.

`physicalSourceChannels` mantém `(V,C_n,C_a)`. `cauchyLaguerre_nine_source_crossings` preserva cada cruzamento `a,b : Fin 3` com tamanhos, profundidades, coeficientes e raios independentes. `cauchyLaguerre_nine_source_crossings_headTail` conserva uma cauda física em cada um desses nove pares.

A conservação quiral é uma especialização do teorema anterior, e a soma polarizada aplica o produto native + archimedean do PR #82 com os mesmos denominadores. Não se afirma sinal para a forma assinada.

`laguerreFinitePair_eq_original` e `laguerreFiniteHeadTailPair_eq_original` identificam os novos pairings com o Cauchy original; `laguerreFiniteHeadTailPair_eq_old_ledger` identifica a apresentação anterior de cabeça + cauda. `laguerreMaterialLedger` substitui os pairings Cauchy da referência e dos dois setores mistos por pairings efetivos da mesma isometria/lift, preservando sinais, defeito de métrica e Green original.

`laguerreMaterialLedger_eq_mismatch` mantém exatamente o mismatch Γ/native. `laguerreMaterialLedger_counterexampleFamily` aplica a família refutada anterior ao novo ledger para todas as janelas, profundidades e cortes. `laguerreNativeOrientation_materialLedger` mantém ainda os setores exteriores e o defeito de métrica na orientação nativa.

## Validação e fronteiras

Registro novo: `audit/cauchy-laguerre-isometry-registry.json`, com 104 raízes públicas em sete módulos. Cada raiz tem `#check`, `#print axioms` e o guard de fechamento transitivo dos tipos e corpos, incluindo dependências privadas, reutilizado de `NativePhysicalSewingAuditSupport`.

Registro anterior: `audit/gamma-cauchy-transport-registry.json`, com 405 raízes em 41 módulos, preservado sem alterações. Nenhum pin ou módulo C2 preexistente foi alterado.

Comandos reproduzíveis:

```bash
bash scripts/audit_cauchy_laguerre_isometry.sh
bash scripts/audit_gamma_cauchy_transport.sh
lake build --wfail
bash scripts/static_audit.sh
bash scripts/audit.sh
```

O primeiro script compila cada auditoria com `--wfail`, executa `lake env lean -E warning`, registra hashes e o ambiente, e conclui com build raiz e auditoria de integração. O segundo repete a cobertura anterior. O guard aceita somente `propext`, `Classical.choice`, `Quot.sound` e rejeita qualquer dependência não verificada.

Provas antigas reutilizadas: Gram/head-tail/momentos, síntese física injetiva, shift contrativo, máscaras ortogonais, forma quiral e ledgers/refutações Γ.

Novas especializações: ação do shift nas colunas, máscaras `0,…,R`, canais e pernas originais, nove cruzamentos, pairings e ledgers transportados.

Novas construções físicas: colunas literais em ℓ², isometria no fecho e identificação de coordenadas; extensão do passo físico e certificação integral Hardy; lift Hilbertiano com cauda física, refinamento e obstrução por dimensão.

Fronteiras abertas: completude Laguerre em todo L² e sobrejetividade; ponte universal Weyl/Γ→Cauchy; identificação de relógios; extensão ou contração do retorno quiral original; controle uniforme de fontes crescentes; cálculo funcional global; positividade física assinada. O passo `S_1=I−Hardy` não é identificado com o retorno quiral `Q_k`. O mismatch refutado permanece explicitamente não nulo.

Não foram usados canários numéricos como certificados nesta construção. Resultados de CI sem jobs não contam como validação Lean.

## Execução observada e checkpoint

Código certificado: `43950ea35260fbb4317105d8e32721484cf3c262`. Os dois scripts completos terminaram com sucesso, incluindo builds raiz com 10.179 jobs, auditorias estáticas e o script geral de integração. São 104 novas raízes (72 teoremas, 29 definições, duas abreviações e uma instância) mais 405 raízes anteriores, em 48 módulos ao todo.

| Módulo novo | Raízes públicas | Fecho transitivo de tipos e corpos |
| --- | ---: | ---: |
| NativeCauchyHardyStep | 8 | 5378 |
| NativeCauchyLaguerreColumns | 9 | 5046 |
| NativeCauchyLaguerreHeadTail | 15 | 5531 |
| NativeCauchyLaguerreIsometry | 19 | 5400 |
| NativeCauchyLaguerreLedgers | 13 | 7242 |
| NativeCauchyLaguerreShift | 20 | 5687 |
| NativeCauchyLaguerreSources | 20 | 5695 |

Evidências persistidas em `research/cauchy-laguerre-isometry-2026-10-13/`: `validation.json`, arquivos completos de logs dos dois scripts, logs de kernel, resumos, hashes de fontes e a fotografia da CI externa. As execuções do GitHub no commit de código retornaram `startup_failure` com `jobs=[]`; a CI externa é inconclusiva, e não é a evidência de validação Lean.

Os dois arquivos C2 não rastreados no checkout principal mantiveram os hashes `5bfe06e8d15432c4d6cab6719dc22a0376019243f3e896329ea9ab9dd7458cb0` e `b6f05d0241058885da362b5cb20d3968d704a667da3ffc443714a69f3564623c`. O manifest também manteve o hash registrado acima.
