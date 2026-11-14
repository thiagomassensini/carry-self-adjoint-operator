# Prompt Luna A — PSD + Hardy nonrecurrence

## A. Origem e proveniência

Este trabalho está no repositório `thiagomassensini/carry-self-adjoint-operator`, na branch `agent/luna-a-psd-hardy-20261114`. A base técnica é o head da PR #110, `842e5f602047358137f1d206444cc8accde5c59c` (`codex/hardy-pade-c3`), que permanece aberta contra `main`; o `main` consultado estava em `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. A PR #110 fornece a não recorrência Hardy usada abaixo; seus resultados não foram duplicados.

Ambiente: Lean `leanprover/lean4:v4.32.0`. Pins relevantes preservados: Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, geometry-of-numbers `d7cc54f5c485320f1fada33118e9e6101488819a` e NativeCarryC3Crosswalk `150cfc7fb08da96bf8117f15869cc2b819d593c2`. Nenhum pin foi alterado.

Arquivos criados:

- `CarrySelfAdjointOperator/AllPrefixPSDNonrecurrence.lean`
- `CarrySelfAdjointOperator/CompletedNativeSemidefiniteHardyGate.lean`
- `CarrySelfAdjointOperator/CompletedNativeSemidefiniteHardyGateAudit.lean`
- `scripts/validate-luna-a-psd-hardy.py`
- `research/luna-a-psd-hardy/CHECKPOINT.md`

## B. Resultados demonstrados em Lean

O teorema abstrato `momentHankelPrefix_posDef_of_all_posSemidef_of_noFiniteMomentRelationAt` vale para qualquer sequência real, deslocamento e ordem. Suas premissas são somente semidefinição positiva de todos os prefixos deslocados e `NoFiniteMomentRelationAt` no mesmo deslocamento; sua conclusão é positividade definida de cada prefixo.

Para a fonte original, `canonicalHankel_posSemidef_of_nativeSourceBoundary_nonneg` e `canonicalShiftedHankel_posSemidef_of_nativeSourceBoundary_nonneg` derivam PSD das duas torres da não negatividade das energias de fronteira `nativeSourceFiniteBoundaryEnergy (2*n)`. O transporte usa `nativeSourceFiniteBoundaryEnergy_even_split`, o split de paridade original, `primeDepthGeometricMoment_eq_canonical` e o fator quatro que aparece nessa identidade.

`canonicalHankelPair_posDef_of_nativeSourceBoundary_nonneg` conclui PD das duas torres sob duas premissas explícitas: `InfinitePositiveRealNativeZeros` e não negatividade de todas as energias originais. A primeira entra apenas pelo teorema Hardy já existente; aqui não se prova a existência desses zeros. A segunda não é provada pelo critério.

`nativeSourceGammaCorrectionGap` é definido exatamente como `rawGammaWronskianBalance.im - ‖gammaSourceSynthesis‖²`, nos nós, pesos e coordenadas existentes. `HasNativeSourceGammaCorrectionEnvelope` exige, para cada ordem fixa `n`, uma função `ε → 0` que eventualmente limite esse gap superiormente por `ε(k) * ‖x‖²` para todo vetor de fronteira. Sob essa hipótese, `nativeSourceFiniteBoundaryEnergy_nonneg_of_gammaCorrectionEnvelope` prova não negatividade da energia original, e `canonicalHankelPair_posDef_of_gammaCorrectionEnvelope` transporta o resultado às duas torres, ainda sob a premissa Hardy.

## C. Lei abstrata PSD + não recorrência

Para vetor `x` no prefixo de tamanho `n` e índice monomial `j`, a prova comprime o prefixo PSD de tamanho `n+j+1` ao bloco indexado por `Fin n ⊕ Unit`: o primeiro setor mantém o prefixo e o último índice é `j`. A energia comprimida em `x + t·e_j` é um polinômio quadrático em `t`. Se a energia inicial é zero, a semidefinição para todo `t` força o coeficiente linear a desaparecer; a prova usa `t = -b/(c+1)` e `c ≥ 0`, sem inversa nem determinante.

Assim, um vetor de energia zero gera a relação finita `Σᵢ xᵢ h_(shift+i+j)=0` para todo `j`. `NoFiniteMomentRelationAt` força todos os coeficientes a zero. A ordem `n=0` está incluída no teorema.

## D. Adaptação à fonte completada

O resultado reutiliza o split de fronteira já formalizado e conserva as duas somas ordenadas de paridade. O coeficiente ímpar já contém `nativeSourceOddBoundaryCoefficient = 2 * primeDepthGeometricMoment`; combinado com a normalização do split, ele produz o fator global `4`. Nenhum coeficiente, fase, peso ou completion é renormalizado.

A condição de energia não negativa aparece como hipótese matemática. A equivalência entre essa condição de sinal e PSD de uma matriz finita da fonte não é usada para encerrar circularmente a obrigação: o split transfere diretamente as energias de testes de paridade para cada bloco Hankel.

## E. Envelope Gamma condicional

O controle analítico reutilizado é `rawGamma_chiralJetInput_eventually_energy_control`: para todo `η>0`, em cada ordem fixa, a diferença entre `4*(‖Gamma‖² - rawGamma.im)` e a energia de fronteira tem módulo limitado por `η*‖x‖²` eventualmente. Pela definição do gap `D`, isso é `|-4D - E| ≤ η‖x‖²`.

Se `D ≤ ε(k)‖x‖²` com `ε(k)→0`, a estimativa dá `E ≥ -4ε(k)‖x‖² - η‖x‖²` eventualmente. Se `E<0` e `x≠0`, escolher `η = -E/(10‖x‖²)` e usar eventualmente `ε(k)<η` contradiz essa desigualdade. O caso `x=0` segue da definição da energia.

**Classificação A3: PARTIAL condicional.** A interface e sua consequência estão provadas; a existência do envelope não está estabelecida.

## F. Proveniência de sinais e limitações

Não há resultado de sinal incondicional novo. A1 é uma implicação geral, A2 preserva a energia de fronteira como premissa, e A3 preserva o envelope Gamma como premissa. `InfinitePositiveRealNativeZeros` é declarado no módulo Hardy como hipótese fornecida pelo usuário.

Em particular, o trabalho não prova positividade Hankel para uma fonte arbitrária, não prova a energia da fonte não negativa, não prova o envelope de A3 e não demonstra all-order positivity incondicional. Não se introduziu uma Gram positiva nem uma hipótese theta para fechar esses sinais.

## G. Obrigações ainda abertas

1. Provar a desigualdade independente que dá o envelope assinado `D(n,k,x) ≤ εₙ(k)‖x‖²`, uniforme em `x` para cada ordem fixa.
2. Estabelecer a premissa de infinitude de zeros reais positivos caso se queira usar a conclusão Hardy sem fornecê-la como hipótese.
3. Sem essas duas entradas, o sinal das energias originais e a positividade definida das torres permanecem condicionais.

## H. Validação e auditoria

O script `scripts/validate-luna-a-psd-hardy.py` compila explicitamente os três módulos da pesquisa com `-DwarningAsError=true`, executa o build Lake para os mesmos módulos, audita os axiomas públicos e roda `git diff --check`.

Comandos executados durante esta fase:

- `lake env lean -DwarningAsError=true CarrySelfAdjointOperator/AllPrefixPSDNonrecurrence.lean` — passou.
- `lake env lean -DwarningAsError=true CarrySelfAdjointOperator/CompletedNativeSemidefiniteHardyGate.lean` — passou.
- `lake env lean -DwarningAsError=true CarrySelfAdjointOperator/CompletedNativeSemidefiniteHardyGateAudit.lean` — passou.
- `lake build CarrySelfAdjointOperator.AllPrefixPSDNonrecurrence` — passou.
- `lake build CarrySelfAdjointOperator.CompletedNativeSemidefiniteHardyGate` — passou.
- `lake build CarrySelfAdjointOperator.CompletedNativeSemidefiniteHardyGateAudit` — passou.
- `git diff --check` — passou.

`#print axioms` foi executado transitivamente para A1, A2, A3 e as interfaces reutilizadas de Hardy, split e Gamma. Todas as declarações listaram apenas `propext`, `Classical.choice` e `Quot.sound`. Não há `sorry`, `admit`, `native_decide` ou novos axiomas nos módulos criados.

Limitação do ambiente: a worktree nova inicialmente clonou dependências até esgotar o espaço disponível. Esse cache recém-criado foi removido e a validação reutilizou o cache existente do mesmo manifest. A árvore de trabalho WIP original permaneceu intacta.

## I. Próximo passo mínimo

Formalizar, a partir da estimativa radial Gamma original, o envelope superior uniforme em vetores para um `n` fixo; esse é o único passo novo necessário para converter A3 de condicional em um sinal fonte demonstrado nessa ordem.
