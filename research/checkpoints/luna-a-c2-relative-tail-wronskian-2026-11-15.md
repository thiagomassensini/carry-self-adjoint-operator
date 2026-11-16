# Checkpoint — A cauda relativa C2 (2026-11-15)

## Base e integração

- Base de referência: `c999ce41ccdec0ff194e7969bf1f7f329d374d3a` (`origin/main`).
- PR #117 conferida: head `87e448a6c2fdd35b61cc3f6ff824bef9dc1b4b88`, branch `codex/luna-f-exact-tail-2026-11-14`; a base indicada acima é ancestral desse head.
- A branch desta tarefa é `luna/a-cauda-relativa-20261115`, empilhada sobre o head da #117 para consumir as declarações da cauda exata.
- HEAD Lean publicado e validado: `3364591cf0e60f79a72d1017ea1874f73d825ea3`.
- PR de revisão (aberta, sem merge): [#122](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/122), base `codex/luna-f-exact-tail-2026-11-14`.
- A PR #120 não foi necessária: nenhum consumidor final foi fechado.
- Não há `AGENTS.md` no repositório nem diretório da worktree; o arquivo global do Codex estava vazio.

## Formalização adicionada

Arquivo: `CarrySelfAdjointOperator/C2RelativeTailWronskian.lean`.

- `c2RelativeResponse_cleared_identity` e `c2RelativeResponse_scalar_identity`: identidade algébrica e forma com denominadores explícitos.
- `c2LogarithmicResponse_addTail_eq_wronskian` e `c2LogarithmicResponse_addTail_eq_relative_deriv`: versão `HasDerivAt` e quociente relativo da cauda.
- `c2ProductWronskian_cancel_dressing` e `c2LogarithmicResponse_cancel_commonDressing`: cancelamento do dressing e independência explícita de `L` para o erro entre respostas.
- `c2LogarithmicResponse_addTail_eq_zero_of_proportional`: correção nula quando `T = aH` para escalar constante `a`.
- `nativeC2ExactTailRelativeWronskian` e `nativeC2ExactTailRelativeWronskian_eq_central_legs`: Wronskiano no parâmetro original, incluindo o seed da carta finita, e expansão `central + pernas` via `c2FiniteChartJet_eq_central_add_legCorrection`.
- `completedNativeC2_relativeLogarithmicResponse_eq_i_mul_exactTailWronskian`: instância para a cauda C2 original; usa `nativeC2ExactCenterTail`, a igualdade exata da característica completada, a derivada da cauda ao longo da faixa aberta e o dressing original. O fator de cadeia `i` produz o sinal `+i Xi/2`.
- `c2SignedCrossing_eq_four_im_inner`, `c2SignedCrossing_add_imaginary_leg` e `c2SignedCrossing_joint_variation`: orientação reutiliza `norm_chiral_balance_eq_source_cross`; as variações são igualdades assinadas.
- `nativeSourceC2Approx_signed_leg_crossing`, `nativeSourceC2_signed_tail_crossing_variation` e os dois adaptadores `nativeSourceC2_*Tail_eq_originalExactCenterTailSynthesis`: instâncias vetoriais usam as sínteses e caudas existentes, com os pesos Hermite–Biehler completos e os estados Cauchy originais.

Auditoria: `CarrySelfAdjointOperator/C2RelativeTailWronskianAudit.lean` imprime os axiomas das declarações públicas acima. Todas listam somente `propext`, `Classical.choice` e `Quot.sound`; nenhum axioma, `sorry` ou `admit` foi introduzido.

## Verificação executada

- Módulo e audit compilados com Lean `v4.32.0` e `-DwarningAsError=true`.
- Os `.olean` de dependências vieram do cache já existente em `/home/thlinux/carry-self-adjoint-operator/.lake`; os dois artefatos desta tarefa foram escritos no diretório `.lake/build` compartilhado apenas para a compilação/auditoria. Isto valida os módulos contra aquele cache, não é declaração de build limpo completo da worktree isolada.
- `git diff --check` executado.
- Nenhum experimento numérico, intervalo certificado ou build total foi usado.

## Obrigações abertas

- A desigualdade de sinal positiva all-order permanece aberta e não é afirmada aqui.
- A hipótese de envelope/cauda `HasNativeSourceC2LegTailBounds` e a estimativa assinada central-mais-pernas continuam sem prova.
- A resposta escalar requer não anulação explícita das características finita e completada (`hHead`, `hFull`); esses denominadores não foram descartados.
- As identidades vetoriais não provam positividade do cruzamento nem convergência das caudas.
- O corte de erro sem hipótese de sinal da PR #117 foi mantido e não refeito.
