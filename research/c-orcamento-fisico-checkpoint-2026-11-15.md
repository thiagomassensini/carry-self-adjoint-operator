# C — orçamento relativo do retorno: checkpoint (2026-11-15)

## Base, worktree e dependências

- Repositório: `thiagomassensini/carry-self-adjoint-operator`.
- Worktree isolada: `/home/thlinux/worktrees/c-orcamento-fisico-20261115`.
- Branch: `luna/c-orcamento-fisico-20261115`.
- Base/HEAD inicial: `015135997a586ec8111fc21bfeead015b1a49316`, HEAD da PR #120 (`codex/nonrecurrence-gamma-integers-20261114`).
- A PR #120 está aberta contra `main` e fornece o gate
  `canonicalHankelPair_posDef_of_nativeSourceBoundary_nonneg_of_harmonicNonrecurrence`,
  sem hipótese `InfinitePositiveRealNativeZeros`. Esta entrega é empilhada sobre
  aquela branch; não altera nem incorpora a PR #120.
- A PR #117 está aberta em outra base (`codex/luna-e-carrier-compensation-2026-11-14`)
  e fornece o fechamento da cauda C². Esse resultado não prova o sinal da energia
  física nem a existência do orçamento de retorno aqui assumido.
- Não há `AGENTS.md` aplicável na worktree nem arquivos versionados com esse nome
  na base examinada. Alterações de outras worktrees/checkouts foram preservadas.

## Trabalho Lean

- `NativeSourceRelativeReturnBudget.lean` usa as sínteses originais
  `radialIncidentSynthesis` e `radialReturnedSynthesis` após
  `nativeSourceChiralJetInput`, e reescreve o controle de storage através de
  `storage_re_eq_norm_balance`.
- O orçamento aditivo formalizado é
  `‖Oₙₖ x‖² ≤ ‖Iₙₖ x‖² + eₙ(k) ‖x‖²`, com `eₙ → 0`. Com o controle eventual
  `|2Sₙₖ(x) − Eₙ(x)| ≤ ε ‖x‖²`, uma contradição prova `Eₙ(x) ≥ 0`.
- A versão multiplicativa requer `ηₙ(k) ≥ 0`, o retorno limitado por
  `(1 + ηₙ(k)) ‖Iₙₖx‖²`, a cota incidente por `Bₙ(k) ‖x‖²` e
  `ηₙ(k) Bₙ(k) → 0`. Ela produz o erro aditivo `eₙ(k)=ηₙ(k)Bₙ(k)`.
- `Bₙ(k)` é instanciado pelo quadrado da norma de operador da aplicação linear
  incidente original. A cota é demonstrada por `ContinuousLinearMap.le_opNorm`;
  o domínio continua sendo `Fin (2*n) → ℂ` com a norma Pi sup existente. O lema
  `nativeSourceInput_coordinate_norm_le` também registra a cota por coordenada.
- O orçamento em `HasNativeSourceOperatorRelativeReturnBudget` permanece uma
  hipótese explícita. Assim, o gate é fechado condicionalmente; a existência
  desse orçamento para a fonte C² continua aberta.
- `NativeSourceRelativeReturnBudgetCounterexample.lean` é um exemplo escalar
  genérico, não um contraexemplo C²: para `Iₖx=kx`, `Oₖx=(k+1/k)x`, o excesso
  relativo `2/k²+1/k⁴` tende a zero, mas seu produto com `Bₖ=k²` tende a `2`,
  enquanto `‖Iₖx‖²−‖Oₖx‖²=−(2+1/k²)‖x‖²`.
- A extensão opcional por determinantes em blocos não foi necessária para o
  fechamento condicional do gate e não foi incluída.

## Build e auditoria

Comandos executados na worktree, usando Lean 4.32.0:

```text
lake build --wfail CarrySelfAdjointOperator.NativeSourceRelativeReturnBudget
lake build --wfail CarrySelfAdjointOperator.NativeSourceRelativeReturnBudgetCounterexample
lake build --wfail CarrySelfAdjointOperator.NativeSourceRelativeReturnBudgetAudit
```

Os três alvos passaram. O build final da auditoria terminou em 9636 jobs.
`NativeSourceRelativeReturnBudgetAudit.lean` usa `#print axioms` nos lemas de
orçamento, na composição com o gate existente e nas identidades/limites do
exemplo escalar. Todos imprimiram somente os axiomas padrão `[propext,
Classical.choice, Quot.sound]`; nenhum axioma, `sorry` ou `admit` foi
introduzido. As mensagens informativas de replay das dependências sobre `ring`
não são avisos; `--wfail` terminou com sucesso.

Não foram usados cálculos intervalares ou experimentos de multiprecisão: esta
entrega contém provas Lean e a identidade analítica genérica acima, não uma
demonstração analítica do orçamento físico da fonte.
