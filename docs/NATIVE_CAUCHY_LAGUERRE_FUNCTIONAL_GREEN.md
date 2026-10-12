# Realização funcional Cauchy–Laguerre e Green

## Entrada e escopo

O trabalho começou em `main` no commit `9f801d4abb45e246a8d020d2b3af4f763b3d743c`, depois da integração dos PRs #70–#72. Todos os 16 pins do manifesto coincidem com os HEADs efetivos dos pacotes. Lean `v4.32.0`; mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`. Nenhum pin ou métrica foi alterado. Os dois arquivos de trabalho não rastreados `C2OddTfvdTransport*.lean` foram preservados.

A instrução principal é o prompt funcional de 12/10/2026; a pesquisa consolidada fornece o contexto matemático. Os resultados dos PRs anteriores são reutilizados. CI externo está bloqueado por pagamento, conforme informado pelo responsável: execução com zero jobs é inconclusiva. A evidência matemática deste relatório é o build local no `llm` e a auditoria de axiomas.

## F1 — Modos mensuráveis e momentos

`NativeLaguerreLogMoments.lean` prova integrabilidade e o valor de todos os momentos, para `n : ℕ` e `a > -1`:

`∫₀¹ u^a (-log u)^n du = n! / (a+1)^(n+1)`.

A prova usa a substituição verdadeira `u = exp(-t)` e a integral Gamma existente no mathlib. Não usa testes numéricos nem uma tabela finita de momentos.

`NativeLaguerreLpModes.lean` constrói todos os `λ_r = L_r(-log u)` como classes no espaço complexo original `Lp ℂ 2 volume`, com representante certificado quase em toda parte. Prova a integrabilidade quadrática de todos os graus logarítmicos e seus produtos internos fatoriais. A ortonormalidade foi provada para as ordens 0, 1 e 2; ortonormalidade all-order ainda não foi demonstrada.

Para todos `r,j`, `laguerreMode_feature` identifica o overlap funcional com a coluna `feature r j` já certificada pelo PR #70. `laguerreMode_radial_state` mantém a amplitude física `√(k+1)` exatamente uma vez. Não se representa um modo logarítmico não constante como função contínua no intervalo fechado.

## Gates ainda abertos nesta etapa

- F1: ortonormalidade all-order.
- F2: `OPEN_LAGUERRE_COMPLETENESS`; não existe nesta etapa uma equivalência unitária sobre todo o espaço físico.
- F3: operador físico limitado e sua matriz funcional all-order.
- F4: domínio maximal, auto-adjunção do relógio geométrico e cálculo funcional.
- F5: inverso Green no Hilbert original, aplicado à fonte completada.
- F6: compressão do operador físico e vazamento do complemento.
- F7: transporte das duas entradas completas, controle de cauda e costura física multibase. A forma assinada não foi declarada positiva.

## Validação

O módulo funcional compila isoladamente. O arquivo `NativeLaguerreLpModesAudit.lean` imprime os axiomas de todas as 14 declarações públicas novas. Todas as 14 declarações usam apenas `propext`, `Classical.choice` e `Quot.sound`. `lake build --wfail` completo passou no llm com 10115 jobs.
