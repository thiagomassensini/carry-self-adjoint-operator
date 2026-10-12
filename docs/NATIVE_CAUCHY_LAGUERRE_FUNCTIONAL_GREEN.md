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
- F3: somente a redução da matriz all-order à expressão binomial fechada continua aberta.
- F4: Jacobi all-order e `OPEN_FUNCTIONAL_CALCULUS`; domínio maximal, densidade, auto-adjunção e fechamento estão certificados.
- F5: extensão além de entradas de suporte finito; reconstrução funcional da fonte finita completada está certificada.
- F6: extensão das compressões para todos os cortes R; aqui o corte 0–2 é funcionalmente certificado.
- F7: cota de cauda com constante universal π e costura física multibase. O transporte de duas entradas completas e seus quatro setores é certificado; a forma assinada não foi declarada positiva.

## Validação

O módulo funcional compila isoladamente. O arquivo `NativeLaguerreLpModesAudit.lean` imprime os axiomas de todas as 14 declarações públicas novas. Todas as 14 declarações usam apenas `propext`, `Classical.choice` e `Quot.sound`. `lake build --wfail` completo passou no llm com 10115 jobs.

## F3 — Avanço no Hilbert original

`NativeIntervalMultiplier.lean` constrói multiplicação limitada por qualquer coeficiente contínuo e, em particular, o operador físico `M_u`. Prova `M_u φ_j = φ_(j+1)`, preservando a meia-densidade e a amplitude radial. Prova auto-adjunção, norma no máximo 1 e positividade de `M_u` e `I-M_u`. Isso é positividade do operador radial no Hilbert original, sem implicação de positividade da forma assinada de duas pernas.

Todos os elementos da matriz funcional são identificados como somas finitas exatas de momentos Gamma. A forma binomial `choose(r+s,r)/2^(r+s+1)` foi provada para as ordens 0–2. Não se utiliza uma inversa unitária Laguerre.

PR F1: #73; commit `9e989338943cce9d918df687104d71377002a329`; merge `ed58af5b39df24d36358216284a380aeb47cc8c7`. O build completo de main passou após o merge. As execuções externas 38290535010 e 38290478230 deram `startup_failure`; a infraestrutura não executou a prova Lean.

Validação F3: módulo isolado e build completo `--wfail` aprovados; 20 declarações públicas auditadas, somente os axiomas padrão.

## F6 — Compressão física e entrada exterior

`NativePhysicalLaguerreCompression.lean` constrói a projeção ortogonal verdadeira sobre o span dos três modos certificados. O teorema `physicalFirstThree_compression_square` comprime `M_u²` antes de substituir o operador comprimido. `physicalFirstThreeLeakage_eq_gram` identifica o vazamento como `B* B`; sua positividade é certificada. `physicalFirstThree_outside_input` retém `P M_u² (I-P) h` para uma entrada física arbitrária. Não se presume que a entrada pertence ao subespaço truncado.

Validação F6: módulo isolado, build completo `--wfail` (10117 jobs) e auditoria das 11 declarações públicas, incluindo a instância de dimensão finita, aprovados com apenas os axiomas padrão.

## F4 — Relógio geométrico maximal

`NativeGeometricLogClock.lean` define multiplicação por `log u` no domínio maximal `{f : H | MemLp ((log u) f) 2 volume}`. Prova que esse domínio é denso, que o adjunto coincide com o operador original, e portanto que o relógio é auto-adjunto e fechado. A prova usa o regularizador físico `M_u`, injetivo quase em toda parte, e o produto limitado e contínuo `u log u`. Não depende de completude Laguerre.

Todos os monômios logarítmicos, todos os modos Laguerre e todas as colunas de meia-densidade nativas, com sua amplitude, pertencem ao domínio. A ação no núcleo logarítmico e sua expansão em qualquer ordem são exatas. As linhas Jacobi 0–2 foram verificadas como igualdades de vetores físicos. A identidade `exp(log u)=u` é provada quase em toda parte; isso é um canário espectral e não um teorema de cálculo funcional de operadores. A coordenada Weyl literal `1+log(ell*u)` mantém `1+log ell` e `log u`; não se identifica o relógio material diagonal com esse relógio geométrico.

PR F3/F6: #74; commits `1a8b7c8` e `8a9a342`; merge `2002f3058927952d2e5249b66c99277783291949`; main revalidada com `--wfail`.

Validação F4: módulo isolado, build completo `--wfail` (10118 jobs), auditoria de todas as 21 declarações públicas; somente os axiomas padrão.

## F5/F7 — Inverso físico e pairing com todos os setores

`NativePhysicalGreenResolvent.lean` constrói o multiplicador recíproco `(1-q u)^(-1)` para `0 ≤ q < 1`, prova os inversos esquerdo e direito de `I-q M_u`, e a cota de norma `(1-q)^(-1)`. Constrói `q M_u (I-q M_u)^(-2)` no Hilbert original; sua positividade e auto-adjunção pertencem somente ao operador Green nesse Hilbert.

O adaptador `continuousPairToSource_physical_advance` liga o avanço previamente certificado ao operador verdadeiro nas duas pernas. `physicalCompletedFiniteGreen_reconstruct` resolve a fonte completada de suporte finito, antes do pairing, preservando os dois traços, o bulk e os termos `E b`, `E x`, `M_u E x` e `E Sx`. O fator q é o do inverso da válvula original; não há fonte intermediária normalizada nem truncamento da entrada.

`physicalCompletedFiniteGreen_signed_pairing` usa duas entradas independentes. `physicalCompletedFiniteGreen_four_sectors` conserva principal–principal, principal–resíduo, resíduo–principal e resíduo–resíduo depois do inverso. A primeira entrada permanece conjugada pela forma original. Resíduo com autopairing nulo não autoriza apagar cruzamentos.

PR F4: #75; commit `4aaf4b419dff3446f09fdf4d792dce888710ca5d`; merge `a668b28b5cf52b0c4992e367de2de73ced1d3a07`; main revalidada.
