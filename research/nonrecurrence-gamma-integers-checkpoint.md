# Checkpoint — não recorrência harmônica nos inteiros pares

## Base e isolamento

- Repositório: `thiagomassensini/carry-self-adjoint-operator`.
- Base: `c999ce41ccdec0ff194e7969bf1f7f329d374d3a`.
- Branch: `codex/nonrecurrence-gamma-integers-20261114`.
- Worktree: `/home/thlinux/worktrees/carry-nonrecurrence-gamma-20261114`.
- O checkout original não foi alterado; suas mudanças anteriores continuam presentes.

## Resultado matemático formalizado

Foi provado, sem `InfinitePositiveRealNativeZeros`, que

```lean
canonicalCompletedNativeLogDerivativeMoment_noFiniteMomentRelation
```

tem tipo

```lean
NoFiniteMomentRelation canonicalCompletedNativeLogDerivativeMoment
```

A demonstração preserva o residual Hardy extraído da relação dos momentos. A função inteira de comparação

```lean
completedNativeHarmonicComparison s
  = (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2
```

concorda com o carrier nativo em um germe e recebe o residual por continuação analítica. A avaliação em `z = -I * (t - 1/2)` produz uma identidade entre dois polinômios reais e a derivada de `X`.

Nos pontos `t = 2(n+1)`, foi compilada a fórmula exata

\[
\frac{X'(t)}{X(t)}=
\frac1t+\frac1{t-1}-\frac{\log\pi}{2}
+\frac{H_n-\gamma}{2}+\frac{\zeta'(t)}{\zeta(t)}.
\]

O termo de zeta tende a zero pela convergência de `LSeries 1` e de sua derivada. Consequentemente, a sequência real do logaritmo derivado tende a `+∞`, mas dividida por `n+1` tende a zero. Uma razão de polinômios reais, separada pelos graus do numerador e denominador, não pode ter ambos os comportamentos.

O denominador composto tem apenas finitas raízes; o lema existente fornece sua não anulação eventual nos inteiros pares.

Também foi formalizado que `X(t)` é positivo como número complexo ordenado (real positivo) para esses pontos: o fator quadrático é positivo, `Gammaℝ(t)` é reduzido ao produto real positivo `π^(-t/2) Γ(t/2)`, e `ζ(t)>0`. A não anulação usada na contradição decorre então dessa positividade.

## Gate de positividade

Foi adicionada uma versão do gate PSD→PD que requer somente

```lean
∀ n x, 0 ≤ nativeSourceFiniteBoundaryEnergy (2*n) x
```

como hipótese de sinal. Ela usa a não recorrência harmônica para ambos os shifts dos prefixos. A hipótese de sinal não foi provada. As versões condicionais antigas, incluindo a que assume `InfinitePositiveRealNativeZeros`, foram preservadas.

## Arquivos da entrega

- `CarrySelfAdjointOperator/CompletedNativeHardyAnalytic.lean`: interfaces públicas pequenas para o residual Hardy sobre coeficientes complexos e reais.
- `CarrySelfAdjointOperator/CompletedNativeEntireComparison.lean`: comparação inteira, derivada nos inteiros pares, limites de crescimento, contradição de graus e teorema incondicional.
- `CarrySelfAdjointOperator/CompletedNativeSemidefiniteHardyGate.lean`: gate adicional que usa a não recorrência incondicional.
- `CarrySelfAdjointOperator/CompletedNativeNonrecurrenceUnconditionalAudit.lean`: `#check` e auditorias de axiomas das declarações novas.

## Verificação e axiomas

`lake build --wfail CarrySelfAdjointOperator.CompletedNativeNonrecurrenceUnconditionalAudit` concluiu com sucesso (9.634 jobs), incluindo `CompletedNativeEntireComparison`, o gate e a auditoria. O output de `#print axioms` dos teoremas centrais lista somente `propext`, `Classical.choice` e `Quot.sound`. O checkpoint será atualizado com o SHA do commit e o link do PR após a publicação.

Não foram adicionados axiomas, `sorry` ou `admit` nos arquivos da entrega. A declaração explícita de positividade é mais forte do que a não anulação estritamente necessária na contradição e atende ao enunciado aritmético do prompt.

## Hipóteses abertas

- A não negatividade da energia de fronteira continua sendo uma premissa externa do gate PSD→PD.
- Nenhuma energia, positividade de Hankel, RH ou infinitude de zeros reais foi concluída a partir desta missão.
- O teorema continua estritamente sobre ausência de relação finita; não é apresentado como teorema sobre zeros.
