# Luna Fonte C2 — checkpoint A

Data: 15/11/2026
Base: `carry-self-adjoint-operator` main, `c999ce41ccdec0ff194e7969bf1f7f329d374d3a`
Branch: `codex/luna-fonte-c2-error-transport-20261115`

## Resultado compilado

O módulo `CarrySelfAdjointOperator/C2SourceFormErrorTransport.lean` formaliza
uma comparação finita de formas para sequências reais `m, mt`, qualquer shift
`s`, dimensão `N` e vetor complexo `x`. Sob

```lean
∀ j, |m j - mt j| ≤ (j+1) * 16^(j+1) * η
```

prova-se

```lean
complexSourceMomentForm m s N x ≥ complexSourceMomentForm mt s N x -
  16^(s+1) * η * ((s+1) * (c2ErrorA0 x)^2 + 2*c2ErrorA0 x*c2ErrorA1 x)
```

com `A0 = Σ 16^i ‖xᵢ‖` e `A1 = Σ i·16^i ‖xᵢ‖`. A forma usa
`Re(conj xᵢ * xⱼ)` e a prova mantém todos os termos cruzados. O teorema
`complexSourceMomentForm_ofReal` identifica a forma com
`sourceMomentQuadratic` para vetores reais, conectando o lema abstrato à
definição nativa existente.

O módulo e `C2SourceFormErrorTransportAudit.lean` compilam com
`-DwarningAsError=true`. A auditoria transitiva de ambos os teoremas imprime
somente `[propext, Classical.choice, Quot.sound]`; não há `sorry`, `admit` nem
axioma novo.

## O que não foi fechado

O resultado acima é o Lema 3 abstrato. Ele não prova que a carta C2 real está
afastada de zero, não produz um aproximante `W`, e não fornece a hipótese de
erro dos coeficientes.

Na base atual, `c2FiniteChartValue` é uma soma finita. Não encontrei uma
definição Lean de `V` como a soma infinita alinhada da segunda diferença junto
com os resultados analíticos quantitativos exigidos. Assim, permanecem por
formalizar:

1. Convergência local uniforme/holomorfia dessa soma C2 no disco e
   `|V(s)-1| ≤ 14/75`.
2. Resto complexo explícito de Euler–Maclaurin para a cauda balanceada, sem
   separar as três séries divergentes.
3. Transporte do erro uniforme de `V-W` para `log V-log W` e daí para todos os
   coeficientes pares do logaritmo completado.

O próximo elo concreto é um teorema de fonte que construa `V` a partir dos
brackets C2 originais, prove sua convergência uniforme no disco e forneça a
cota `14/75`. Sem ele não há uma aplicação honesta do lema de comparação a
momentos da fonte.

## Validação reproduzível

```sh
cd /home/thlinux/worktrees/luna-fonte-c2-error-transport-20261115
lake env sh -c 'LEAN_PATH=/home/thlinux/carry-self-adjoint-operator/.lake/build/lib/lean:$LEAN_PATH lean -DwarningAsError=true --root=. -o .lake/build/lib/lean/CarrySelfAdjointOperator/C2SourceFormErrorTransport.olean CarrySelfAdjointOperator/C2SourceFormErrorTransport.lean'
```

A auditoria foi compilada da mesma forma, usando um overlay Lean temporário que
combina os `.olean` da base com o módulo novo deste worktree. O build padrão da
biblioteca inteira não foi completado: ele começou a reconstruir milhares de
módulos por não haver cache isolado no worktree. Nenhum fonte no checkout
original foi alterado.
