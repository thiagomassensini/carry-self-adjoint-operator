# Checkpoint 008 — obstrução algébrica de polo adjunto

## Estado

O módulo

`CarrySelfAdjointOperator/FiveFieldStokesAdjointPoleAlgebra.lean`

compila com `lake build --wfail`.

## Resultado formal

Para matrizes complexas `2 × 2`, foram provados:

- `matrixCommutator_smul_right`;
- `matrixCommutator_two_eq_neg_sandwich` sob `A * A = 0`;
- `matrixCommutator_three_nilpotent`:
  `ad_A^3(B) = 0` quando `A² = 0`;
- `matrixCommutator_nonzero_eigenvector_vanishes`:
  se `ad_A(B) = r • B` e `r ≠ 0`, então `B = 0`.

O último theorem é exatamente o núcleo finito-dimensional do argumento da
nota `STOKES_ADJOINT_RATIONAL_OBSTRUCTION.md`: o coeficiente principal de um
polo de ordem `r` teria de ser um autovetor não nulo de `ad_A` com autovalor
`r`, mas para um resíduo quadrado-zero isso é impossível.

## Limite matemático preservado

Ainda não foram introduzidos conexão `L`, resíduos concretos, a equação
adjunta global ou os polinômios `Q_k`. Portanto o resultado não afirma ainda
que os campos Stokes do problema são não-endpoint; ele apenas fornece o lema
exato que essa redução deverá usar.

## Próximo bloqueio

Para subir deste lema ao resultado racional completo, o repositório precisa
fornecer em Lean:

1. a conexão matricial e seus resíduos;
2. a decomposição local em polos;
3. a noção de solução racional da equação adjunta;
4. o controle no infinito que limita o grau.

Esses objetos não aparecem nas notas como definições Lean reutilizáveis.
