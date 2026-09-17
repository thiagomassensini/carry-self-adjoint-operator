# Checkpoint 017 — interface mínima da tangente efetiva

Data: 2026-09-16

Novo módulo: `CarrySelfAdjointOperator/FiveFieldTangentWitnessBridge.lean`.

## O bridge fechado

Foi formalizada a interface exata entre os coeficientes Laurent da variação
efetiva e a reconstrução concreta dos checkpoints 015–016.

Sob `t1 != 0`, `t2 != 0` e `t2 != t1`, se um candidato `dA` satisfaz

```
twoJumpResidueMoments t1 t2 dA
  = twoJumpTangentLaurentCoefficients kappa t1 t2 A H,
```

então:

```
twoJumpTangentResiduesLinear kappa t1 t2 A H = dA.
```

Aplicando as coordenadas nativas e o funcional bilinear, também vale

```
twoJumpScalarFromMoments kappa t1 t2 A u H
  = twoJumpRadialPairingLinear u
      (twoJumpResidueCoordinateLinear A dA).
```

Há ainda a versão que recebe diretamente o vetor de quatro coordenadas.
Assim, quando a análise variacional fornecer os três coeficientes da
derivada da família física, não será necessário reabrir a fórmula dos
denominadores nem repetir a álgebra de inversão.

## O que o bridge não afirma

O witness `hLaurent` ainda não é produzido pelo estado `state_at_n`. As
notas e scripts definem essa família finita numericamente/analiticamente,
mas não há declaração Lean existente para `state_at_n`, `native_vector` ou
para a equação variacional `delta L = X' + [X,L]`. Portanto não foi criada
uma definição que apenas renomeasse a reconstrução como derivada física.

O próximo lema mínimo concreto é a formalização de uma família finita de
estado (começando em um `n` fixo) e a prova, sob não-nulidade explícita, de
que sua derivada em `a1`/`a2` satisfaz esse witness. Depois disso, a ponte de
cauda do checkpoint 016 poderá ser instanciada com o vetor efetivo.

## Validação

```
lake env lean CarrySelfAdjointOperator/FiveFieldTangentWitnessBridge.lean
lake build --wfail CarrySelfAdjointOperator.FiveFieldTangentWitnessBridge
lake env lean gitignore/FECHAMENTO_FORMALIZAR/FiveFieldTangentWitnessBridgeAxioms.lean
```

Resultado: os três theorems retornam somente
`[propext, Classical.choice, Quot.sound]`.

Nenhum arquivo Lean preexistente foi editado; a alteração de 117 linhas em
`CompletedNativeCameraTfvdGreenFrameDefectCrosswalk.lean` continua fora.
