# Checkpoint 004 — cinco campos e doze canais tipados

Data: 2026-09-16

## Módulos Lean compilados

- `CarrySelfAdjointOperator.FiveFieldCapstoneMinimal`;
- `CarrySelfAdjointOperator.FiveFieldCapstoneDynamicsMinimal`;
- `CarrySelfAdjointOperator.FiveFieldCapstoneChannels`.

Validação:

```text
lake build CarrySelfAdjointOperator.FiveFieldCapstoneMinimal
lake build CarrySelfAdjointOperator.FiveFieldCapstoneDynamicsMinimal
lake build CarrySelfAdjointOperator.FiveFieldCapstoneChannels
```

Todos os três builds passaram.

## Conteúdo fechado

1. As matrizes `R3` e `RS` do capstone foram verificadas contra os readouts
   coordenados.
2. As identidades de transporte dos jatos Green misto e one-variable foram
   verificadas por álgebra complexa.
3. `FiveScalarFieldState` empacota exatamente os cinco campos escalares nas
   doze posições de canal exigidas pelo capstone.
4. `FiveFieldReadoutBridge` nomeia a única ponte final entre o tensor físico e
   o readout.

## Estado atual da prova

A camada finito-dimensional e a camada de transporte estão formalizadas. O
que continua aberto não é uma reorganização de sinais ou índices: é provar,
a partir das definições analíticas/RH dos artefatos, a proposição
`FiveFieldReadoutBridge`. Os audits numéricos apenas conferem essa ponte no
ponto físico e não devem ser usados como prova.

## Próximo teorema mínimo

Separar a ponte em duas obrigações, para que o próximo bloqueio fique
diagnosticável:

- uma decomposição física `cubicTauTensor = endpoint + GreenBlock + StokesBlock`;
- um crosswalk que identifica os seis canais Green e os seis canais Stokes
  com `FiveScalarFieldState.toChannelState`.

Se os artefatos não contiverem essas duas identidades em forma simbólica, o
resultado correto será um relatório de lacuna, não um axioma introduzido para
fazer o build passar.
