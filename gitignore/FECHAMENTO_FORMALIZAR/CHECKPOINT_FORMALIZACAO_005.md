# Checkpoint 005 — ponte final separada em dois teoremas

Data: 2026-09-16

## Módulo

`CarrySelfAdjointOperator.FiveFieldCapstoneBridgeMinimal`

Validação concluída sem warnings fatais:

```text
lake build --wfail CarrySelfAdjointOperator.FiveFieldCapstoneBridgeMinimal
```

## Interface mínima da lacuna

O módulo define:

- `FiveFieldPhysicalDecomposition`: o tensor físico é endpoint mais os dois
  readouts;
- `FiveFieldChannelCrosswalk`: os vetores físicos de canais coincidem com o
  empacotamento dos cinco campos;
- `cubicTauTensor_eq_fiveScalarFieldReadout_of_decomposition`: as duas
  obrigações implicam o capstone;
- `FiveFieldReadoutBridge_of_decomposition_and_crosswalk`: a mesma composição
  vista como a ponte nomeada do capstone.

## Diagnóstico final do corpus

Nenhuma nota ou artefato lido contém uma definição simbólica Lean do tensor
físico nem as duas igualdades acima. O Python `native_carry_five_field_capstone.py`
carrega estados e alvo de arquivos externos e verifica uma reconstrução
numérica; isso não fornece premissas para `FiveFieldPhysicalDecomposition` nem
para `FiveFieldChannelCrosswalk`.

Logo os teoremas mínimos restantes são exatamente esses dois. O próximo passo
honesto exige trazer para o repositório as definições analíticas dos campos,
do tensor da tau e do crosswalk RH/FIK. Sem isso, qualquer prova do capstone
final teria de introduzir um axioma equivalente à conclusão.

## Estado persistente

Até aqui estão compilados e checkpointados:

1. readout matricial exato;
2. transporte diferencial de jatos;
3. embalagem dos cinco campos em doze canais;
4. composição final condicional;
5. decomposição explícita da ponte em duas obrigações.
