# Checkpoint 009 — limite honesto da formalização do capstone

Data: 2026-09-16

## O que está compilado

A cadeia algébrica construída a partir das notas agora contém:

1. `FiveFieldCapstoneMinimal`: estado de canais, matrizes `R3` e `RS`,
   readouts e soma endpoint + Green + Stokes;
2. `FiveFieldCapstoneDynamicsMinimal`: transporte dos jatos Green misto e
   dos dois sistemas one-variable;
3. `FiveFieldCapstoneChannels`: empacotamento dos cinco campos escalares nos
   doze canais;
4. `FiveFieldCapstoneBridgeMinimal`: separação da ponte física nas duas
   proposições mínimas `FiveFieldPhysicalDecomposition` e
   `FiveFieldChannelCrosswalk`;
5. `FiveFieldStokesReadoutAlgebra`: polarização cúbica exata do bloco
   Stokes-normal;
6. `FiveFieldStokesCumulativeAlgebra`: linearidade dos três cumulantes sob
   `v₁ f₁ + v₂ f₂`;
7. `FiveFieldStokesCumulativeReadout`: identificação algébrica do readout dos
   seis canais com o campo misto de uma direção `(v₁,v₂)`;
8. `FiveFieldStokesAdjointPoleAlgebra`: obstrução finito-dimensional para
   polos adjuntos em resíduos quadrado-zero.

Os módulos novos foram verificados com `lake build --wfail` e com
`lake env lean`. Os theorems auditados retornam somente

`[propext, Classical.choice, Quot.sound]`.

## O bloqueio real restante

O corpus de notas e os audits Python não fornece, no código Lean do
repositório:

- uma definição do tensor físico `cubicTauTensor`;
- a conexão matricial `L`, seus resíduos e sua equação adjunta;
- os funcionais radiais `Q_m(U_k)`;
- as definições analíticas dos campos `C_mix`, `C_j`, `X_j`, `S_1`, `S_2`;
- uma igualdade simbólica entre esses objetos físicos e os doze canais do
  readout.

O script `native_carry_five_field_capstone.py` lê estados e alvo numéricos de
arquivos externos e verifica uma reconstrução no ponto físico. Ele não pode
ser convertido em premissa Lean sem introduzir um axioma equivalente ao
capstone.

## Teorema mínimo que falta

O fechamento final continua sendo exatamente:

```text
FiveFieldPhysicalDecomposition ∧ FiveFieldChannelCrosswalk
```

Uma vez fornecidas essas duas identidades a partir das definições analíticas,
`cubicTauTensor_eq_fiveScalarFieldReadout_of_decomposition` fecha o theorem
capstone por composição algébrica já compilada.

## Classificação

`OUTCOME C — ponte física ainda independente.`

Não há mais um bloqueio de sinais, índices, matrizes, cumulantes ou
polarização no trecho formalizado. O próximo trabalho precisa trazer os
objetos analíticos/RH para o ambiente Lean; continuar apenas com as notas
atuais exigiria assumir a conclusão.
