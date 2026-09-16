# Checkpoint 015 — reconstrução tangente concreta validada

Data: 2026-09-16

## Retomada e fonte

Continuação direta do checkpoint 014, usando `scalar_from_H` em
`native_carry_chiral_endpoint_theorem.py` e a seção 4–5 de
`CHIRAL_ENDPOINT_THEOREM_FROM_DARBOUX_ORTHOGONALITY.md`.

Novo módulo: `CarrySelfAdjointOperator/FiveFieldTangentReconstruction.lean`.

Para `T0,T1,T2`, as fórmulas implementadas são literalmente:

```
dA1 = (t2*T1-T2)/(t1*(t2-t1))
dA2 = (T2-t1*T1)/(t2*(t2-t1))
dA0 = T0-dA1-dA2
```

Os dois round trips recuperam exatamente os três coeficientes e os três
resíduos, sob `t1 != 0`, `t2 != 0`, `t2 != t1`. A equivalência de igualdade
estabelece unicidade. Os dois round trips e a unicidade kernel-checkaram.

Também implementados os três estágios lineares concretos:

1. os comutadores que levam `H0,H1,H2` a `T0,T1,T2`;
2. reconstrução e passagem às quatro variações coordenadas;
3. o funcional bilinear `u^T Omega w / 2`, sem conjugação.

Os denominadores das coordenadas são totalizados em Lean. Interpretar
`dA01/A01` como uma derivada logarítmica exige não-nulidade das entradas
do chart; não se afirmou essa interpretação sem suas hipóteses.

## Continuação em validação

`FiveFieldTangentTailReadout.lean` passa a integral de Bochner por esse mapa
concreto, prova integrabilidade das densidades polinomiais finitas e compõe
com a identidade de endpoint do checkpoint 012.

Isso ainda NÃO identifica o resíduo reconstruído com a derivada efetiva da
família física. A identidade `JD^T Omega_native JD = kappa Omega0` também
continua separada. Não há hipótese nova afirmando essas conclusões.

## Teste do operador fornecido

Executado o novo anexo `native_carry_height_moment_jacobi_operator_pure_native.py`
com ordem 2, 80 dígitos de trabalho, 35 dígitos de saída, 32 amostras por raio,
raios 0.4 e 0.32, cutoff 4, dois workers e `--compare-count 0`.

SHA256 do anexo:
`906a6511dacccdf2798efbdd53d62afa4aafef613d65319b1057f244ebc53790`.
Uma cópia byte a byte foi preservada neste diretório com o mesmo nome;
o SHA256 foi comparado após a cópia.

Resultados guardados em `native_operator_camera2_order2_audit.json` e
`native_operator_camera3_order2_audit.json`. Os quatro momentos e as duas
alturas registradas são textualmente iguais entre câmeras 2 e 3:

```
14.606864893060023368967322128399102
48.64801900795257966513353886652019
```

A discrepância relativa máxima entre os raios é cerca de `2.64e-53`.
Nenhuma consulta de referência clássica foi executada (`compare-count=0`).
Não é prova de invariância em todas as câmeras, positividade all-order,
realização da energia TFVD ou convergência espectral. O próprio script
marca explicitamente o crosswalk TFVD como não assumido.

## Validação e Git

O módulo de reconstrução passou em `lake build --wfail`.
`FiveFieldTangentReconstructionAxioms.lean` auditou os seis theorems e as
quatro definições de mapas lineares com suas provas: somente
`[propext, Classical.choice, Quot.sound]`, sem `sorry`.

O módulo de cauda ainda está em validação e fica FORA deste commit.
O primeiro erro foi a instância `ContinuousENorm` das funções com valores
matriciais; uma instância local sobre a função finita equivalente resolveu
esse ponto. Seguiu-se um limite de elaboração na integrabilidade.

Não houve alteração de arquivos Lean preexistentes.
Após confirmação explícita de destino e conteúdo pelo usuário, o push dos
dez commits anteriores passou: `8f3e824..fd2bcec`, na branch
`agent/c3-native-hilbert-trace-glue-crosswalk` de
`github.com/thiagomassensini/carry-self-adjoint-operator`.
