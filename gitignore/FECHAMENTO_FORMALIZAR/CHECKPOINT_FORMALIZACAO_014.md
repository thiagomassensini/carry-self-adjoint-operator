# Checkpoint 014 — bloco de fusão calculado das matrizes

Data: 2026-09-16

Novo módulo: `CarrySelfAdjointOperator/FiveFieldDecoratedFusionBlock.lean`.
Fontes: `FUSION_GOLDMAN_CROSS_TERM_E_OBSTRUCAO_PREREDUCAO.md` e
`native_carry_fusion_goldman_lab.py`.

## Objetos e resultados

Definidos concretamente `M(a,eta)=I+a*X(eta)` e sua inversa polinomial
`I-a*X(eta)`. Provadas as duas identidades de inversa e as duas derivadas
complexas em amplitude e decoração. Os coeficientes não são inseridos como
dados: `decoratedFusionBlock` é definido pela fórmula matricial de traço
`(1/2) trace ((M1inv*dM1)*(dM2*M2inv))`.

`decoratedFusionBlock_eq` calcula exatamente as quatro entradas desse bloco,
com linhas `(a1,eta1)` e colunas `(a2,eta2)`. Para `d=eta1-eta2`, são:

- `-d^2/2`;
- `-a2*d*(a2*d-2)/2`;
- `a1*d*(a1*d-2)/2`;
- `(a1*a2/2)*(a1*a2*d^2-2*(a1+a2)*d+2)`.

Também provados:

- `trace(M1*M2)=2-a1*a2*(eta1-eta2)^2`;
- `[M1,M2]_(0,1)=-2*a1*a2*(eta1-eta2)`;
- para reta fixa comum, o bloco é `[[0,0],[0,a1*a2]]`;
- em `a1=-8/33`, `a2=-3/11`, `eta1=eta2=0`, a entrada transversal é
  exatamente `8/121`.

São oito teoremas. Não houve alteração de sinal ou fórmula das notas.

## Distinção indispensável

O bloco é a correção de fusão **antes da redução**, sem o fator global
`kappa`. Não é uma definição da forma reduzida, nem uma identificação com
o Jacobiano da conexão física. Em particular, a matriz wild reduzida de
uma nota posterior não deve ser identificada automaticamente com este bloco.

As notas posteriores também distinguem o primeiro jato simbólico da forma
wild do audit numérico convergente da Hessiana e da identidade simplética
diferenciada. Nenhuma dessas verificações numéricas foi convertida em
hipótese Lean ou usada nestes teoremas.

## Estado acumulado desta retomada

1. Checkpoint 012: a identidade de endpoint agora é uma integral de cauda
   efetiva, para qualquer polinômio finito com coeficientes complexos.
2. Checkpoint 013: resíduo local, tangentes, coeficiente KK e obstrução
   adjunta foram formalizados para as matrizes explícitas das notas.
3. Checkpoint 014: o termo de fusão dessas matrizes também foi calculado
   exatamente, incluindo sua especialização racional.

Isso remove obrigações analíticas e matriciais concretas. Ainda não prova
o capstone físico completo.

## Próximo ponto mínimo de integração

Ainda é preciso formalizar a aplicação de reconstrução tangente da conexão
física e seu readout, usando as fórmulas `scalar_from_H` / `dA0,dA1,dA2` do
script `native_carry_chiral_endpoint_theorem.py` e a construção analítica do
Jacobiano em `native_carry_RH_jacobian_analytic_lab.py`.

Dois alvos distintos continuam explícitos:

`integral_(tj,infinito) exp(-s)*Rk(s) ds = (2*i/pi)*Omega_native(Uk,Aj)`;

`JD.transpose * Omega_native * JD = kappa * Omega0`.

O resultado de cauda já permite compor a primeira igualdade com o endpoint
assim que a realização concreta estiver tipada e provada. A álgebra local e
a fusão recém-formalizadas não substituem, por si sós, esses dois alvos.
As notas permanecem a fonte para construí-los; não foi concluído que sejam
impossíveis ou que precisem ser assumidos como axiomas.

## Validação

Validação final concluída:

- `lake env lean` dos três módulos passou;
- `lake build --wfail CarrySelfAdjointOperator.FiveFieldChiralEndpointTail
  CarrySelfAdjointOperator.FiveFieldDecoratedLeveltLocal
  CarrySelfAdjointOperator.FiveFieldDecoratedFusionBlock` passou sem avisos;
- os três arquivos `*Axioms.lean` foram reexecutados depois do build conjunto;
- os 26 teoremas desta retomada retornaram somente
  `[propext, Classical.choice, Quot.sound]`.

Os erros intermediários foram de namespace, coerção real/complexa, escolha
local de norma matricial e igualdade entre funções parcialmente aplicadas.
Não foi necessário corrigir nenhuma identidade matemática das notas nos
três trechos formalizados.

Nenhum arquivo Lean preexistente foi editado. A alteração de 117 linhas em
`CompletedNativeCameraTfvdGreenFrameDefectCrosswalk.lean` continua fora dos
commits desta tarefa, assim como os demais arquivos preexistentes não
rastreados. Os checkpoints são locais; não houve push nem execução de CI.
