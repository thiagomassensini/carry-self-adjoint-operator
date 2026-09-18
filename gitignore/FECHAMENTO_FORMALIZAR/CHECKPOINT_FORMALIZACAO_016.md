# Checkpoint 016 — cauda pelo readout tangente concreto

Data: 2026-09-16

Novo módulo: `CarrySelfAdjointOperator/FiveFieldTangentTailReadout.lean`.
Continua a reconstrução do checkpoint 015, commit `064a158`.

## Resultados

O funcional `L = twoJumpScalarFromMoments kappa t1 t2 A u` não é recebido
como hipótese: é a composição explícita dos comutadores, inversão dos
coeficientes de Laurent, variações coordenadas e `u^T Omega w / 2`.

1. `twoJumpScalarFromMoments_integral`: a integral de Bochner comuta com L,
   para densidades integráveis. A continuidade vem da dimensão finita.
2. `twoJumpPolynomialMomentDensity_integrable`: integrabilidade efetiva de
   `sum_m exp(-t)*t^m • P_m`, para qualquer família finita de coeficientes
   com valores em triplas de matrizes 2x2.
3. `twoJumpScalarFromMoments_polynomial_tail`: o polinômio escalar projetado
   é integrado pelo mesmo L da reconstrução, não por um funcional abstrato.
4. `twoJumpMoment_endpoint_eq_reconstructed_tail`: composição da dualidade
   de endpoint já provada com a integral da densidade matricial.
5. `twoJumpProjectedTail_eq_reconstructed_pairing`: normalização exata
   `2*i/pi`, incluindo o sinal negativo da densidade projetada nas notas.

## Igualdade precisa do quinto theorem

Para `H = integral_x^infty sum_m exp(-t)*t^m • P_m`, seja

```
v = twoJumpResidueCoordinateLinear A
      (twoJumpTangentResiduesLinear kappa t1 t2 A H)
```

Então:

```
integral_x^infty exp(-t) *
  (4/(pi*i) * sum_m L(-P_m)*t^m)
= (2*i/pi) * (u0*v2 + u1*v3 - u2*v0 - u3*v1).
```

A constante foi derivada da definição concreta `L(H)=Omega(u,v)/2` e de
`i^-1=-i`. Não há conjugação nem mudança da orientação da forma bilinear.
Não foi introduzida uma hipótese equivalente à conclusão física.

## Fronteira exata que continua aberta

`v` é a tangente RECONSTRUÍDA da densidade. Falta demonstrar que ela é a
derivada efetiva em amplitude da família física. Não basta renomeá-la.

Fontes concretas para a próxima formalização:

- `native_carry_RH_jacobian_analytic_lab.py`, `state_at_n`: recorrência
  racional dos seis dados `R0,R1,R2,r0,r1,r2`;
- `native_vector`: `[log(R1/R0),log(R2/R0),r1,r2]`;
- `E_int` e `eta_column`: densidades matriciais e a mesma reconstrução
  agora formalizada;
- colunas de amplitude do Jacobiano: derivadas de `native_vector` em
  `a1,a2` (calculadas por `mp.diff` no script, não uma prova Lean);
- correção Darboux: `JD[:,2]=E1+(4/121)*C[:,1]`,
  `JD[:,3]=E2-(4/121)*C[:,0]`.

Depois da identificação tangente, ainda é preciso provar o pullback
`JD^T Omega_native JD = kappa Omega0` para essa família concreta.
A existência de fórmulas e audits nas notas não foi confundida com a
formalização dessas duas obrigações. Tampouco se concluiu que sejam
impossíveis ou que precisem de axiomas.

Todos os novos objetos são matrizes finitas, mapas lineares, recorrências
de endpoint e integrais exponenciais. Não foi usada uma função clássica
como definição do operador nativo ou como atalho para essas identidades.

## Engenharia e validação

A instância local `ContinuousENorm` explicita que a tripla matricial é
uma função finita `Fin 3 -> Fin 2 -> Fin 2 -> Complex`. Não cria um carrier
matemático novo. Foi necessário um orçamento local maior de elaboração
para a prova de integrabilidade; as fórmulas não mudaram.

Validação final concluída:

- `lake env lean CarrySelfAdjointOperator/FiveFieldTangentReconstruction.lean`: passou;
- `lake env lean CarrySelfAdjointOperator/FiveFieldTangentTailReadout.lean`: passou;
- `lake build --wfail CarrySelfAdjointOperator.FiveFieldTangentReconstruction
  CarrySelfAdjointOperator.FiveFieldTangentTailReadout`: passou sem avisos,
  incluindo a versão final do quinto theorem;
- `FiveFieldTangentTailReadoutAxioms.lean`: os cinco theorems retornaram
  somente `[propext, Classical.choice, Quot.sound]`;
- juntamente com o checkpoint 015, são 11 novos theorems auditados e quatro
  definições de mapas lineares também auditadas, sem `sorry` ou novos axiomas.

Esses comandos validam os novos alvos e suas dependências, não constituem
afirmação de build global de todo o checkout nem acompanhamento do CI remoto.

Nenhum arquivo Lean preexistente foi alterado. A modificação anterior de
117 linhas em `CompletedNativeCameraTfvdGreenFrameDefectCrosswalk.lean`
continua fora dos commits, assim como os arquivos soltos preexistentes.
