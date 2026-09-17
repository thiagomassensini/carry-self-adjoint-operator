# Checkpoint 006 — linearidade dos canais cumulativos de Stokes

## Estado

O módulo

`CarrySelfAdjointOperator/FiveFieldStokesCumulativeAlgebra.lean`

agora compila com `lake build --wfail`.

## Resultado formal

Foi definida a extensão sintática

`stokesCumulativeChannels (f : ℝ → ℂ) (t1 t2 : ℝ) : Fin 3 → ℂ`

com os três cumulantes

1. `∫ Iic 0, f`;
2. `∫ Iic 0, f + ∫ Ioc 0 t1, f`;
3. `∫ Iic 0, f + ∫ Ioc 0 t1, f + ∫ Ioc t1 t2, f`.

O theorem

`stokesCumulativeChannels_linear`

prova, para campos globalmente integráveis `f1`, `f2` e escalares complexos
`v1`, `v2`, a identidade exata

`channels (v1*f1 + v2*f2) = v1 • channels f1 + v2 • channels f2`.

## Correções Lean relevantes

- `integral_add` exige a integrabilidade dos campos já escalados;
  ela é obtida por `Integrable.const_mul` depois da restrição ao conjunto.
- Cada integral dentro do vetor foi parentizada explicitamente; sem isso,
  a vírgula da notação de integral absorvia o próximo somando no integrando.

## Limite matemático preservado

Este checkpoint formaliza somente linearidade dos cumulantes. Ele não afirma
que os campos concretos das notas são integráveis, não identifica os campos
com objetos do repositório e não cria uma ponte física implícita.

## Próxima obrigação mínima

Construir uma ponte algébrica entre dois pares de campos escalares e os seis
canais `S10,S11,S12,S20,S21,S22`, usando a linearidade acima e o theorem
`stokesCumulativeReadout_eq_cubicPolarization`. A igualdade desses campos com
as quantidades físicas ainda precisa ser uma hipótese/ponte explícita.
