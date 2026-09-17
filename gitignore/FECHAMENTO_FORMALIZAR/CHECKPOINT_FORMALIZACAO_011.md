# Checkpoint 011 — dualidade de endpoint em toda ordem, kernel-checked

Data: 2026-09-16

## Entrega

Novo módulo:
`CarrySelfAdjointOperator/FiveFieldChiralEndpointRecurrence.lean`.

São definições concretas da recorrência, não estruturas que exigem a
identidade final como campo:

- `twoJumpHomogeneousMoment t1 t2 u0 u1`;
- `twoJumpMomentF t1 t2`, com dados iniciais `(1,0)`;
- `twoJumpMomentG t1 t2`, com dados iniciais `(0,1)`;
- `recurrenceEndpointPolynomial x`, com
  `E_0=1`, `E_(m+1)=(m+1)E_m+x^(m+1)`.

Os nomes `MomentF`/`MomentG` designam os coeficientes `f_m`/`g_m` das notas;
não designam o fator de carta nem a característica do operador.

## Sete teoremas provados

1. `recurrenceEndpointPolynomial_eq_factorial_sum`:
   `E_m(x) = m! * ∑_(r=0)^m x^r/r!`.
2. `recurrenceEndpointPolynomial_initial_residual`: o resíduo em `m=0`
   é `(x-t1)(x-t2)`.
3. `recurrenceEndpointPolynomial_residual`: em `m=n+1`, o resíduo é
   `x^(n+1)(x-t1)(x-t2)`.
4. `twoJumpHomogeneousMoment_eq_basis`: quaisquer dados iniciais são
   reconstruídos por `u0*f_m + u1*g_m`.
5. `twoJumpHomogeneousMoment_eq_endpoint`: em qualquer dos dois endpoints,
   a recorrência com dados `(1,x+1)` coincide com `E_m(x)`.
6. `twoJumpMoment_endpoint_duality`:
   `f_m + (x+1)*g_m = E_m(x)` para `x=t1` ou `x=t2`, para todo `m`.
7. `twoJumpMoment_projected_endpoint_duality`: para qualquer conjunto finito
   de índices e coeficientes complexos,
   `∑ r_m*f_m + (x+1)*∑ r_m*g_m = ∑ r_m*E_m(x)`.

Não se supõe `t1 ≠ t2`. O passo algébrico também vale quando coincidem.
Não há truncamento de ordem, ajuste numérico, axioma físico, `sorry`, ou
dependência matemática de zeta/Xi nestes enunciados/provas.

## Validação

Executados com sucesso:

```bash
lake env lean CarrySelfAdjointOperator/FiveFieldChiralEndpointRecurrence.lean
lake build --wfail CarrySelfAdjointOperator.FiveFieldChiralEndpointRecurrence
lake env lean gitignore/FECHAMENTO_FORMALIZAR/FiveFieldChiralEndpointRecurrenceAxioms.lean
```

O build do alvo terminou sem avisos. A auditoria inclui os valores iniciais
`f_2`, `g_2`, `E_2`, os dois endpoints e o caso coincidente.

`#print axioms` dos sete teoremas retornou, em todos os casos:

```text
[propext, Classical.choice, Quot.sound]
```

Os únicos ajustes da prova foram comutatividade no caso `E_1` e indicar
explicitamente o índice `(m+1)` na reescrita da soma fatorial. Não houve
correção matemática das notas neste trecho.

## O que isto fecha — e o que não fecha

Fecha o núcleo algébrico das seções 1–3 de
`CHIRAL_ENDPOINT_THEOREM_FROM_DARBOUX_ORTHOGONALITY.md`.

Ainda não foi provada aqui a representação por integral de cauda, a ponte
entre caudas e direções de amplitude, nem a realização concreta do pullback
simplético. Portanto não é o fechamento completo do capstone nem uma prova
da identidade física de endpoint diagonal.

O diagnóstico correto é: uma etapa simbólica concreta foi retirada das
obrigações restantes. A frase final do checkpoint 009 continua substituída
pela ressalva do checkpoint 010.

## Próximo passo mínimo, já nas mesmas notas

Formalizar a representação de `E_m` pela cauda exponencial, para `x : ℝ`:

```lean
recurrenceEndpointPolynomial (x : ℂ) m =
  (Real.exp x : ℂ) *
    ∫ s in Set.Ioi x, (Real.exp (-s) : ℂ) * (s : ℂ) ^ m
```

Depois aplicar linearidade de uma soma finita para obter literalmente
`α_R+(x+1)β_R = exp(x) * ∫_(x,∞) exp(-s)R(s) ds` nos endpoints.
Isso prepara a ponte de caudas sem assumir ortogonalidade Darboux nem
introduzir Xi na construção. A identificação com o polinômio físico e a
identidade simplética continuam sendo obrigações distintas.

## Preservação do checkout

Nenhum arquivo Lean anterior foi editado nesta etapa. A alteração preexistente
em `CompletedNativeCameraTfvdGreenFrameDefectCrosswalk.lean` e os demais
arquivos não rastreados permanecem intocados.

O arquivo `FiveFieldStokesReadoutAlgebra.lean`, produzido na etapa anterior,
ainda estava fora do controle de versão embora fosse importado pelos módulos
de cumulantes já registrados. Ele será incluído sem alteração no checkpoint
Git desta retomada para preservar essa dependência de fonte.
