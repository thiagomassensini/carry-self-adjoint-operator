# Transporte de Newton para potências logarítmicas

Esta rodada fecha a mudança triangular entre os jets de profundidade e os
jets logarítmicos na torre de uma base `p`.

Definindo

$$
E_j^{(q)}(k)=\binom{k}{j}q^k,
$$

o teorema principal é

$$
k^r q^k=
\sum_{j=0}^r S(r,j)j!E_j^{(q)}(k),
$$

onde `S(r,j)` é `Nat.stirlingSecond r j`. O coeficiente diagonal é `r!`,
portanto a transformação em qualquer prefixo finito é invertível.

No repositório, isso está em
[NewtonStirlingTransport.lean](../CarrySelfAdjointOperator/NewtonStirlingTransport.lean):

- `pow_eq_sum_stirlingSecond_descFactorial` prova a identidade de Stirling em
  números naturais;
- `pow_mul_amplitude_eq_sum_newtonJet` transporta a identidade para qualquer
  anel comutativo;
- `factorial_mul_newtonJet_eq_power_sub_lower` dá a recuperação triangular;
- `mk_power_amplitude_eq_stirling_projective` dá a mesma igualdade no anel de
  séries formais;
- `stirlingNewtonMatrix_det` e `stirlingNewtonMatrix_mulVec_bijective` provam
  a invertibilidade exata do frame finito;
- `stirlingNewtonMatrix_mulVec_newtonJet` mostra a ação sobre os jets reais.

## Forma nativa na torre `p^k`

Usando a amplitude crítica já formalizada,

$$
q_p=\operatorname{primeCarryAmplitudeRatio}(p)=p^{-1/2},
$$

o teorema `tower_log_power_criticalAmplitude_eq_stirling_newtonJet` prova:

$$
(\log(p^k))^r\,p^{-k/2}
=
(\log p)^r
\sum_{j=0}^r S(r,j)j!E_j^{(q_p)}(k).
$$

O fator `log p` é conservado explicitamente; não há divisão por ele. A
profundidade `k`, a ordem `r` e o índice horizontal dos slopes permanecem
objetos distintos.

## O que isso fecha e o que não fecha

O transporte algébrico entre as duas escolhas de frame está fechado para toda
ordem e para todo prefixo finito. A série `Y_q^r(1+Y_q)` continua sendo a
coordenada projetiva já existente, com a dilatação `X ↦ qX`.

Isso ainda não prova que a mudança de frame seja unitária para a métrica do
Hilbert, nem que o Gram Newton seja o Gram dos momentos nativos. Também não
identifica o índice de profundidade com a altura espectral e não acrescenta
hipóteses sobre zeros ou resolventes.

## Auditoria

[NewtonStirlingTransportAudit.lean](../CarrySelfAdjointOperator/NewtonStirlingTransportAudit.lean)
imprime os axiomas dos nove resultados centrais. O módulo foi conectado ao
agregador principal, `Audit.lean` e `KernelConstructionAudit.lean`.
