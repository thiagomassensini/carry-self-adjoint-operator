# Jet em toda ordem com o resto preservado

## Resultado desta rodada

Foram formalizados 13 teoremas em `AllOrderLogJetLedger.lean`. O resultado principal usa a característica reduzida e os momentos nativos já existentes. Para qualquer família finita de parâmetros complexos, defina apenas na notação desta explicação

$$
P_S(u)=\prod_{i\in S}(1-a_i u),
\qquad
R_S(u)=\frac{\Phi(u)}{P_S(u)},
\qquad
\Phi=\texttt{completedNativeEvenCharacteristic}.
$$

Então, para todo `n : ℕ`, o Lean prova

$$
\boxed{
h_n=\sum_{i\in S}a_i^{n+1}
-\frac{\left.\partial_u^n\operatorname{logDeriv}R_S(u)\right|_{u=0}}{n!}.
}
$$

Nome completo:

```lean
CarrySelfAdjointOperator.AllOrderLogJet.nativeMoment_eq_finiteFactors_add_remainder
```

A igualdade é complexa, com o momento real canônico incluído em `ℂ`. Não há um novo operador, uma nova Jacobi ou uma redefinição dos momentos.

Os parâmetros `a_i` são livres na identidade algébrica. Não foram obtidos de uma lista de zeros, calibrados por `h₀`, nem declarados como dados espectrais ou como o cutoff de uma câmera. A liberdade desses parâmetros faz o resto indispensável: a igualdade não certifica que uma escolha particular seja a medida procurada.

O produto vale 1 no centro. Sua não anulação numa vizinhança é demonstrada; a divisão é localmente regular. O resto é o quociente concreto `Φ/P_S`, não uma função desconhecida postulada para fechar a igualdade.

## Transporte do jet completo

Para germes analíticos `A,B` normalizados por `A(0)=B(0)=1`, o teorema

```lean
AllOrderLogJet.unit_logJet_mul
```

prova, para todo `m : ℕ`,

$$
\partial^{m+1}\log(AB)(0)
=\partial^{m+1}\log A(0)+\partial^{m+1}\log B(0).
$$

A prova controla a ramificação de `Complex.log` numa vizinhança de 1 antes de diferenciar. Não usa uma identidade global irrestrita para o logaritmo complexo de produtos. A ordem zero dos logaritmos normalizados vale zero diretamente.

Esse lema serve ao transporte por fatores analíticos normalizados de roda/câmera. Ele não refaz a prova aritmética de que a atualização de uma roda possui determinado fator, nem a identificação nativa já presente nos módulos de câmera.

Para o produto finito específico, a avaliação explícita é

$$
\partial^{m+1}\log P_S(0)=-m!\sum_{i\in S}a_i^{m+1}.
$$

Teorema: `AllOrderLogJet.finiteFactor_logJet_iterated`.

## Cadeia reutilizada

Na prova do resultado nativo:

1. `completedNativeEvenCharacteristic_analyticAt`;
2. `completedNativeEvenCharacteristic_zero_ne_zero`;
3. `completedNativeLogDerivative`, a resposta reduzida já existente;
4. `completedNativeLogDerivativeTaylorCoefficient_eq_canonical`.

Da mathlib fixada pelo projeto:

- `logDeriv_prod`, `logDeriv_div` e `logDeriv_mul`;
- `iter_deriv_inv_linear`;
- transporte de derivadas iteradas por igualdade eventual;
- `iteratedDeriv_fun_sum` e as regras de soma, diferença e constante;
- `HasDerivAt.clog` e abertura do plano cortado do logaritmo complexo.

A extração TFVD em todas as ordens permanece no módulo existente `CompletedNativeTfvdWronskianMoments.lean`. A correção completa de câmera permanece em `CompletedC3AllOrderChartResponseCorrection.lean`.

Também foi conferido o módulo fixado `CPFormal.Analytic.CpMinimalProvenanceQuotient`: `ker_minimalProvenanceJointMap` e `minimalProvenance_factorization` já demonstram a fatorização pelo quociente que preserva `(Q,A)`. Nenhum quociente foi reconstruído nesta rodada.

## Correção do ledger de vizinhos

`AllOrderLogJet.reciprocalLedger_split` prova a decomposição exata para todo expoente e quaisquer conjuntos finitos `T ⊆ S`:

$$
\begin{aligned}
\sum_{i\in S}\left[(x-\gamma_i)^{-m}+(x+\gamma_i)^{-m}\right]
={}&\sum_{i\in T}(x-\gamma_i)^{-m}\\
&+\sum_{i\in T}(x+\gamma_i)^{-m}\\
&+\sum_{i\in S\setminus T}
\left[(x-\gamma_i)^{-m}+(x+\gamma_i)^{-m}\right].
\end{aligned}
$$

Na assinatura Lean usa-se a potência natural da inversa, inclusive para `m=0`. A identidade é algébrica; uma aplicação a distâncias analíticas exige separadamente que as distâncias relevantes não sejam nulas.

Logo, ao selecionar os dois vizinhos por `T`, seus termos refletidos precisam permanecer no ledger. O teorema `reciprocalGap_parity` conserva o sinal do vizinho direito em cada paridade.

Os valores exatos da correção nos exemplos de ordens 6 e 7 também foram verificados pelo kernel:

```text
reflectedNeighborCorrection_six:
  1/3^6 + 1/5^6 = 16354/11390625

reflectedNeighborCorrection_seven:
  1/3^7 + 1/5^7 = 80312/170859375
```

`reflectedNeighborCorrection_pos` mostra que a correção dos dois refletidos é positiva para localizações reais positivas, em qualquer ordem. Esse sinal é o da correção local, não o do Gram nativo completo.

## O que permanece matematicamente aberto nesta rota

A nova identidade não permite apagar `R_S` nem atribuir sinal aos seus coeficientes. Ela também não promove um produto finito a produto infinito sobre todo o espectro.

Para a realização quiral existente, a obrigação continua sendo

```lean
CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive
```

isto é, para cada tamanho finito, contratividade eventual para todas as combinações dos vetores nativos na grade radial. A passagem de semidefinição positiva à versão estrita continua usando a não degenerescência já nomeada no projeto.

O avanço desta rodada é a identidade em ordem arbitrária com contribuição restante explícita. Não é uma nova prova de sinal, um novo controle uniforme de cauda, ou a identificação de uma medida geométrica positiva.

## Arquivos e validação

- Novo módulo: `CarrySelfAdjointOperator/AllOrderLogJetLedger.lean`.
- Novo audit: `CarrySelfAdjointOperator/AllOrderLogJetAudit.lean`.
- Integração em `CarrySelfAdjointOperator.lean` e `CarrySelfAdjointOperator/Audit.lean`.
- Registro de validação: `research/all-order-logjet-2026-09-05/validation.txt`.
- Auditoria dos axiomas: `research/all-order-logjet-2026-09-05/axioms.log`.

Base desta rodada: `9a87c27553fc08832415cc42946a8d5356ec418f`.
Branch: `agent/all-order-logjet-ledger`.
Os pins e o toolchain foram preservados. O resultado permanece em branch separada, pois a identificação positiva em toda ordem não foi concluída.

## Proveniência da nota

- `CRONOLOGIA_BRACKET_AOS_MOMENTOS_19_21_JUL_2026.md`, leitura integral anterior; SHA256 `f22e4736ab22d4ada80f122e68bd1e15cd9befc824979dd2597ef167ac8ee11e`.
- `c2_canon_volumes_I_II/c2_canon_green_logjet_proximo_zero_volume_II.md`, Parte VII, §§6–10 e §§14–15; SHA256 `d02aa2e84fba203894c65b7983e9ff16f531353da17d9093e8769e225caf8316`.

Os rótulos antigos de pendências foram confrontados com as declarações atuais. Os documentos originais não foram alterados.
