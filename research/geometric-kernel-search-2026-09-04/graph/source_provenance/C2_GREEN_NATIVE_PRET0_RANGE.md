# Faixa nativa pre-T0 do coequalizer

## Resultado

`STOP_NATIVE_PRET0_GENERATOR_NOT_PERSISTED`

A auditoria foi feita na direção forward. Nenhuma seção do coequalizer foi
escolhida e nenhum endpoint pós-`T0` foi invertido. Os quatro construtores
canônicos auditados têm hashes de fonte persistidos, mas nenhum carrega ao
mesmo tempo todos os eixos

```text
p_A, tau, d_J, p_T, j, K, m, cell, corner, orientation, flags, role.
```

| Construtor | Eixos carregados | Eixos ausentes |
|---|---|---|
| `contextual_flags_for_native_cell` | K, m, cell, corner, orientation, flags, p_T, j | p_A, tau, d_J, role |
| `laplace_jordan_lift_audit` | p_A, tau, d_J, orientation | p_T, j, K, m, cell, corner, flags, role |
| `centered_coordinates` | p_A, tau, d_J | p_T, j, K, m, cell, corner, orientation, flags, role |
| `pre_sigma0_endpoint_audit` | p_T, j, cell, corner, orientation, flags | p_A, tau, d_J, K, m, role |

O ledger de flags retém `40` registros completos de
geometria de pares. Neles, porém, `d_Jordan` é literalmente o marcador
“summed over d_J|ell before endpoint”; `tau` e `p_A` não aparecem. O construtor
one-leg J/H retém `p_A,tau,d_J`, mas não retém `cell,corner,flags,role,K,m` nem
o fator de torre `p_T,j`. Compor essas duas descrições agora exigiria inventar
um join que não pertence aos construtores originais.

Consequentemente `E_native^preT0`, `R_native` e `K_native` não foram definidos.
Não foi provada nem a realizabilidade nativa do modo Möbius, nem sua exclusão.
Em particular, nenhum dos checkpoints de classificação de faixa em
`PASS_NATIVE_PRET0_RANGE_CONSTRUCTED, PASS_NATIVE_RANGE_COEQUALIZER_KERNEL_CLASSIFIED, PASS_MOBIUS_MODE_NATIVE_REALIZABLE, STOP_MOBIUS_MODE_NOT_IN_NATIVE_RANGE, PASS_NATIVE_RANGE_ELIMINATES_FREE_JH_GAUGE, PASS_NATIVE_A_DESCENDS_ON_RESTRICTED_QUOTIENT, STOP_NATIVE_A_NONZERO_ON_NATIVE_COEQUALIZER_KERNEL` foi emitido.

## Dados que faltam

- no lado dos flags nativos: `p_A`, `tau`, o valor cru de `d_J` e o papel J/H;
- no lado das features J/H: o flag C2 completo, `K=k_eff`, a fibra ímpar `m` e
  o nível de torre `p_T,j`;
- no endpoint pós-T0: a proveniência anterior ao somatório em `d_J`.

A fronteira correta é `NEEDS_NATIVE_PRET0_GENERATOR_PERSISTENCE`, anterior a
qualquer quociente enriquecido.
