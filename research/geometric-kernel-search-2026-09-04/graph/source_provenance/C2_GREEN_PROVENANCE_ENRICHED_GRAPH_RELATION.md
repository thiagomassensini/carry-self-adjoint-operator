# Relação de grafo com proveniência enriquecida

## Estado

Os resultados `PASS_TOWER_NUMBER_DESCENDS_THROUGH_JH_COEQUALIZER` e
`PASS_CLOSED_POST_T0_TOWER_BOUNDARY_RELATION` permanecem válidos: o operador
número age no eixo `j`, enquanto o coequalizer age em `d_J`.

Isso não fornece a descida da perna `A` na faixa nativa. Como a faixa ainda não
foi construída, não há `Qtilde`, não há escalas enriquecidas e não foi testada
a identidade `Qtilde N=Ntilde Qtilde`. O frontier histórico
`NEEDS_PROVENANCE_ENRICHED_GRAPH_RELATION` não foi ativado definitivamente; ele pressupõe
uma classificação nativa que ainda falta.

O próximo objeto necessário é o construtor forward persistido que associe, em
cada contribuição C2, os eixos

```text
p_A,tau,d_J,J/H-role,cell,corner,orientation,flags,p_T,j,K,m.
```

Somente então se pode formar `R_native`, calcular `K_native`, decidir se o
modo Möbius é realizável e, se houver witness, ativar o enriquecimento mínimo.
A fronteira atual é `NEEDS_NATIVE_PRET0_GENERATOR_PERSISTENCE`.
