# Relação de grafo do coequalizer J/H

## Resultado

`PASS_TOWER_NUMBER_DESCENDS_THROUGH_JH_COEQUALIZER`  
`PASS_CLOSED_POST_T0_TOWER_BOUNDARY_RELATION`  
`STOP_NATIVE_A_NONZERO_ON_COEQUALIZER_KERNEL`

O carrier forward correto é o produto tensorial

```text
(p_A,tau,d_J,flags,role) tensor (p_T,j).
```

O coequalizer age somente no primeiro fator:

```text
Q=Q_JH tensor I_tower,
N=I_JH tensor diag(j).
```

Daí `QN=Nbar Q` literalmente. Em particular,

```text
N(D(N) intersect ker Q) subset ker Q.
```

Não foi escolhida seção. Os quocientes `H_Q^0` e `H_Q^-1` são completados
pelas respectivas normas de quociente. Como `N:H0->Hminus1` é isométrico e
`j>=1`, tomar o ínfimo nas classes fornece

```text
||Nbar [x]||_(Q,-1)=||[x]||_(Q,0).
```

Portanto

```text
R_Q=Graph(Nbar) subset H_Q^0 direct_sum H_Q^-1
```

é fechada, single-valued e tem parte multivaluada `{0}`.

Somar os níveis `j` produziria outra operação, semelhante à síntese escalar
posterior. Isso não é `Q_JH` e violaria o firewall `d_J != j`.

## A perna A não desce

No core `ell=2`, `tau=1`, a classe-gauge `(1,-1)` nos canais `d_J=1,2` é
apagada por `Q`. A análise one-leg tem pesos

```text
(sqrt(J_2tau(1))phi_1, sqrt(J_2tau(2))phi_2)
 =(1/2,sqrt(3)/2),
```

e portanto vê o gauge como `(1-sqrt(3))/2`, que é não nulo. Logo
`ker Q` não está contido em `ker A_even_pre`. Não existe mapa de `A` no
quociente atual, e nenhum bound de grafo posterior a essa descida foi
declarado.
