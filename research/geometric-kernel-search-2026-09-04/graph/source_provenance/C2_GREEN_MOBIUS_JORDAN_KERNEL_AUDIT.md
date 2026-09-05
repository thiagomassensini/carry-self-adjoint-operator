# Auditoria do kernel Möbius–Jordan

## Qualificação

`QUALIFY_STOP_NATIVE_A_AS_FREE_MODULE_ONLY`

Na fibra livre `ell=2`, `tau=1`, `n=2`, os divisores são `(1,2)` e

```text
mu_2=(mu(1),mu(2))=(1,-1).
Q mu_2=1-1=0,
A_even_pre mu_2=(1-sqrt(3))/2 != 0.
```

A não anulação é exata: uma igualdade `1=sqrt(3)` implicaria `1=3` após
quadrar. Para todo `ell>1`, somente divisores square-free contribuem, de modo
que

```text
sum_(d|ell) mu(d)=product_(p|ell)(1-1)=0.
```

O script confirmou essa identidade por aritmética inteira em
`ell=2,...,128`; a prova
é o produto sobre subconjuntos dos primos distintos de `ell`, não uma inferência
numérica.

## Escopo

Esse vetor vive no módulo livre de coeficientes `d_J`. Como
`E_native^preT0` não está persistido, não existe nesta rodada um input C2 `x`
com imagem demonstrada `mu_2`, nem uma prova de que tal input seja impossível.
A pertença nativa permanece `not determined`. Portanto o
stop histórico não foi promovido a
`STOP_NATIVE_A_NONZERO_ON_NATIVE_COEQUALIZER_KERNEL`.
