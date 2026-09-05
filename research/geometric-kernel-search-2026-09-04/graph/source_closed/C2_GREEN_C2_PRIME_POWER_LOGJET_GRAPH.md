# Jet primo-potência C2 e escala de grafo

## Resultado

`PASS_C2_PRIME_POWER_LOGJET_CORE`  
`PASS_POSITIVE_TAU_LOGJET_GRAPH`  
`PASS_ZERO_TIME_LOGJET_IN_HMINUS1`

O jet nativo é obtido da massa C2 finita, sem usar uma função externa. Para um
primo material ímpar `p_T`,

```text
A_(M,p_T)(x)=sum_(j>=0)a_M(p_T^j)x^j,
B_(M,p_T)(x)=x partial_x log A_(M,p_T)(x).
```

A normalização Richardson é o objeto formal

```text
A_red=A_(2M,p_T)^2/A_(M,p_T),
kappa_(M,p_T,j)=P_j^R(M)/j.
```

Os 15 coeficientes persistidos verificam
exatamente essa identidade por Newton e por expansão formal independente. A
feature one-leg congelada é `phi_(tau,d_J)(n)=1_(d_J|n)n^-tau`; portanto sua
especialização literal em `n=p_T^j` é

```text
rho_(p_T,j)(tau)=p_T^(-j tau),
```

e não `p_T^(-2j tau)`. Logo

```text
(log p_T) N h_(M,p_T,tau)
 =sum_(j>=1) log(p_T) P_j^R(M) rho_(p_T,j)(tau)e_(p_T,j)
```

coeficiente a coeficiente.

## A inversão global confirma a restrição primo-potência

Também foi reproduzido, com frações exatas, o construtor global fornecido pelo
usuário: massa nos cutoffs `400/800`, divisão de Dirichlet em todos os ímpares
e correção `2*b_800-b_400`. As massas coincidem com a soma bilateral C2 em
todos os 199 núcleos ímpares
do cutoff baixo e nos 399 do
cutoff alto.

Para as 53 primo-potências
ímpares menores que 200, o coeficiente global é exatamente
`log(p_T)P_j^R(400)`. Os compostos mistos permanecem como coordenadas
separadas; por exemplo,

```text
n=15: (log 3+log 5)/4096,
n=21: (log 3+log 7)/2048.
```

Esses cumulantes mistos não são níveis `j` e não são divisores Jordan `d_J`.
Eles reforçam a necessidade de preservar a proveniência completa antes de uma
relação enriquecida, sem alterar o jet primo-potência auditado aqui.

## Endpoint de tempo zero

No limite unit-mass, `P_j=1` e

```text
h_(p_T,0)=sum_(j>=1)j^-1 e_(p_T,j).
```

Esse vetor está em `H0=l2`, mas seu fluxo `N h=(1,1,...)` não está. Ele vive
canonicamente em `Hminus1`, pois

```text
||N y||_(Hminus1)^2=sum_j |j y_j|^2/j^2=||y||_(H0)^2.
```

Assim `N:H0->Hminus1` tem norma exatamente um. Para `Re(tau)>0`, o fluxo já
está em `H0`; a parte imaginária produz somente fases unitárias e

```text
||(log p_T)N h_(p_T,tau)||_H0^2
 =log(p_T)^2/[p_T^(2 Re(tau))-1].
```

Quando `Re(tau)` desce a zero, o quadrado da norma cresce como
`log(p_T)/(2 Re(tau))`; isso é a passagem controlada de Hilbert para rigged graph,
não um vetor `l2` escondido.

## Firewall

`p_A`, `p_T`, `j`, `K=k_eff`, `d_J` e `tau` permanecem eixos distintos. A
identidade de suporte auditada foi

```text
H_(p_A,0)(d_J)=log(p_A) se d_J=p_A^a; 0 nos demais d_J.
```

Somente nesse canal não nulo se identifica literalmente `p_A=p_T`. O topo
2-ádico continua vindo do carry/unit-mass nativo, não deste jet material.
