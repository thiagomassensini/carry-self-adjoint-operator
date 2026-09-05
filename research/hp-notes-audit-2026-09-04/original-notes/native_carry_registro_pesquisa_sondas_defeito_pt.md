# Sondas de Defeito Native-Carry, POVM de Cauchy–Stieltjes e Estrutura Tau Holonômica

> Versão consolidada e formatada (GitHub/VSCode-friendly) da linha de pesquisa: sondas de defeito via readout de bordo → observabilidade não-colapsante → POVM de Cauchy/Stieltjes → família de Weyl emergente → realização Jacobi/Painlevé do modo misto → derivação tau/sigma → anulador holonômico mínimo → álgebra de operadores de criação de três cores.
>
> A matemática usa os delimitadores padrão `$...$` / `$$...$$` (GitHub e VS Code com extensões de Markdown+Math renderizam isso nativamente).

---

## Sumário

1. [Readout de Bordo como Observável Fixo](#1-readout-de-bordo-como-observável-fixo)
2. [Defect States como Sondas do Readout](#2-defect-states-como-sondas-do-readout)
3. [Observabilidade Não-Colapsante dos Defect States (Gate — Fechado)](#3-observabilidade-não-colapsante-dos-defect-states-gate--fechado)
4. [Limite Único da Covariância de Métrica de Retorno (Gate — Fechado)](#4-limite-único-da-covariância-de-métrica-de-retorno-gate--fechado)
5. [Par Espectral de Câmeras: $G_C$, $H_C$, $L_C$](#5-par-espectral-de-câmeras-g_c-h_c-l_c)
6. [Segundo Momento Centrado e o POVM de Câmeras](#6-segundo-momento-centrado-e-o-povm-de-câmeras)
7. [Limite Funcional: Hierarquia Polinomial → POVM Analítico](#7-limite-funcional-hierarquia-polinomial--povm-analítico)
8. [Transformada de Cauchy/Stieltjes e a Família de Weyl Emergente das Câmeras](#8-transformada-de-cauchystieltjes-e-a-família-de-weyl-emergente-das-câmeras)
9. [Redução do Modo Misto às Três Escalas (3, 4, 6)](#9-redução-do-modo-misto-às-três-escalas-3-4-6)
10. [Realização Jacobi do Modo Misto](#10-realização-jacobi-do-modo-misto)
11. [Sistema Coupled-$P_V$ de Dois Jumps](#11-sistema-coupled-p_v-de-dois-jumps)
12. [Ponte Pushforward $C_2$ → Tau/Sigma](#12-ponte-pushforward-c_2--tausigma)
13. [Derivação Sigma/Tau e Toda Radial](#13-derivação-sigmatau-e-toda-radial)
14. [Anulador Mínimo da Tau (Gate — Fechado)](#14-anulador-mínimo-da-tau-gate--fechado)
15. [Compatibilidade Toda–Holonômica Triangular](#15-compatibilidade-todaholonômica-triangular)
16. [Álgebra Holonômica de Criação de Três Cores](#16-álgebra-holonômica-de-criação-de-três-cores)
17. [Dressing por Resultantes em Pares / Yang–Baxter Abeliano](#17-dressing-por-resultantes-em-pares--yangbaxter-abeliano)
18. [Registro de Status](#18-registro-de-status)
19. [Próximos Passos em Aberto](#19-próximos-passos-em-aberto)
20. [Ramo de Alturas: Weyl Completada e Operador de Jacobi Fixo](#20-ramo-de-alturas-weyl-completada-e-operador-de-jacobi-fixo)

---

## 1. Readout de Bordo como Observável Fixo

Define o readout nativo como função apenas de $t$, fixado *antes* de qualquer zero ser conhecido:

$$
R(t) := Q_{\text{eff}} E e^{-itL}\alpha, \qquad Q_{\text{eff}} E = C_{\text{native}}
$$

de modo que

$$
R(t) = C_{\text{native}} \, e^{-itL}\alpha .
$$

Nada em $Q_{\text{eff}}, E, L, \alpha$ precisa saber onde estão os zeros.

### 1.1 Portas de bordo

Dados traços de Green fixos $\Gamma_0, \Gamma_1 : \operatorname{dom} S^* \to \mathcal B$ e uma aplicação fixa $J : \operatorname{Ran}(Q_{\text{eff}}) \to \mathcal B$, define o readout de bordo

$$
r(t) := J R(t) = J Q_{\text{eff}} E e^{-itL}\alpha .
$$

Para qualquer defect state $f_z \in \ker(S^*-z)$ (com $z$ **independente** das alturas procuradas):

$$
O_{f_z}(t) = \langle \Gamma_0 f_z, r(t)\rangle_{\mathcal B}, \qquad
O_{f_z}^{(1)}(t) = \langle \Gamma_1 f_z, r(t)\rangle_{\mathcal B}.
$$

### 1.2 Vetor de porto completo

$$
\Gamma f = \begin{pmatrix}\Gamma_0 f \\ \Gamma_1 f\end{pmatrix}, \qquad
\mathbf R(t) = \begin{pmatrix} J_0 R(t) \\ J_1 R(t)\end{pmatrix},
\qquad
O_f(t) = \langle \Gamma f, \mathbf R(t)\rangle_{\mathcal B \oplus \mathcal B}.
$$

### 1.3 Família canônica de sondas (nenhum zero escolhido)

Fixa uma extensão de referência $A_0 = S^*|_{\ker \Gamma_0}$, dando o campo-$\gamma$ $\gamma(z): \mathcal B \to \ker(S^*-z)$. Escolhe uma base ortonormal $(e_j)$ de $\mathcal B$:

$$
f_{z,j} := \gamma(z) e_j, \qquad
O_{z,j}(t) = \langle \Gamma f_{z,j}, \mathbf R(t)\rangle, \qquad
E_z(t) = \sum_j |O_{z,j}(t)|^2 .
$$

### 1.4 Energia do subespaço de defeito

Com $D_z = \Gamma(\ker(S^*-z)) \subseteq \mathcal B\oplus\mathcal B$ e $P_{D_z}$ seu projetor ortogonal:

$$
D_z(t) = \| P_{D_z} R(t)\|^2, \qquad G_z(t) = \|(I-P_{D_z})R(t)\|^2 .
$$

**Não-circularidade:** primeiro $t \mapsto R(t)$ é definido universalmente; só depois se pergunta se $F_z(t) = 0$. Isso difere fundamentalmente de definir $D_t$ = "subespaço associado ao zero em $t$" e depois descobrir que $R(t)\in D_t$ (o que seria circular).

> **Nota histórica:** essa construção já havia sido feita em `RELACAO_DE_BORDO_UNITARIA_CARRY_WEYL.md` / `OBSERVACAO_DE_BORDO_ANGULAR_CONSERVATIVA.md`, com
> $$\chi_N(t) = Q_{\text{eff},N}\,\Gamma_0^{W}f_{t,N} = C_N e^{-itL_N}\alpha_N, \qquad \Gamma_1^W f_{t,N}=0,$$
> $$\chi_N(t)=0 \iff \Gamma_0^W f_{t,N} \in \ker Q_{\text{eff},N}.$$
> A peça **nova** é de fato projetar sobre um subespaço de defect states $P_{D_z}R(t)$ mantendo $z$ e $t$ independentes.

---

## 2. Defect States como Sondas do Readout

A relação de bordo fornece, para cada $z$ independente de $t$,

$$
g_z(e) = \gamma^W(z) e, \qquad
g_z(e) \sim \begin{pmatrix}P(z)e \\ e\end{pmatrix}, \qquad
P(z) = J_B^*(z-H)^{-1}J_E W_\infty(z),
$$

finitamente: $P_N(z) = (z-H_{BB,N})^{-1}H_{BE,N}$.

### 2.1 Readout de defeito / frame de sondas

$$
D_N(z) := Q_N \gamma^W_N(z) = Q_{E,N} + Q_{B,N}P_N(z).
$$

Para uma base ortonormal do endpoint $(e_j)$: $g_{z,j}=\gamma^W(z)e_j$, $d_{z,j} = D(z)e_j = Q g_{z,j}$.

Sonda agregada:

$$
\Phi(z,t) = \sum_j |\langle d_{z,j}, \chi(t)\rangle|^2
= \|D(z)^*\chi(t)\|^2 = \langle \chi(t), D(z)D(z)^*\chi(t)\rangle .
$$

Se $D(z)$ cobre $Y_N := \operatorname{Ran} C_N$, os $d_{z,j}$ formam um **frame**, logo

$$
\sigma_{\min}(D(z))^2\|\chi(t)\|^2 \le \Phi(z,t) \le \sigma_{\max}(D(z))^2 \|\chi(t)\|^2
\quad\Longrightarrow\quad
\boxed{\Phi(z,t)=0 \iff \chi(t)=0.}
$$

### 2.2 Escolhendo $z$ sem olhar para nenhum zero

Toma $z=i\eta$. Como $H_{BB}$ é autoadjunto, $\|(i\eta-H_{BB})^{-1}\|\le 1/\eta$, então $\|P(i\eta)\|\le \|H_{BE}\|/\eta \to 0$ e $D(i\eta)\to Q_E$.

A coercividade do endpoint (cutoff 32: $\lambda_{\min}(E^*E)=0.4278226151>0$) mais a sobrejetividade de $Q_E$ em $Y=\operatorname{Ran}C_{\text{native}}$ dão um limiar explícito

$$
\eta > \frac{\|Q_B\|\,\|H_{BE}\|}{\sigma_{\min}(Q_E)}
\;\Longrightarrow\; D(i\eta)\ \text{sobrejetivo.}
$$

**Numérica** (câmeras $2,\dots,7$, cutoffs $8,16,32$): $\eta_8=5{,}0211$, $\eta_{16}=5{,}1983$, $\eta_{32}=5{,}4448$; menores valores singulares de $D(i\eta)$: $2{,}7384, 3{,}9282, 5{,}5391$ (full row rank, números de condição $\approx 7$). Identidade de frame branqueado $\|W_z\chi(t)\|^2=\|\chi(t)\|^2$ verificada até $\sim10^{-15}$.

---

## 3. Observabilidade Não-Colapsante dos Defect States (Gate — Fechado)

Parametriza os defect states pela fonte de bordo $u$:

$$
(z-H_M)f = J_E u,\qquad f^{(M)}_{z,u} = (z-H_M)^{-1}J_E u ,
$$

$$
S_M(z) := Q_M(z-H_M)^{-1}J_E = C_M(z-L_M)^{-1}E_M^* .
$$

Operador de frame:

$$
S_M(z)S_M(z)^* = C_M R_z E_M^* E_M R_z^* C_M^*, \qquad R_z=\operatorname{diag}\frac{1}{z-\log n}.
$$

Cota do endpoint (medida pitagórica): $c_E I \le E_M^*E_M \le I$, $c_E \simeq 0{,}04610258216$, dando

$$
c_E\, C_M W_z C_M^* \;\le\; S_M(z)S_M(z)^* \;\le\; C_M W_z C_M^*,\qquad W_z = \operatorname{diag}|z-\log n|^{-2}.
$$

### 3.1 Limite de Gram periódica

Para as câmeras $2,\dots,7$:

$$
G = \begin{pmatrix}
6 & 0 & 10 & 0 & 16/3 & 0\\
0 & 6 & 0 & 0 & 6 & 0\\
10& 0 & 22& 0 & 16/3 & 0\\
0 & 0 & 0 & 20& 0 & 0\\
16/3&6&16/3&0&44&0\\
0 & 0 & 0 & 0 & 0 & 42
\end{pmatrix}
\succ 0, \qquad \lambda_{\min}(G) = 1{,}0094141749\ldots
$$

com $A_M(z) := \sum_{n\le M}|z-\log n|^{-2} \sim M/(\log M)^2$, e

$$
\frac{C_M W_z C_M^*}{A_M(z)} \longrightarrow G \qquad\Longrightarrow\qquad
\liminf_{M\to\infty}\lambda_{\min}\!\left(\frac{S_MS_M^*}{A_M(z)}\right) \ge c_E\lambda_{\min}(G) \approx 0{,}04653659993 > 0.
$$

**Este é o gate**: a cota inferior de frame não colapsa.

### 3.2 Observável

$$
\overline S_M(z) = A_M(z)^{-1/2}S_M(z), \qquad \Phi_M(z,t) = \|\overline S_M(z)^*\chi_M(t)\|^2.
$$

$$
\boxed{\chi(t)=0 \iff \Phi_M(z,t)\to 0.}
$$

Numérica: $z=6i$ fixo, cotas inferiores de frame (normalizadas) $0{,}8236, 0{,}8180, 0{,}7917, 0{,}7815, 0{,}7734$ para $M=8,16,32,64,128$ — bem acima do piso teórico $0{,}0465$. Em $t=14{,}134725141734695$ (primeiro zero não-trivial da zeta), o observável normalizado decai $0{,}796\to0{,}0968\to0{,}0119\to0{,}00149\to0{,}000185$.

```
GATE: NON-COLLAPSING DEFECT-STATE OBSERVABILITY — FECHADO
```

---

## 4. Limite Único da Covariância de Métrica de Retorno (Gate — Fechado)

A covariância euclidiana crua $S_M(z)S_M(z)^*/A_M(z)$ é não-colapsante mas sua unicidade de limite não segue diretamente. Usa a métrica de retorno nativa:

$$
G_{E,M} = I + M_{MB,M}^*M_{MB,M}, \qquad E_M^*G_{E,M}E_M = I.
$$

Define

$$
\Sigma_M^{\text{ret}}(z) = S_M(z)\,G_{E,M}\,S_M(z)^* = C_M\,W_M(z)\,C_M^* ,\qquad W_M(z)=\operatorname{diag}|z-\log n|^{-2}.
$$

**Não sobra endpoint, Poisson, bulk ou pseudoinversa dentro da covariância.** O lema periódico dá

$$
\frac{\Sigma_M^{\text{ret}}(z)}{A_M(z)} \xrightarrow{\|\cdot\|} G_C \qquad \text{para todo } z\notin\mathbb R \text{ fixo,}
$$

**convergência em norma de operador**, independente de $z$. Observável:

$$
\Psi_M(z,t) = \frac{\|G_{E,M}^{1/2}S_M(z)^*\chi_M(t)\|^2}{A_M(z)} \longrightarrow \langle \chi(t), G_C\chi(t)\rangle,
$$

$$
\boxed{\lim_M \Psi_M(z,t)=0 \iff \chi(t)=0.}
$$

Identidade $S_MG_ES_M^*=C_MW_MC_M^*$ verificada com erro $6\times10^{-15}$–$7{,}5\times10^{-14}$.

```
UNIQUE RETURN-METRIC DEFECT COVARIANCE LIMIT — FECHADO
```

*(Em aberto: unicidade da covariância euclidiana crua $S_MS_M^*/A_M$ — não necessária para detecção de zeros.)*

---

## 5. Par Espectral de Câmeras: $G_C$, $H_C$, $L_C$

Testar um intertwining direto $A_M(z)S_M(z)=S_M(z)W_M(z)$ falha (resíduos $\sim 0{,}11$–$0{,}12$), então $G_C$ **não** é uma Weyl comprimida. Mas aplicando o gerador antes de observar,

$$
T_M(z) := Q_M H_M(z-H_M)^{-1}J_E = C_ML_M(z-L_M)^{-1}E_M^*, \qquad T_M(z) = zS_M(z)-Q_{E,M},
$$

e

$$
T_M(z)\,G_{E,M}\,S_M(z)^* = C_M L_M |z-L_M|^{-2}C_M^*
$$

(erros $2{,}8\times10^{-14}$–$1{,}5\times10^{-13}$).

### 5.1 Primeiro momento

Com $\mu_M(z) = \frac{\sum(\log n)|z-\log n|^{-2}}{\sum|z-\log n|^{-2}}$ e centralização, a mesma periodicidade dá

$$
\Xi_M(z) \to H_C, \qquad (H_C)_{bc} = (G_C)_{bc}\log(\min(\ell_b,\ell_c)),\quad \ell_2=4.
$$

$$
H_C =
\begin{pmatrix}
6\log4 & 0 & 10\log4 & 0 & \tfrac{16}{3}\log4 & 0\\
0 & 6\log3 & 0 & 0 & 6\log3 & 0\\
10\log4 & 0 & 22\log4 & 0 & \tfrac{16}{3}\log4 & 0\\
0&0&0&20\log5&0&0\\
\tfrac{16}{3}\log4 & 6\log3 & \tfrac{16}{3}\log4 & 0 & 44\log6 & 0\\
0&0&0&0&0&42\log7
\end{pmatrix}
$$

### 5.2 Problema de autovalor generalizado

$$
L_C = G_C^{-1/2}H_CG_C^{-1/2},\qquad
\det(H_C-\lambda G_C) = 35840(\lambda-\log4)^2(\lambda-\log3)(\lambda-\log5)(\lambda-\log7)\big(139\lambda-198\log6+27\log3+64\log2\big).
$$

$$
\operatorname{spec}(L_C) = \left\{\log3,\ \log4,\ \log4,\ \log5,\ \log7,\ \frac{198\log6-27\log3-64\log2}{139}\right\}
$$

numericamente: $1{,}098612,\ 1{,}386294,\ 1{,}386294,\ 1{,}609438,\ 1{,}945910,\ 2{,}019744$.

**Leitura:** $G_C$ = métrica assintótica de observabilidade; $H_C$ = primeiro momento espectral do gerador visto pelos defect states; $L_C$ = operador espectral próprio das câmeras.

```
Weyl → defect states → S(z) → (G_C, H_C) → L_C
```

---

## 6. Segundo Momento Centrado e o POVM de Câmeras

Centraliza a sonda do gerador:

$$
Z_M(z) := T_M(z) - \mu_M(z)S_M(z), \qquad Z_MG_{E,M}Z_M^* = C_M(L_M-\mu_M)^2|z-L_M|^{-2}C_M^*
$$

(erros $3{,}5\times10^{-14}$–$1{,}9\times10^{-13}$). Limite:

$$
(J_C)_{bc} = (G_C)_{bc}\left[1+\log^2(\min(\ell_b,\ell_c))\right].
$$

### 6.1 Operador de variância

$$
M_C^{(2)} = G^{-1/2}JG^{-1/2}, \qquad V_C = M_C^{(2)} - L_C^2 \ge 0 \quad(\text{complemento de Schur } J-HG^{-1}H\ge0).
$$

$$
\operatorname{spec}(V_C) = \{1,1,1,1,1,\ 0{,}816849691525\ldots\}, \qquad \operatorname{rank}(V_C-I)=1,
$$

modo excepcional $(-6,-3,2,0,3,0)$ misturando as câmeras $2,3,4,6$ (câmeras $5,7$ excluídas). $[L_C, M_C^{(2)}] = 0$ (erro $2{,}75\times10^{-15}$).

### 6.2 Medida operatorial (POVM)

Com $y(x)=1+\log x$, $D(x)=\operatorname{diag}(\mathbf 1_{x\le \ell_b})$:

$$
d\Sigma_C(x) = D(x)M_0D(x)\,dx, \qquad G_C=\int d\Sigma_C,\quad H_C=\int y\,d\Sigma_C,\quad J_C=\int y^2\,d\Sigma_C.
$$

Branqueado: $dE_C = G^{-1/2}d\Sigma_CG^{-1/2}$, $\int dE_C=I$ (norma do comutador $\le 1{,}53\times10^{-16}$: **POVM comutativo**).

**Modos puros** $b=3,4,5,7$: $\nu_b(dx)=\tfrac1b\mathbf 1_{(0,b]}(x)dx$ (modo $4$ duplo), com $y_b = \log b + 1 - E$, $E\sim\operatorname{Exp}(1)$:

$$
\mathbb E[y_b]=\log b,\qquad \operatorname{Var}(y_b)=1,\qquad \kappa_r(y_b)=(-1)^r(r-1)!\ \ (r\ge2).
$$

**Modo misto**: $\nu_*(dx) = \tfrac{16}{139}dx$ em $(0,3]$, $\tfrac{25}{139}dx$ em $(3,4]$, $\tfrac{33}{139}dx$ em $(4,6]$, reproduzindo o autovalor $\frac{198\log6-27\log3-64\log2}{139}$ e a variância $0{,}81684969\ldots$

Dilatação: $(Yf)(x)=(1+\log x)f(x)$ autoadjunto, isometria $V$ com $V^*YV=L_C$, $V^*Y^2V=M_C^{(2)}$.

```
CAMERA POVM STRUCTURE — FECHADO
```

---

## 7. Limite Funcional: Hierarquia Polinomial → POVM Analítico

Função geradora:

$$
F_M(s;z) = \frac{1}{A_M(z)}C_M\,e^{s(L_M-\mu_M(z))}W_M(z)\,C_M^*, \qquad
F_M(s;z)\to F_C(s),
$$

$$
(F_C(s))_{bc} = (m_0)_{bc}\,\frac{e^{s\ell_{bc}}}{s+1}, \qquad \Re s > -1,
$$

localmente uniforme, **independente de $z$**. Pelo teorema de Cauchy $\Rightarrow$ para todo $k\ge0$,

$$
\frac{1}{A_M(z)}C_M(L_M-\mu_M)^kW_MC_M^* \to \int y^k\,d\Sigma_C(y),
$$

logo para qualquer polinômio $p$:

$$
\frac{1}{A_M(z)}C_Mp(L_M-\mu_M)W_MC_M^* \to \int p(y)\,d\Sigma_C(y).
$$

### 7.1 Identidade finita das sondas de defeito

$$
U_M[p;z] := Q_Mp(H_M-\mu_M)(z-H_M)^{-1}J_E = C_Mp(L_M-\mu_M)(z-L_M)^{-1}E_M^*,
$$
$$
U_M[p;z]\,G_{E,M}\,S_M(z)^* = C_Mp(L_M-\mu_M)W_MC_M^*
$$

(auditado $p=1,y,\dots,y^6$ + polinômio misto, erro relativo máximo $<1{,}8\times10^{-15}$).

### 7.2 Recorrência dos momentos

$$
P_0(t)=1,\qquad P_k(t)=(1+t)^k - kP_{k-1}(t), \qquad
\sum_{k\ge0}P_k(t)\frac{s^k}{k!} = \frac{e^{s(1+t)}}{1+s},
$$

$$
(M_C^{(k)})_{bc} = (G_C)_{bc}\,P_k(\log \ell_{bc}).
$$

$P_0=1,\ P_1=t,\ P_2=t^2+1$ (recuperando $G,H,J$), $P_3=t^3+3t-2$, $P_4=t^4+6t^2-8t+9$, $P_5=t^5+10t^3-20t^2+45t-44$, $P_6=t^6+15t^4-40t^3+135t^2-264t+265$.

### 7.3 Cálculo funcional do POVM

$$
\Phi_C(p) = \int p(y)\,dE_C(y), \qquad \Phi_C(y^2)\ne \Phi_C(y)^2 \quad(\text{obstrução de variância}).
$$

Realização completa: $\Phi_C(p) = V^*p(Y)V$ para todo polinômio $p$.

```
POLYNOMIAL / ANALYTIC DEFECT-PROBE FUNCTIONAL LIMIT — FECHADO
```

---

## 8. Transformada de Cauchy/Stieltjes e a Família de Weyl Emergente das Câmeras

Convenção anti-Herglotz:

$$
\mathfrak M_C(\lambda) = \int \frac{1}{\lambda-y}\,dE_C(y), \qquad \Im\lambda\ne 0.
$$

### 8.1 Fórmula fechada via $E_1$

$$
F_\ell(\lambda) = \int_0^\ell \frac{dx}{\lambda-1-\log x} = e^{\lambda-1}E_1(\lambda-1-\log\ell),
$$

$$
(\mathbf M_\Sigma(\lambda))_{bc} = (M_0)_{bc}\,F_{\ell_{bc}}(\lambda), \qquad \ell_{bc}=\min(\ell_b,\ell_c).
$$

Decomposição em modos: $\mathfrak M_C(\lambda) = m_3P_3+m_4P_4+m_5P_5+m_7P_7+m_*P_*$ ($P_4$ rank $2$), com

$$
m_b(\lambda) = e^{a_b}E_1(a_b),\quad a_b=\lambda-1-\log b\quad(b=3,4,5,7),
$$

$$
m_*(\lambda) = \frac{33F_6(\lambda)-8F_4(\lambda)-9F_3(\lambda)}{139} = \frac{198\phi_6-32\phi_4-27\phi_3}{139}.
$$

### 8.2 Estrutura Nevanlinna

$$
-\Im\mathfrak M_C(\lambda) = (\Im\lambda)\int\frac{dE_C(y)}{|\lambda-y|^2} > 0 \quad(\Im\lambda>0),
$$

então $\mathfrak M_C(\lambda)$ é invertível fora de $\mathbb R$; define $\mathfrak W_C(\lambda) = \mathfrak M_C(\lambda)^{-1}$, uma família Nevanlinna/Herglotz genuína: $\Im\mathfrak W_C(\lambda) > 0$.

Numérica (menor autovalor de $-\Im M$ / $\Im W$ em $\lambda = 1{+}i,\ 2{+}0{,}75i,\ -1{+}0{,}5i$):
$0{,}438/1{,}382,\ 0{,}778/1{,}004,\ 0{,}096/0{,}847$.

### 8.3 Realização

$$
\mathfrak M_C(\lambda) = V^*(\lambda-Y)^{-1}V, \qquad \mathfrak W_C(\lambda)=\mathfrak M_C(\lambda)^{-1}
$$

é exatamente a família de Weyl da relação de bordo $\mathcal T_C=\{\{f,Yf+Vu\}\}$, $\Gamma_0^Wf=V^*f,\ \Gamma_1^Wf=u$.

### 8.4 Identidade finita das sondas de defeito (novamente)

$$
\frac{1}{A_M(z_0)}U_M(\lambda;z_0)\,G_{E,M}\,S_M(z_0)^* = \frac{1}{A_M(z_0)}C_M(\lambda-(L_M-\mu_M))^{-1}W_M(z_0)C_M^*
$$

(erro relativo máximo $1{,}35\times10^{-15}$), convergindo (norma de operador, localmente uniforme em compactos de $\mathbb C\setminus\mathbb R$) para $\mathbf M_\Sigma(\lambda)$, **independente de $z_0$**.

### 8.5 Expansão em alta energia

$$
\mathfrak M_C(\lambda) = \frac{I}{\lambda}+\frac{L_C}{\lambda^2}+\frac{M_C^{(2)}}{\lambda^3}+O(\lambda^{-4}),
\qquad
\mathfrak W_C(\lambda) = \lambda I - L_C - \frac{V_C}{\lambda} + O(\lambda^{-2}),
$$

ou seja, o operador de variância do segundo momento $V_C$ é o primeiro coeficiente de retorno da família de Weyl emergente (assinatura de complemento de Schur $\lambda - \text{endpoint} - \text{retorno}(\lambda)$).

### 8.6 Realização Jacobi/fração contínua dos modos puros

$y = \log b + 1 - T$, $T\sim\operatorname{Exp}(1)$ $\Rightarrow$ matriz de Jacobi Laguerre $a_n=\log b - 2n$, $b_n=n+1$:

$$
w_b(\lambda) = \lambda-\log b - \cfrac{1^2}{\lambda-(\log b-2)-\cfrac{2^2}{\lambda-(\log b-4)-\cfrac{3^2}{\ddots}}}.
$$

### 8.7 Separação de parâmetros

$$
z_0 = \text{âncora auxiliar da sonda de defeito (desaparece)}, \qquad
\lambda = \text{parâmetro espectral da Weyl emergente}, \qquad
t = \text{parâmetro angular da característica nativa}.
$$

Nenhuma identidade $z_0=\lambda$, $z_0=t$, ou $\lambda=t$ é postulada.

```
CAMERA POVM CAUCHY/STIELTJES TRANSFORM — FECHADO
EMERGENT CAMERA WEYL FAMILY — CONSTRUÍDA
```

---

## 9. Redução do Modo Misto às Três Escalas (3, 4, 6)

**Entrada de invariância de representação:** o shear $C_2$-bilateral $\leftrightarrow$ Haar
$$
h_2 = \tfrac32 c_2 - \tfrac12 c_4
$$
transporta *toda* a medida operatorial por congruência ($d\Sigma' = A\,d\Sigma\,A^*$); depois do branqueamento, os POVMs são unitariamente equivalentes (status: `DOUBLE_LOG4_INVARIANT_UNDER_MATCHED_C2_HAAR_COORDINATE_CHANGE`). Portanto a lei Jacobi/Riccati do modo misto derivada abaixo pertence à classe espectral do modo, não à escolha de coordenada $C_2$ — **desde que o horizonte físico seja casado**.

O modo misto (overlap das câmeras $2,3,4,6$) reduz a uma combinação assinada de três escalas puras:

$$
\nu_* = \frac{198\,\nu_6 - 32\,\nu_4 - 27\,\nu_3}{139}, \qquad \nu_b(dx) = \frac1b\mathbf 1_{(0,b]}(x)\,dx,
$$

densidade positiva em $x$: $\frac{16}{139}$ em $(0,3]$, $\frac{25}{139}$ em $(3,4]$, $\frac{33}{139}$ em $(4,6]$.

### 9.1 Forma de Laguerre com dois jumps

$$
t = \log(6/x) = 1+\log6-y \quad\Longrightarrow\quad
d\omega_*(t) = \frac{96}{139}e^{-t}\left[1+\tfrac12\mathbf1_{[0,\log(3/2)]}(t) + \tfrac9{16}\mathbf1_{[0,\log2]}(t)\right]dt.
$$

Localizações dos jumps (fixas, exatas): $\tau_1=\log(3/2)$, $\tau_2=\log2$.

---

## 10. Realização Jacobi do Modo Misto

Função-$m$:

$$
m_*(\lambda) = \frac{198m_6(\lambda)-32m_4(\lambda)-27m_3(\lambda)}{139}, \qquad m_b(\lambda)=e^{\lambda-1-\log b}E_1(\lambda-1-\log b).
$$

Momentos em forma fechada:

$$
P_0(u)=1,\quad P_k(u)=(1+u)^k-kP_{k-1}(u), \qquad
\mu_k^* = \frac{198P_k(\log6)-32P_k(\log4)-27P_k(\log3)}{139}.
$$

### 10.1 Jacobi canônica via Hankel/Stieltjes

$$
h_n = \int\pi_n(y)^2\,d\nu_*(y),\qquad y\pi_n = \pi_{n+1}+a_n\pi_n+b_n^2\pi_{n-1},
$$

$$
\Delta_n = \det(\mu_{i+j}^*)_{i,j=0}^{n-1}, \qquad h_n=\frac{\Delta_{n+1}}{\Delta_n}, \qquad
b_{n+1}^2 = \frac{\Delta_{n+2}\Delta_n}{\Delta_{n+1}^2}.
$$

**Formas fechadas:**

$$
a_0 = \frac{134\log2+171\log3}{139} \approx 2{,}019744054368917,
$$

$$
b_1^2 = 1-\frac{18}{19321}\left(457\log^22 - 512\log2\log3+304\log^23\right) \approx 0{,}903797373046302^2.
$$

Numericamente ($n=1,\dots,4$): $a_1=-0{,}191862,\ b_2=1{,}937198$; $a_2=-2{,}189962,\ b_3=2{,}969645$; $a_3=-4{,}160535,\ b_4=3{,}988413$; $a_4=-6{,}144091,\ b_5=4{,}993892$.

### 10.2 Fração contínua / Riccati

$$
m_*(\lambda) = \cfrac{1}{\lambda-a_0-\cfrac{b_1^2}{\lambda-a_1-\cfrac{b_2^2}{\lambda-a_2-\ddots}}},
\qquad
m_{n+1}(\lambda) = \frac{\lambda-a_n-m_n(\lambda)^{-1}}{b_{n+1}^2}.
$$

Erros de truncação em $\lambda=1+i$: $N=5\to3{,}0\times10^{-2}$, $N=10\to8{,}2\times10^{-3}$, $N=20\to1{,}2\times10^{-3}$, $N=35\to1{,}5\times10^{-4}$; em $\lambda=10i$, $N=20 \to \sim10^{-16}$.

**Nenhuma forma elementar fechada** $a_n=A+Bn$, $b_n=C+Dn$ é afirmada ou encontrada — a lei exata é a construção de Stieltjes/Hankel/Riccati (bate com a literatura conhecida de coupled-$P_V$ / Painlevé para pesos Laguerre multi-jump).

```
REPRESENTATION-INVARIANT MIXED-MODE JACOBI REALIZATION — FECHADO (sentido espectral)
```

---

## 11. Sistema Coupled-$P_V$ de Dois Jumps

Especialização de Lyu–Chen–Xu (arXiv:2202.00943), $\alpha=0$, $m=2$, $(\omega_0,\omega_1,\omega_2)=(33,-8,-9)$.

### 11.1 Dados iniciais exatos

$$
h_0 = 33-8e^{-\tau_1}-9e^{-\tau_2} = \frac{139}{6}, \qquad
R_{0,1}=-\frac{32}{139},\quad R_{0,2}=-\frac{27}{139},\quad r_{0,1}=r_{0,2}=0.
$$

### 11.2 Sistema discreto em $n$

$$
r_{n+1,k} = \left(\tau_k - \tau_1R_{n,1}-\tau_2R_{n,2} - 2n-1\right)R_{n,k} - r_{n,k},
$$

$$
\frac{1}{R_{n,1}} = 1 + \frac{R_{n-1,1}}{r_{n,1}^2}\left[\frac{r_{n,2}^2}{R_{n-1,2}} + \frac{(n+r_{n,1}+r_{n,2})^2}{1-R_{n-1,1}-R_{n-1,2}}\right],
\qquad
R_{n,2} = \frac{R_{n-1,1}}{R_{n-1,2}}\frac{r_{n,2}^2}{r_{n,1}^2}R_{n,1}.
$$

### 11.3 Coeficientes Jacobi a partir do ladder

$$
a_n = \log6-2n-\tau_1R_{n,1}-\tau_2R_{n,2},\qquad
b_n^2 = \frac{(n+r_{n,1}+r_{n,2})^2}{1-R_{n,1}-R_{n,2}} + \frac{r_{n,1}^2}{R_{n,1}} + \frac{r_{n,2}^2}{R_{n,2}}\quad(n\ge1),
$$

com a identidade de produto $r_{n,k}^2 = b_n^2R_{n,k}R_{n-1,k}$.

### 11.4 Deformação radial, Riccati, coupled-$P_V$

Com $\tau_k(\eta)=\eta\tau_k$, $\delta=\eta\,d/d\eta$:

$$
\delta R_k = 2r_k + \left[\eta(\tau_1R_1+\tau_2R_2)-\eta\tau_k+2n\right]R_k,
$$
$$
\delta r_k = \frac{r_k^2}{R_k} - R_k\left[\frac{(n+r_\Sigma)^2}{1-R_\Sigma}+\frac{r_1^2}{R_1}+\frac{r_2^2}{R_2}\right].
$$

Com $u_k = R_k\dfrac{n+r_\Sigma}{R_\Sigma-1}$, $v_k = \dfrac{r_k}{R_k}\dfrac{R_\Sigma-1}{n+r_\Sigma}$:

$$
\delta u_k = -\eta\tau_ku_k - u_k\!\sum_j u_j(v_j-1)(2v_k+v_j-1) - 2nu_kv_k+2nu_k,
$$
$$
\delta v_k = \eta\tau_kv_k + (v_k-1)\!\sum_j u_j(v_j-1)(v_k+v_j) + n(v_k-1)^2.
$$

### 11.5 Toda

$$
\delta\log\beta_n = \alpha_{n-1}-\alpha_n+2,\qquad (\delta-1)\alpha_n = \beta_n-\beta_{n+1},
\qquad \alpha_n=1+\log6-a_n,\quad \beta_n=b_n^2.
$$

Auditado (dps=100, $N$ até 64): erros máximos — aux-discreto $1{,}6\times10^{-94}$, fórmula de $\alpha$ $6{,}2\times10^{-92}$, fórmula de $\beta$ $9{,}9\times10^{-92}$, diferença em $r$ $2{,}8\times10^{-95}$, identidade de produto $3{,}6\times10^{-102}$, Riccati $R$/$r$ $\sim10^{-99}$, coupled-$P_V$ $\sim10^{-99}$, Toda $\sim10^{-98}$–$10^{-99}$.

```
MIXED 3–4–6 TWO-JUMP LADDER / DISCRETE RICCATI SYSTEM — FECHADO
COUPLED-P_V SPECIALIZATION — IDENTIFICADO E AUDITADO
```

---

## 12. Ponte Pushforward $C_2$ → Tau/Sigma

> **Correção de memória:** o objeto-limite antigo do pushforward $C_2$ é $Z(s)=\zeta_{\text{odd}}(s)=(1-2^{-s})\zeta(s)$ — a parte ímpar, com o fator local diádico removido — **não** uma "zeta deslocada." $a_M(m)\to1$, a inversão ponderada $b_M(m)\to\Lambda(m)$, daí $L=-Z'/Z$.

As duas construções (pushforward $C_2$ antigo, tau do modo misto atual) são **objetos diferentes** que compartilham uma arquitetura:

$$
\text{medida em escala logarítmica} \to \text{pushforward/Jacobiano} \to \text{função de partição} \to \text{derivada logarítmica.}
$$

### 12.1 Jacobiano $C_2$ discreto

Dois ramos $2^km\pm1$, $k\ge2$, massa $2^{-k}$ cada, $2\sum_{k\ge2}2^{-k}=1$:

$$
J_{C2}(s) = 2\sum_{k\ge2}2^{-k}e^{-sk\log2} = \frac{2^{-1-2s}}{1-2^{-1-s}}, \qquad J_{C2}(0)=1.
$$

### 12.2 Jacobiano contínuo do modo misto

$$
J_*(s) = \int e^{-s\xi}\,d\nu_*(\xi) = \frac{198-32(2/3)^s-27(1/2)^s}{139(1+s)}, \qquad J_*(0)=1.
$$

O $1/(1+s)$ é o Jacobiano contínuo universal da exponencial; $(2/3)^s,(1/2)^s$ são os dois defeitos de escala (o segundo exatamente diádico).

### 12.3 Redução tau/sigma de Hankel

$$
D_n(\eta) = \det(\mu_{i+j}(\eta))_{i,j=0}^{n-1}, \qquad
\sigma_n = \delta\log D_n,\ \ \delta = t_1\partial_{t_1}+t_2\partial_{t_2},
$$

$$
\partial_{t_k}\log h_j = -R_{j,k} \;\Rightarrow\; \sigma_n = -\sum_{j=0}^{n-1}(t_1R_{j,1}+t_2R_{j,2}), \qquad
\sigma_n = n^2-b_n^2+t_1r_{n,1}+t_2r_{n,2}.
$$

$$
a_n = \log6-2n+\sigma_{n+1}-\sigma_n, \qquad b_n^2 = \frac{D_{n+1}D_{n-1}}{D_n^2}.
$$

Em $\eta=0$: fundo Laguerre puro $D_n(0)=16^n\prod_{j=0}^{n-1}(j!)^2$, $a_n(0)=\log6-2n$, $b_n(0)=n$.

```
D_n → σ_n = δ log D_n → (a_n, b_n)
```

é a redução escalar canônica. **Nenhuma identidade $D_n=Z$ é afirmada**; o paralelo é arquitetural, não literal.

---

## 13. Derivação Sigma/Tau e Toda Radial

### 13.1 Peso radial e gerador de momentos

$$
w_\eta(\xi) = e^{-\xi}\left[33-8\theta(\xi-t_1)-9\theta(\xi-t_2)\right], \qquad t_k=\eta\tau_k,
$$

$$
\mathcal J_\eta(s) = \int_0^\infty e^{-s\xi}w_\eta(\xi)\,d\xi = \frac{33-8e^{-(s+1)t_1}-9e^{-(s+1)t_2}}{s+1},
\qquad \mu_j(\eta)=(-1)^j\partial_s^j\mathcal J_\eta(0).
$$

### 13.2 Tau e sigma

$$
D_n(\eta)=\det[\mu_{i+j}(\eta)],\qquad \Theta_n(\eta)=D_n(\eta)/D_n(0), \qquad
\sigma_n(\eta) = \eta\,\partial_\eta\log\Theta_n(\eta).
$$

$$
\boxed{b_n^2 = \eta\sigma_n' - \sigma_n + n^2}, \qquad \boxed{a_n = \log6-2n+\sigma_{n+1}-\sigma_n}.
$$

### 13.3 Tau-Toda (bilinear, escalar, exata)

$$
b_n^2 = n^2\,\frac{\Theta_{n+1}\Theta_{n-1}}{\Theta_n^2}
\quad\Longrightarrow\quad
\boxed{\eta^2(\log\Theta_n)'' = n^2\!\left(\frac{\Theta_{n+1}\Theta_{n-1}}{\Theta_n^2}-1\right)}
$$

$$
\Longleftrightarrow \eta^2\left[\Theta_n\Theta_n''-(\Theta_n')^2\right] = n^2\left[\Theta_{n+1}\Theta_{n-1}-\Theta_n^2\right].
$$

### 13.4 Sigma-Toda

$$
\boxed{\eta\,\partial_\eta\log\!\left(\eta\sigma_n'-\sigma_n+n^2\right) = \sigma_{n-1}-2\sigma_n+\sigma_{n+1}.}
$$

### 13.5 Sigma-PDE (geral, $m=2$, $\alpha=0$)

$$
\left(\sqrt{q_1^2+4\beta r_1^2}+\sqrt{q_2^2+4\beta r_2^2}+2\beta\right)^2 - (q_1+q_2)^2 = 4\beta(n+r_1+r_2)^2,
$$

com $\beta=\delta\sigma-\sigma+n^2$, $r_k=\partial_{t_k}\sigma$, $q_k=\delta r_k$.

### 13.6 Restrição radial e polarização residual

$S(\eta)=\sigma(\eta\tau_1,\eta\tau_2)$, $u=r_1+r_2$: $S'=\tau_1r_1+\tau_2r_2$, então

$$
r_1 = \frac{\tau_2u-S'}{\tau_2-\tau_1}, \qquad r_2 = \frac{S'-\tau_1u}{\tau_2-\tau_1}.
$$

A PDE fecha somente em $(S,u)$, **não** em $S$ sozinho — nenhuma ODE escalar de segunda ordem tipo JMO-$P_V$ é afirmada para o fluxo radial de dois jumps sem uma identidade extra que elimine $u$.

### 13.7 Dados iniciais

$$
\Theta_n(0)=1,\quad\sigma_n(0)=0,\quad a_n(0)=\log6-2n,\quad b_n(0)=n, \qquad
\sigma_n'(0) = \frac{n}{16}(8\log3+\log2).
$$

```
J_η(s) → {μ_k} → D_n → σ_n → (a_n, b_n)
```

---

## 14. Anulador Mínimo da Tau (Gate — Fechado)

Como $\tau_2/\tau_1 = \log2/\log(3/2)\notin\mathbb Q$ (nenhuma relação $pa+qb=0$ exceto $p=q=0$, por fatoração única), a tau do modo misto **não** colapsa o fluxo de dois canais a um $P_V$-JMO escalar. Em vez disso, existe uma redução holonômica completa.

### 14.1 Decomposição exponencial-polinomial

Pela identidade de Andréief,

$$
D_n(\eta) = \frac1{n!}\int \Delta(x)^2\prod_{j=1}^n w_\eta(x_j)\,dx
= \sum_{\substack{p,q\ge0\\p+q\le n}} P_{n,p,q}(\eta)\,e^{-(pa+qb)\eta}, \qquad a=\log(3/2),\ b=\log2.
$$

Com $r=n-p-q$, o grau exato (contagem de pares cruzados da Vandermonde) é

$$
\boxed{\deg P_{n,p,q} = 2(pq+pr+qr) = n^2-(p^2+q^2+r^2)}.
$$

Coeficiente líder $\propto a^{2pr}b^{2qr}(b-a)^{2pq}\cdot 33^r(-8)^p(-9)^q \cdot(\text{integrais Laguerre internas positivas}) \neq 0$ — o grau é **exato**, não apenas um upper bound.

### 14.2 Anulador mínimo

Todas as frequências $pa+qb$ são distintas $\Rightarrow$

$$
\boxed{
\mathcal H_n^{\min} = \prod_{\substack{p,q\ge0\\p+q\le n}}
\left(\partial_\eta + pa+qb\right)^{1+n^2-p^2-q^2-(n-p-q)^2}
}, \qquad
\boxed{N_n = \left(\frac{n(n+1)}2\right)^2+n+1.}
$$

Ordens $n=0,\dots,10$: $1, 3, 12, 40, 105, 231, 448, 792, 1305, 2035, 3036$.

**Casos:**

- $n=1$: $\mathcal H_1=\partial_\eta(\partial_\eta+a)(\partial_\eta+b)$, ordem $3$.
- $n=2$: $\mathcal H_2 = \partial_\eta(\partial_\eta+a)^3(\partial_\eta+b)^3(\partial_\eta+2a)(\partial_\eta+a+b)^3(\partial_\eta+2b)$, ordem $12$.
- $n=3$: ordem $40$, com o setor central $(1,1,1)$ (frequência $a+b=\log3$) em multiplicidade $7$.

### 14.3 Redução escalar

$g_n = D_n'/D_n = \sigma_n/\eta$; dividindo $\mathcal H_n^{\min}D_n=0$ por $D_n$ via polinômios de Bell completos $D_n^{(k)}/D_n = B_k(g_n,\dots,g_n^{(k-1)})$ dá uma ODE escalar não-linear de ordem $N_n-1$ para $g_n$ — **elimina a polarização $u$ completamente no nível da tau** (embora não necessariamente mínima como ODE não-linear; Painlevé/Toda podem dar ordem menor).

Fechamento explícito para $n=1$:

$$
g'' + 3gg' + g^3 + \log3\,(g'+g^2) + \log(3/2)\log2\, g = 0.
$$

```
MINIMAL CONSTANT-COEFFICIENT TAU ANNIHILATOR — FECHADO
POLARIZATION ELIMINATED AT TAU LEVEL BY HOLONOMIC CLOSURE — FECHADO
```

---

## 15. Compatibilidade Toda–Holonômica Triangular

### 15.1 Lei de crescimento do anulador

Com $r=n-p-q$, incrementando $n\to n+1$ (i.e. $r\to r+1$) em $(p,q)$ fixo:

$$
m_{n+1}(p,q)-m_n(p,q) = 2(p+q),
$$

mais uma nova casca de bordo em $p+q=n+1$ ($r=0$): $m_{n+1}(p,q)=1+2pq$. Então

$$
H_{n+1}^{\min} = K_n\,H_n^{\min}, \qquad
K_n = \prod_{p+q\le n}(\partial_\eta+pa+qb)^{2(p+q)} \prod_{p+q=n+1}(\partial_\eta+pa+qb)^{1+2pq}.
$$

Incremento de ordem: $N_{n+1}-N_n = (n+1)^3+1$, dividido em

$$
B_n = \frac{2n(n+1)(n+2)}{3}\ (\text{engrossamento do bulk}), \qquad
S_n = \frac{n(n+1)(n+2)}{3}+n+2\ (\text{nova casca}), \qquad B_n+S_n=(n+1)^3+1.
$$

### 15.2 Sem Darboux linear $D_n \to D_{n+1}$

Qualquer operador linear de coeficientes constantes $P(\partial_\eta)$ aplicado a $Q(\eta)e^{-\lambda\eta}$ preserva a frequência $\lambda$; como $D_{n+1}$ contém frequências genuinamente novas ($p+q=n+1$) com coeficientes não nulos, **nenhum operador linear de coeficientes constantes leva $D_n\mapsto D_{n+1}$.**

### 15.3 O mapa de Bäcklund correto é Toda

Da seção 13.3:

$$
\Theta_{n+1} = \frac{\Theta_n^2}{\Theta_{n-1}}\left[1+\frac{\eta^2}{n^2}(\log\Theta_n)''\right] =: T_n[\Theta_{n-1},\Theta_n].
$$

### 15.4 Flag holonômica

$V_n := \ker H_n^{\min}$; como $H_{n+1}^{\min}=K_nH_n^{\min}$, $V_n\subset V_{n+1}$, $\dim V_n=N_n$, e

$$
\dim(V_{n+1}/V_n) = (n+1)^3+1.
$$

O mapa de Toda/Bäcklund seleciona uma trajetória específica dentro dessa flag holonômica canônica $V_0\subset V_1\subset V_2\subset\cdots$.

```
Θ_n ∈ ker H_n^min          H_n^min → K_n H_n^min = H_{n+1}^min   (linear, holonômico)
(Θ_{n-1}, Θ_n) --Toda--> Θ_{n+1}                                (não-linear, dinâmico)
```

```
TODA–HOLONOMIC TRIANGULAR COMPATIBILITY — FECHADO
```

---

## 16. Álgebra Holonômica de Criação de Três Cores

### 16.1 Espaço de Fock

$$
\mathcal F_n = \bigoplus_{p+q+r=n} \mathcal E_{pqr}, \qquad
\mathcal E_{pqr} = \operatorname{span}\left\{\frac{\eta^k}{k!}e^{-(pa+qb)\eta} : 0\le k\le d(p,q,r)\right\}, \qquad d(p,q,r)=2(pq+pr+qr).
$$

$\dim\mathcal F_n = N_n = \left[\frac{n(n+1)}2\right]^2+n+1.$

### 16.2 Operadores de criação

$$
C_0|p,q,r;k\rangle = |p,q,r{+}1;k\rangle, \quad
C_a|p,q,r;k\rangle = |p{+}1,q,r;k\rangle, \quad
C_b|p,q,r;k\rangle = |p,q{+}1,r;k\rangle,
$$

funcionalmente $C_0f=f$, $C_af=e^{-a\eta}f$, $C_bf=e^{-b\eta}f$.

$$
\boxed{[C_0,C_a]=[C_0,C_b]=[C_a,C_b]=0.}
$$

### 16.3 Operadores número, frequência, capacidade

$P,Q,R$ = operadores número de cada cor; $N=P+Q+R$; $\Lambda=aP+bQ$; $\mathsf V = 2(PQ+PR+QR)$ (capacidade, autovalor $d(p,q,r)$).

$$
[N,C_i]=C_i, \qquad [\Lambda,C_0]=0,\ [\Lambda,C_a]=aC_a,\ [\Lambda,C_b]=bC_b,
$$

$$
[\mathsf V,C_0] = 2(P+Q)C_0, \qquad [\mathsf V,C_a]=2(Q+R)C_a, \qquad [\mathsf V,C_b]=2(P+R)C_b.
$$

Com $\nabla=\partial_\eta+\Lambda$: $\nabla C_i = C_i\nabla$ — **os criadores são intertwiners exatos dos blocos de Jordan.**

### 16.4 Jets de interação sem curvatura

$$
\Delta_0 = 2(p+q), \qquad \Delta_a=2(q+r), \qquad \Delta_b = 2(p+r),
$$

satisfazendo a condição de flatness (curvatura discreta zero) $\Delta_i(x)+\Delta_j(x+e_i) = \Delta_j(x)+\Delta_i(x+e_j)$.

### 16.5 Adjuntos e defeito de dupla comutação

Hilbertizando $|p,q,r;k\rangle$ como ortonormal $\Rightarrow C_i^*C_i=I$ (isometria), mas $C_iC_i^*\ne I$:

$$
\operatorname{rank}(I-C_0C_0^*) = 2(p+q), \quad \operatorname{rank}(I-C_aC_a^*)=2(q+r), \quad \operatorname{rank}(I-C_bC_b^*)=2(p+r).
$$

Para $i\ne j$, o defeito de dupla comutação

$$
D_{ij}^{(n)} = C_i^{(n)*}C_j^{(n)} - C_j^{(n-1)}C_i^{(n-1)*}
$$

tem $\operatorname{rank} D_{ij}^{(n)} = \tfrac23(n-1)n(n+1) = B_{n-1}$ — **exatamente a dimensão de engrossamento do bulk** da seção 15.1.

```
engrossamento do bulk = defeito de dupla comutação dos operadores de criação
```

### 16.6 Criador físico bare

$$
C_{\text{bare}} = 33\,C_0 - 8\,C_a - 9\,C_b, \qquad
\frac{1}{n!}C_{\text{bare}}^n|\Omega\rangle = \sum_{p+q+r=n}\frac{(-8)^p(-9)^q33^r}{p!q!r!}\,|p,q,r;0\rangle.
$$

Isso reproduz apenas os jets $k=0$ — os jets de interação $k=1,\dots,d(p,q,r)$ vêm do dressing de Vandermonde (seção 17).

```
THREE-COLOR HOLONOMIC CREATION ALGEBRA — CONSTRUÍDA
```

---

## 17. Dressing por Resultantes em Pares / Yang–Baxter Abeliano

### 17.1 Vandermonde = produto de resultantes ao quadrado

Com $s_0=0,\ s_a=a,\ s_b=b$ e polinômios $P_a,P_b,P_0$ construídos a partir dos três blocos de raízes:

$$
\Delta(A,B,Z)^2 = \Delta(A)^2\Delta(B)^2\Delta(Z)^2\, V_{ab}V_{a0}V_{b0}, \qquad
V_{ab}=\operatorname{Res}(P_a,P_b)^2,\ \ V_{a0}=\operatorname{Res}(P_a,P_0)^2,\ \ V_{b0}=\operatorname{Res}(P_b,P_0)^2,
$$

equivalente à identidade multiplicativa do discriminante $\operatorname{Disc}(P_0P_aP_b)=\prod_i\operatorname{Disc}(P_i)\prod_{i<j}\operatorname{Res}(P_i,P_j)^2$.

### 17.2 Flatness abeliana

Como operadores de multiplicação escalar, $[V_{ab},V_{a0}]=[V_{ab},V_{b0}]=[V_{a0},V_{b0}]=0$, então

$$
V_{ab}^{12}V_{a0}^{13}V_{b0}^{23} = V_{b0}^{23}V_{a0}^{13}V_{ab}^{12}
$$

— uma relação tipo Yang–Baxter **abeliana** (multiplicatividade escalar, não uma $R$-matriz não-comutativa genuína).

### 17.3 Operador de criação vestido

Para uma configuração existente $\mathcal X$ com polinômio $P_{\mathcal X}(\lambda)=\prod_{\rho\in\mathcal X}(\lambda-\rho)$, criando uma nova partícula de cor $i$ em $\rho_i = s_i\eta+y$:

$$
(\widehat C_i\Psi)(\mathcal X\cup\{\rho_i\}) = \omega_i\, e^{-\rho_i}\,P_{\mathcal X}(\rho_i)^2\,\Psi(\mathcal X), \qquad
(\omega_0,\omega_a,\omega_b)=(33,-8,-9).
$$

### 17.4 Flatness exata da criação vestida

$$
\widehat C_j(\mathcal X+\rho_i)\,\widehat C_i(\mathcal X) = \widehat C_i(\mathcal X+\rho_j)\,\widehat C_j(\mathcal X)
$$

(3D-consistency verificada para todas as seis ordenações de três criações).

### 17.5 Realização de Fock da tau

Com $\widehat C = \widehat C_0+\widehat C_a+\widehat C_b$:

$$
D_n(\eta) = \frac1{n!}\langle \mathfrak I,\ \widehat C^{\,n}\Omega\rangle,
$$

i.e. `vácuo → n criações vestidas → integrar coordenadas locais → D_n`.

### 17.6 Recuperando o grau pitagórico

$$
d(p,q,r) = 2pq+2pr+2qr = n^2-p^2-q^2-r^2,
$$

coeficiente líder $(b-a)^{2pq}a^{2pr}b^{2qr}L_pL_qL_r$, $L_m=\prod_{j=0}^{m-1}(j!)^2$ — não nulo, confirmando que o grau é exato (prova independente via resultantes).

```
PAIRWISE RESULTANT DRESSING — FECHADO
ABELIAN YANG–BAXTER / CREATION FLATNESS — FECHADO
```

---

## 18. Registro de Status

| # | Gate | Status |
|---|------|--------|
| 1 | Observabilidade não-colapsante dos defect states | **FECHADO** |
| 2 | Limite único da covariância de métrica de retorno | **FECHADO** (limite da covariância euclidiana crua: em aberto, não necessário) |
| 3 | Par espectral de câmeras $(G_C,H_C,L_C)$ | **FECHADO** |
| 4 | Segundo momento centrado + POVM de câmeras comutativo | **FECHADO** |
| 5 | Limite funcional polinomial/analítico | **FECHADO** |
| 6 | Transformada de Cauchy/Stieltjes das câmeras | **FECHADO** |
| 7 | Família de Weyl emergente das câmeras | **CONSTRUÍDA** |
| 8 | Realização Jacobi do modo misto 3–4–6 (sentido espectral) | **FECHADO** |
| 9 | Especialização coupled-$P_V$ de dois jumps | **FECHADO / AUDITADO** |
| 10 | Anulador mínimo de coeficientes constantes da tau | **FECHADO** |
| 11 | Eliminação de polarização via fechamento holonômico da tau | **FECHADO** |
| 12 | Compatibilidade Toda–holonômica triangular | **FECHADO** |
| 13 | Álgebra de operadores de criação de três cores | **CONSTRUÍDA** |
| 14 | Dressing por resultantes em pares / Yang–Baxter abeliano | **FECHADO** |
| 15 | Weyl comum de alturas $m_\Xi$ e gate Pick/Green | **CONSTRUÍDA; POSITIVIDADE GLOBAL CONDICIONAL À RH** |
| 16 | Operador fixo de alturas $T_N=J_N^{-1/2}$ por momentos | **CONSTRUÍDO / AUDITADO ATÉ ORDEM 28** |
| — | Fatoração $G_N=X_N^*X_N$, $K_N=X_N^*Y_{\rm carry}X_N$ diretamente pela TFVD/Green nativa | **EM ABERTO — GATE PRINCIPAL** |
| — | Colapso escalar JMO-$P_V$ da sigma-PDE de dois jumps | **NÃO ENCONTRADO** (obstrução estrutural: $\log2/\log(3/2)\notin\mathbb Q$) |
| — | Pushforward $C_2$ $Z(s)=\zeta_{\text{odd}}(s) \equiv$ tau $D_n$ | **NÃO AFIRMADO** (apenas analogia arquitetural) |

---

## 19. Próximos Passos em Aberto

1. **Aniquiladores vestidos.** Construir $\widehat A_i$ para o espaço de Fock vestido por resultantes e calcular $[\widehat A_i,\widehat C_j]$; espera-se que seja a forma operatorial do defeito de dupla comutação $D_{ij}^{(n)}$ (seção 16.5).
2. **Ordem não-linear mínima.** A ODE escalar de ordem $N_n-1$ para $g_n=\sigma_n/\eta$ obtida via redução por polinômios de Bell não é afirmada mínima como equação *não-linear* — comparar com reduções genuínas do tipo Painlevé.
3. **Rede triangular ↔ intertwining de Toda.** Formalizar como $H_n^{\min}\to H_{n+1}^{\min}$ (linear, holonômico) e $\Theta_n\to\Theta_{n+1}$ (não-linear, Toda) coerem como dois fluxos compatíveis na mesma flag $V_0\subset V_1\subset\cdots$.
4. **Identificação da medida/segundo momento para $\det(H_C-\lambda G_C)$ vs. verificação formal em Lean** — todos os status "fechado" acima são fechados por *auditoria numérica + derivação simbólica*, não por prova verificada por máquina.
5. **Fatoração Green dos momentos de altura.** Derivar, a partir dos defect
   states e do retorno TFVD native-carry, operadores $X_N$ e um
   $Y_{\rm carry}\ge0$ tais que
   $G_N=X_N^*X_N$ e $K_N=X_N^*Y_{\rm carry}X_N$, compatíveis em $N$.
   Esse é o passo que poderia transformar a positividade observada em geometria
   nativa; aumentar cutoffs, sozinho, não o substitui.

---

### Nota de reprodutibilidade

As auditorias numéricas ao longo do texto usaram `mpmath` com 90–340 dígitos decimais; as magnitudes de erro reportadas são discrepâncias absolutas/relativas entre grandezas derivadas independentemente por forma fechada e por construção iterativa/numérica (ortogonalização de determinante de Hankel vs. recursão de ladder discreta vs. truncamento de fração contínua vs. diferenciação de integral de Cauchy). Onde o código-fonte Python estava disponível inline na conversa original, ele foi omitido aqui por questão de extensão; as fórmulas são declaradas por completo em LaTeX para que as auditorias sejam reproduzíveis de forma independente.

---

## 20. Ramo de Alturas: Weyl Completada e Operador de Jacobi Fixo

### 20.1 Separação dos dois parâmetros espectrais

O operador de câmeras $L_C$ construído nas seções 5--10 tem espectro de
**escalas logarítmicas**. A variável de órbita $t$ em
$e^{-itL}$ é dual a essas escalas; ela não pode ser obtida renomeando os
autovalores $\log n$ ou os autovalores de $L_C$.

Para obter um operador cujos autovalores sejam alturas, foi necessário abrir um
segundo canal de Weyl. As identidades exatas das câmeras dão

$$
\chi_b(s)=\kappa_b(s)\zeta(s),
$$

e, depois de remover o fator geométrico conhecido $\kappa_b$ e completar,

$$
F(z)=\xi\!\left(\frac12+iz\right),
\qquad
m_\Xi(z)=-\frac{F'(z)}{F(z)}.
$$

Todas as câmeras fiéis produzem a mesma $m_\Xi$. O teste de Weyl/Green correto é

$$
K_\Xi(z,w)=
\frac{m_\Xi(z)-\overline{m_\Xi(w)}}{z-\overline w}\succeq0.
$$

Essa positividade para todo o semiplano superior equivale a todos os zeros de
$F$ serem reais. Portanto ela tem a força lógica da RH e não foi declarada
provada por amostragem numérica.

### 20.2 Redução par e momentos

Como $F$ é par, escreva $F(z)=F(0)\Phi(z^2)$ e ponha

$$
q(u)=-\frac{\Phi'(u)}{\Phi(u)}
=\frac{m_\Xi(z)}{2z}
=\sum_{k\ge0}h_ku^k.
$$

Sob o gate global,

$$
h_k=\sum_{\gamma>0}r_\gamma\gamma^{-2k-2}
=\int y^k\,d\rho(y),
\qquad
\rho=\sum_{\gamma>0}r_\gamma\gamma^{-2}
\delta_{\gamma^{-2}}.
$$

Na amplificação que preserva multiplicidades, $\widehat Y=\widehat T^{-2}$ é
classe traço e

$$
\Phi(u)=\det(I-u\widehat T^{-2}),\qquad
q(u)=\operatorname{Tr}(\widehat T^2-uI)^{-1},\qquad
h_k=\operatorname{Tr}(\widehat T^{-2k-2}).
$$

Assim a função completada é, condicionalmente ao gate, um determinante
espectral de Fredholm genuíno do operador fixo.

Os números $h_k$ são calculáveis diretamente pelos coeficientes de Taylor de
$F$, sem fornecer uma tabela de zeros. Formam-se os Hankels

$$
G_N=(h_{i+j}),\qquad K_N=(h_{i+j+1}),
$$

e, se positivos,

$$
G_N=R_NR_N^T,qquad
J_N=R_N^{-1}K_NR_N^{-T},qquad
\boxed{T_N=J_N^{-1/2}}.
$$

$T_N$ é uma única matriz real simétrica, fixa e independente de $t$. Não é o
pencil $2\times2$ dependente do ponto de avaliação.

### 20.3 Auditoria atual

Com até 340 dígitos, dois círculos de Cauchy independentes e 56 workers:

- $G_{28}$ e $K_{28}$ ficaram positivos na precisão testada;
- $J_{28}$ ficou tridiagonal até defeito $2{,}77\times10^{-269}$;
- a primeira altura teve erro $4{,}67\times10^{-79}$;
- quatorze alturas foram recuperadas progressivamente, sem serem
  usadas na construção;
- o controle com $-i\zeta'/\zeta$ sem completação falhou no gate de
  Herglotz, mostrando que o termo arquimediano é estrutural.

O modelo escalar é cíclico: multiplicidades aparecem nos pesos/resíduos. Uma
amplificação por fibras é necessária para realizá-las também como dimensões de
autoespaço.

### 20.4 Fechamento de Green finito

Na base dos jets monomiais, o operador generalizado

$$
A_N=G_N^{-1}K_N
$$

é o shift $S_Ne_j=e_{j+1}$ em todos os graus $j<N-1$ e difere dele somente
por uma condição de bordo de posto um:

$$
\boxed{A_N=S_N+c_Ne_{N-1}^*,\qquad
c_N=G_N^{-1}(h_N,\ldots,h_{2N-1})^T.}
$$

Ele satisfaz exatamente

$$
A_N^*G_N=G_NA_N=K_N.
$$

O shift interior com a métrica $G_N$ deixa um parâmetro real de extensão. A
torre de momentos o seleciona por

$$
(G_Nc_N)_{N-1}=h_{2N-1}.
$$

Logo esse parâmetro de bordo vem da compatibilidade entre ordens; ele não é a
altura $t$ e não é ajustado contra uma tabela de zeros.

Portanto o operador é primeiro autoadjunto na métrica de retorno $G_N$; a
Cholesky apenas o transporta para a matriz euclidiana simétrica $J_N$. Essa
condição de bordo é determinada pelos momentos e não contém parâmetros livres.

### 20.5 Gate geométrico remanescente

A construção fornece o alvo, mas ainda importa a completação $\xi$ como dado
clássico externo. O próximo teorema não é “ajustar melhor os autovalores”; é
derivar os Grams de momentos pela geometria já existente:

$$
\boxed{
G_N=X_N^*X_N,
\qquad
K_N=X_N^*Y_{\rm carry}X_N,
\qquad Y_{\rm carry}\ge0.
}
$$

Se essa fatoração sair dos defect states/TFVD/Green e for compatível em toda
ordem, ela fecha exatamente a ponte que ainda falta entre a geometria
native-carry e o operador de alturas. As derivações, o firewall lógico, os
números completos e o posicionamento bibliográfico estão em
`NATIVE_CARRY_CANONICAL_HEIGHT_WEYL_GATE_LOG.md` e
`NATIVE_CARRY_HEIGHT_MOMENT_JACOBI_OPERATOR_LOG.md`.
