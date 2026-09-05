# Jets de defeito TFVD, mapa $X_N$ e positividade de $Y_{\mathrm{carry}}$

Data da auditoria: 17 de agosto de 2026.

## Adendo de cronologia causal

O autor esclareceu depois desta auditoria que a ordem histórica da descoberta
foi

$$
\text{geometria do carry}
\to\text{pushforward}
\to\text{TFVD}
\to\text{Green}
\to\text{Weyl},
$$

e que essa cadeia nasceu sem primos, zeros, zeta ou fatores de Euler. Isso
muda a interpretação, mas não altera as identidades finitas abaixo.

Onde esta nota diz que falta um crosswalk, deve-se ler: **o crosswalk ainda
não foi localizado e certificado no corpus disponível**, e não que a ponte
tenha de ser inventada posteriormente ou que o operador tenha sido construído
a partir dos zeros. A tarefa correta é recuperar a derivação geométrica
Green$\to$Weyl e provar que sua apresentação por jets coincide com a
realização finita encontrada aqui.

O registro detalhado dessa correção está em
`CARRY_GEOMETRY_TFVD_GREEN_WEYL_CAUSAL_CHRONOLOGY.md`.

Repositórios conferidos:

- `thiagomassensini/primos`, `main` em `239a00fa1d80509a7049b74902cbffb28fb31516`;
- PR 47 de `primos`, head `dee56dec8a9e52af0f9a75795da988afb0ff0e87`;
- `thiagomassensini/genuine-zero-uniform-atlas-energy`, `main` em
  `6b58e161395121137dd0b37028db358675a229f0`;
- PR 9 do atlas, head auditado `ec69f8cacff31f583f7519d43e7a712fa7f6844b`.

## Conclusão curta

Há uma derivação exata, em toda ordem finita positiva, que expressa o mapa já
denotado por $X_N$ como mapa de jets de um estado de defeito:

$$
\boxed{
X_Ne_j=x_j,
\qquad
x_j=\frac{1}{j!}\,\partial_u^j\gamma_N(0)
=Y_N^jx_0.
}
$$

Com

$$
\gamma_N(u)=(I-uY_N)^{-1}x_0,
\qquad
x_0=\sqrt{h_0}\,e_0,
$$

obtêm-se exatamente

$$
\boxed{G_N=X_N^*X_N},
\qquad
\boxed{K_N=X_N^*Y_NX_N}.
$$

Além disso, $X_N$ não é somente equivalente ao fator já encontrado por
Cholesky: na base ortonormal de polinômios ele é literalmente

$$
\boxed{X_N=L_N^*},
\qquad G_N=L_NL_N^*.
$$

A positividade também fecha finitamente:

$$
\boxed{Y_N\geq0\iff K_N\geq0},
$$

pois $X_N$ é invertível. Entretanto, é importante separar duas afirmações:

1. a identidade de Green antissimétrica fornece simetria/autoadjunticidade e o
   primeiro kernel de Weyl;
2. o sinal $Y_N\geq0$ exige a identidade de **energia Green positiva**, ou,
   equivalentemente, que o kernel deslocado de $q$ seja positivo.

Portanto, “Green puro” não dá o sinal. Green mais o readout quadrático positivo
do carry dá o sinal diretamente por uma fatoração $Y_N=C_N^*C_N$.

O Lean já contém quase todas as peças abstratas e vários crosswalks finitos,
mas não encontrei no estado auditado um teorema que identifique os jets da Weyl
de alturas com os estados de defeito TFVD e, simultaneamente, identifique
$K_N$ com a energia Green positiva nativa. Esse é o lema novo e preciso que
falta para chamar o $Y_N$ de `Y_carry` sem circularidade.

## 1. Dados de momentos

Partimos da função par reduzida

$$
F(z)=F(0)\Phi(z^2),
\qquad
q(u)=-\frac{\Phi'(u)}{\Phi(u)}
=\sum_{k\geq0}h_ku^k.
$$

Em ordem $N$, definimos os dois Hankels

$$
(G_N)_{ij}=h_{i+j},
\qquad
(K_N)_{ij}=h_{i+j+1},
\qquad 0\leq i,j<N.
$$

Suponha, nesta ordem finita,

$$
G_N>0,
\qquad K_N\geq0.
$$

Se $G_N=L_NL_N^*$ é o Cholesky inferior, ponha

$$
\boxed{
Y_N=L_N^{-1}K_NL_N^{-*},
\qquad
X_N=L_N^*.
}
$$

Então

$$
X_N^*X_N=L_NL_N^*=G_N
$$

e

$$
X_N^*Y_NX_N
=L_N\left(L_N^{-1}K_NL_N^{-*}\right)L_N^*
=K_N.
$$

Essa é a fatoração Green já observada, agora com interpretação de jets.

## 2. Por que as colunas de $X_N$ são jets

Defina

$$
x_0=X_Ne_0=\sqrt{h_0}\,e_0.
$$

Para $0\leq j<N-1$, a estrutura Hankel dá a identidade de colunas

$$
K_Ne_j=G_Ne_{j+1}.
$$

Logo

$$
\begin{aligned}
Y_NX_Ne_j
&=L_N^{-1}K_NL_N^{-*}L_N^*e_j\\
&=L_N^{-1}K_Ne_j\\
&=L_N^{-1}G_Ne_{j+1}\\
&=L_N^*e_{j+1}\\
&=X_Ne_{j+1}.
\end{aligned}
$$

Por indução,

$$
\boxed{X_Ne_j=Y_N^jx_0},
\qquad 0\leq j<N.
$$

Agora introduza o estado de defeito finito

$$
\boxed{\gamma_N(u)=(I-uY_N)^{-1}x_0}.
$$

Perto de $u=0$,

$$
\gamma_N(u)=\sum_{j\geq0}u^jY_N^jx_0,
$$

portanto

$$
\boxed{
x_j=Y_N^jx_0
=\frac{1}{j!}\partial_u^j\gamma_N(0).
}
$$

Assim, $X_N$ é o operador que empacota os primeiros $N$ jets dos estados
de defeito.

## 3. As duas identidades de Weyl/Green

Defina a aproximação racional de Weyl

$$
q_N(u)=\langle x_0,(I-uY_N)^{-1}x_0\rangle
=\langle x_0,\gamma_N(u)\rangle
$$

e a função de fronteira

$$
M_N(u)=u q_N(u).
$$

As identidades de resolvente fornecem

$$
\boxed{
\frac{M_N(u)-\overline{M_N(v)}}{u-\bar v}
=\langle\gamma_N(v),\gamma_N(u)\rangle
}
$$

e

$$
\boxed{
\frac{q_N(u)-\overline{q_N(v)}}{u-\bar v}
=\langle\gamma_N(v),Y_N\gamma_N(u)\rangle.
}
$$

A primeira é a identidade de Green/Weyl dos estados de defeito. Expandindo-a
em $u,\bar v$,

$$
\frac{u q(u)-\bar v\,\overline{q(v)}}{u-\bar v}
=\sum_{i,j\geq0}h_{i+j}u^i\bar v^j,
$$

e então

$$
\langle x_i,x_j\rangle=h_{i+j}.
$$

A segunda identidade expande como

$$
\frac{q(u)-\overline{q(v)}}{u-\bar v}
=\sum_{i,j\geq0}h_{i+j+1}u^i\bar v^j,
$$

portanto

$$
\langle x_i,Y_Nx_j\rangle=h_{i+j+1}.
$$

Isso recupera simultaneamente $G_N$ e $K_N$ a partir dos jets.

## 4. Derivação direta de $Y_N\geq0$

Para qualquer $c\in\mathbb C^N$,

$$
\langle X_Nc,Y_NX_Nc\rangle=c^*K_Nc.
$$

Como $X_N$ é invertível,

$$
K_N\geq0
\quad\Longrightarrow\quad
Y_N\geq0.
$$

Se a identidade Green positiva nativa produzir um mapa de energia $B_N$ tal
que

$$
K_N=B_N^*B_N,
$$

defina

$$
C_N=B_NX_N^{-1}.
$$

Então

$$
\boxed{
Y_N=X_N^{-*}K_NX_N^{-1}=C_N^*C_N\geq0.
}
$$

Esta é a forma exata da derivação “direto da identidade de Green”: a forma
quadrática Green/TFVD precisa ser identificada com o Hankel deslocado.

### Por que a identidade antissimétrica não basta

A identidade de Lagrange--Green

$$
\langle S^*f,g\rangle-\langle f,S^*g\rangle
=\langle\Gamma_1f,\Gamma_0g\rangle
-\langle\Gamma_0f,\Gamma_1g\rangle
$$

prova simetria da relação de fronteira e realidade de seus slopes. Ela não
seleciona o semieixo positivo do espectro. Um operador autoadjunto pode ter
espectro negativo e continuar satisfazendo Green. Por exemplo, $Y=-I$ em
$\mathbb C$ é autoadjunto, mas não positivo.

O dado adicional equivalente ao sinal é um dos seguintes:

- positividade do kernel deslocado de $q$;
- $q$ pertencer à classe Stieltjes adequada;
- uma identidade nativa $K_N=B_N^*B_N$;
- uma realização direta $Y_{\mathrm{carry}}=C^*C$.

## 5. O que já está em Lean

### Peças realmente formalizadas

1. `CpFiniteSeededTfvdGreenIdentity.lean` prova a decomposição finita exata da
   forma TFVD em fluxo Green, endpoint e defeito de proveniência. O comentário
   do teorema de endpoint registra corretamente que seu fechamento não implica
   sozinho o fechamento da forma bilinear de bordo.

2. `CpNativeGpreHilbertGluedGreenDefect.lean` prova que o defeito Green Hilbert
   colado é exatamente o Wronskiano vertical e que um domínio isotrópico dá uma
   relação simétrica.

3. `CpNativeCarrySelfAdjointBoundaryRelation.lean` prova diretamente por Green
   que todo slope de uma relação simétrica é real. Também prova que a relação
   TFVD vertical livre é o plano inteiro e não é simétrica: é necessária uma
   restrição/colagem genuína.

4. `CpNativeCarryReflectedLogBoundaryCayley.lean` constrói uma relação
   autoadjunta concreta no canal diagonal refletido. Ela é o gráfico do operador
   zero. O próprio módulo preserva como alvo a ponte que põe o fechamento do
   bracket nessa condição; portanto ela ainda não é o operador de alturas.

5. `CpTfvdSeededFiniteBesselConservation.lean` contém uma energia positiva
   genuína: a energia TFVD finita é igual ao quadrado da norma do estado de
   proveniência. Essa é a peça natural para fornecer um candidato a $B_N$.

6. `CpNativeCarrySelfAdjointBoundaryPencil.lean` formaliza toda a consequência
   abstrata de uma realização autoadjunta fixa, mas declara explicitamente que
   nenhuma instância da realização é construída ali.

### Guardrails Lean que impedem uma identificação circular

1. `CpC2GpreGreenActivationGuard.lean` mostra que cancelamento escalar das
   câmeras não implica energia quadrática zero, mesmo com amplitudes positivas.
   O módulo não declara uma instância do gate de ativação.

2. `CpTfvdGpreCollapseInterface.lean` nomeia como dado faltante o colapso TFVD
   fixo e independente do atlas que reproduz os momentos nativos.

3. `CpTfvdSeededNativeMomentSourceAudit.lean` mostra que postular esse source em
   todo zero cru já tem a força do alvo global; ele não pode ser fabricado a
   partir da conclusão desejada.

Esses guardrails são compatíveis com a derivação presente. Eles dizem que o
mapa de jets pode ser construído finitamente, mas a identificação

$$
\text{energia TFVD nativa}=K_N\text{ da Weyl de alturas}
$$

deve ser provada por uma igualdade independente.

### PR 47 e atlas de cutoff

A PR 47 prova uma ponte exata muito útil a montante:

$$
\text{profundidades nas câmeras primas}
\longrightarrow \log n
\longrightarrow \Lambda
\longrightarrow \text{derivada da câmera finita}.
$$

Ela fornece a primeira derivada/log-jet sem quociente e sem hipótese de zero.
Seus próprios guardrails dizem que isso ainda não contém a geometria Green
completa de endpoint/bulk. Para a construção atual, a PR 47 ajuda a produzir os
jets aritméticos, mas não prova a positividade deslocada da Weyl de alturas.

No repositório do atlas, a `main` já contém bounds exatos da cauda escalada para
valor, primeira derivada e segunda derivada. A PR 9, ainda draft no ponto
auditado, agora define a energia infinita concreta C2--C7, prova a convergência
pontual, prova que um zero Genuine anula a energia limite e fecha os capstones
regional, no strip e global condicionados somente ao certificado de
coercividade finita eventual. O próprio ledger registra esse certificado como
a fronteira quantitativa restante. Nenhum desses módulos define ainda $X_N$,
um gamma-field de alturas ou $Y_{\mathrm{carry}}$.

## 6. Lema de crosswalk que falta

Uma interface não circular suficiente seria:

1. construir um espaço Hilbert TFVD $\mathcal H_{\mathrm{TFVD}}$, um domínio
   colado fixo e estados de defeito $\gamma_{\mathrm{TFVD}}(u)$;
2. provar, sem lista de zeros,

   $$
   M_{\mathrm{TFVD}}(u)=u\,q(u),
   \qquad q(u)=-\partial_u\log\Phi(u);
   $$

3. provar uma identidade de energia positiva

   $$
   \frac{q(u)-\overline{q(v)}}{u-\bar v}
   =\langle E\gamma_{\mathrm{TFVD}}(v),
      E\gamma_{\mathrm{TFVD}}(u)\rangle;
   $$

4. definir, no subespaço cíclico,

   $$
   Y_{\mathrm{carry}}=E^*E;
   $$

5. comparar coeficientes em $u,\bar v$ para obter

   $$
   \langle x_i,x_j\rangle=h_{i+j},
   \qquad
   \langle x_i,Y_{\mathrm{carry}}x_j\rangle=h_{i+j+1}.
   $$

Daí seguem automaticamente

$$
X_N^*X_N=G_N,
\qquad
X_N^*Y_{\mathrm{carry}}X_N=K_N,
\qquad
Y_{\mathrm{carry}}\geq0.
$$

O ponto realmente novo não é mais a álgebra matricial. É a igualdade escalar
e energética entre o gamma-field TFVD e a Weyl de alturas.

## 7. Auditoria numérica independente de zeros

O laboratório `native_carry_height_moment_jacobi_operator_lab.py` foi estendido
para construir $X_N$ duas vezes:

1. como Cholesky de $G_N$;
2. como matriz de Krylov dos jets $Y_N^jx_0$.

Teste real executado:

- ordem $N=12$;
- 140 dígitos decimais;
- dois círculos de Cauchy, raios 16 e 13;
- 96 amostras por círculo;
- 56 workers;
- sem Newton;
- sem aritmética intervalar;
- sem alturas de zeros, inclusive na auditoria posterior.

Resultados:

| identidade | resíduo |
|---|---:|
| $X_N^{\mathrm{jets}}-L_N^*$ | $1.7252\times10^{-133}$ |
| $G_N-X_N^*X_N$ | $1.1325\times10^{-145}$ |
| $K_N-X_N^*Y_NX_N$ | $8.0083\times10^{-146}$ |
| $Y_N-C_N^*C_N$ | $2.6496\times10^{-120}$ |
| kernel Green de $M_N$ | $7.5679\times10^{-144}$ |
| kernel de energia de $q_N$ | $8.4164\times10^{-143}$ |

Também foram observados

$$
\lambda_{\min}(G_{12})=3.0616\times10^{-76}>0,
$$

$$
\lambda_{\min}(K_{12})=4.6977\times10^{-80}>0,
$$

e

$$
\lambda_{\min}(Y_{12})=4.4097\times10^{-6}>0.
$$

A discrepância relativa máxima entre os momentos calculados nos dois raios foi
$1.70\times10^{-35}$. O teste confirma a derivação finita; não substitui a
prova de positividade em todas as ordens.

## 8. Links primários

- [PR 47: prime-tower carry / von Mangoldt](https://github.com/thiagomassensini/primos/pull/47)
- [Self-adjoint boundary pencil](https://github.com/thiagomassensini/primos/blob/main/CPFormal/Analytic/CpNativeCarrySelfAdjointBoundaryPencil.lean)
- [Self-adjoint boundary relation](https://github.com/thiagomassensini/primos/blob/main/CPFormal/Analytic/CpNativeCarrySelfAdjointBoundaryRelation.lean)
- [Hilbert glued Green defect](https://github.com/thiagomassensini/primos/blob/main/CPFormal/Analytic/CpNativeGpreHilbertGluedGreenDefect.lean)
- [Finite seeded TFVD Green identity](https://github.com/thiagomassensini/primos/blob/main/CPFormal/Analytic/CpFiniteSeededTfvdGreenIdentity.lean)
- [Finite TFVD Bessel conservation](https://github.com/thiagomassensini/primos/blob/main/CPFormal/Analytic/CpTfvdSeededFiniteBesselConservation.lean)
- [C2/Gpre Green activation guard](https://github.com/thiagomassensini/primos/blob/main/CPFormal/Analytic/CpC2GpreGreenActivationGuard.lean)
- [TFVD/Gpre collapse interface](https://github.com/thiagomassensini/primos/blob/main/CPFormal/Analytic/CpTfvdGpreCollapseInterface.lean)
- [PR 8: exact scaled-tail analytic bounds](https://github.com/thiagomassensini/genuine-zero-uniform-atlas-energy/pull/8)
- [PR 9: concrete empirical limit/confinement bridge](https://github.com/thiagomassensini/genuine-zero-uniform-atlas-energy/pull/9)
