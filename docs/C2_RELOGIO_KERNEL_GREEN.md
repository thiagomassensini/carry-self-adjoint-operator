# O relógio corrigido no kernel Green–Wronskian

Denote por $I(s)$ a integral do relógio C2 e por $D(s)$ a
correção original. Ponha $s_0=1/2$, $F(z)=D(s_0+iz)I(s_0+iz)$
perto do centro e
\[
 L(t)=\log\frac{D(s_0+t)I(s_0+t)}{D(s_0)I(s_0)} .
\]
O logaritmo é um germe analítico no centro. Sua série é
$\sum_{n\ge0}(-1)^nh_nt^{2n+2}/(n+1)$ no disco local.

## Transporte de dois argumentos

O novo módulo Lean usa a mesma densidade $f(x)=(1+e^x)^{-1}$
e integra $x^{s-1}f(x)$ também para $s$ complexo. O
majorante que já controla a fonte real controla a norma
do integrando complexo no mesmo intervalo de partes reais.
A mudança de escala $x\mapsto2x$ na densidade de pernas
reproduz e cancela o mesmo $1+2^{-s}$ que aparece no fator
da carta. Com a correção completa, o produto complexo
é o germe nativo $F(-it)$ na coordenada $t$.

Use $\mathcal Q(t,v)=\tfrac12\operatorname{dslope}(L')(t,v)$,
onde a diagonal toma a derivada. Se $R=-F'/(2F)$, a identidade
hermitiana na convenção do CSA é
\[
 \mathcal Q(i\bar z,iw)=\operatorname{dslope}(R)(\bar z,w).
\]
A primeira coordenada é $i\bar z=-\overline{iz}$. Fora de
$w=\bar z$, o lado direito é
$(R(w)-R(\bar z))/(w-\bar z)$.
Na colisão, os dois lados usam a derivada removível.
No eixo real do relógio os blocos de coeficientes são
$JH_NJ$ e $-JK_NJ$, com os cruzamentos entre paridades
iguais a zero. Após a rotação analítica os fatores de $i$
dão os coeficientes $H_N$ e $K_N$ na polarização de altura.

O Lean liga a mesma função à leitura material TFVD/Green
completa de seis fontes, fora da colisão e em qualquer corte.
Em cada dimensão radial fixa, as seções de amostras inteiras,
incluindo os cruzamentos, coincidem a partir de algum índice
de escala. Os limites mistos das diferenças finitas da leitura
material no eixo real são os coeficientes polarizados em
cumulantes corrigidos.
[Identificação TFVD anterior](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/d7e973eefbc7377b88c3fb986bab6caf898000a9/CarrySelfAdjointOperator/PrimeDepthAllOrderMomentBridge.lean#L404)

## Uma parcela exata do cancelamento

Integre por partes, para $\Re s>0$. O produto que resulta é
\[
 sI(s)=\int_0^\infty x^s(-f'(x))\,dx,
\qquad
 -f'(x)=\frac{e^x}{(1+e^x)^2}.
\]
Os termos de bordo desaparecem por $\Re s>0$ no zero e pelo
decaimento de $f$ no infinito. Seja $Y=\log x$ sob a lei com
densidade proporcional a $x^{s_0}(-f'(x))\,dx$. Se $X$ tem
a lei do relógio original, então
\[
 M_X(t)=\frac{s_0}{s_0+t}M_Y(t).
\]
Como $s_0/(s_0+t)$ é a função geradora de $-E$, com
$E\sim\operatorname{Exp}(s_0)$, a igualdade identifica
$X\overset d=Y-E$, para $E$ independente de $Y$.
No logaritmo, o fator $s$ do completamento retira
exatamente essa componente em toda ordem. Em particular
ela explica $4$ da variância $4{,}72147833737748$
do relógio original.

Pela duplicação da Gamma, com
$Q(s)=(1-2^{1-s})/(s-1)$,
\[
 D(s)=\frac{\sqrt{\pi}\,s\,(2\sqrt{\pi})^{-s}}
             {\Gamma((s+1)/2)\,Q(s)},\qquad
 Q(s)=\int_0^{\log2}e^{(1-s)b}\,db.
\]
Se $G=\tfrac12\log Z$, com $Z\sim\operatorname{Gamma}(3/4,1)$,
e $B$ tem densidade proporcional a $e^{b/2}$ em $[0,\log2]$,
a característica normalizada em coordenada de relógio é
\[
 e^{L(t)}=(2\sqrt{\pi})^{-t}
       \frac{M_Y(t)}{M_G(t)M_{-B}(t)}.
\]
Essas identidades usam funções geradoras perto de zero.
Depois do cancelamento exponencial, a diferença do logaritmo
é literalmente a diferença entre os jatos destas três leis.
Em ordem dois,
\[
 2h_0=\operatorname{Var}(Y)-\operatorname{Var}(G)
                          -\operatorname{Var}(B).
\]
A quadratura do primeiro termo e as expressões dos outros
dois dão, aproximadamente, $0{,}72147833738$, $0{,}63546991192$
e $0{,}03979843923$. A identidade probabilística é uma
dedução analítica. A checagem numérica é diagnóstica.
[Duplicação da Gamma](https://dlmf.nist.gov/5.5#E5)

A diferença $X-X'$ concentra naturalmente os cumulantes
pares. Para a própria característica ser par, ainda é a
identidade nativa que garante que os termos ímpares da fonte
e da correção se cancelam. No nível matricial, dividir por
funções geradoras de leis positivas subtrai respostas
logarítmicas. O sinal da diferença exige controle conjunto
dos cruzamentos.

## A desigualdade material

O comparador positivo concreto do CSA é o Gram Cauchy
incidente. O defeito é o Gram do retorno pelo multiplicador
quiral. Para qualquer vetor de coeficientes, com as mesmas
amplitudes em ambos os canais, a leitura física é a diferença
das duas normas quadradas, com o fator de normalização $1/2$.
O Lean transporta para o kernel do relógio a equivalência
entre semidefinição positiva da seção e contração desse
retorno em todo o span. Em duas amostras radiais, as alturas
são $it$ e $2it$. Se os valores do multiplicador são $\chi_0$
e $\chi_1$, o determinante exige o controle
\[
 8|\chi_1-\chi_0|^2 \le
 (1-|\chi_0|^2)(1-|\chi_1|^2).
\]
O CSA já certifica esse cruzamento, além das diagonais, para
tilts suficientemente pequenos. O módulo transporta essa
semidefinição positiva ao kernel do relógio em dimensão dois.
A contração em toda dimensão segue em aberto. O sinal ímpar
no eixo do relógio é o fator da rotação de coordenada.
[Energia incidente e retornada](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/d7e973eefbc7377b88c3fb986bab6caf898000a9/CarrySelfAdjointOperator/CompletedNativeTfvdSixSourceChiralDefect.lean#L111)
· [Cruzamento de duas amostras](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/d7e973eefbc7377b88c3fb986bab6caf898000a9/CarrySelfAdjointOperator/CompletedNativeChiralTwoPointControl.lean#L55)
