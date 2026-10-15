# Quarto canal positivo e a família theta comum

Data: 2026-10-15. Repositório canônico: `carry-self-adjoint-operator`, servidor `llm`. Base: `6275d8fa066743436b50c2ebba1355f38f82eca1`.

## A derivada efetiva da quarta etapa

A resposta da fonte completada permanece a existente, sintetizada antes do readout, localmente

\[
r_0(z)=-F'(z)/(2F(z)).
\]

A redução é a mesma em cada etapa:

\[
A_j=\operatorname{dslope}(r_j,0,\cdot),\qquad
 a_j=\operatorname{Re}A_j(0),\qquad
r_{j+1}=\frac{\operatorname{dslope}(A_j,0,\cdot)}{a_jA_j}.
\]

Escrevendo \(m_j=\texttt{canonicalCompletedNativeLogDerivativeMoment}\ j\),

\[
\Delta_0=m_0m_2-m_1^2,\qquad \Delta_1=m_1m_3-m_2^2,
\]

foi formalizado o teorema sobre a resposta analítica **já definida**:

\[
\boxed{r_3'(0)=a_3=\frac{m_1\Delta_1}{\Delta_0^2}>0.}
\]

A escala não foi definida por esse quociente. Primeiro se extrai a derivada pela recorrência da fonte; depois se aplica o certificado theta independente de \(\Delta_1\).

`NativeCompletedSourceFourthPositiveChannel.lean` também prova:

- \(r_3(0)=0\);
- \(A_3(0)=a_3\in\mathbb R\);
- analiticidade de \(A_3\) e da resposta residual seguinte \(r_4\) no centro;
- uma vizinhança aberta de zero onde os quatro primeiros eixos são não nulos;
- o prefixo de quatro canais e sua identidade de energia para qualquer número finito de entradas.

## Como a conta algébrica foi ligada aos jatos analíticos

A mudança \(t=z^2\) fornece exatamente a expansão descrita pelo usuário. A formalização usa diretamente os jatos em \(z\), evitando introduzir uma nova resposta:

\[
[z^4]r_1=0,
\qquad
[z^5]r_1=\frac{m_3}{m_0^2}-\frac{2m_1m_2}{m_0^3}+\frac{m_1^3}{m_0^4},
\]

\[
[z^2]r_2=0,
\qquad
[z^3]r_2=\frac{m_0^2\Delta_1}{m_1^3}.
\]

Esses coeficientes vêm das identidades de germes analíticos

\[
A_0r_1=\operatorname{dslope}(A_0,0,\cdot)/a_0,
\qquad
A_1r_2=\operatorname{dslope}(A_1,0,\cdot)/a_1.
\]

O jato quadrático nulo de \(r_2\) dá \(r_3(0)=0\). O jato cúbico, dividido por \(a_2^2\), fornece a derivada de \(r_3\). As realidades, sinais e não anulações necessários são demonstrados pelos resultados da própria fonte, sem hipótese de positividade do kernel pretendido.

## Quatro canais, com o residual inteiro

Para os canais existentes

\[
W_n=\prod_{j<n}r_j,\qquad
\phi_j=\frac{W_jA_j}{\sqrt{a_j}},\qquad
K_j(z,w)=\frac{r_j(w)-\overline{r_j(z)}}{w-\bar z},
\]

há uma vizinhança da fonte em que, para \(w\ne\bar z\),

\[
\boxed{K_0(z,w)=\sum_{j<4}\overline{\phi_j(z)}\phi_j(w)
 +\overline{W_4(z)}W_4(w)K_4(z,w).}
\]

`nativeKernel_four_positive_channels_local` identifica a expressão com o kernel original de \(-F'/(2F)\). Para qualquer \(N\) finito, sob as condições de regularidade e separação exibidas, `chain_four_channel_finite_energy` mantém todos os cruzamentos:

\[
\sum_{i,k}\bar c_ic_k K_0(z_i,z_k)
=\sum_{j<4}\left|\sum_i c_i\phi_j(z_i)\right|^2
 +\sum_{i,k}\overline{c_iW_4(z_i)}c_kW_4(z_k)K_4(z_i,z_k).
\]

Nenhum sinal ou desaparecimento foi atribuído ao último termo. As fórmulas divididas acima não incluem a diagonal real removível \(w=\bar z\).

## Já existe uma representação theta comum em todas as ordens

Os módulos existentes `NativeSourceThetaMomentPolynomials.lean`, `NativeSourceAllOrderSchur.lean`, `NativeSourceSchurThetaIntegral.lean` e `NativeSourceSchurThetaMasses.lean` fornecem uma família única, determinada pela fonte.

Seja \(c_0\) o coeficiente constante da característica completada, \(\Phi\) o kernel theta positivo original e

\[
H_{s,n}=(m_{i+j+s})_{0\le i,j<n},\quad
b_{s,n}=(m_{i+n+s})_{0\le i<n},
\]

\[
R_{s,n}=c_0\left(m_{2n+s}-b_{s,n}^{\mathsf T}H_{s,n}^{-1}b_{s,n}\right).
\]

A inversa total do Lean aparece na definição; a costura geral de Schur usa a positividade/invertibilidade do prefixo anterior, explicitamente. Os polinômios \(P_k=\texttt{nativeThetaMomentPolynomial}\ k\) são gerados pela recorrência dos coeficientes da característica, e

\[
\int_0^\infty P_k(u)\Phi(u)\,du=m_k.
\]

Com \(v=(-H_{s,n}^{-1}b_{s,n},1)\), define-se

\[
Q_{s,n}(u)=c_0\sum_{i,j=0}^{n}v_iv_jP_{i+j+s}(u).
\]

A identidade existente, válida em todas as ordens, é

\[
\boxed{R_{s,n}=\int_0^\infty Q_{s,n}(u)\Phi(u)\,du
=M^+_{s,n}-M^-_{s,n}.}
\]

Aqui \(M^+=\int\max(Q,0)\Phi\) e \(M^-=\int\max(-Q,0)\Phi\). A positividade estrita da energia nativa de fronteira em todas as ordens equivale exatamente a

\[
\forall n,\quad M^-_{0,n}<M^+_{0,n}\quad\text{e}\quad M^-_{1,n}<M^+_{1,n}.
\]

Esse é um critério formalizado. A desigualdade geral permanece aberta.

## Nova ligação: a quarta escala é um membro dessa mesma família

`NativeCompletedSourceFourthThetaScale.lean` identifica

\[
R_{1,1}=c_0\frac{\Delta_1}{m_1},
\]

\[
\boxed{
a_3=\frac{m_1^2}{c_0\Delta_0^2}
\int_0^\infty Q_{1,1}(u)\Phi(u)\,du.
}
\]

O fator é estritamente positivo. Assim, a escala da resposta efetiva está ligada ao mesmo objeto theta usado no critério de todas as ordens. Foi demonstrado também

\[
0<M^-_{1,1}<M^+_{1,1}.
\]

A massa negativa é efetiva, não um artefato descartado. O coeficiente de grau oito é

\[
[u^8]Q_{1,1}=-1/10080.
\]

Mais geralmente, o teorema existente `nativeSchurThetaPolynomial_odd_density_eventually_neg` prova a cauda negativa no setor ímpar em todas as ordens. Isso impede ler **essa densidade particular** como uma norma quadrada ponto a ponto; não refuta a positividade de sua integral ou outras representações da fonte.

## O próximo alvo estrutural

A família theta comum e sua construção já estão disponíveis. O que falta é um mecanismo uniforme de dominação das massas assinadas, ou um transporte exato que converta essa mesma integral em uma energia positiva.

A válvula projetiva também já está ligada a essa família: `nativeThetaPolynomialSeries_eq_projectiveValve` gera os polinômios a partir da série da característica e do numerador derivado. A identidade preserva a fonte, mas não fornece o sinal da integral. O transporte Green existente é \(Q\mapsto Q''-Q/4\), com fluxos de fronteira controlados; ele troca o sinal do termo dominante e tampouco torna os dois setores positivos ponto a ponto.

Uma obrigação estrutural concreta para a próxima investigação é controlar \(M^-_{s,n}\) por \(M^+_{s,n}\), para os dois setores e todo \(n\), usando as relações da fonte e da válvula. A especialização \((s,n)=(1,1)\) agora está calibrada com a derivada da cadeia e com seu certificado theta. Uma indução ou estimativa uniforme que preserve esse balanço seria um avanço adicional; sua existência não foi demonstrada aqui.

Continuam abertas a positividade de todas as escalas, o domínio adequado em todas as profundidades, o controle do residual infinito e a identificação com o defeito do transporte físico. Nenhuma dessas obrigações foi introduzida como axioma.

## Validação

- Alvo `CarrySelfAdjointOperator.NativeCompletedSourceFourthPositiveChannelAudit`, com `lake build --wfail`: sucesso, 9980 jobs.
- Build padrão completo `lake build --wfail`: sucesso, 10209 jobs.
- Auditoria de 35 raízes públicas: fechamento de 6859 declarações por tipos e corpos; apenas `propext`, `Classical.choice`, `Quot.sound`.
- Nenhum `sorry`, `admit` ou novo axioma. O manifesto de dependências não foi alterado.
- Trabalho isolado em `/home/thlinux/carry-fourth-positive-channel`; os dois arquivos C2 preexistentes não rastreados no checkout canônico foram preservados.

Os resumos de build e de axiomas ficam em `verification.log`, com SHA256 dos logs integrais; o estado final de publicação e a verificação após integração são registrados na entrega.
