# Rigidez de resíduos para os readouts atômicos prime-carry e all-naturals

> Relatório de uma subinvestigação. Consulte o [estado consolidado da entrega](../README.md) para a integração dos dois novos módulos Lean, a auditoria final e a obrigação que continua aberta.

Derivação matemática independente, 2026-09-04. Este suplemento não afirma que a prova global abaixo já esteja formalizada em Lean. A holomorfia/continuação da característica nativa é verificada separadamente. Nenhum arquivo original foi alterado.

## 1. Enunciado geral com as hipóteses necessárias

Seja

$$
\rho=\sum_{j\ge1}m_j\delta_{\lambda_j},\qquad
m_j>0,\quad \sum_jm_j<\infty,
$$

com átomos distintos `lambda_j>0`, limitados superiormente, e apenas 0 como possível ponto de acumulação dos lambda_j. Defina

$$
a_\rho(t)=t\sum_j\frac{m_j}{1-\lambda_jt^2}.
$$

Os polos são os pontos reais discretos `t=±lambda_j^(-1/2)`. Em cada um deles,

$$
\boxed{\operatorname{Res}_{t=\pm\lambda_j^{-1/2}}a_\rho(t)
=-\frac{m_j}{2\lambda_j}.}
$$

Se vários labels têm a mesma lambda, é preciso **somar as massas desses labels primeiro**: m_j na fórmula é a massa total do átomo, não a massa individual antes da degenerescência.

Suponha que F seja holomorfa, não identicamente zero, em um aberto complexo conexo Omega contendo o eixo real inteiro, e que

$$
a_\rho(t)=-\frac{F'(t)}{2F(t)}
$$

em algum aberto não vazio de Omega onde ambos os lados são regulares. A identidade de funções meromorfas estende a igualdade por Omega. Se N_j é a ordem do zero de F no polo real correspondente, necessariamente

$$
\boxed{\frac{m_j}{\lambda_j}=N_j\in\mathbb N_{>0}.}
$$

Essa é a condição de quantização relevante. **Massas m_j fracionárias não são um problema:** é a razão m_j/lambda_j que tem de ser uma multiplicidade inteira para essa identificação específica de log-derivada. Uma medida dos momentos pode perfeitamente ter massa m_j=N_j lambda_j, usualmente não inteira.

### Justificativa analítica completa

Para qualquer compacto K afastado dos polos, ponha `R=max_K |t|`. Na cauda, `lambda_j R²≤1/2`, portanto

$$
\left|\frac{t m_j}{1-\lambda_jt^2}\right|\le2R m_j.
$$

A soma de massas é finita. A cauda converge uniformemente em K pelo teste M; os termos restantes são finitos e holomorfos em K. Assim a define uma função meromorfa em C, com somente os polos indicados.

Fixe um átomo lambda e um dos pontos a com `lambda a²=1`. O restante da série é holomorfo perto de a. O termo singular satisfaz

$$
1-\lambda t^2=-\lambda(t-a)(t+a),\qquad
(t-a)\frac{m t}{1-\lambda t^2}
=-\frac{m t}{\lambda(t+a)}\longrightarrow-\frac{m}{2\lambda}.
$$

Para F holomorfa de ordem finita N em a, a fatoração local é `F(t)=(t-a)^N g(t)`, com g holomorfa e g(a)≠0. Logo

$$
-\frac{F'(t)}{2F(t)}=-\frac N{2(t-a)}-\frac{g'(t)}{2g(t)}.
$$

O segundo termo é holomorfo localmente, e o resíduo é −N/2. Comparar os resíduos prova m/lambda=N; como m,lambda>0, N não pode ser 0.

**Limite essencial do argumento:** se F for exigida somente em um pequeno disco na origem, sem continuação até os polos, não existe essa contradição. Para qualquer a holomorfa nesse disco, `F=F(0) exp(-2 integral a)` fornece uma solução local não nula. A rigidez surge da continuação holomorfa até os polos reais, não da positividade do kernel ou da existência de um germe local.

## 2. Prime-carry: definição e agregação das profundidades

No Hilbert real com índices `(p,k)`, p primo e k≥1, defina

$$
S_{p,k}=\frac1{\log p},\qquad
u_{p,k}=\frac{p^{-k/2}}{\log p}.
$$

S é simétrico, positivo e limitado, de norma 1/log2. A fonte pertence a l² porque

$$
\|u\|^2=\sum_p\frac1{(p-1)\log^2p}
\le2\sum_{n\ge2}\frac1{n\log^2n}<\infty.
$$

Ao agregar todas as profundidades de um mesmo primo, o observável positivo V=S² e a massa são

$$
\lambda_p=\frac1{\log^2p},\qquad
m_p=\frac1{(p-1)\log^2p},
$$

pois `sum_(k≥1) p^-k=1/(p-1)`. O readout é

$$
a(t)=t\sum_p\frac1{(p-1)(\log^2p-t^2)},
$$

e tem resíduos `−1/[2(p−1)]` em t=±logp.

A uniformidade local também pode ser vista diretamente: para `logp≥2R`,

$$
\left|\frac t{(p-1)(\log^2p-t^2)}\right|
\le\frac{4R}{3(p-1)\log^2p},
$$

majorante somável. Não é necessário usar o teorema dos números primos para essa convergência; a comparação com todos os inteiros basta. Há primos arbitrariamente grandes pelo argumento de Euclides.

## 3. Massa e dilatação não consertam os resíduos desse candidato

Sejam alpha,beta reais não nulos e

$$
S'=\beta S,\qquad u'=\alpha u.
$$

Mesmo para beta<0, o observável `(S')²=beta²S²` continua positivo. O readout transformado é

$$
\begin{aligned}
a_{\alpha,\beta}(t)
&=t\langle u',(I-t^2(S')^2)^{-1}u'\rangle\\
&=\alpha^2t\langle u,(I-\beta^2t^2S^2)^{-1}u\rangle\\
&=\boxed{\frac{\alpha^2}{\beta}a(\beta t)}.
\end{aligned}
$$

O polo positivo pode ser escrito `|logp/beta|`; ambos os polos têm o mesmo resíduo. Se a função antiga tem resíduo r em t0, a composição `alpha²/beta *a(beta t)` tem resíduo `alpha² r/beta²` em t0/beta. Portanto

$$
\boxed{\operatorname{Res}a_{\alpha,\beta}
=-\frac{\alpha^2}{2\beta^2(p-1)}.}
$$

Equivalentemente, as massas e os átomos transformados são `m'_p=alpha²m_p`, `lambda'_p=beta²lambda_p`; a multiplicidade necessária seria

$$
N_p=\frac{m'_p}{\lambda'_p}=\frac C{p-1},\qquad C=\frac{\alpha^2}{\beta^2}>0.
$$

Escolha um primo `p>C+1`. Então `0<N_p<1`, impossível para uma ordem inteira. Assim **nenhuma escolha de duas constantes não nulas de massa e dilatação transforma esse readout prime-carry na log-derivada de uma F holomorfa continuável por todo o eixo real**. Uma constante aditiva em a, ou qualquer correção holomorfa perto desses polos, não altera os resíduos e não resolve essa incompatibilidade.

## 4. Variante all-naturals com coeficiente 1/n

Esta variante tem índices n≥2, não os pares `(n,k)`. Defina

$$
S_n=1/\log n,\qquad u_n=\frac1{\sqrt n\log n},\qquad
\lambda_n=1/\log^2n,\quad m_n=1/(n\log^2n).
$$

Então

$$
a(t)=t\sum_{n\ge2}\frac1{n(\log^2n-t^2)}.
$$

A mesma comparação garante normalidade local fora dos polos t=±logn. O resíduo sem escala é −1/(2n); com alpha,beta é

$$
-\frac{\alpha^2}{2\beta^2n}.
$$

A multiplicidade exigida seria C/n, que pertence a (0,1) para todo inteiro n>C. A mesma incompatibilidade global permanece sob qualquer massa/dilatação constante não nula.

Essa afirmação não se aplica por troca silenciosa a uma construção com índices `(n,k)`: nessa outra construção, a agregação das profundidades mudaria o coeficiente para 1/(n−1).

## 5. O kernel positivo continua válido

Nada acima refuta o kernel já construído para esses S,u. Para todo t real que não seja polo, as duas pernas

$$
\Phi(t)_j=\left(\frac{\sqrt{m_j}}{1-\lambda_jt^2},
\frac{t\sqrt{\lambda_jm_j}}{1-\lambda_jt^2}\right)
$$

pertencem a l²⊕l²: na cauda o denominador fica afastado de 0 e os termos restantes são finitos. Seu Gram satisfaz

$$
\langle\Phi(x),\Phi(z)\rangle
=\frac{a(z)-a(x)}{z-x},
$$

com valor a'(x) na diagonal. Todas as matrizes Gram são positivas semidefinidas, e as famílias pares/ímpares são independentes em toda ordem porque os átomos são infinitos, distintos e de massa positiva.

A conclusão correta é: **o readout destes candidatos positivos tem resíduos incompatíveis com a log-derivada da característica holomorfa global pretendida**. Resolver isso requer alterar os dados efetivos de massa/observável/readout ou demonstrar uma correção com os resíduos necessários. Uma troca isométrica de apresentação que preserve o observável e a fonte conserva massas espectrais, momentos e resíduos; ela não modifica essa condição.


## 6. Núcleo local agora formalizado em Lean

Arquivo remoto `~/carry-self-adjoint-operator/CarrySelfAdjointOperator/AtomicLogDerivativeResidue.lean`, SHA-256 `631f7e90f8d95222018b03bcd765a6dc2f22c432235d5a8868210dd804ad95d8`.

| Linha | Declaração | Conteúdo formal |
| --- | --- | --- |
| 18 | `tendsto_mul_logDeriv_eq_analyticOrderNatAt` | Limite `(z-a) logDeriv F z → N`, para F analítica de ordem finita. |
| 58 | `tendsto_mul_neg_half_logDeriv_eq_analyticOrderNatAt` | Limite do readout negativo/meio para `−N/2`. |
| 69 | `tendsto_mul_atomicParityReadout` | Limite `(z-a) w z/(1-v z²) → −w/(2v)`, com `a≠0`, `v a²=1`. |
| 103 | `tendsto_mul_atomicParityReadout_add` | O mesmo limite após somar um resto contínuo em a. |
| 117 | `atomicParityReadout_mass_div_eigenvalue_eq_analyticOrderNatAt` | Igualdade eventual do readout atômico com `−logDeriv F/2` implica `w/v=N`. |

O último lema usa a igualdade de funções em uma vizinhança perfurada, não assume uma identidade de resíduos nem a quantização como hipótese. Resto analítico é suficiente porque a prova precisa apenas de continuidade. O caso N=0 também está incluído nos lemas de limite.

Validação: `lake build CarrySelfAdjointOperator.AtomicLogDerivativeResidue` passou com 3099 jobs, sem warnings. `#print axioms` dos cinco teoremas retorna somente `propext`, `Classical.choice`, `Quot.sound`; nenhum `sorryAx`. A convergência global da série prime-carry, sua continuação e a incompatibilidade após escala permanecem como demonstração matemática neste suplemento, não como novas declarações Lean.
