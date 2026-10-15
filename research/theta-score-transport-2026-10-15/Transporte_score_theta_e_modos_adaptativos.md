# Transporte do score theta e controle por modos da própria fonte

Data: 2026-10-15. Repositório canônico: `llm:/home/thlinux/carry-self-adjoint-operator`. Base: `4f6fdb474fae0c89cacc6772f680a4aa08d581b9` (PR #101).

A identidade transportada foi formalizada para todas as ordens. Uma estimativa explícita da cauda passou com intervalos no primeiro caso ímpar. O teste de ordem maior revelou que um único modo perde resolução relativa à margem; dois modos recuperam uma margem positiva nesse teste. A positividade geral continua aberta.

## 1. Identidade do peso completo — Lean

Mantemos o kernel original `completedNativeXiCosineKernel`, denotado por Φ, os momentos originais m, todos os cruzamentos e o polinômio crítico Q já definido pela fonte. Definimos

\[
V(u)=-u\frac{\Phi'(u)}{\Phi(u)}.
\]

`NativeXiThetaDifferentiation.lean` demonstra a derivada da série infinita mediante majorantes locais somáveis. Uma família de átomos gaussianos tem derivadas e decaimento exponencial, incluindo o termo de grau seis que aparece em Φ′. Não se define Φ por truncamento.

`NativeThetaScoreTransport.lean` demonstra integrabilidade de todo polinômio vezes Φ′ e da densidade V P Φ. O fluxo u P Φ vale zero em u=0 e tende a zero no infinito pelo decaimento da fonte. Assim, para todo polinômio real P,

\[
\mathcal I(uP')=-\mathcal I(P)+\int_0^\infty V(u)P(u)\Phi(u)\,du.
\]

Combinando essa integração por partes com o cancelamento de convoluções do PR #101:

\[
\boxed{(4n+5)R_{1,n}=2c_0\eta_n^2+\int_0^\infty VQ_{1,n}\Phi},
\]
\[
\boxed{(4n+3)R_{0,n}=\int_0^\infty VQ_{0,n}\Phi}.
\]

Teoremas: `nativeSchurScore_odd_balance` e `nativeSchurScore_even_balance`. A única hipótese matricial é a invertibilidade do prefixo anterior (`IsUnit`), sem hipótese de sinal do novo pivô. As hipóteses analíticas da fonte estão provadas, não deixadas como premissas opacas. Essas são identidades em todas as ordens, não demonstrações de seus sinais.

## 2. Modos, score e resto — Lean

Escreva j=n+1≥1, p=π exp(2u), e

\[
\Phi_j(u)=4\pi j^2e^{5u/2}(2pj^2-3)e^{-pj^2},\qquad
V_j(u)=u\left(2pj^2-\frac92-\frac6{2pj^2-3}\right).
\]

`NativeThetaModeScore.lean` identifica cada Φ_j com duas vezes o termo inteiro positivo já existente. Demonstra sua derivada, a identidade V_j Φ_j=−u Φ_j′, a monotonicidade dos slopes e a somabilidade necessária. Logo, para u≥0,

\[
\delta_1(u):=\sum_{j\ge2}(V_j-V_1)\Phi_j
=(V-V_1)\Phi\ge0,\qquad V\ge V_1.
\]

Esse resto é a diferença de scores multiplicada pelo peso da fonte. Não foi identificado com o defeito geométrico do transporte físico. Sua integral contra Q pode ter qualquer sinal porque Q muda de sinal. A positividade de δ_1 não permite descartar os cruzamentos ou substituí-los por uma energia positiva.

## 3. Estimativa explícita da cauda — derivação matemática

A estimativa geométrica desta seção foi derivada e utilizada no certificador externo; ela **não foi incorporada ao Lean** neste trabalho.

Para K≥1, use a média ponderada apenas no score,

\[
V^{[K]}=\frac{\sum_{j=1}^K V_j\Phi_j}{\sum_{j=1}^K\Phi_j}.
\]

O peso das integrais permanece o Φ completo. Para j≥1, p≥π>3,

\[
\frac{\Phi_j}{\Phi_1}\le2j^4e^{-p(j^2-1)},\qquad
0\le V_j-V_1\le2puj^2.
\]

A primeira desigualdade usa (2pj²−3)/(2p−3)≤2j². A segunda segue da expressão racional do slope e de 6/(2p−3)≤2. Como V_1≤V^[K]≤V_j para j>K, essas relações dão

\[
0\le V-V^{[K]}\le4pu\sum_{j\ge J}j^6e^{-p(j^2-1)},\quad J=K+1.
\]

A razão entre termos consecutivos é limitada por

\[
r_J=\left(\frac{J+1}{J}\right)^6e^{-\pi(2J+1)}<1\quad(J\ge2).
\]

Portanto há um limite computável para a cauda infinita:

\[
\boxed{0\le V-V^{[K]}\le B_K(u):=
\frac{4puJ^6e^{-(J^2-1)p}}{1-r_J}.}
\]

Para K=1, B_1=256pu exp(−3p)/(1−r_2). Isso controla o erro conservando o peso completo:

\[
\left|\int (V-V^{[K]})Q\Phi\right|
\le\int B_K|Q|\Phi=:\mathcal E_{s,n,K}.
\]

Se A_{s,n,K} for o termo quadrático (no setor ímpar) mais a integral de V^[K] Q Φ, obtemos

\[
|(4n+2s+3)R_{s,n}-A_{s,n,K}|\le\mathcal E_{s,n,K}.
\]

Assim, A>𝓔 basta para positividade. Ainda falta provar essa dominação uniformemente em n.

## 4. Certificado finito externo com a cauda inteira

`scripts/certify_theta_score_first_odd.py` usa os intervalos publicados da própria fonte. Os dados de entrada são momentos pares de `thetaTail`; sua conversão para coeficientes de Φ segue a fórmula Green original antes da recorrência dos momentos logarítmicos. O script verifica os hashes das fontes e do integrador original.

Para s=1,n=0, Q=m₀u²/2−u⁴/12. A estimativa utiliza |Q|≤|m₀|u²/2+u⁴/12, o B_1 explícito, o Φ completo e todos os erros dos modos omitidos e de u>3. Uma série geométrica limita Φ e as caudas modais; a cauda no infinito usa, para T=3,

\[
\int_T^\infty u^k e^{au-be^{2u}}du
\le\frac{T^ke^{aT-be^{2T}}}{2be^{2T}-a-k/T},
\]

quando o denominador é positivo. A prova usa u^k≤T^k exp(k(u−T)/T) e exp(2u)≥exp(2T)(1+2(u−T)). O erro de uma integral assinada recebe intervalo simétrico; os erros das majorantes positivas recebem [0,erro].

Replicação independente: 384 bits/8 modos e 512 bits/10 modos, intervalos sobrepostos.

| Quantidade | Valor aproximado certificado |
|---|---:|
| 5R₁,₀ | 9,23963574198782 × 10⁻⁵ |
| A₁,₀,₁−𝓔₁,₀,₁ | 9,23476321213805 × 10⁻⁵ > 0 |
| 𝓔₁,₀,₁/(5R₁,₀) | 0,00037782911016437 |

Esse certificado verifica uma estimativa nova no caso cuja positividade já era conhecida. Os intervalos são evidência matemática computacional externa, sem uso como premissas Lean. Não certificam outras ordens.

## 5. Direções críticas maiores — somente experimento

`probe_theta_score.py` resolve os sistemas críticos originais e monta todas as somas ordenadas antes de integrar. A quadratura é dividida nas raízes positivas de Q. Usa momentos de entrada intervalares convertidos para pontos médios, precisão arbitrária, corte u=3 e um número finito de modos. Os testes de ordem maior **não têm encerramento intervalar das caudas** e são rotulados exploratórios.

Para K=1, a razão entre o erro com envelope modal e a margem transportada evoluiu assim:

| n | Setor par | Setor ímpar |
|---:|---:|---:|
| 0 | 0,0000208003 | 0,000149588 |
| 1 | 0,000356936 | 0,000519604 |
| 2 | 0,000326658 | 0,00314176 |
| 3 | 0,0110418 | 0,0254237 |
| 4 | 0,0328489 | 0,0526212 |
| 5 | 0,188119 | 0,374261 |
| 6 | 0,527104 | **2,36649** |

O envelope modal aqui é a integral de |Q| δ_K Φ/(Σ_{j≤K}Φ_j), ainda com todos os modos retidos no experimento. Ele é mais preciso que B_K. Até esse envelope dá limite inferior negativo para K=1,s=1,n=6. O limite geométrico mais grosseiro também falha nesse teste. Isso não é um pivô negativo: R₁,₆≈6,9491185704×10⁻⁴⁴ permanece positivo no cálculo.

Repetindo essa mesma direção crítica com K=2:

| Quantidade em s=1,n=6 | Um modo | Dois modos |
|---|---:|---:|
| Envelope modal / margem | 2,3664947323 | 2,9548318653 × 10⁻⁷ |
| Majorante geométrica / margem | 4,1808484439 | 3,9182104548 × 10⁻⁷ |
| A−erro geométrico | −4,8840487738 × 10⁻⁴² | 2,0152441839 × 10⁻⁴² |

O teste com dois modos foi repetido em 90 dígitos/10 modos e 110 dígitos/12 modos. Os valores reportados se mantiveram; o erro relativo na identidade integrada caiu de cerca de 2,8×10⁻⁵⁴ para 7,2×10⁻⁷⁶. Para um modo, a repetição em 110 dígitos/12 modos também confirmou os valores. A estabilidade dessas quadraturas não as transforma em certificados intervalares.

## 6. Próxima obrigação e validação

A direção concreta passa a ser uma estimativa com K=K(n). O objetivo suficiente é obter, diretamente da fonte, L_{s,n}>0 e θ<1 tais que

\[
A_{s,n,K(n)}\ge L_{s,n},\qquad
\mathcal E_{s,n,K(n)}\le\theta L_{s,n}.
\]

Escolher K comparando com um pivô já positivo é apenas um diagnóstico numérico. Para provar todas as ordens, a margem do termo principal precisa ser demonstrada sem pressupor o sinal do novo pivô. A pequena cauda theta, sozinha, não demonstra essa margem. Também continuam abertas a identificação com a energia do transporte físico e a passagem a um operador infinito positivo/autoadjunto com os dados requeridos.

Validação formal pré-publicação: `lake build --wfail CarrySelfAdjointOperator.NativeThetaScoreTransportAudit` (9842 jobs) e `lake build --wfail` (10216 jobs), ambos passaram. Auditoria: 46 raízes públicas, fecho de 5636 declarações; apenas `propext`, `Classical.choice`, `Quot.sound`. Sem `sorry`, `admit` ou novos axiomas. O estado final de publicação, a repetição em main e os SHAs constam em `verification.json`.
