# Escolha a priori de K(n), cauda uniforme e margem principal

Data: 2026-10-15. Fonte canônica: `llm:/home/thlinux/carry-self-adjoint-operator`, base `31b2f68f254b108d4d70dca5717e06effdb6c343` (PR #102).

Foi possível escolher **K(n)=n+2** sem consultar o novo pivô e derivar uma estimativa da cauda válida em todas as ordens. Não foi obtida a margem positiva uniforme do termo principal. O alvo quantitativo foi certificado externamente para 0≤n≤20, nas duas paridades. Uma tentativa de provar o sinal ponto a ponto foi refutada para a própria densidade ímpar, para qualquer prefixo modal finito.

## 1. Objetos preservados

Mantemos Φ, os momentos logarítmicos originais, Q_{s,n}, os vetores críticos e todos os cruzamentos ordenados. A expansão em modos é a da fonte, sem medida ajustada, métrica trocada ou amplitude reajustada. Para j≥1 e u≥0, p=πe^{2u},

\[
\Phi_j=4\pi j^2e^{5u/2}(2pj^2-3)e^{-pj^2},\quad
V_j=u\left(2pj^2-\frac92-\frac6{2pj^2-3}\right),\quad
\Phi=\sum_{j\ge1}\Phi_j.
\]

Usamos K modos no score,

\[
V^{[K]}=\frac{\sum_{j=1}^K V_j\Phi_j}{\sum_{j=1}^K\Phi_j},
\]

mantendo o peso **Φ completo** na integral. Defina

\[
A_{s,n,K}=\begin{cases}
\int V^{[K]}Q_{0,n}\Phi,&s=0,\\
2c_0\eta_n^2+\int V^{[K]}Q_{1,n}\Phi,&s=1.
\end{cases}
\]

O PR #102 fornece, com o prefixo anterior invertível,

\[
(4n+2s+3)R_{s,n}-A_{s,n,K}
=\int(V-V^{[K]})Q_{s,n}\Phi,\quad s\in\{0,1\}.
\]

## 2. Prefixos — formalizado no Lean

`NativeThetaAdaptivePrefix.lean` demonstra, para todo K≥1:

\[
V_1\le V^{[K]}\le V,\qquad V^{[K]}\longrightarrow V\text{ ponto a ponto}.
\]

Demonstra também a identidade exata do resto inteiro:

\[
(V-V^{[K]})\Phi=\sum_{j>K}(V_j-V^{[K]})\Phi_j\ge0.
\]

Cada novo modo dá o incremento

\[
\Phi_{\le K+1}(V^{[K+1]}-V^{[K]})
=\Phi_{K+1}(V_{K+1}-V^{[K]})\ge0.
\]

São afirmações sobre o score e as densidades modais. Multiplicar por Q não preserva esse sinal, pois Q pode mudar de sinal. Não identificamos esse resto com o defeito geométrico do transporte físico.

## 3. Derivação da estimativa da cauda em todas as ordens

Esta seção é uma prova matemática pela série explícita da fonte. **A ligação entre o erro integral e a majorante não foi formalizada no Lean neste trabalho.** O Lean verifica os prefixos, o limite escalar da seção 4 e o limite dos polinômios por seus coeficientes.

Para J=K+1≥2,

\[
\frac{\Phi_j}{\Phi_1}\le2j^4e^{-p(j^2-1)},\qquad
0\le V_j-V_1\le2puj^2.
\]

Como V_1≤V^[K]≤V_j para j>K, a média ponderada do score completo dá

\[
0\le V-V^{[K]}
\le\frac{4puJ^6e^{-(J^2-1)p}}{1-r_J},\qquad
r_J=\left(\frac{J+1}{J}\right)^6e^{-\pi(2J+1)}.
\]

A razão entre dois termos consecutivos de j⁶exp(−p(j²−1)) é no máximo r_J. Além disso r_J≤r_2. Para o peso inteiro, a razão da majorante de j⁴exp(−pj²) é no máximo q_4=16exp(−3π), portanto

\[
\Phi(u)\le\frac{8\pi^2e^{9u/2}e^{-p}}{1-q_4}.
\]

Se P tem grau ≤d e

\[
M(P)=\sum_k|[u^k]P|,
\]

então |P(u)|≤M(P)e^{du} para u≥0. A prova usa u^k≤e^{ku} e conserva todos os coeficientes do polinômio já sintetizado. Essa desigualdade está formalizada como `nativeThetaPolynomial_eval_bound`.

Multiplicando as três estimativas e usando e^{2u}≥1+2u, obtemos, quando λ=2πJ²−d−13/2>0,

\[
\begin{aligned}
\mathcal E(P,K)&:=\int_0^\infty(V-V^{[K]})|P|\Phi\\
&\le\frac{32\pi^3J^6M(P)}{(1-r_2)(1-q_4)}
\int_0^\infty u e^{(d+13/2)u-\pi J^2e^{2u}}du\\
&\le\boxed{\frac{32\pi^3J^6M(P)e^{-\pi J^2}}
{(1-r_2)(1-q_4)(2\pi J^2-d-13/2)^2}}.
\end{aligned}
\]

A última integral é limitada por e^{−πJ²}∫u e^{−λu}du=e^{−πJ²}/λ². A majorante também justifica a integrabilidade das densidades de erro e das integrais dos prefixos. Não há cauda modal ou cauda em u omitida nessa fórmula.

## 4. Regra explícita e escala positiva a priori

Para Q_{s,n}, s∈{0,1}, o grau é d=4n+2s+2≤4n+4. Escolhemos

\[
\boxed{K(n)=n+2,\qquad J=n+3.}
\]

Essa escolha envolve somente a ordem. Como πJ²≥d+13/2, temos λ≥πJ². Também (1−r_2)(1−q_4)>1/2. Por exemplo, r_2<1/100 e q_4<1/100 seguem de π>3 e das somas de Taylor inferiores de exp(15) e exp(9); os intervalos do certificador verificam essas constantes.

Consequentemente,

\[
\boxed{\mathcal E(Q_{s,n},n+2)
\le B_{s,n}:=64\pi(n+3)^2e^{-\pi(n+3)^2}M(Q_{s,n}).}
\]

Defina a escala positiva, antes de inspecionar os pivôs,

\[
\boxed{L_{s,n}=e^{-(n+3)^2}M(Q_{s,n})>0.}
\]

A não anulação do coeficiente líder de Q prova M(Q)>0 em todas as ordens. `NativeThetaAdaptiveBudget.lean` formaliza essa positividade e

\[
\boxed{B_{s,n}\le\tfrac12 L_{s,n}.}
\]

A prova escalar vale para qualquer polinômio. Escrevendo t=(n+3)²≥9, a quinta parcela da exponencial dá exp(2t)≥(2t)⁵/120≥512t≥128πt. Como π>3, isso implica 64πt exp(−πt)≤exp(−t)/2. Não se ajustaram constantes a pivôs numéricos.

**Assim, a cauda está controlada em relação a uma escala positiva explícita em todas as ordens. Ainda não demonstramos que o termo principal excede essa escala.** O teorema adicional suficiente seria

\[
\boxed{A_{s,n,n+2}\ge L_{s,n}\quad\text{para todo }n,\ s=0,1.}
\]

Se essa desigualdade for provada sob invertibilidade do prefixo anterior, a identidade transportada dará (4n+2s+3)R≥L/2>0, permitindo a indução dos prefixos. A desigualdade principal não é uma hipótese já verificada para todos os n, nem foi adicionada como axioma.

## 5. Uma tentativa direta de margem não funciona — Lean

A própria densidade ímpar refuta o caminho de positividade ponto a ponto. Para u≥1, o primeiro score e todos os scores médios finitos satisfazem V^[K](u)≥u≥1. Por outro lado, Q_{1,n}(u) tende a −∞, pelo seu coeficiente líder negativo, já formalizado anteriormente.

Logo, para todo n, todo K≥1 e qualquer constante real C,

\[
C+V^{[K]}(u)Q_{1,n}(u)<0\quad\text{para }u\text{ suficientemente grande}.
\]

`NativeThetaPrincipalDensityObstruction.lean` demonstra essa afirmação e a impossibilidade de essa expressão ser não negativa em toda a semirreta. Aplique C=2η_n² para incluir exatamente a contribuição do quadrado central na densidade contra Φ, cuja massa é c₀. A multiplicação por Φ>0 conserva a cauda negativa.

É uma obstrução àquela densidade ponto a ponto. Não demonstra integral negativa, não refuta a positividade do operador e não exclui outra representação positiva obtida por um transporte exato. A próxima prova de margem precisa ser integrada e usar as compensações da fonte.

## 6. Certificação finita da margem proposta

`scripts/certify_adaptive_theta_budget.py` conserva a recorrência e o vetor crítico originais. Reutiliza os intervalos de momentos pares de `thetaTail` do certificado publicado de 1024 bits, confere hashes das fontes e faz a conversão Green para os coeficientes da característica. Para cada n e s, resolve o sistema crítico em Arb, preserva todos os cruzamentos ao montar Q e calcula intervalos de M, L, R e da majorante integral explícita.

O certificador prova, para cada caso inspecionado,

\[
(4n+2s+3)R_{s,n}-\mathcal E^{\rm upper}_{s,n}-L_{s,n}>0,
\qquad \mathcal E^{\rm upper}_{s,n}<L_{s,n}/2.
\]

Isso verifica A≥L nessas ordens por meio da identidade exata e do controle do erro. **A verificação finita usa os intervalos do próprio Schur; ela não constitui um novo mecanismo independente para o sinal em todas as ordens.** K e L foram escolhidos antes desse cálculo.

Foram certificados 42 casos: n=0,…,20 nas duas paridades. A execução em 768 bits foi repetida em 1024 bits; todos os intervalos reportados se sobrepuseram. Não foi feita nova quadratura: reutilizamos os intervalos da fonte, não pontos médios. A entrada e a precisão limitam a faixa certificada; não há extrapolação para n>20.

A menor razão entre margem transportada e L no conjunto foi aproximadamente **7,89048733236**, no setor ímpar em n=0. A maior razão da majorante de erro para L foi aproximadamente **1,45451432407×10⁻⁶**, também nesse caso. As margens passam com folga nos casos finitos, mas isso não prova seu crescimento ou seu sinal para toda ordem.

## 7. Estado exato da investigação

- **Lean:** prefixos e resto modal inteiro; incremento não negativo dos scores; convergência ponto a ponto; estimativa do polinômio por seus coeficientes; positividade de L; limite escalar B≤L/2; obstrução ponto a ponto para a densidade ímpar original.
- **Prova matemática na nota:** ligação entre o erro integral da fonte completa e B, uniforme em n, com K(n)=n+2 e ambas as paridades. Essa ligação ainda precisa ser incorporada ao Lean.
- **Intervalos externos:** A≥L para 0≤n≤20, s=0,1, replicados em duas precisões. Nenhum intervalo foi usado como premissa Lean.
- **Aberto:** A≥L uniformemente na ordem, ou outra estimativa integrada positiva que baste. Também não se fechou a identificação com a energia do transporte físico, o operador infinito ou a hipótese dos zeros.

O alvo uniforme não foi concluído. A escolha dos modos e o controle da cauda deixaram de depender de um pivô já positivo; a coerção integrada do termo principal continua sendo a obrigação central. Detalhes de build, auditoria, publicação e preservação dos arquivos C2 estão nos artefatos de entrega em `verification.json`.
