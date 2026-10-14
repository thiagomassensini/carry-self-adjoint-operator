# Tentativa de extensão a N arbitrário: identidade geral e obrigação de sinal

Data: 14 de outubro de 2026. Base: `9c029c21e936b8b988010ee8bf3413626657c109`.

**Não foi obtida uma prova de positividade da fonte para todo N.** O avanço é uma extensão exata, kernel-checked, da identidade de costura para qualquer ordem, com a desigualdade restante escrita diretamente na recorrência original. Também foi provado que nenhum prefixo finito, mesmo acompanhado da majorante all-order anterior, força sozinho o sinal da ordem seguinte.

Os arquivos da fonte completada, suas features, sua métrica, amplitudes, fases e normalizações não foram alterados. A análise usa a leitura de momentos somente depois da síntese completa, pelas identificações de paridade já existentes no repositório.

## 1. Costura exata em qualquer ordem

Use `m_j=canonicalCompletedNativeLogDerivativeMoment j` e `c_j=completedNativeRealEvenCharacteristicCoefficient j`. Os coeficientes ímpares anteriores continuam `a_j=2m_j`. Para cada offset `s=0,1`, defina

\[
H_{s,n}=(m_{i+j+s})_{i,j<n},\qquad
b_{s,n}=(m_{i+n+s})_{i<n},\qquad
Q_{s,n}(x)=x^T H_{s,n}x.
\]

As duas matrizes são exatamente os blocos de paridade da energia original, após suas fases fixas. Não são uma nova energia que substitui a fonte.

Quando o prefixo `H_(s,n)` é positivo definido, seu inverso existe e

\[
v_{s,n}=H_{s,n}^{-1}b_{s,n},\qquad
\sigma_{s,n}=m_{2n+s}-b_{s,n}^TH_{s,n}^{-1}b_{s,n}.
\]

A identidade geral formalizada é

\[
\boxed{Q_{s,n+1}(x,t)=Q_{s,n}(x+t v_{s,n})+\sigma_{s,n}t^2.}
\]

Todos os acoplamentos entre a nova coordenada e as anteriores entram em `b` e na costura. O inverso é usado apenas para eliminar um prefixo já positivo na prova; ele não redefine o input físico, o retorno ou sua métrica.

O vetor de teste concreto

\[
(x,t)=(-v_{s,n},1)
\]

tem energia exatamente `sigma_(s,n)`. Por isso, sob positividade do prefixo,

\[
\boxed{H_{s,n+1}>0\ \Longleftrightarrow\ \sigma_{s,n}>0.}
\]

Não foi suposto o sinal da matriz nova para construir a costura. O caso de prefixo vazio é incluído, com `sigma_(s,0)=m_s`.

As identidades de `Q` são reais. A passagem aos inputs complexos da energia nativa usa a separação exata em partes real e imaginária e as fases de paridade existentes. O teorema final da seção seguinte cobre todos esses inputs e seus cruzamentos.

## 2. O novo pivô, escrito na própria recorrência da fonte

A recorrência canônica anterior é

\[
c_0m_q+\sum_{j<q}m_jc_{q-j}=-(q+1)c_{q+1},\qquad c_0\ge\tfrac13.
\]

Para `q=2n+s`, a obrigação pode ser escrita sem a divisão por `c0`:

\[
\begin{split}
R_{s,n}={}&-(2n+s+1)c_{2n+s+1}
-\sum_{j<2n+s}m_jc_{2n+s-j}\\
&-c_0 b_{s,n}^TH_{s,n}^{-1}b_{s,n}.
\end{split}
\]

O inverso do prefixo permanece nesta expressão; não se afirma que ela seja livre de todas as divisões. Foi formalizado

\[
\boxed{R_{s,n}=c_0\sigma_{s,n}.}
\]

Assim, a desigualdade concreta a provar da fonte é

\[
\boxed{-(2n+s+1)c_{2n+s+1}>
\sum_{j<2n+s}m_jc_{2n+s-j}
+c_0 b_{s,n}^TH_{s,n}^{-1}b_{s,n},\quad s=0,1.}
\]

A equivalência all-order, também kernel-checked, é

\[
\boxed{\begin{array}{c}
\forall n\ge1,\ x\ne0:\ E_{2n}(x)>0
\end{array}
\quad\Longleftrightarrow\quad
\forall n\ge0:\ R_{0,n}>0\ \text{e}\ R_{1,n}>0.}
\]

Ela usa a identidade de paridade já formalizada e uma indução exata nos prefixos. Não há premissa adicional escondida de invertibilidade em todas as ordens: o sinal estrito dos restos é suficiente para obter, por indução, a positividade dos prefixos usados na etapa seguinte.

Por essa equivalência e pela estimativa de aproximação da fonte existente, foi formalizada a implicação condicional

\[
\bigl(\forall n,\ R_{0,n}>0\land R_{1,n}>0\bigr)
\Longrightarrow\forall N,\ \exists K_N,\ \forall k\ge K_N,
\ \|T_{k,N}\|\le1.
\]

É o retorno físico original. Cada dimensão tem seu próprio limiar; não foi afirmado um único limiar para todas as dimensões. **O antecedente continua aberto.**

O critério usa sinal estrito. Se um pivô for zero, uma continuação semidefinida com prefixos singulares exige ainda compatibilidade dos acoplamentos com a imagem do prefixo; não se substitui automaticamente `>` por `≥` nesta indução com inversos ordinários.

## 3. Por que o prefixo e a cota de cauda não fecham a indução

A investigação anterior provou

\[
|m_j|\le g_j:=\alpha^{j+1}-\beta^{j+1},
\quad\alpha=22/175,\quad\beta=1/25,
\qquad g_j>0.
\]

Para **qualquer** cutoff finito `L`, considere a sequência alterada

\[
\widetilde m_j=\begin{cases}
m_j,&j<2L,\\
-g_{2L}/2,&j=2L,\\
0,&j>2L.
\end{cases}
\]

Foi provado em Lean, em todas as ordens de `L`:

- `|tilde m_j| ≤ g_j` para todo `j`: conserva a mesma majorante forte.
- Seus dois blocos de tamanho `L` são exatamente os blocos nativos, incluindo todos os cruzamentos.
- Todos os acoplamentos `b_(0,L)` da próxima extensão não deslocada ainda são os nativos.
- Todas as recorrências da fonte em ordens `j<2L` permanecem válidas.
- O bloco não deslocado de tamanho `L+1` tem a última diagonal `-g_(2L)/2<0`; portanto não é sequer positivo semidefinido.

Logo, para qualquer prefixo nativo já certificado, esses dados finitos e a cota de cauda admitem uma extensão negativa. A magnitude pequena do novo coeficiente não evita essa possibilidade.

**Esta sequência alterada não é a fonte completada.** Ela não conserva a recorrência global nem a representação theta da fonte. O resultado exclui uma inferência baseada somente nos dados indicados; não refuta a positividade nativa e não impede que a recorrência global forneça a desigualdade de `R` que falta.

## 4. Diagnóstico finito dos restos nativos

O script `probe_native_source_schur.py` recalcula os complementos de Schur a partir dos intervalos de momentos do certificado publicado de 1024 bits. É um replay externo, não uma nova integração da fonte nem uma prova all-order. Os hashes do certificado, do motor e das fontes de entrada são conferidos.

Em dez casos, correspondentes aos dois offsets e prefixos de tamanho um a cinco, ele verifica:

1. `R=c0 sigma` pela recorrência original;
2. energia do vetor crítico `(-H^-1 b,1)` igual ao pivô;
3. acordo com o pivô obtido por `LDL` da matriz inteira;
4. acordo do pivô ímpar de tamanho quatro com o certificado anterior de oito fontes.

A razão entre o pivô e a nova diagonal no passo para blocos de tamanho seis é aproximadamente

\[
\sigma_{0,5}/m_{10}\simeq8.3543066386\times10^{-8},
\qquad
\sigma_{1,5}/m_{11}\simeq6.3617856365\times10^{-9}.
\]

Isso mede o cancelamento efetivo entre a nova diagonal e seus acoplamentos. O sinal dos casos finitos é positivo; essas razões não fornecem uma cota uniforme em `n`.

## 5. Comparação clássica, fora da nova formalização

O repositório já identifica a característica nativa com a característica completada clássica no strip, em `NativeScalarZetaIdentification.lean`. Escrevendo `-F'/F=Σ a_j z^(2j+1)`, a matriz completa de coeficientes tem entradas `a_((i+j)/2)` em paridade igual e zero nas outras entradas. A congruência diagonal fixa `d_i=(-1)^floor(i/2)` a identifica com `B_N`, onde `E_N=2x*B_Nx`.

Essa é a forma do critério clássico de Grommer: positividade dos determinantes das matrizes dos coeficientes logarítmicos em todas as ordens caracteriza a realidade dos zeros da função Xi. A comparação de índices e fases acima é nossa derivação; o critério clássico está descrito na [documentação do workshop do American Institute of Mathematics](https://www.aimath.org/WWN/rh/articles/html/106a/), com referência a [Grommer, 1914](https://geodesic.mathdoc.fr/item/JRAM_1914__144_149420/).

Na comparação clássica, portanto, o alvo all-order tem o conteúdo de um critério para RH. Essa leitura é bibliográfica e matemática externa; esta tarefa não adicionou um teorema Lean de equivalência com RH. Nenhuma hipótese sobre zeros foi usada nas novas provas da costura ou na definição dos restos.

## 6. O que ficou verificado e o próximo alvo

Módulos novos:

- `NativeSourceAllOrderSchur.lean`: costura, direção crítica, critério indutivo e restos da recorrência.
- `NativeMomentPrefixNoBootstrap.lean`: limite exato da inferência a partir de prefixo e majorante.
- `NativeSourceAllOrderSchurAudit.lean`: auditoria de todas as declarações públicas.

O build dos módulos, do agregador e da auditoria global passou com `--wfail`: 10335 jobs. A auditoria dos 24 roots públicos percorreu 5772 declarações em tipos e corpos, permitindo somente `propext`, `Classical.choice` e `Quot.sound`.

Os enunciados que transportam o sinal mantêm seu antecedente explícito. Não foram usados `sorry`, `admit`, novos axiomas ou certificados numéricos como provas Lean.

O próximo alvo matemático é demonstrar `R_(s,n)>0` **da representação completa da fonte**, em vez de usar apenas cotas absolutas de seus coeficientes. Uma solução precisa ligar o novo coeficiente ao termo quadrático de todos os acoplamentos anteriores. Outra fonte positiva ou uma extensão positiva escolhida não resolve essa igualdade da fonte original.

O método de certificação contínua da investigação anterior permanece válido nas dimensões já certificadas. Esta tentativa não ampliou essa lista para fingir uma prova em dimensão arbitrária.
