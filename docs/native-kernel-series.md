# Série da fonte original: cauda em todas as ordens e faixas inteiras da grade

Data: 14 de outubro de 2026. Base: `a9dee06f515a329955dfdcb02ec1a6ae4dd28d25`.

O avanço é passar de pontos isolados da grade a um intervalo inteiro, incluindo o limite de bordo. A fonte completada, o retorno, as amplitudes, as diferenças finitas, as features físicas e sua métrica permanecem os mesmos. Os termos cruzados continuam presentes.

## Resultado e nível de prova

**Lean:** quatro declarações públicas novas provam uma cota mais forte dos coeficientes logarítmicos reais, sua normalização nos coeficientes ímpares da fonte e uma estimativa de cauda infinita. As provas valem em todas as ordens, sem hipótese de positividade.

**Análise escrita e certificado externo Arb:** a série é transportada pelas diferenças finitas originais. Uma fatoração auxiliar e uma cota rigorosa da cauda certificam positividade para todos os inputs complexos e todo `h` no intervalo indicado:

| N | Intervalo contínuo certificado | Grade original coberta | Erro relativo, arredondado para cima |
|---:|---:|---:|---:|
| 8 | `0 ≤ h ≤ 1/256` | todo `k ≥ 255` | `< 0.624` |
| 10 | `0 ≤ h ≤ 1/2048` | todo `k ≥ 2047` | `< 0.735` |
| 12 | `0 ≤ h ≤ 1/32768` | todo `k ≥ 32767` | `< 0.480` |

Aqui `h=1/(k+1)`; `h=0` denota a extensão por série, que é a matriz de bordo. Para `h>0`, a positividade implica contratibilidade do retorno original e anula seu canal de Jordan negativo inteiro. Não se trata de um teste em uma direção ou de um valor arredondado do canal negativo. A restrição a prefixos, já formalizada em `radialReturnTransfer_norm_le_one_of_prefix`, fornece também as dimensões menores com o mesmo limiar.

O limiar anterior suficiente de oito fontes, `k+1 ≥ 2^164`, foi substituído nesta investigação por `k+1 ≥ 256`, mediante um certificado diferente e uma estimativa muito menos dissipativa.

**Limite:** a positividade nativa em dimensão arbitrária continua aberta. A identificação analítica da série com o kernel, o transporte por Stirling e a estimativa combinatória da cauda abaixo ainda não foram formalizados em Lean. O certificado das faixas é uma prova assistida externa, apoiada nessa derivação escrita. Não foi importado como uma premissa numérica Lean.

## 1. Uma majorante obtida da própria fonte

Escreva `c_n` para `completedNativeRealEvenCharacteristicCoefficient n`, `m_n` para `canonicalCompletedNativeLogDerivativeMoment n` e `a_n` para `nativeSourceOddBoundaryCoefficient n`. A normalização anterior é conservada: `a_n=2m_n`.

As cotas theta já demonstradas dão

\[
c_0\ge\tfrac13,\qquad |c_{n+1}|\le\frac1{35\,25^n}
\le c_0\,\delta\beta^n,
\quad \delta=\frac3{35},\quad\beta=\frac1{25}.
\]

A recorrência original dos momentos é

\[
c_0m_n+\sum_{j<n}m_jc_{n-j}=-(n+1)c_{n+1}.
\]

Defina `alpha=beta+delta=22/175`. Indução forte, com a identidade exata

\[
\delta\left((n+1)\beta^n+
\sum_{j<n}(\alpha^{j+1}-\beta^{j+1})\beta^{n-j-1}\right)
=\alpha^{n+1}-\beta^{n+1},
\]

fornece

\[
\boxed{|m_n|\le\alpha^{n+1}-\beta^{n+1},\qquad
|a_n|\le2\alpha^{n+1}.}
\]

Essas desigualdades são kernel-checked no módulo `CompletedNativeLogCoefficientMajorant.lean`. A antiga cota `|m_n| ≤ (1/2)(3/4)^n` permanece válida; a nova explora mais diretamente as constantes da fonte.

Também foi formalizado, para `alpha |w| < 1`,

\[
\boxed{\sum_{n\ge0}|a_{n+M}|\,|w|^{n+M}
\le\frac{2\alpha(\alpha|w|)^M}{1-\alpha|w|}.}
\]

A somabilidade faz parte do enunciado. Esta é uma cota dos coeficientes reais da fonte; não afirma sinal de Hankel nem identifica por si só a série com um operador fora de seu domínio analítico estabelecido.

## 2. Transporte exato da série, preservando a síntese

Use a característica completada `F`, `G(y)=F(iy)` e `r(y)=G'(y)/G(y)`. No disco local sem zeros usado aqui,

\[
r(y)=\sum_{n\ge0}(-1)^na_ny^{2n+1},
\qquad K(u,v)=\frac{r(u)+r(v)}{u+v}
=\sum_{n\ge0}(-1)^na_n\sum_{q=0}^{2n}(-1)^qu^{2n-q}v^q.
\]

A igualdade da série com `r` segue dos coeficientes já identificados, da analiticidade e da recorrência do produto; a majorante assegura convergência absoluta no domínio local. Para `|y|≤1/4`, as cotas anteriores da característica dão `G≠0`. A nova majorante implica ainda `|r(y)|≤88/1389<1`, tornando não nulas as amplitudes originais.

Se `S(p,a)` é um número de Stirling de segunda espécie, a identidade inteira

\[
\frac1{a!}\sum_{j=0}^{a}(-1)^{a-j}\binom aj(j+1)^p=S(p+1,a+1)
\]

transporta exatamente as diferenças finitas antigas. Removendo apenas as fases unitárias fixas `eta_a` para escrever uma matriz real `Q`, suas entradas são

\[
Q_{ab}(h)=\sum_{n\ge\lceil(a+b)/2\rceil}
2m_n h^{2n-a-b}
\sum_{q=b}^{2n-a}(-1)^{n+q}
S(2n-q+1,a+1)S(q+1,b+1).
\]

A matriz complexa original é `diag(eta)* Q diag(eta)` com o primeiro fator conjugado transposto. As fases continuam `eta_a=1` em ordem par e `eta_a=-i` em ordem ímpar. Essa congruência unitária é escrita explicitamente; nenhum termo misto é apagado.

No limite `h=0`,

\[
B_{ab}=\begin{cases}(-1)^{(a+b)/2+a}a_{(a+b)/2},&a+b\text{ par},\\
0,&a+b\text{ ímpar},\end{cases}
\qquad E_N(x)=2x^*B_Nx.
\]

Em `h>0`, `Q` é a forma `Re storage` no chart original, com o fator físico `1/h`, as amplitudes e os fatoriais antigos. A identificação é da forma completa, antes de qualquer leitura de momentos.

## 3. Cota uniforme da cauda do kernel transportado

Trunque a soma em `n<M`, com `M≥N`, e denote o polinômio resultante por `P_M(h)`. Para `0≤h≤H`, ponha `R=NH` e `z=alpha R²`. A fórmula integral de diferenças finitas de monômios implica

\[
S(p+1,a+1)\le\binom pa(a+1)^{p-a}.
\]

A identidade de Vandermonde na soma sobre `q` dá

\[
\sum_{q=b}^{2n-a}\binom{2n-q}{a}\binom qb
=\binom{2n+1}{a+b+1}.
\]

Portanto, com `d=a+b+1`,

\[
|(Q-P_M)_{ab}|\le
2\alpha R^{-a-b}\sum_{n\ge M}\binom{2n+1}{d}z^n.
\]

A razão de termos consecutivos desta última série é

\[
z\frac{(2n+3)(2n+2)}{(2n+3-d)(2n+2-d)}.
\]

Para `n≥M` e `2M+2>d`, ela decresce: cada fator é `1+d/(2n+c-d)`. Se seu valor `rho_M` em `M` é menor que 1, a cauda inteira tem a cota racional

\[
\boxed{T_{ab}=2\alpha R^{-a-b}\binom{2M+1}{d}
\frac{z^M}{1-\rho_M}.}
\]

Essa estimativa inclui `h=0`, pois todos os expoentes omitidos `2n-a-b` são não negativos. Nenhuma avaliação numérica de uma soma infinita substitui a cauda: `T` é calculada por aritmética racional e encerrada por Arb.

## 4. Certificação de todos os inputs e de todo o intervalo

Cada execução recalcula os momentos theta com integrais novas e os envelopes de cauda do motor da investigação anterior. Não utiliza zeros, avaliação de zeta, momentos de cache ou uma medida positiva escolhida para ajustar a energia.

A fatoração intervalar de `B=P_M(0)` fornece uma matriz triangular auxiliar. Seu inverso é substituído por uma matriz triangular `W` de números diádicos **exatos**, com diagonal positiva, portanto invertível. Essa matriz serve apenas para verificar o sinal. A fonte, as features, a métrica e o chart de entrada não são redefinidos por ela.

O motor verifica

\[
\varepsilon=\|WBW^T-I\|_\infty+
\sum_{d\ge1}\|WP_{M,d}W^T\|_\infty H^d+
\|\,|W|T|W|^T\|_\infty<\tfrac34.
\]

Todos os máximos e somas são feitos em bolas Arb; não há seleção de cotas por comparação em ponto flutuante. Como as matrizes são reais simétricas, a norma por soma de linhas limita todos os autovalores do erro. Para todo `h` do intervalo,

\[
WQ(h)W^T\ge(1-\varepsilon)I>0,
\quad Q(h)\ge\frac{1-\varepsilon}{\|W\|_F^2}I.
\]

Margens em coeficientes conservadoras, arredondadas para baixo, para `Re storage`:

| N | Margem uniforme menor que a certificada |
|---:|---:|
| 8 | `2.23e-23` |
| 10 | `4.51e-30` |
| 12 | `1.63e-36` |

As margens de `E_N=2x*B_Nx` têm o fator 2 adicional. Elas não são autovalores na norma física do retorno e não são apresentadas como tais.

A amplitude não nula e a transformação triangular das diferenças finitas tornam o chart invertível. Logo a positividade da forma no chart cobre todo o espaço incidente original. O defeito `I-T* T` é positivo; o mesmo retorno é contrativo e seu porto de Jordan negativo é zero em toda a faixa da grade.

## 5. Auditoria e reprodução

Arquivos da execução: `research/native-kernel-series-2026-10-14/`.

- `certificate-768.json`: 768 bits, 40 termos do kernel, 16 modos theta, corte espacial 256.
- `certificate-1024.json`: 1024 bits, 44 termos, 20 modos theta, corte 256. Recalcula as integrais e confirma os mesmos intervalos.
- `audit.json`: confere hashes dos motores e das fontes Lean, sobreposição dos momentos das duas execuções, a recorrência logarítmica e a identidade inteira entre diferenças binomiais e Stirling até grau 79.
- O auditor recalcula a cauda hiperbólica e compara **todas as entradas** de `Re storage` calculadas diretamente pelo retorno original com a série, em `H` e `H/2`, nas três dimensões. O cálculo direto usa `H_ij/h`, `q_i`, amplitudes, pesos binomiais e fatoriais originais; não usa Stirling no chart.

Essas comparações auditam implementação, sinais e normalizações. A passagem analítica da série e a prova geral da majorante combinatória continuam sendo a derivação escrita das seções anteriores.

Comandos no host `llm`, a partir do repositório:

```sh
/home/thlinux/.elan/bin/lake build --wfail CarrySelfAdjointOperator.CompletedNativeLogCoefficientMajorantAudit CarrySelfAdjointOperator CarrySelfAdjointOperator.Audit
/home/thlinux/miniforge3/bin/python3 scripts/certify_native_kernel_series.py --output research/native-kernel-series-2026-10-14/certificate-768.json
/home/thlinux/miniforge3/bin/python3 scripts/certify_native_kernel_series.py --bits 1024 --terms 44 --modes 20 --cutoff 256 --output research/native-kernel-series-2026-10-14/certificate-1024.json
/home/thlinux/miniforge3/bin/python3 scripts/check_native_kernel_series.py --engine scripts/certify_native_kernel_series.py --certificate research/native-kernel-series-2026-10-14/certificate-768.json --replication research/native-kernel-series-2026-10-14/certificate-1024.json --output research/native-kernel-series-2026-10-14/audit.json
```

Os quatro novos roots Lean passam pela auditoria de tipos e corpos: 5060 declarações no fecho, somente `propext`, `Classical.choice` e `Quot.sound`. O build isolado passou com 9393 jobs; o build do módulo de auditoria, agregador e auditoria global passou com 10332 jobs, usando `--wfail`. Não foram usados `sorry`, `admit`, novos axiomas ou certificados externos como provas Lean.

## 6. A obrigação restante para N arbitrário

A majorante e o transporte dão um método aplicável a qualquer `N` fixo, desde que uma margem nativa seja efetivamente certificada. Isso não prova que o procedimento sempre conseguirá produzir essa margem: o sinal de `B_N` continua sendo a obrigação matemática.

O progresso resolve o controle da cauda e reduz fortemente a perda de precisão da aproximação pela grade. Ainda falta uma desigualdade da própria fonte que force todos os complementos de Schur de `B_N` a serem não negativos, ou uma representação positiva equivalente que preserve a síntese original.

O próximo passo verificável é formalizar o transporte por diferenças finitas e sua cauda, aproveitando a cota all-order agora kernel-checked. Em paralelo matemático, a procura da razão estrutural deve se concentrar no sinal desses complementos de Schur da fonte; aumentar apenas a lista de dimensões não fecha essa obrigação.
