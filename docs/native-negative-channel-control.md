# Controle do canal negativo: oito fontes e estimativa explícita da grade

## Resultado e alcance

O estudo preserva o retorno original, as meias-densidades, os coeficientes do chart e os cruzamentos. Há três níveis distintos de resultado:

1. **Lean:** foi formalizado um controle quantitativo do canal negativo para todos os inputs a partir de sua energia nas colunas da base. O desaparecimento desse traço implica não negatividade da energia nativa, sem exigir convergência forte dos vetores positivos. Uma hipótese mais fraca de dominância relativa dos canais também basta. As hipóteses de desaparecimento ou dominância não foram demonstradas para todas as ordens.
2. **Certificado externo Arb:** novas integrais da fonte, com caudas espaciais, modais e de Taylor controladas, certificam uma margem positiva da forma nativa de oito fontes. Também certificam positividade do defeito do retorno, em todos os inputs originais, em 11 pares finitos `(N,k)`.
3. **Derivação analítica, fora do Lean:** uma estimativa explícita compara a grade com a forma de bordo. Com a margem de oito fontes certificada externamente, ela implica que o canal negativo inteiro é zero quando `k+1 ≥ 2^164`. A derivação de cálculo complexo está escrita abaixo; a auditoria automática verifica suas constantes racionais, não formaliza essa análise.

**Não foi demonstrada positividade em todas as dimensões.** O passo de oito fontes deixou de depender apenas de um pivô numérico, mas sua instanciação nativa completa ainda não é um teorema Lean.

## 1. O alvo quantitativo formalizado

Para dimensão par `2n`, mantenha os estados do chart original

\[
v^-_{n,k}(x)=P^-_{k,2n}J_{n,k}x.
\]

Definimos o traço de energia negativa nas colunas originais:

\[
\tau_n(k)=\sum_{j<2n}\|v^-_{n,k}(e_j)\|^2.
\]

A síntese linear e Cauchy–Schwarz dão, com todos os cruzamentos presentes,

\[
\boxed{\quad
\|v^-_{n,k}(x)\|^2
\le\tau_n(k)\sum_{j<2n}|x_j|^2.
\quad}
\]

A soma dos quadrados dos coeficientes é explícita. Ela não substitui a norma física herdada nem redefine as features. O teorema é `nativeSourceJordanNegativeState_norm_sq_le_trace`.

Em dimensão fixa, `tau_n(k) → 0` equivale ao desaparecimento das normas das colunas negativas. O controle acima então se estende a todo input. A identidade assinada já existente fornece

\[
E_{2n}(x)=\lim_k2\bigl(\|v^+_{n,k}(x)\|^2-\|v^-_{n,k}(x)\|^2\bigr)\ge0.
\]

As declarações `nativeSourceBoundary_nonneg_of_trace_envelope` e `nativeSourceBoundary_nonneg_all_N_of_leakageTrace` mantêm o envelope e os limites como hipóteses explícitas. Ordens ímpares são tratadas por inclusão de uma coordenada zero.

O novo teorema `nativeSourceBoundary_nonneg_of_asymptotic_channel_dominance` exige somente, para cada input considerado,

\[
\|v^-_{n,k}(x)\|^2
\le\|v^+_{n,k}(x)\|^2+\varepsilon_n(k)\sum_j|x_j|^2,
\qquad \varepsilon_n(k)\to0.
\]

O canal negativo pode persistir nessa segunda rota. Sua existência não seria, por si só, um contraexemplo ao sinal da energia.

## 2. Fonte usada pelo certificado externo

Escreva `F` para `completedNativeOperatorCharacteristic` e

\[
G(y)=F(iy),\quad r(y)=G'(y)/G(y),\quad h=(k+1)^{-1},\quad y_j=(j+1)h.
\]

O script parte da integral theta original, por `x=exp(2u)`:

\[
A(y)=\int_1^\infty x^{-3/4}\sum_{m\ge1}e^{-\pi m^2x}
\cosh\!\left(\tfrac y2\log x\right)dx,
\qquad G(y)=\tfrac12-(\tfrac14-y^2)A(y).
\]

A representação real é `XiThetaCosine.completedNative_eq_thetaTail_cosine`; a continuação holomorfa ao disco usado aqui segue da representação integral e da analiticidade da característica no strip. Essa continuação e as manipulações de análise complexa abaixo não foram adicionadas como novas provas Lean nesta alteração.

Os valores de `A` e `A'` são encerrados por momentos theta calculados novamente com Arb. O resto da série de cosseno hiperbólico é majorado por uma integral positiva adicional. As integrais finitas usam o indicador de ramo analítico do integrador; as duas caudas infinitas usam envelopes exponenciais documentados no código.

Para `p` inteiro não negativo, o envelope usado é calculado exatamente na forma

\[
I_p(a,L)=\int_L^\infty x^pe^{-ax}dx
=e^{-aL}\sum_{j=0}^p\frac{p!}{(p-j)!}\frac{L^{p-j}}{a^{j+1}}.
\]

As relações `m² ≥ 1+3(m−1)` e `(M+1+j)² ≥ (M+1)²+(2M+3)j` controlam as séries modais. Não são usadas tabelas de zeros, avaliação de zeta, momentos de cache, métricas ajustadas ou o sinal desejado como premissa.

O quociente original na grade é

\[
q_j=\frac{G'(y_j)-G(y_j)}{G'(y_j)+G(y_j)}.
\]

A matriz incidente é `H_(ij)=1/(i+j+2)`; a escala física comum `k+1` permanece na definição do carrier. O defeito em coeficientes é

\[
S_{ij}=H_{ij}(1-q_iq_j).
\]

Uma fatoração intervalar `LDL*` de `S` com todos os pivôs estritamente positivos certifica o sinal em **todos os inputs complexos**, e não somente em uma direção. Os autovalores generalizados de `H^{-1}S`, quando isolados, são os do defeito no produto interno original. Nenhuma fatoração desse tipo é usada para definir ou modificar a fonte.

## 3. Oito fontes: margem de bordo certificada externamente

Se `c_j` são os coeficientes da característica par e `a_j` os coeficientes ímpares originais de `-F'/F`, os dados de entrada continuam vindo da mesma integral. O script usa a recorrência sem divisão de ajuste:

\[
c_0a_n+\sum_{j<n}a_jc_{n-j}=-2(n+1)c_{n+1}.
\]

A matriz nativa de bordo `B_N`, definida por `E_N(x)=2x*B_Nx`, tem entradas

\[
(B_N)_{ab}=\begin{cases}
(-1)^{(a+b)/2+a}a_{(a+b)/2},&a+b\text{ par},\\
0,&a+b\text{ ímpar}.
\end{cases}
\]

A normalização é a mesma de `nativeSourceFiniteBoundaryEnergy_eq_coefficient_sum`.

O certificado verifica todos os oito pivôs de

\[
\boxed{B_8-2^{-90}I>0.}
\]

Assim ele certifica externamente uma margem em todos os coeficientes:

\[
E_8(x)\ge2^{-89}\sum_{j<8}|x_j|^2.
\]

As caixas theta antigas continuam insuficientes para o sinal. O certificado novo usa enclosures muito mais estreitos de integrais da fonte; ele não refuta o contramodelo das caixas anteriores nem explica, sozinho, o sinal em dimensão arbitrária.

O pivô novo do bloco ímpar na convenção `h_j=a_j/2` fica em um intervalo estritamente positivo em torno de

\[
2.96226172771768967793983120612514\times10^{-23}.
\]

A execução reforçada, com 768 bits e corte espacial 256, fornece para esse pivô um raio publicado menor que `6×10^-241`. Essa leitura é um intervalo externo Arb, não um novo axioma nem um teorema nativo importado no Lean.

## 4. Da grade à borda: uma constante explícita

O ponto de partida são duas cotas da própria fonte, já formalizadas em `CompletedNativeAllOrderMomentUpperBound.lean`:

\[
c_0\ge1/3,\qquad |c_{m+1}|\le\frac1{35\,25^m}.
\]

Elas são as declarações `completedNativeRealEvenCharacteristicCoefficient_zero_ge_third` e `completedNativeRealEvenCharacteristicCoefficient_succ_abs_upper`. Sua auditoria axiomática é incluída entre os suportes desta alteração.

No disco `|y| ≤ R=1/4`, a série par de `G` e sua derivada dão

\[
|G(y)-c_0|\le\frac{R^2}{35(1-R^2/25)}=\frac5{2793},
\]
\[
|G(y)|\ge\frac{926}{2793}>0,\qquad
|G'(y)|\le\frac{2R}{35(1-R^2/25)^2}.
\]

A razão da última cota pelo limite inferior de `|G|` é menor que 1. Portanto `r` é ímpar, holomorfa nesse disco e satisfaz `|r| ≤ 1`. Isso é controle de regularidade; ainda não fornece sinal de um kernel.

A fatoração completada existente reduz o kernel radial, depois das amplitudes originais e antes das diferenças finitas, a

\[
K(u,v)=\frac{r(u)+r(v)}{u+v}.
\]

A singularidade em `u+v=0` é removível, pois `r` é ímpar. Uma fórmula útil é

\[
K(u,v)=\int_0^1 r'(-v+t(u+v))dt.
\]

Cauchy no disco `1/4` fornece `|K(u,v)| ≤ 8` no bidisco de raio `1/8`.

Denote por `Q_N(h)` a matriz da energia `Re storage` no chart original `J`. Com `w_(a,r)=(-1)^(a-r) binom(a,r)` e a fase antiga `eta_a=1` para `a` par, `eta_a=-i` para `a` ímpar,

\[
(Q_N(h))_{ab}=\frac{\overline{\eta_a}\eta_b}{a!b!h^{a+b}}
\sum_{r\le a,s\le b}w_{a,r}w_{b,s}K((r+1)h,(s+1)h).
\]

Esta é a síntese original completa. A igualdade usa a amplitude antiga `i(1+r(y))/sqrt(2)` e o quociente antigo `(r(y)-1)/(r(y)+1)`. No limite, `Q_N(0)=B_N`; as fases e o fator 2 de `E_N` são conservados.

A representação integral das diferenças finitas normalizadas identifica cada entrada com uma média de `∂_u^a ∂_v^b K/(a!b!)`. Se `Nh ≤ 1/16`, Cauchy no bidisco e variação entre `0` e os pontos dessa média dão

\[
|(Q_N(h)-B_N)_{ab}|
\le Nh\,8(a+b+2)16^{a+b+1}
\le N^2 16^{2N}h.
\]

Logo, por Cauchy–Schwarz nos coeficientes,

\[
\boxed{\quad
|x^*(Q_N(h)-B_N)x|
\le N^3 16^{2N}h\sum_{j<N}|x_j|^2.
\quad}
\]

A cota é uniforme em todos os inputs, em cada dimensão fixa. Não exige positividade de `B_N`. A prova escrita dessa estimativa é uma derivação analítica desta investigação, **não uma formalização Lean do cálculo complexo**.

## 5. Consequência para o canal negativo de oito fontes

Mesmo sem um limiar explícito, a margem externa já satisfaz a premissa do teorema Lean existente `radialReturnTransfer_even_eventually_norm_le_one_of_boundary_margin`, com `n=4` (a soma dos quadrados domina a norma sup dos coeficientes). Esse teorema implica contratibilidade eventual do mesmo retorno; `radialReturnJordanNegativePort_eq_zero` dá então desaparecimento eventual do canal negativo. A instanciação dessa cadeia permanece externa porque a margem nativa foi certificada por Arb.

Para `N=8`, a constante do erro é `8³ 16^16=2^73`. A margem externa anterior implica

\[
h\le2^{-164}\quad\Longrightarrow\quad
Q_8(h)\ge(2^{-90}-2^{73}h)I\ge2^{-91}I.
\]

A amplitude do chart é não nula porque `|r|<1`; as diferenças finitas formam uma transformação triangular invertível para `h>0`. Assim o sinal transporta-se aos inputs incidentes originais, com a mesma métrica. O defeito é positivo, o retorno é contrativo e seu canal negativo inteiro é zero:

\[
\boxed{k+1\ge2^{164}\quad\Longrightarrow\quad P^-_{k,8}=0.}
\]

Isso fecha externamente o desaparecimento eventual do canal negativo em oito fontes. O limiar é uma cota conservadora derivada das estimativas; não é apresentado como o primeiro valor de contratibilidade.

O argumento combina um certificado externo finito de bordo com a derivação analítica acima. **Não é um teorema Lean de oito fontes.** As premissas numéricas externas não foram inseridas como axiomas ou hipóteses opacas da fonte formal.

## 6. Casos finitos certificados

Os dois runs certificam `LDL*` positivo em todos os casos:

| Fontes N | k |
|---|---|
| 7 | 31 |
| 8 | 31, 63, 127, 255, 511, 1023 |
| 10 | 63, 255 |
| 12 | 63, 255 |

Nos casos certificados, o canal negativo é exatamente zero, como consequência do sinal do defeito inteiro. As linhas de 10 e 12 fontes são certificações finitas; não provam um limite nessas dimensões.

Para oito fontes, por exemplo, o menor autovalor físico é aproximadamente `1.91167×10^-35` em `k=31` e `5.06123×10^-58` em `k=1023`. Esses autovalores se aproximarem de zero não significa que exista energia negativa: seus intervalos são positivos. O retorno aproxima-se de `-I` e as fontes se aproximam do centro.

Não foram certificados todos os inteiros entre os valores amostrados e o limiar analítico. Para 12 fontes, o LDL é decisivo mesmo quando o algoritmo de isolamento dos autovalores não consegue separá-los; essa limitação é registrada no JSON.

## 7. Reprodução e auditoria

No servidor `llm`, foi usado `/home/thlinux/miniforge3/bin/python3`, com `python-flint 0.8.0`. A partir da raiz do repositório:

```bash
python scripts/certify_native_negative_channel.py --output research/native-negative-channel-2026-10-14/certificate-512.json
python scripts/certify_native_negative_channel.py --bits 768 --modes 16 --degree 32 --cutoff 256 --output research/native-negative-channel-2026-10-14/certificate-768.json
python scripts/check_native_negative_channel_certificate.py --certificate research/native-negative-channel-2026-10-14/certificate-512.json --replication research/native-negative-channel-2026-10-14/certificate-768.json --output research/native-negative-channel-2026-10-14/audit.json
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnLeakageControlAudit
```

Os JSON incluem os hashes do engine e das fontes Lean de definição. A auditoria recompõe os LDL a partir dos enclosures publicados, compara os dois runs e faz duas quadraturas diretas do quociente, que não passam pela expansão de Taylor dos momentos. Verifica também, por frações exatas, as constantes da derivação. O campo `analytic_calculus_argument_mechanically_checked` permanece `false`.

## Obrigação que permanece

Para `N` arbitrário, a estimativa de erro é explícita; falta provar o sinal da matriz nativa `B_N` ou obter uma estimativa independente do canal negativo. A campanha não fornece uma família de margens positivas para todas as dimensões.

Também não foi construída uma família física positiva coerente entre dimensões, uma medida espectral das alturas ou um operador global identificado com essas alturas. A certificação de oito fontes e os controles formais desta alteração não têm esse alcance.

## Validação realizada

- `lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnLeakageControlAudit`: passou, 9828 jobs. São 11 novas declarações públicas e quatro suportes analíticos anteriores; o fechamento percorreu 6095 declarações e aprovou a guarda axiomática.
- `lake build --wfail`: passou, 10188 jobs.
- `lake build --wfail CarrySelfAdjointOperator.Audit`: passou, 10329 jobs.
- As raízes auditadas usam somente `propext`, `Classical.choice`, `Quot.sound`. Não foram adicionados `sorry`, `admit` ou axiomas novos nas fontes de prova.
- Os dois certificados externos passaram, e `audit.json` registrou `PASS_EXTERNAL_CERTIFICATE_AUDIT_NOT_LEAN`, incluindo hashes, repetição com parâmetros mais fortes e duas quadraturas diretas do quociente.
- Os dois arquivos C2 preexistentes e `lake-manifest.json` conservaram seus hashes de entrada. O cache de build da worktree foi copiado com arquivos independentes, sem compartilhar registros de build mutáveis.
