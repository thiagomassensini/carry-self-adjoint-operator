# Investigação geométrica S,u / Fredholm — 2026-09-04

> Relatório de uma subinvestigação. Consulte o [estado consolidado da entrega](../README.md) para a integração dos dois novos módulos Lean, a auditoria final e a obrigação que continua aberta.

## Resultado

Construímos pares positivos concretos a partir das fibras de potências primas, do peso carry e do relógio `log p`, sem usar os momentos nativos nem zeros tabelados. As identidades locais vetor–traço, a preservação do kernel por Naimark e o fator de determinante associado às multiplicidades são deduções algébricas exatas. O modelo global de relógio puro com fonte carry possui Grams estritamente positivos em toda ordem, mas seu readout tem massas que não podem ser multiplicidades de zeros de uma função holomorfa no strip nativo, mesmo após massa e dilatação globais fixas.

Uma segunda construção usa o **Gram de rank um em cada fibra carry**. Ela coloca a massa também no operador, produz `V≥0` de classe traço e satisfaz exatamente `m_atom/λ=1`. A variante diagonal dos números materiais também satisfaz essa condição. Ambas são propostas geométricas desta investigação; não são identificações da característica completada já demonstradas nas fontes. Seus primeiros invariantes, calculados até cutoff `10^7`, continuam separados dos nativos mesmo com liberdade de massa e escala.

O [suplemento de massa atômica e Gram por fibra](/tmp/carry-geometric-atomic-residue-supplement.md) contém a prova em papel da condição de multiplicidade, as hipóteses de continuação, as declarações Lean atuais que asseguram a holomorfia da característica nativa no strip, as duas novas candidatas e seus testes. A origem do peso e a positividade construída permanecem válidas; o passo ainda exigido é obter o readout específico da completion através das relações completas de retorno e cumulantes.

Foram executados o teste simbólico da fibra `m=12`, crivos até dez milhões e quadraturas theta em 50/80 dígitos; os limites de cauda são analíticos. Esses testes numéricos não são novas provas Lean. Nenhum Lean ou Git foi alterado nesta investigação.

## 1. Fibra local: fórmula vetor–traço sem pressupor Hankel

Fonte concreta: servidor `llm`,
`/home/thlinux/carry-lab/Organizar/TFVD_PRIMOS_HILBERT_COVARIANT_MASS_GAP_EXTENDED/baseline_v1/sources/user_uploaded/c2_cumulant_naimark_intertwiner.py`, linhas 1–24 e 71–123.

Para `m≥2`, sejam `P_m={p primo : p|m}`, `v_p=v_p(m)` e

$$
\mathcal T_m=\{(p,k):p\in P_m,\ 1\le k\le v_p\}.
$$

O espaço de torre é `H_m=ℂ^{T_m}`; o espaço de ports é `K_m=ℂ^{P_m}`. O mapa que o script constrói é

$$
(A_m x)_p=\frac1{\sqrt{v_p}}\sum_{k=1}^{v_p}x_{p,k}.
$$

Assim `A_m A_m*=I`; `A_m*A_m` é a projeção nos vetores constantes em cada bloco primo. O relógio `D_m=diag(log p)` entrelaça `A_mD_m=E_mA_m`, onde `E_m=diag(log p)` nos ports. O vetor original da nota, `w_{p,k}=√(log p/log m)`, tem norma 1 pela fatoração `log m=Σ_p v_p log p` e `A_mw` coincide com a amplitude valuation–Naimark do atlas. Isso é informação aritmética própria da fonte, anterior a qualquer sequência `h_n`.

### 1.1 Inverso do relógio solicitado

Como `p≥2`, `log p>0`. Defina, agora,

$$
S_m=\operatorname{diag}((\log p)^{-1}),\qquad
V_m=S_m^2=\operatorname{diag}((\log p)^{-2}),\qquad
u_m(p,k)=(\log p)^{-1}.
$$

`S_m` e `V_m` são positivos; `ν_m` é o vetor das entradas diagonais de `√V_m`. Equivalentemente, em Hilbert–Schmidt, use o vetor `√V_m` e multiplicação à esquerda por `√V_m`. Todas as identidades seguintes são somas diagonais finitas:

$$
\boxed{\langle\nu_m,S_m^{2n}\nu_m\rangle
=\operatorname{Tr}(V_m^{n+1})
=\sum_{p|m}\frac{v_p}{(\log p)^{2n+2}}.}
$$

Para `t²` fora do espectro de `V_m^{-1}`, ponha

$$
q_m(t^2)=\langle\nu_m,(I-t^2V_m)^{-1}\nu_m\rangle
=\sum_{p|m}\frac{v_p}{(\log p)^2-t^2}
=\operatorname{Tr}[V_m(I-t^2V_m)^{-1}].
$$

A característica que este readout **de fato** produz é

$$
F_m(t)=\det(I-t^2V_m)
=\prod_{p|m}\left(1-\frac{t^2}{(\log p)^2}\right)^{v_p},
\qquad -\frac{F_m'(t)}{2F_m(t)}=tq_m(t^2).
$$

Seus zeros são `±log p`. O fato de ser uma característica local positiva verdadeira não a identifica com a característica nativa completada.

### 1.2 Kernel exato local e compressão

Defina o par

$$
\Phi_m(t)=\big((I-t^2V_m)^{-1}\nu_m, tS_m(I-t^2V_m)^{-1}\nu_m\big).
$$

Para `x,z` reais fora dos polos,

$$
\begin{aligned}
\langle\Phi_m(x),\Phi_m(z)\rangle
&=\sum_{p|m}v_p\frac{(\log p)^2+xz}
 {((\log p)^2-x^2)((\log p)^2-z^2)}\\
&=\frac{zq_m(z^2)-xq_m(x^2)}{z-x}.
\end{aligned}
$$

Na diagonal usa-se a derivada. O sinal é o exigido por `dslope(-F'/2F)`.

Se `\bar S_m=diag((log p)^{-1})` nos ports, então

$$
A_m S_m=\bar S_m A_m,\qquad
\bar\nu_m(p)=(A_m\nu_m)_p=\frac{\sqrt{v_p}}{\log p}.
$$

Todos os vetores `S_m^j ν_m` estão no subespaço constante de cada bloco; por isso `A_m` preserva todos os seus produtos internos, os jets e o kernel acima. **O vetor comprimido precisa conservar o fator `√v_p`.**

O traço ordinário do operador comprimido, porém, perde multiplicidades:

$$
\operatorname{Tr}(V_m^{n+1})
=\sum_p\frac{v_p}{(\log p)^{2n+2}},\qquad
\operatorname{Tr}(\bar V_m^{n+1})
=\sum_p\frac1{(\log p)^{2n+2}}.
$$

Exatamente,

$$
\boxed{
\det(I-t^2V_m)=\det(I-t^2\bar V_m)
\prod_{p|m}\left(1-\frac{t^2}{(\log p)^2}\right)^{v_p-1}.}
$$

O último produto é o determinante no setor `ker A_m`, que também é invariante pelo relógio. Pode-se conservar esse setor ou substituir o traço comprimido por `τ_m(X)=Tr(W_m X)`, `W_m=diag(v_p)`. O readout vetorial com fonte `√v_p/log p` já preserva essa informação, mas não autoriza trocar `τ_m` pelo traço ordinário. Isso explica precisamente como um mapa lossless para os estados observados pode não preservar um determinante espectral com multiplicidades.

**Teste simbólico:** servidor Python/SymPy, fibra `m=12` (`v_2=2,v_3=1`), com símbolos reais não nulos `a=log 2,b=log 3`: `AA*=I`, `AS=\bar S A`, fonte comprimida `(√2/a,1/b)` e `kernel−dslope=0`; determinante cheio e comprimido diferem por `1−t²/a²`. Não se usaram aproximações de zeros.

## 2. Par global com o peso carry: positivo, explícito e readout diferente

O relógio puro na torre global tem infinitas cópias de `log p` para cada primo. Portanto `S=diag(1/log p)` é limitado e positivo, mas `V=S²` não é compacto nem de classe traço: já o subespaço `{(2,k):k≥1}` tem autovalor fixo `(log 2)^{-2}` e dimensão infinita. A fonte crua `1/log p` tampouco pertence a ℓ².

O peso carry corrige a fonte de maneira concreta. Em `H=ℓ²{(p,k):p primo,k≥1}`, tome

$$
S e_{p,k}=\frac1{\log p}e_{p,k},\qquad
u_{p,k}=\frac{p^{-k/2}}{\log p}.
$$

A lei `p^{-k/2}` é a amplitude quadrática de carry. Então

$$
\|\nu\|^2=\sum_p\sum_{k\ge1}\frac{p^{-k}}{(\log p)^2}
=\sum_p\frac1{(p-1)(\log p)^2}<\infty.
$$

A convergência segue de `1/(p−1)≤2/p` e da comparação com `Σ_{n≥2}1/(n(log n)²)`. `S` é limitado por `1/log 2`, positivo e injetivo. Logo temos um par global concreto, sem exigir antes positividade de `h`:

$$
\boxed{g_n=\langle\nu,S^{2n}\nu\rangle
=\sum_p\frac1{(p-1)(\log p)^{2n+2}}.}
$$

A medida correspondente é

$$
\rho_{\rm geo}=\sum_p\frac1{(p-1)(\log p)^2}\,
\delta_{(\log p)^{-2}}.
$$

Ela tem massa finita, suporte infinito, contido em `(0,(log 2)^{-2}]`; portanto os Hankels ordinário e deslocado são estritamente positivos em qualquer ordem. A prova: um polinômio não nulo só pode se anular em finitos pontos; todos os átomos e suas posições são positivos.

Entretanto o readout é exatamente

$$
q_{\rm geo}(v)=\sum_p\frac1{(p-1)((\log p)^2-v)}.
$$

Já `g_0≥1/(log 2)²>1`, enquanto `canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth` prova `h_0<1/16`. Logo este par cru não passa o primeiro teste nativo, e uma isometria apenas preservaria a diferença. Essa é uma afirmação sobre o par definido aqui; não é uma proibição de outro operador derivado do retorno completo.

Há um segundo diagnóstico exato. Integrar o readout perto de zero dá

$$
\exp\left(-\int_0^v q_{\rm geo}(u)du\right)
=\prod_p\left(1-\frac v{(\log p)^2}\right)^{1/(p-1)}.
$$

Os resíduos em `v=(log p)²` correspondem a expoentes `1/(p−1)`, fracionários para `p≥3`. Portanto esse germen não pode ser o determinante Fredholm inteiro de um operador positivo com o traço ordinário: nesse caso os expoentes seriam multiplicidades inteiras. Resíduos fracionários são perfeitamente compatíveis com o kernel positivo vetorial original. A restrição de identificação, porém, é mais ampla que Fredholm: a continuação do readout até seus polos reais exige `m_atom/λ` inteiro para que ele seja `−F′/(2F)` de uma função holomorfa não localmente nula. O suplemento demonstra essa condição, verifica o strip Lean atual e constrói novas candidatas que a satisfazem. A fonte carry fornece uma medida positiva; identificar a característica nativa exige outra transformação demonstrada do observável/multiplicidades.

## 3. A cola direta dos scripts e sua reparação exata exigida

`c2_cumulant_naimark_global_candidate.py`, linhas 54–68, empilha as médias locais:

$$
T_\beta((m,p),p^k)=
\frac{m^{-\beta}}{\sqrt{v_p(m)}}\,\mathbf1_{1\le k\le v_p(m)}.
$$

Nas linhas 71–103 mede o resíduo da identidade Green, permite ajuste escalar por mínimos quadrados e, em 135–150, testa a polarização da incidência. É uma sonda finita; o script não declara uma ligação com a característica completada.

Para uma coluna fixa `p^k`, a norma quadrática tem a contribuição

$$
\sum_{v_p(m)=k}\frac1{k m^{2\beta}}
=\frac{p^{-2\beta k}}k\sum_{p\nmid r}r^{-2\beta}.
$$

No peso crítico `β=1/2` ela diverge. Para `β>1/2`, a matriz inteira é Hilbert–Schmidt, pois

$$
\|T_\beta\|_{HS}^2=\sum_{m\ge2}\omega(m)m^{-2\beta}<\infty.
$$

Aqui `ω(m)` conta primos distintos e `ω(m)≤log m/log 2`. Esse contraste não é um no-go para a rota do carry: ele mostra que, na cola crítica, é necessário inserir as diferenças, a deconvolução/retorno ou as moléculas completas **antes** de identificar ocorrências de escala. A molécula de quatro cantos com cancelamentos `M_0=M_1=0` das notas Haar trata precisamente outro objeto, com caudas melhoradas; não é coberta por essa divergência da incidência crua.

## 4. Outros determinantes auditados e o papel da completion

### 4.1 Determinante já presente nas notas de alturas

`Downloads/hp/NATIVE_CARRY_HEIGHT_MOMENT_JACOBI_OPERATOR_LOG.md`, linhas 202–275, apresenta
`Φ(u)=det(I−u\widehat T^{-2})`. Porém `\widehat T` é a amplificação da medida positiva de momentos previamente obtida; `r_y=ρ({y})/y` é a multiplicidade. A seção é uma consequência condicional do gate, não uma construção positiva independente que o descarregue.

`IDENTIDADE_PROJETIVA_EXATA_LIMITE_OPERADOR_ALTURAS.md` começa com `G_N>0`, `K_N≥0` e produz `J_N=L_N^{-1}K_NL_N^{-*}`. Sua identidade exata de Schur para diferenças entre resolventes é útil depois da positividade. Também não constrói o operador sem essa hipótese.

### 4.2 Determinantes C2 antigos: escopo finito auditável

Servidor `/home/thlinux/hipotese_riemann/markdown/c2_operatorial_determinantal_bridge.md`, linhas 130–224:

$$
P_s^{(K)}=D_s^{-1}P^{(K)}D_s,
\quad
\det(I-\lambda P_s^{(K)})
=(1-\lambda/2)^{K-3}(1-\lambda+2^{-K}\lambda^2).
$$

A independência em `s` vale para essa compressão que esquece a fibra `m`. Não se estende ao operador completo com retorno e bordo. Para romper a conjugação, o termo adicional deve carregar informação que foi apagada da fibra; simplesmente somar mais profundidades não muda a identidade.

O script `/home/thlinux/hipotese_riemann/experiments/c2_return_determinant_test.py`, linhas 45–90, usa `R_ij=w(n_i)n_j^{-s}`. Ele tem rank no máximo 1. Exatamente:

$$
\det(I-R)=1-\sum_jw(n_j)n_j^{-s},\qquad
\operatorname{Tr}(R^r)=\left(\sum_jw(n_j)n_j^{-s}\right)^r.
$$

A expansão de logdet truncada do script é uma aproximação que exige controle do raio espectral; esse toy não oferece um operador constante positivo com novos cumulantes.

### 4.3 Retorno métrico existente

Servidor `carry-lab/foda/native_carry_defect_return_metric_covariance_limit_lab.py`, linhas 1–30 e 118–160, implementa

$$
E_M^*G_{E,M}E_M=I,
\qquad
S_M(z)G_{E,M}S_M(w)^*
=C_M(z-L_M)^{-1}(\bar w-L_M)^{-1}C_M^*,
$$

com `L_M=diag(log n)`. A versão polarizada segue da identidade finita da métrica e da identidade resolvente. É uma peça real para construir um kernel positivo de readout. O parâmetro resolvente `z` e a altura nativa `t` continuam distintos.

O inverso do relógio ambiente, sem observável com massa somável, não oferece por si só um Fredholm: `Σ_{n≥2}(log n)^{-2}` diverge. A identidade isométrica do retorno preserva essa massa. Os limites de covariância normalizados do script são Grams de câmera; não são uma igualdade de determinantes com `F(t)/F(0)`.

### 4.4 A completion tem de entrar antes da identificação espectral

Fonte Lean atual `CarrySelfAdjointOperator/CompletedOperatorCharacteristic.lean`, linhas 28–40:

$$
s=\tfrac12+it,\quad
A(t)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2),\quad
F(t)=A(t)\,\mathrm{nativeScalar}(s).
$$

O fator polinomial normalizado isolado é

$$
\frac{s(s-1)}{(1/2)(-1/2)}=1+4t^2.
$$

Ele corresponderia ao fator `det(I−t²V)` de um autovalor negativo `−4`, se fosse interpretado isoladamente. Portanto uma soma ortogonal de fatores individualmente positivos não implementa automaticamente a completion; é necessário provar a identidade do produto completo com seus cancelamentos. O resultado não proíbe uma representação positiva do produto completado.

A comparação concreta mais econômica para qualquer novo candidato `V_M` ou `(S_M,u_M)` é a recorrência nativa completa

$$
\sum_{k=0}^n h_k c_{n-k}=-(n+1)c_{n+1},
$$

presente em `CompletedNativeWeylMoments.lean` e `CompletedNativeRealWeylMoments.lean`. Provar essa recorrência para traços/readouts geométricos obtidos independentemente, com `c` da característica completada, identifica a sequência por unicidade; não se precisa pressupor que os `h` sejam positivos. Mas as fontes auditadas ainda não fornecem a igualdade de coeficientes que inicia essa passagem.

## 5. Situação Lean e módulo independente possível

Busca atual nas fontes consumidas de `FiniteNativeCarryOperator`, `CPFormal`, `NativeCarrySpectralWeyl` e `CarrySelfAdjointOperator`: não localizei a fórmula local valuation–Naimark vetor–traço, nem a identidade do determinante escondido, nem uma construção Hilbert–Schmidt/Fredholm positiva independente para a característica completada.

Peças próximas já presentes:

- `CPFormal/Carry/CpMultibaseCameraAtlas.lean:58`: fatoração exata de `Real.log n` pela soma `v_p(n) log p`.
- `CPFormal/Carry/CpMultibaseCameraAtlasHilbert.lean:109`: `logEval_factorizationVector`.
- `CompletedC3NaimarkCoisometricBlock.lean`: bloco coisométrico C3; é outro mapa, não a média de fibras do script.
- `CompletedGreenJetSignedHeightIntertwiner.lean:461`: coisometria do cutoff transportado; não identifica o readout nativo de um traço logarítmico.
- Mathlib `LinearAlgebra/Matrix/Trace.lean:48,158–167`: `Matrix.trace_diagonal`, `trace_mul_comm`, `trace_mul_cycle`.
- Mathlib `LinearAlgebra/Matrix/Determinant/Basic.lean:77`: `Matrix.det_diagonal`.

Um módulo finito independente poderia parametrizar um conjunto finito de blocos, multiplicidades positivas `v_p` e números positivos `λ_p`; usar `Σ p, Fin(v_p)` como índice de torre; definir `S=diag(λ_p^{-1})`, fonte `λ_p^{-1}`, a média `A` e provar as identidades de §1. Especializar `λ_p=log p` e `v_p=m.factorization p` dá origem aritmética. O módulo deve nomear sua característica local própria e manter explícita a igualdade adicional ainda necessária com a característica completada.

## Proveniência dos arquivos remotos centrais

| Arquivo no servidor `llm` | SHA256 |
|---|---|
| `carry-lab/Organizar/TFVD_PRIMOS_HILBERT_COVARIANT_MASS_GAP_EXTENDED/baseline_v1/sources/user_uploaded/c2_cumulant_naimark_intertwiner.py` | `b53b7809a2fa6b2daf770989fd99cff9a71da8968f00826313ed14225b53a49e` |
| Mesmo diretório, `c2_cumulant_naimark_global_candidate.py` | `d2844b4c5869c92ff940394c62d826c4af08888b1d68903cde4a5a8e0cfd33f8` |
| `carry-lab/foda/native_carry_defect_return_metric_covariance_limit_lab.py` | `ba0803715a0de5e3ff3fae63eefae6878573f3f9d6c8aef36aa138ed57a2bd1f` |
| `carry-lab/foda/native_carry_mobius_log_clock_connected_dressing_lab.py` | `bc5532731404eb086d773710ba6cfd3931da59cd31609263d8e2d115e2bb4507` |
| `hipotese_riemann/markdown/c2_operatorial_determinantal_bridge.md` | `6cb5b96a0d4a54723d7ff9706b629d36ef72c5aad7261413c84033ddb74f8e69` |
| `hipotese_riemann/experiments/c2_return_determinant_test.py` | `c0e61c7d6f6b08b71b940d21167bde8d375a58042728fda79a02a192cecc95f7` |
| `carry-self-adjoint-operator/CarrySelfAdjointOperator/CompletedOperatorCharacteristic.lean` | `de21570ecf684ee42e8222ccbc598b6bb84c21404c8cd55f815504ab3ae093a2` |

As referências com prefixo `Downloads/` são arquivos locais do notebook; as demais desta tabela são relativas a `/home/thlinux` no servidor `llm`. Não houve edição dos originais.


## 6. Invariantes de forma: cálculo solicitado até dez milhões

Artefatos locais e no servidor, com o mesmo nome:

- `/tmp/carry_prime_power_pair_audit.py`;
- `/tmp/carry_prime_power_pair_audit.json`.

A execução usou **um worker**, crivo por `bytearray` e somas `math.fsum`; demorou 6,9 segundos incluindo as duas quadraturas theta. Foram 78.498 primos até `10^6` e 664.579 até `10^7`. Nenhum zero tabelado foi usado.

### 6.1 Cauda sem hipótese de contagem de primos

Para `P≥2` e `n≥0`, pela comparação com todos os inteiros e a integral de uma função decrescente,

$$
0\le g_n-g_n^{(P)}
\le \frac P{P-1}\sum_{r>P}\frac1{r(\log r)^{2n+2}}
\le \boxed{\frac P{P-1}\frac1{(2n+1)(\log P)^{2n+1}}}.
$$

Não se invocou PNT, estimativa da densidade de primos ou extrapolação numérica. A desigualdade da cauda é analítica. Os intervalos computados abaixo acrescentam margem numérica `10^{-10}` às somas em ponto flutuante; não são intervalos verificados por biblioteca de aritmética intervalar nem pelo kernel Lean.

| Momento | Prefixo `p≤10^7` | Cota analítica da cauda |
|---|---:|---:|
| `g_0` | 2,7275181055575612 | 0,0620420750475292 |
| `g_1` | 4,73337471406446 | 0,00007960449701249243 |
| `g_2` | 9,319726667794868 | 0,00000018384905230141408 |
| `g_3` | 19,009222533342747 | 0,0000000005054822412324587 |

As razões

$$
R_2=\frac{g_0g_2}{g_1^2},\qquad
R_3=\frac{g_0^2g_3}{g_1^3},\qquad
R_{\rm adj}=\frac{g_1g_3}{g_2^2}
$$

são invariantes sob `(S,ν)↦(aS,cν)` com `a,c>0`, pois `g_n↦c²a^{2n}g_n`. Portanto elas testam uma identificação que já permite ajustar livremente massa e escala; são mais informativas que comparar apenas `g_0`.

| Razão | Prefixo `10^6`, mais cauda | Prefixo `10^7`, mais cauda | Nativo pela quadratura theta |
|---|---:|---:|---:|
| `R_2` | [1,13421599; 1,16438558] | [1,13452595; 1,16037175] | 2,410719741809124 |
| `R_3` | [1,33269797; 1,40450146] | [1,33341417; 1,39483606] | 6,890919499842071 |
| `R_adj` | [1,03592559; 1,03595336] | [1,03592633; 1,03594380] | 1,185724320093168 |

A separação é ampla: **o par de relógio puro com fonte carry não parece tornar-se nativo apenas por escala e massa**. A parte nativa dessa comparação é uma auditoria numérica de alta precisão, não uma nova desigualdade formal Lean. O desacordo cru de `g_0>1>1/16>h_0` admite prova analítica e usa o lema Lean existente de `h_0`; a afirmação mais forte envolvendo essas razões ainda não foi formalizada.

### 6.2 Origem dos números nativos

O script usa a função theta que já entra na característica concreta:

$$
A(u)=2\sum_{r\ge1}e^{u/2-\pi r^2e^{2u}},\qquad
A_j=\int_0^\infty u^jA(u)\,du.
$$

Por integração por partes em `K=A''−A/4`,

$$
\mu_0=\frac12-\frac{A_0}4,\qquad
\mu_{2j}=(2j)(2j-1)A_{2j-2}-\frac{A_{2j}}4\quad(j\ge1),
\qquad c_j=\frac{(-1)^j\mu_{2j}}{(2j)!}.
$$

Aplica-se então a recorrência completa

$$
h_n=\frac{-(n+1)c_{n+1}-\sum_{k=0}^{n-1}h_kc_{n-k}}{c_0}.
$$

Foram integradas `A_0,A_2,A_4,A_6,A_8`, com `r=1,…,8` e `0≤u≤6`, em precisões 50 e 80 dígitos. O fator `e^{−πr²e^{2u}}` torna as caudas escolhidas muito menores que a precisão exibida; a quadratura não é intervalar. Os valores concordam nas casas apresentadas:

$$
\begin{aligned}
h_0&\simeq0.0231049931154189707889338104303390140,\\
h_1&\simeq0.0000371725992852696861648662624717405785,\\
h_2&\simeq0.000000144173931400973279695381556094821,\\
h_3&\simeq0.000000000663031680252990869873272081961357.
\end{aligned}
$$

### 6.3 Independência de todas as potências, com origem nas coordenadas

A independência não é inferida dos números calculados. Se

$$
\sum_{j=0}^N c_jS^j\nu=0,
$$

a coordenada `(p,1)` dá

$$
\frac{p^{-1/2}}{\log p}\sum_{j=0}^Nc_j(\log p)^{-j}=0.
$$

O prefator é não nulo. O polinômio `P(X)=Σ_jc_jX^j` se anula em todos os números distintos `(log p)^{-1}`, e há infinitos primos. Logo `P=0` e todos os coeficientes se anulam. A mesma prova se aplica separadamente às potências pares e ímpares. Isso comprova, em papel, independência completa das órbitas e positividade estrita dos dois Hankels do par geométrico.

O domínio não é uma hipótese adicional: `S` é limitado por `1/log 2`, de modo que `S^jν∈H` para todo `j`. Esta conclusão vale para o readout vetorial do par e não aplica qualquer determinante Fredholm ao operador `V=S²`, que possui multiplicidade infinita em cada primo e não é de classe traço.
