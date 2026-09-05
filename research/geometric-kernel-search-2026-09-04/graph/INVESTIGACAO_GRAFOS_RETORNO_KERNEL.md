# Garimpo executado: grafos de proveniência, retorno e pares geométricos `(S,u)`

Data: 2026-09-04. Trabalho no servidor `ssh llm`, sem alteração de fontes Lean, notas originais ou Git. Resultados remotos em `/home/thlinux/carry-kernel-geometric-search-20260904/graph/`; cópia local dos principais JSON/scripts em `/tmp/carry-geometric-graph-data/`.

## Resultado que interessa à costura

Há operadores e métricas concretos nas fontes, além da torre diagonal: a análise Green all-bases fornece a forma positiva limitada

$$
V_G=F^{-1/2}B^*BF^{-1/2},\qquad F=E^*E+B^*B,
$$

e a curvatura C2 fornece $V_{C2}=B_{C2}^*B_{C2}$. Ambos dão candidatos $S=\sqrt V$ e kernels do tipo já formalizado. Executamos os laboratórios e calculamos momentos de fontes geométricas explícitas. Nenhum dos candidatos testados foi identificado com os momentos nativos. A igualdade específica do readout permanece o ponto a demonstrar.

O candidato do relógio com a massa crítica é particularmente bem definido:

$$
S_n=\frac1{\log n},\quad
u_n=\frac1{\sqrt n\log n},\quad n\ge2.
$$

Ele possui um Hilbert infinito, operador limitado, fonte em $\ell^2$, kernel positivo e independência de todas as potências. Seus invariantes diferem dos nativos: $I_2=1.53285511088\ldots$ versus $2.41071974180\ldots$. Portanto, esse candidato específico não resolve a identificação, mesmo permitindo multiplicar a fonte por uma constante e dilatar o parâmetro. Isso não restringe outros observáveis, fontes ou acoplamentos geométricos.

## Fontes executadas e localização das peças

| Fonte no servidor | Linhas relevantes | SHA256 |
|---|---|---|
| `Documents/c2_green_closed_native_endpoint_graph_delivery_LR2Col/c2_green_closed_native_endpoint_graph.py` | 211–260 Newton/logjet; 287–420 convolução ímpar; 523–627 escala de Hilbert; 660–763 coequalizador; 765–818 não descida | `610022b7f1d0f29755b9abd52f4ea23da12e2d71cba4c0f61ea6b5ebf058d140` |
| `Documentos/C2_GREEN_NATIVE_RANGE_PROVENANCE_GRAPH_ENTREGA_20260719/c2_green_native_range_provenance_graph.py` | 191 testemunho livre; 272 inventário de construtores; 359 gate da imagem; 389 porta Haar; 412 grafo enriquecido | `a63138f1386a0851aa4283afe4301e3c1b61839bbba337c21ba37935a9f2647f` |
| `carry-lab/foda/native_carry_defect_return_metric_covariance_limit_lab.py` | 4–35 identidade/limite declarados; 94–103 covariância; 106–169 construção de `E`, Poisson e métrica; 260–279 CLI | `ba0803715a0de5e3ff3fae63eefae6878573f3f9d6c8aef36aa138ed57a2bd1f` |
| `carry-lab/native_carry_transverse_coercivity_cutoff_bundle_20260815/native_carry_pythagorean_green_measure_lab.py` | 4–36 pesos e estimativas; 141–195 análises; 198–266 normalização; 298–334 argumento de limites uniformes | `5993b476eb9c5f2c63f664cdd9f305a222432fc3cb7ac58afbaa3e81a183a3ef` |
| Mesmo bundle, `c2_green_discrete_valve_return_audit.py` | 278 peso; 328–381 `B`, trace, Green e retorno; 384–444 inversão exata; 446 Green local; 500 topologia; 549 coequalizador | `f7b4786f09dc42a1e72df55065243a7aa2d8a1450df8ee5dff3ce567072651c0` |
| Mesmo bundle, `native_carry_pythagorean_node_weyl_colligation_lab.py` | 108–174 coligação normalizada; 177–217 blocos espectrais; 396–435 retorno efetivo | `754c9e8f8fd8e285b7d916d122ef240fd517092c3f21e6fc871694d98ec18f35` |
| Mesmo bundle, `native_carry_collective_operator_lab.py` | 76–86 readout matricial | `006180ccfd317daebd1fd8003666d758c9f456a951dd096e88f61769fed2743b` |
| Mesmo bundle, `native_carry_primitive_real_operator_all_bases_fixed.py` | 309–380 câmeras C2 e naturais saturadas | `c68d4bb274f36eb4dc5572afe64394787876f64bc8f2e50573654f2ab712ecee` |

Todos os caminhos dessa tabela são relativos a `/home/thlinux/`. O inventário integral, incluindo as dependências copiadas, está em `source_manifest.json` e `labs_source_manifest.json`.

## Execução dos dois grafos antigos

Os dois diretórios de entrega foram copiados byte a byte: 31 arquivos. `run_graph_reaudit.py` carrega essas cópias e redireciona seus caminhos de relatório; os scripts antigos escrevem relatórios fora de `--result-dir`, por isso executar o `main` original diretamente não preservaria o pacote.

Cinco auditorias puras foram recalculadas e seus payloads coincidiram exatamente com os JSON históricos:

- `global_odd_convolution_audit`: a massa global sobre núcleos ímpares e a convolução de Dirichlet não se reduzem à única coordenada de potência prima. Foram preservados, por exemplo, os termos mistos de 15 e 21.
- `hilbert_scale_audit`: a fonte de massa unitária é $h_j=1/j$, e o fluxo $Nh$ exige a escala de Hilbert inferior.
- `endpoint_support_audit`: o suporte aritmético do endpoint continua distinguindo a potência prima.
- `coequalizer_graph_audit`: o quociente de divisor e o operador de número da torre comutam porque atuam em fatores diferentes.
- `a_descent_audit`: o pequeno testemunho livre $g=(1,-1)$ é anulado por $Q$, mas não por $A$.

Também foram executadas 15 comparações exatas de Newton versus derivada logarítmica formal, com resíduos simbólicos nulos, e a identidade de Möbius no módulo livre até 1024. O campo de fonte literal exigido pelo antigo `exact_logjet_audit` não foi falsificado: apenas seu núcleo matemático foi reexecutado.

Os `main` completos não concluíram, porque faltam os arquivos históricos obrigatórios anteriores à entrega. Uma busca posterior em `carry-lab`, `Documents` e `Documentos` confirmou ausência de numerosos nomes, incluindo `c2_green_native_a_endpoint_all_fibres.py`, `c2_green_centered_jordan_krein.py`, `c2_green_unit_mass_tail_boundary.py` e os respectivos relatórios. Alguns predecessores existem, mas não o conjunto necessário. A lista exata consta de `pipeline_attempts.json` e `historical_dependency_search.json`. Esse impedimento diz respeito à reprodução da cadeia histórica completa; não impediu executar suas rotinas algébricas autocontidas.

O gate do segundo script foi reexecutado sobre o **inventário histórico armazenado**, sem promover esse replay a uma auditoria dos construtores atuais. Ele registra que a imagem nativa necessária não estava definida naquele conjunto de quatro construtores. Não demonstra que ela seja impossível, nem que não possa existir em descobertas posteriores.

## Reparação explícita da proveniência: cálculo novo e exato

O testemunho histórico usa

$$
Q=(1,1),\quad A=(1/2,\sqrt3/2),\quad g=(1,-1).
$$

Preservar ambas as leituras dá

$$
E=\begin{pmatrix}1&1\\1/2&\sqrt3/2\end{pmatrix},\qquad
G=E^*E=
\begin{pmatrix}
5/4&1+\sqrt3/4\\1+\sqrt3/4&7/4
\end{pmatrix}.
$$

$E$ é invertível, $G>0$, $\det G=1-\sqrt3/2>0$, $Qg=0$, mas $Eg=(0,(1-\sqrt3)/2)\ne0$. Verificamos exatamente $E^{-1}E=I$ e a preservação de energia. Depois de tensorizar com quatro níveis da torre, a relação com o operador $N=I\otimes\operatorname{diag}(1,2,3,4)$ também foi verificada exatamente.

Essa é uma construção explícita que conserva o dado perdido por $Q$. Sua limitação precisa: ela foi construída no pequeno módulo livre, sem identificação demonstrada com a imagem nativa. Além disso, uma extensão tensorial constante multiplica todos os momentos pela mesma energia do fator de divisor, preservando os invariantes $I_k$. Portanto, reparar a proveniência dessa forma não basta para transformar o espectro da torre em outro readout. Resultado: `exact_joint_provenance_repair.json`.

## A escala da torre e seu observável

Nas notas do grafo,

$$
H_0=\ell^2(j\ge1),\qquad
\|y\|_{-1}^2=\sum_{j\ge1}|y_j|^2/j^2,
\qquad N:H_0\to H_{-1},\quad (Nx)_j=jx_j.
$$

$N$ é uma isometria **entre essas duas normas**. A identificação coordenada canônica $U_{-1}:H_{-1}\to\ell^2$, $U_{-1}y=y/j$, satisfaz $U_{-1}N=I$. Esse fato foi checado exatamente em corte e vale coordenada por coordenada no infinito. Logo a simples normalização do mapa entre espaços não produz um observável cíclico de infinitas ordens: produz a identidade. É necessário especificar o observável espectral adicional. Resultado: `rigged_identification_check.json`.

Escolhendo $S=N^{-1}$ e a fonte já presente $u_j=1/j$,

$$
m_k=\langle u,S^{2k}u\rangle=\sum_{j\ge1}j^{-2k-2},
\qquad a(t)=t\sum_{j\ge1}\frac1{j^2-t^2}.
$$

As primeiras somas pares dão $I_2=m_0m_2/m_1^2=10/7$ e $I_3=m_0^2m_3/m_1^3=15/7$. As somas foram recalculadas por Euler–Maclaurin, sem uso de ordinadas de zeros ou ajuste aos momentos nativos.

## Relógio logarítmico com a massa crítica: candidato escolhido e verificado

Para o corte do relógio $L=\operatorname{diag}(\log n)$ com massa carry $1/n$, $n\ge2$, tome

$$
B_M(t)=\sum_{n=2}^M\frac{1/n}{t-\log n}.
$$

A parte ímpar negativa é exatamente

$$
\frac{B_M(-t)-B_M(t)}2
=t\sum_{n=2}^M\frac{1/(n\log^2n)}{1-t^2/\log^2n}.
$$

Assim a regularização $S_n=1/\log n$, $u_n=1/(\sqrt n\log n)$ tem uma origem precisa como diferença de resolventes do relógio. A escolha dessa combinação ainda precisa ser identificada com a leitura da característica completada; não consta aqui como teorema nativo existente. As parcelas $B_M(t)$ isoladas divergem, enquanto a diferença converge localmente para $|t|<\log2$.

$\|S\|=1/\log2$ e $\|u\|^2=\sum_{n\ge2}1/(n\log^2n)<\infty$. As potências são linearmente independentes: se um polinômio $p$ satisfaz $p(S)u=0$, então $p(1/\log n)=0$ para todos os naturais $n\ge2$, logo $p=0$. A mesma observação vale para a torre. Isso fornece positividade estrita dos Grams ordinário e deslocado em todas as ordens desses **momentos candidatos**.

| Candidato definido previamente | $I_2$ | $I_3$ |
|---|---:|---:|
| Momentos nativos da referência independente | 2.4107197418091241443 | 6.8909194998420713776 |
| $S_j=1/j$, $u_j=1/j$ | 1.4285714285714285714 | 2.1428571428571428571 |
| $S_n=1/\log n$, $u_n=1/(\sqrt n\log n)$ | 1.5328551108828039274 | 2.5406743933392406467 |
| $S_j=1/j$, $u_j=3^{-j/2}/j$ | 1.0567260772111606667 | 1.1309793587403132188 |
| $S_j=3^{-j/2}$, $u_j=1/j$ | 1.4026695468705552019 | 2.0596852530538140528 |

Também foram testadas as bases 5 e 7 e a combinação de semigrupo/fonte crítica. Todos os resultados estão em `geometric_diagonal_candidates.json`. Não houve seleção de parâmetros para aproximar a referência.

Para o candidato logarítmico, as somas foram feitas de duas formas independentes quanto ao corte e precisão: `(N,m,dps)=(256,48,120)` e `(512,64,160)`. A discrepância relativa máxima entre oito momentos foi $5.27\cdot10^{-121}$. As derivadas de $f(x)=1/(x\log^q x)$ foram calculadas por recorrência de coeficientes inteiros. O resto analítico após correções de Euler–Maclaurin até $m-1$ obedece

$$
|R_m|\le\frac{|B_{2m}|}{(2m)!}\,|f^{(2m-1)}(N)|,
$$

porque as derivadas têm sinal alternado. Os limites de truncamento estão no JSON; o maior entre os oito momentos da segunda execução foi $2.73\cdot10^{-236}$. A aritmética utilizada não é intervalar: o limite analítico controla o resto; a checagem em duas precisões controla empiricamente o arredondamento. Não se promove a execução a prova formal Lean.

## Kernels de retorno efetivamente executados

O laboratório de retorno foi reexecutado com câmeras 2–7, cortes de identidade 8,16,32,64, covariâncias até 8192 e tempos comuns 0,1,2. Nenhuma altura de zero foi usada como entrada deste experimento. Os tempos padrão históricos do CLI foram substituídos explicitamente.

O maior resíduo de $E^*G_EE=I$ foi $1.06\cdot10^{-14}$; o de $S(z)G_ES(z)^*=C R_zR_z^*C^*$ foi $4.43\cdot10^{-14}$. A normalização assintótica converge lentamente; os erros finitos para o Gram limite continuam grandes nos cortes executados, e não foram anunciados como convergência numérica certificada.

Um cálculo adicional usou **duas** resolventes da coligação real, nos cortes 4,8,16, com $z=0.4+1.3i$ e $w=1.7+0.8i$:

$$
(\bar w-z)S(z)G_ES(w)^*=B(z)-B(w)^*,\quad
B(z)=C(z-L)^{-1}C^*.
$$

O maior resíduo de covariância cruzada foi $1.11\cdot10^{-13}$; da identidade sem divisão, $2.88\cdot10^{-13}$. Isso instancia numericamente o mecanismo do novo módulo Lean `ReturnMetricPolarizedKernel`; não introduz um mecanismo distinto. O parâmetro de resolvente continua distinto do tempo da órbita nativa. Dados: `geometric_operator_checks.json`.

## Outra métrica/operador: medida Green all-bases

O laboratório utiliza os pesos derivados

$$
\omega_b(n)=\frac{k_b(n)\log b}{\sum_c k_c(n)\log c},\quad
\mu_G=\omega_b/b,\quad \mu_R=\omega_b(1-1/b),
\quad \widehat A_b=(I-b^{-1/2}U_b)^2.
$$

$E$ contém semente, residual e canais de profundidade um; $B$ contém os canais de profundidade pelo menos dois. Não é o mero observável diagonal da torre. A nota dá estimativas uniformes de $E^*E\ge I/2$ e $F\le(1+C_G)I$ e um bulk não nulo. As execuções finitas até 128 verificaram os indicadores correspondentes; a prova infinita escrita nas notas continua uma derivação a formalizar onde necessário.

Definimos, como **novo candidato**, $V_G=F^{-1/2}B^*BF^{-1/2}$ e $S=\sqrt{V_G}$. No corte 256, o autovalor máximo foi aproximadamente 0.5719426413. A normalização permite duas fontes distintas que não devem ser confundidas: a coordenada $u=e_j$ e a imagem da semente geométrica original $u=F^{1/2}e_j$.

| Fonte no corte 256 | $I_2$ | $I_3$ |
|---|---:|---:|
| $e_1$ na coordenada normalizada | 16.8658559343 | 479.014809677 |
| $F^{1/2}e_1$ | 8.92454675538 | 118.902443025 |
| $e_4$ na coordenada normalizada | 1.49820800250 | 2.33045820304 |
| $F^{1/2}e_4$ | 1.23609021917 | 1.56143671320 |

As tabelas de cortes 8–256 estão no JSON. Não há coincidência nem demonstração de identidade com os momentos nativos; também não foi demonstrado um limite quantitativo desses momentos. A semente $e_1$ **não** tem bulk nulo: as linhas de profundidade dois enxergam seus ancestrais. A posição da fonte e a normalização da métrica importam.

O laboratório antigo usa `pinv` no teste final de Poisson, mas a coligação de nó e nosso cálculo adicional utilizam a inversa à esquerda explícita $(E_n^*E_n)^{-1}E_n^*$, resolvendo um sistema positivo. A identidade matemática é a mesma quando $E_n$ tem posto completo; nenhum desses procedimentos cria o readout nativo ausente.

## Válvula C2: inversão exata, energia de curvatura e distinção de observáveis

O script autocontido foi executado em $\mathbb Q(\sqrt2)$ e $\mathbb Q(\sqrt3)$ até 12 células. Todas as identidades exatas de análise/reconstrução passaram:

$$
GB+R\operatorname{Tr}=I,\quad BG=I,\quad
\operatorname{Tr}R=I,\quad\operatorname{Tr}G=0,\quad BR=0.
$$

Seu bulk é

$$
(B_{C2}f)_j=\frac{\omega_j}{\sqrt2}
(f_{2j-1}-2f_{2j}+f_{2j+1}),\qquad
\omega_j=2^{-v_2(2j)}.
$$

O observável $V=B^*B$ é racional e positivo. A estimativa da segunda diferença fornece $\|B\|\le\sqrt2$, logo $S=\sqrt V$ é limitado. Calculamos exatamente oito momentos para sementes unitárias, com 20 células; a propagação finita garante que esses primeiros momentos são iguais aos do operador infinito, pois seus suportes não chegam ao bordo final.

| Fonte | $I_2$ exato | $I_3$ exato |
|---|---:|---:|
| $e_1$ | 6 | 145/4 |
| $e_2$ | 3/2 | 145/64 |
| $e_3$ | 22/5 | 2604/125 |
| $e_4$ | 3/2 | 11/4 |

Outra escolha exige cuidado: se se normaliza **toda** a válvula quadrada invertível $T=[B;\operatorname{Tr}]$ por $T(T^*T)^{-1/2}$ e se toma apenas a energia do bloco bulk normalizado, obtém-se uma projeção ortogonal. Suas potências positivas coincidem e seu Gram deslocado tem posto no máximo um. Essa dedução vale apenas para esse observável de projeção; não impede usar a energia de curvatura sem essa normalização, nem outra geometria de retorno.

## Ligação exata com o kernel já formalizado e obrigação restante

Para qualquer um dos pares limitados simétricos acima, no domínio de Neumann,

$$
r_t=(I-t^2S^2)^{-1}u,\qquad
\Phi(t)=(r_t,tSr_t),\qquad
a_{S,u}(t)=t\langle u,r_t\rangle
$$

produz

$$
\langle\Phi(x),\Phi(z)\rangle
=\operatorname{dslope}(a_{S,u})(x,z),\qquad
a_{S,u}'(x)=\|\Phi(x)\|^2.
$$

Esses passos já são cobertos pelos módulos novos `PositiveObservableParityKernel` e `PositiveObservableKernelDiagonal`. A construção geométrica oferece entradas para esses teoremas; o que ainda precisa ser identificado é

$$
a_{S,u}(t)=-\frac{F'(t)}{2F(t)}
\quad\text{localmente, ou equivalentemente os coeficientes/Grams exigidos.}
$$

O próximo dado de notas a procurar é uma fórmula que fixe **simultaneamente** o observável e a fonte/readout completados, com os cruzamentos e retornos de bordo, ou uma identidade de traço/determinante que derive esse readout. Apenas uma métrica positiva, um inverso geométrico ou a preservação unitária de energia não escolhe essa função escalar.

## Evidência e integridade

- `run_graph_reaudit.py`: rotinas algébricas antigas, replay datado dos gates e reparação exata de proveniência.
- `run_labs.py`: três laboratórios reexecutados em cópias, no máximo três processos e uma thread BLAS por processo.
- `graph_moment_candidates.py`: comparação de candidatos diagonais definidos sem referência a `h`, Euler–Maclaurin e kernel finito racional.
- `graph_geometric_operator_checks.py`: duas resolventes na coligação, operadores Green e momentos C2 exatos.
- `geometric_diagonal_candidates.json`: oito momentos dos candidatos, invariantes, limites de truncamento, estabilidade numérica, determinantes racionais positivos de ordens 1–4 e identidade polarizada exata.
- `geometric_operator_checks.json`: matrizes Green, momentos de fontes, resíduos e valores C2 exatos.
- `final_integrity.json`: hashes dos resultados e verificação de preservação dos 41 arquivos originais (31 da entrega e 10 scripts/dependências).

A referência nativa foi fornecida separadamente pelo agente principal em `reference/native_moments.json`; seu SHA está incorporado no JSON de candidatos. Não se usaram zeros para construir os operadores ou escolher seus parâmetros. Nenhuma prova Lean foi modificada nesta investigação.
