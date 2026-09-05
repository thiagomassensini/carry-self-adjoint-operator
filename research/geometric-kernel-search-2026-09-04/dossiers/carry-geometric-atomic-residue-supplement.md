# Suplemento: massa atômica, multiplicidade e Gram por fibra

> Relatório de uma subinvestigação. Consulte o [estado consolidado da entrega](../README.md) para a integração dos dois novos módulos Lean, a auditoria final e a obrigação que continua aberta.

Investigação em papel, em 2026-09-04. Fontes Lean verificadas no servidor `llm`, repositório `carry-self-adjoint-operator`, HEAD `b01bf33f5ab78a02ebb8e48e74af2048b58e1637`. Nenhum módulo Lean foi alterado nesta investigação.

## 1. Condição atômica para uma característica holomorfa

Seja `ρ` uma medida positiva finita e

$$
a(t)=t\int\frac{d\rho(\lambda)}{1-\lambda t^2}.
$$

Considere um átomo isolado `λ₀>0`, de massa `m₀=ρ({λ₀})>0`. Exija que a contribuição do complemento seja holomorfa perto de `t₀=λ₀^{-1/2}`. Essa condição vale, por exemplo, quando `λ₀` é isolado no suporte de uma medida de suporte compacto. Então

$$
a(t)=\frac{tm_0}{1-\lambda_0t^2}+b(t),\qquad b\text{ holomorfa perto de }t_0,
$$

e, por cálculo direto,

$$
\boxed{\operatorname{Res}_{t=t_0}a=-\frac{m_0}{2\lambda_0}.}
$$

Se uma função `F` é holomorfa perto de `t₀`, não identicamente zero nesse entorno, e satisfaz `a=−F'/(2F)` no entorno perfurado onde `F≠0`, escreva

$$
F(t)=(t-t_0)^N g(t),\qquad N\in\mathbb N,\quad g(t_0)\ne0.
$$

Logo

$$
-\frac{F'}{2F}=-\frac N{2(t-t_0)}-\frac{g'}{2g},
\qquad
\boxed{\frac{m_0}{\lambda_0}=N=\operatorname{ord}_{t_0}F\in\mathbb N_{>0}.}
$$

A mesma fórmula vale em `−t₀`. Ela exige somente holomorfia local no polo, e não uma representação Fredholm ou holomorfia em todo o plano. Em coordenada par `v=t²`, o resíduo de `q(v)=a(t)/t` em `v₀=1/λ₀` é `−m₀/λ₀`.

Essa condição é sobre a identificação de um readout positivo específico com a log derivada de uma característica holomorfa. **Massas/resíduos fracionários continuam perfeitamente válidos para kernels positivos de resolvente.**

## 2. Aplicação exata ao relógio primo puro com fonte carry

No par

$$
S e_{p,k}=\frac1{\log p}e_{p,k},\qquad
u_{p,k}=\frac{p^{-k/2}}{\log p},
$$

a medida cíclica tem

$$
\lambda_p=(\log p)^{-2},\qquad
m_p=\frac{1}{(p-1)(\log p)^2},\qquad
\frac{m_p}{\lambda_p}=\frac1{p-1}.
$$

Para qualquer primo `p≥3` esse número está estritamente entre 0 e 1, portanto não é uma multiplicidade de zero. Consequentemente

$$
a_{\rm geo}(t)=t\sum_p\frac1{(p-1)((\log p)^2-t^2)}
$$

não pode coincidir com `−F'/(2F)` no domínio continuado de uma característica holomorfa que alcance os pontos `±log p` e não seja localmente zero.

A série define uma função meromorfa em todo o plano: em cada compacto, para todos os primos suficientemente grandes `|(log p)²−t²|≥(log p)²/2`, e a cauda é majorada pela série somável `2Σ_p1/((p−1)(log p)²)`. Os polos `±log p` são discretos, sem acumulação finita. Assim os resíduos acima são resíduos da soma continuada, não apenas de suas parcelas formais.

### 2.1 Igualdade apenas perto de zero: hipótese de continuação necessária

A comparação de um germen perto de zero com polos distantes usa unicidade de continuação meromorfa em um domínio complexo aberto e conexo que contenha o centro e os polos em questão. Um strip horizontal contendo todo o eixo real é suficiente. As duas funções meromorfas coincidem nesse domínio se coincidem em um disco aberto perto de zero — ou em um intervalo real com ponto de acumulação em uma região onde ambas são holomorfas.

Não se infere essa conclusão de um conjunto finito de momentos. Também não seria válido usá-la se a característica estivesse definida somente num disco pequeno cuja fronteira precede os polos.

Uma identidade dos kernels `dslope(a_geo)=dslope(a_F)` em um intervalo perto de zero determina `a_F−a_geo` até uma constante. Essa constante é irrelevante aos resíduos. No caso atual ambas as respostas são ímpares e se anulam no centro, de modo que a constante também é zero.

### 2.2 Toda massa e dilatação fixas

Sob `S↦αS`, `ν↦cν`, com `α,c>0`,

$$
\lambda_p'=\alpha^2\lambda_p,\qquad m_p'=c^2m_p,\qquad
\frac{m_p'}{\lambda_p'}=\frac{\gamma}{p-1},\quad
\gamma=\frac{c^2}{\alpha^2}>0.
$$

Há primos arbitrariamente grandes. Escolhendo `p>γ+1`, o quociente fica em `(0,1)` e não pode ser inteiro. Portanto nenhuma massa global e dilatação global positivas fixas tornam esse readout puro uma log derivada de característica holomorfa no strip inteiro. Esse argumento é exato e não depende da auditoria numérica de `R₂,R₃`.

Multiplicar `F` por um fator holomorfo não nulo perto do polo acrescenta uma log derivada holomorfa e preserva o resíduo. A completion isolada não pode simplesmente remover a multiplicidade fracionária por um fator invertível nesse domínio. Uma modificação geométrica do operador/readout, porém, pode alterar as massas e os polos — a seção 4 constrói uma candidata desse tipo.

## 3. O domínio da característica nativa está formalizado

As hipóteses analíticas requeridas acima existem nas fontes atuais:

| Declaração Lean | Localização | Conteúdo relevante |
|---|---|---|
| `completedNativeHeightDomain` | `CompletedGreenMomentJets.lean:139` | `{z : operatorHeightParameter z ∈ genuineCriticalStrip}` |
| `genuineCriticalStrip` | pacote CPFormal, `Analytic/CpGenuineQuotient.lean:45` | `0<Re s<1` |
| `operatorHeightParameter` | `CompletedOperatorCharacteristic.lean:28` | `s=1/2+iz` |
| `isOpen_completedNativeHeightDomain` | `GlobalKernelProbe.lean:354` | domínio aberto |
| `completedNativeOperatorCharacteristic_analyticAt` | `GlobalKernelProbe.lean:363` | analiticidade complexa em cada ponto do domínio |
| `ofReal_mem_completedNativeHeightDomain` | `CompletedNativeRealWeylMoments.lean:77` | todo `t∈ℝ` pertence ao domínio |
| `completedNativeOperatorCharacteristic_zero_ne_zero` | `CompletedGreenMomentJets.lean:152` | `F(0)≠0`, sem premissa numérica |
| `completedNativeOperatorCharacteristic_not_eventually_zero` | `CompletedNativeLogDerivativePoles.lean:31` | nenhum germen no domínio é identicamente zero |
| `completedNativeOperatorCharacteristic_analyticOrderAt_ne_top` | mesmo arquivo:43 | ordem analítica finita |
| `completedNativeOperatorCharacteristic_analyticOrderNatAt_ne_zero` | mesmo arquivo:52 | ordem natural positiva em cada zero |
| `completedNativeOperatorLogDerivative_meromorphicOrderAt_eq_neg_one` | mesmo arquivo:69 | `−F'/F` tem polo simples em cada zero |

Pelas definições, o domínio de altura é exatamente `−1/2<Im z<1/2`, portanto um strip horizontal aberto e convexo que inclui todos os polos reais `±log p/α`. Não é necessário promover a formalização para uma função inteira em todo `ℂ`: a analiticidade já demonstrada nesse strip basta à aplicação em papel.

### 3.1 Encaixe com a extração atômica já existente

`CompletedNativeJacobiWeylContinuation.lean:28` define, fora do centro,

$$
q_{\rm height}(z)=-\frac{F'(z)}{2zF(z)}.
$$

`CompletedNativeJacobiCyclicAtomicExtraction.lean:418` define

$$
\mathrm{positiveJacobiAtomicCyclicResidue}(z_0)
=\frac2{z_0}\,
\mathrm{meromorphicTrailingCoeffAt}(q_{\rm height},z_0),
$$

e o mesmo arquivo, perto da linha 867, define a massa cíclica como o negativo da parte real desse resíduo. A fatoração local `F=(z−z₀)^N g` daria

$$
\mathrm{TrailingCoeff}(q_{\rm height},z_0)=-\frac N{2z_0},\qquad
\mathrm{CyclicResidue}(z_0)=-\frac N{z_0^2},\qquad
\boxed{\mathrm{CyclicMass}(z_0)=N\lambda_0,\quad\lambda_0=z_0^{-2}.}
$$

A infraestrutura do resíduo, a existência/positividade da massa sob o certificado e a ordem finita já estão no repositório. Não localizei a igualdade explícita final com `analyticOrderNatAt`; ela pode ser obtida da fatoração local analítica e é um alvo pequeno independente para formalização posterior. Não foi formalizada neste suplemento.

## 4. Correção geométrica proposta: Gram de rank um por fibra

A condição de multiplicidade permite construir outra candidata a partir dos mesmos vetores carry, **sem usar `h_n` nativos**. Esta é uma proposta da investigação atual, não uma identificação recuperada das notas nem uma construção já formalizada da completion inteira.

Em cada fibra `H_p=ℓ²{k≥1}`, tome

$$
v_p(k)=\frac{p^{-k/2}}{\log p},\qquad
V_p=|v_p\rangle\langle v_p|,\qquad
\lambda_p=\|v_p\|^2=\frac1{(p-1)(\log p)^2}.
$$

No somatório ortogonal `H=⊕_pH_p`, defina

$$
\boxed{V=\bigoplus_pV_p,\quad S=\sqrt V,\quad u=\bigoplus_pv_p.}
$$

Cada `V_p` é um Gram positivo de rank um, construído diretamente da amplitude carry e do inverso do relógio. Sua única direção espectral positiva é `e_p=v_p/√λ_p`, com autovalor `λ_p`. As outras direções da fibra têm autovalor zero. Como `Σ_pλ_p<∞`, o operador `V` é positivo e de classe traço, e `u∈H`.

Agora o átomo de `u` tem massa **igual** ao autovalor: `m_p=λ_p`. Por isso

$$
\boxed{m_n=\langle u,S^{2n}u\rangle
=\sum_p\lambda_p^{n+1}=\operatorname{Tr}(V^{n+1}),\qquad
\frac{m_p}{\lambda_p}=1.}
$$

O determinante Fredholm desta candidata está bem definido:

$$
F_{\rm fibra}(t)=\det(I-t^2V)=\prod_p(1-t^2\lambda_p).
$$

Ele é inteiro e par, com zeros simples `±√(p−1) log p`, e

$$
-\frac{F_{\rm fibra}'(t)}{2F_{\rm fibra}(t)}
=t\sum_p\frac{\lambda_p}{1-t^2\lambda_p}.
$$

A construção satisfaz a condição atômica exatamente. Também fornece o par de resolventes e o kernel positivo polarizado da investigação principal. Na soma das direções `e_p`, os autovalores positivos distintos têm suporte infinito; a mesma prova polinomial coordenada demonstra independência de todas as potências, pares e ímpares, e positividade estrita dos dois Hankels em toda ordem.

`V` e `S` têm kernel no ambiente completo, constituído pelas direções ortogonais a `v_p` em cada fibra. O subespaço observado canônico `H_c=⊕_p span(v_p)` é invariante e contém `u`; restringir a ele remove somente autovalores zero. Isso preserva o readout e o determinante. A restrição de `S` é injetiva, embora o operador no ambiente completo não seja.

### 4.1 Auditoria dos momentos e da forma

Arquivo reproduzível: `/tmp/carry_rank_one_fiber_pair_audit.py`; resultados: `/tmp/carry_rank_one_fiber_pair_audit.json`, ambos no notebook e no servidor. Execução com um worker, 3,5 segundos. Não foram usados momentos nativos para definir o operador ou seus autovalores.

A cauda de `m_0` é a mesma da fonte carry do relatório principal. Para `k≥2`,

$$
\sum_{p>P}\lambda_p^k
\le\left(\frac P{P-1}\right)^k
\frac1{(k-1)P^{k-1}(\log P)^{2k}}.
$$

O cálculo até `p≤10^7` deu

| Momento | Prefixo | Cota analítica da cauda |
|---|---:|---:|
| `m_0` | 2,7275181055575612 | 0,0620420750475292 |
| `m_1` | 4,515593005717825 | 1,4816484534 × 10⁻¹² |
| `m_2` | 9,088780183878622 | 2,8515944603 × 10⁻²² |
| `m_3` | 18,796606285872777 | 7,3176071309 × 10⁻³² |

Com a cauda analítica e margem computacional `10⁻¹⁰`,

$$
R_2\in[1.2157482657,1.2434025444],\qquad
R_3\in[1.5186942687,1.5885706706].
$$

Os valores nativos, pela quadratura theta e recorrência em 50/80 dígitos, são `R₂≈2.410719741809124` e `R₃≈6.890919499842071`. A nova candidata corrige o problema de multiplicidades, mas a comparação dos invariantes ainda separa seu readout do nativo, mesmo permitindo mudanças globais de massa e escala. A comparação com os valores nativos continua sendo uma auditoria numérica, não uma prova Lean da desigualdade das razões.

## 5. Segunda candidata: Gram diagonal dos números materiais

Outra proposta positiva sem momentos-alvo é

$$
\lambda_n=\frac1{n(\log n)^2},\quad n\ge2,
\qquad
V=\operatorname{diag}(\lambda_n),\quad
S=\operatorname{diag}(\sqrt{\lambda_n}),\quad
u_n=\sqrt{\lambda_n}.
$$

Aqui também `m_atom/λ=1`, `V` é positivo de classe traço, a fonte é de ℓ² e os dois Hankels são estritamente positivos em toda ordem. A característica própria é

$$
F_{\rm materiais}(t)=\prod_{n\ge2}(1-t^2\lambda_n),
$$

inteira, com zeros simples `±√n log n`. Essa proposta altera o operador do modelo de relógio puro: a massa geométrica passa a integrar também os autovalores.

O momento inicial foi reutilizado do cálculo independente do agente de retorno:

$$
m_0=\sum_{n\ge2}\frac1{n(\log n)^2}
\simeq2.1097428012368919744792571976165513263855319843947420.
$$

Fonte local `/tmp/carry-geometric-graph-data/geometric_diagonal_candidates.json`, `candidates[0].moments[0]`; código `graph_moment_candidates.py`, funções `log_tail/log_moments`. Método: Euler–Maclaurin com soma `2,…,511`, integral `1/log 512`, termo `f(512)/2` e correções até `B_126`, precisão 160 dígitos. O limite analítico do resto é `2,73×10⁻²³⁶`; ele controla o truncamento, não arredondamento intervalar. Um cálculo independente com `N=256`, 48 correções e 120 dígitos concordou a cerca de 122 dígitos relativos.

Para `m_1,m_2,m_3`, a soma direta até `n=10^7` fornece:

$$
(m_1,m_2,m_3)\simeq
(1.1892821929110893,\ 1.1510624818766646,\ 1.1790916897303656).
$$

A cauda de ordem `k=n+1≥2` é no máximo

$$
\sum_{r>P}\frac1{r^k(\log r)^{2k}}
\le\frac1{(k-1)P^{k-1}(\log P)^{2k}}.
$$

Em `P=10^7`, a maior cauda entre esses três momentos é inferior a `1,49×10⁻¹²`. As razões são

$$
R_2\simeq1.716953683417900,\qquad
R_3\simeq3.119980337582349,\qquad
R_{\rm adj}\simeq1.058363119015619.
$$

Elas também permanecem afastadas das razões nativas. A massa e a escala globais não modificam essas razões. Os dois novos Grams demonstram que é possível construir geometricamente operadores positivos de classe traço e corrigir a integridade das multiplicidades; a identificação do operador certo com a completion continua exigindo as relações adicionais de retorno/cumulantes, e não foi obtida por essas duas propostas diagonais.
