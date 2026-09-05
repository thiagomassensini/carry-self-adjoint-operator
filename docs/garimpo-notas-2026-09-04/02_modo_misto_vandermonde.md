# Garimpo: modo misto 3–4–6, tau, Vandermonde e mudança de observável

Data da inspeção: 2026-09-04. Escopo: notas locais em `/home/thlinux/Downloads`, comparação com os fontes já copiados em `/tmp/carry-garimpo-local/self-adjoint`. Nenhuma nota ou arquivo Lean foi modificado. As deduções novas abaixo são argumentos matemáticos escritos e cálculos inteiros reproduzidos nesta sessão; não são teoremas Lean já verificados.

## Resultado útil para a costura

O modo misto fornece **mais do que um exemplo de momentos fatoriais**. A própria nota parte de uma medida positiva em uma variável compacta, depois muda para a coordenada logarítmica Laguerre. Podemos voltar ao observável compacto, obter momentos de crescimento exponencial e construir explicitamente um kernel positivo com exatamente a arquitetura par/ímpar exigida pela costura atual.

A etapa ainda não encontrada nas notas deste cluster é identificar **o readout desse observável, com os estados e bordos transportados**, com `canonicalCompletedNativeLogDerivativeMoment`, ou com a log-derivada da característica nativa. Portanto, a antiga comparação fatorial/exponencial só impede identificar diretamente os momentos na variável logarítmica; ela não elimina a rota com mudança de observável.

## 1. Fonte positiva: três variáveis que devem permanecer identificadas

Fontes principais:

- [Ponte C2 pushforward → tau-sigma do modo misto.md](</home/thlinux/Downloads/Ponte C2 pushforward → tau-sigma do modo misto.md>), linhas 29–59: coordenada `xi=log(6/x)`, peso e transformada de Laplace exata.
- [MODO_MISTO_3_4_6_COUPLED_PV_SISTEMA_DISCRETO.md](</home/thlinux/Downloads/MODO_MISTO_3_4_6_COUPLED_PV_SISTEMA_DISCRETO.md>), linhas 8–55: peso, níveis positivos 33,25,16, massa139/6; linhas177–207: mudança de Jacobi entre xi e y.
- [REALIZACAO_JACOBI_COMPLETA_MODO_MISTO_3_4_6.md](</home/thlinux/Downloads/REALIZACAO_JACOBI_COMPLETA_MODO_MISTO_3_4_6.md>), linhas12–45: medida original em x; linhas49–81: coordenada logarítmica; linhas110–132: momentos em y; linhas349–392: congruência C2/Haar e whitening.

As coordenadas são

$$
x\in(0,6],\qquad \xi=\log(6/x)\ge0,\qquad y=1+\log x=1+\log6-\xi.
$$

A medida original é

$$
d\nu_*(x)=\frac1{139}
\begin{cases}
16\,dx,&0<x\le3,\\
25\,dx,&3<x\le4,\\
33\,dx,&4<x\le6.
\end{cases}
$$

Ela tem massa1: `(16*3 + 25*1 + 33*2)/139=1`. A decomposição assinada `(198 nu_6 -32 nu_4 -27 nu_3)/139` é a mesma medida, porque `nu_b` tem densidade1/b em `(0,b]`. Os coeficientes negativos dessa decomposição não tornam negativa a medida resultante.

Após `x=6 exp(-xi)`, ela se torna

$$
d\nu_*(\xi)=\frac6{139}e^{-\xi}
\left(33-8\mathbf1_{\xi\ge\log(3/2)}-9\mathbf1_{\xi\ge\log2}\right)d\xi.
$$

O parâmetro eta da nota sigma/tau move os dois saltos:

$$
w_\eta(\xi)=e^{-\xi}\left(33-8\mathbf1_{\xi\ge\eta\log(3/2)}-9\mathbf1_{\xi\ge\eta\log2}\right),\quad \eta\ge0.
$$

Então `16 exp(-xi) ≤ w_eta(xi) ≤ 33 exp(-xi)`. O peso é positivo em todo intervalo aberto da semirreta. Para qualquer polinômio não nulo, as integrais de `p(xi)^2 w_eta` e de `xi p(xi)^2 w_eta` são estritamente positivas. Essa é uma prova escrita de positividade Hankel ordinária e deslocada em toda ordem para **os momentos em xi**. A fórmula determinantal é

$$
\det(\mu_{i+j})_{i,j<n}=\frac1{n!}\int\Delta(\xi_1,\ldots,\xi_n)^2\prod_{j=1}^n w_\eta(\xi_j)\,d\xi_j>0,
$$

com um fator adicional `prod xi_j` para a matriz deslocada. A justificativa é a identidade de Andréief/Cauchy–Binet integral, integrabilidade de todos os momentos e positividade fora das diagonais. Não se necessita cota coerciva uniforme em n.

Os momentos em xi satisfazem `16 k! ≤ mu_k ≤ 33 k!`. Os momentos em y têm outra assinatura de suporte: y se estende até menos infinito. A Jacobi explicitada no arquivo REALIZACAO usa **y**, não o observável compacto x. Por exemplo, sua diagonal é `log6-2n` no modo puro, coerente com a reflexão da Jacobi Laguerre.

## 2. Transporte compacto já sugerido pela própria mudança de variável

**Dedução desta investigação, a partir da medida declarada:** use

$$
v=e^{-\xi}=x/6\in(0,1].
$$

Na realização de multiplicação por `Y=1+log x`, esse observável é `V=exp(Y-(1+log6)I)`. É positivo e limitado por1 na medida do modo misto. Não é uma amplitude adicionada à teoria; é uma função explicitamente definida da coordenada já presente na nota.

O pushforward tem densidade

$$
d\rho_*(v)=\frac6{139}\left(33-8\mathbf1_{v\le2/3}-9\mathbf1_{v\le1/2}\right)dv,\qquad 0<v\le1.
$$

Consequentemente,

$$
m_k=\int v^k\,d\rho_*(v)
=\mathcal J_*(k)
=\frac6{139(k+1)}\left[33-8(2/3)^{k+1}-9(1/2)^{k+1}\right].
$$

Aqui `J_*(s)` é exatamente a transformada de Laplace de `Ponte C2...`, linhas47–59; os momentos compactos são **valores da transformada nos inteiros**, não derivadas dela na origem. Em particular,

$$
m_0=1,\qquad m_1=\frac{979}{1668},\qquad m_2=\frac{6373}{15012},\qquad 0<m_k\le1.
$$

Os dois Hankels de `m_k` são estritamente positivos em toda ordem pelo mesmo argumento polinomial. Para eta geral, os limiares passam a `exp(-eta log(3/2))` e `exp(-eta log2)`, e a constante de normalização é `Z_eta=33-8 exp(-eta log(3/2))-9 exp(-eta log2)`. A densidade fica entre16/Z_eta e33/Z_eta.

Isso resolve o problema de crescimento para esse **modelo transformado**. Ainda é necessária a identificação com os momentos nativos concretos.

## 3. Kernel par/ímpar explícito no formato da obrigação atual

**Dedução nova, conferida algebricamente nesta sessão; não localizada como teorema Lean do modo misto:** para qualquer medida positiva finita `rho` em `[0,1]`, defina, para `|t|<1`,

$$
Q_\rho(u)=\int\frac{d\rho(v)}{1-uv},\qquad
 a_\rho(t)=tQ_\rho(t^2),
$$

$$
\Psi_\rho(t)(v)=\left(\frac1{1-t^2v},\frac{t\sqrt v}{1-t^2v}\right)
\in L^2(\rho)\oplus L^2(\rho).
$$

A identidade escalar

$$
\frac{\frac z{1-z^2v}-\frac x{1-x^2v}}{z-x}
=\frac{1+xzv}{(1-x^2v)(1-z^2v)}
$$

dá

$$
\langle\Psi_\rho(x),\Psi_\rho(z)\rangle
=\frac{a_\rho(z)-a_\rho(x)}{z-x}.
$$

Na diagonal, ambos os lados são `a_rho'(x)=integral (1+x²v)/(1-x²v)²`. O limite e a derivação são dominados em cada intervalo compacto de `(-1,1)`.

Os coeficientes Taylor normalizados são

$$
\phi_{2i}=(v^i,0),\qquad \phi_{2i+1}=(0,\sqrt v\,v^i).
$$

Logo os Grams pares são `m_(i+j)`, os ímpares são `m_(i+j+1)`, e os cruzamentos de paridade são zero. Para a densidade do modo misto, ambas as famílias são linearmente independentes em toda ordem, porque um polinômio que zera quase em toda parte de um intervalo é o polinômio zero.

Para `rho_*`, o readout fica completamente explícito:

$$
Q_*(u)=\frac6{139u}\left[-33\log(1-u)+8\log(1-2u/3)+9\log(1-u/2)\right],\quad Q_*(0)=1.
$$

Portanto existe um alvo algébrico concreto para comparar com a característica. Escrevendo `F(t)=F(0) Phi_native(t²)`, o que falta nesta rota é

$$
Q_*(u)=-\frac{\Phi_{\rm native}'(u)}{\Phi_{\rm native}(u)},
$$

ou a versão com o observável/medida corretamente transportados que as notas futuras indiquem. Equivalentemente, localmente e com a mesma normalização,

$$
F(t)=F(0)\exp\left(\int \frac{\log(1-t^2v)}v\,d\rho(v)\right),
$$

usando o prolongamento contínuo `log(1-t²v)/v=-t²` em v=0. Essa igualdade **não foi demonstrada nem encontrada** neste cluster. Não se deve definir `rho` a partir da positividade já presumida de h para depois usá-la como prova dessa mesma positividade.

## 4. A fonte dos modos e a fonte da log-derivada: o que foi realmente localizado

[NATIVE_CARRY_PRIMITIVE_TO_SPECTRAL_BRIDGE_AUDIT.md](</home/thlinux/Downloads/NATIVE_CARRY_PRIMITIVE_TO_SPECTRAL_BRIDGE_AUDIT.md>), linhas118–200, constrói numericamente o projetor misto a partir da variância da geometria primitiva branqueada. As massas finitas são

$$
q_{n,M}=\frac1M\left|p_{*,M}^T(G_M^{\rm geo})^{-1/2}c_M(n)\right|^2,
$$

e são comparadas à medida de densidades16/139,25/139,33/139. Isso é uma origem source-side concreta para tentar formalizar o transporte; a evidência apresentada nessa seção é uma auditoria numérica de cutoff, não uma identificação Lean do kernel nativo.

[TRANSFORMADA_CAUCHY_STIELTJES_POVM_E_WEYL_CAMERAS.md](</home/thlinux/Downloads/TRANSFORMADA_CAUCHY_STIELTJES_POVM_E_WEYL_CAMERAS.md>), §§1–4 e7–8, apresenta um mecanismo mais forte do que comparação de momentos: POVM em x, observável `y=1+logx`, resolvente comprimido e limite de probes com o mesmo `G_E`. O observável compacto acima pode ser colocado **nessa mesma realização de multiplicação**, preservando sua origem. A identificação adicional com o parâmetro de altura deve ser um enunciado específico.

[C2_DISCRETE_JACOBIAN_HEIGHT_JACOBI_BRIDGE.md](</home/thlinux/Downloads/C2_DISCRETE_JACOBIAN_HEIGHT_JACOBI_BRIDGE.md>), linhas142–208, contém uma ligação exata diferente:

$$
\frac{\xi'(w)}{\xi(w)}=A_\infty(w)-L_{\rm odd}(w)-\ell_2(w),
$$

$$
L_{\rm odd}=-Z_{\rm odd}'/Z_{\rm odd},\quad
\ell_2(w)=\frac{\log2\,2^{-w}}{1-2^{-w}},
$$

$$
A_\infty(w)=1/w+1/(w-1)-\tfrac12\log\pi+\tfrac12\psi(w/2).
$$

A fórmula foi conferida por derivação logarítmica: `Z_odd=(1-2^-w) zeta(w)` e a completação declarada dão exatamente esses sinais. O bordo arquimediano e o fator local2 são explícitos, e podem alimentar a busca da métrica completa. As linhas212–248 enumeram as operações intermediárias; não há ali uma prova de que essa operação não linear transporte o Gram da medida C2 ou3–4–6 até h. Isso é uma igualdade de **readout escalar**, não a igualdade de produtos internos necessária.

A definição atual em Lean é `completedNativeOperatorCharacteristic = nativeXiCompletionFactor * nativeScalar(operatorHeightParameter z)` em `CompletedOperatorCharacteristic.lean:29–41`. A recorrência nativa e a unicidade dos momentos estão em `CompletedNativeRealWeylMoments.lean:208–266`. Assim, uma rota a verificar é demonstrar que os momentos do observável geométrico correto satisfazem **essa recorrência concreta**; a unicidade existente identificaria a sequência sem reconstruir o operador outra vez.

## 5. Vandermonde: ferramentas aproveitáveis e domínio correto

[Dressing de Vandermonde por resultantes e operadores de criação vestidos.md](</home/thlinux/Downloads/Dressing de Vandermonde por resultantes e operadores de criação vestidos.md>), linhas25–60, contém a fatoração elementar

$$
\Delta(A,B,Z)^2=\Delta(A)^2\Delta(B)^2\Delta(Z)^2
\operatorname{Res}(P_a,P_b)^2\operatorname{Res}(P_a,P_0)^2\operatorname{Res}(P_b,P_0)^2.
$$

Ela acompanha os cruzamentos entre cores de maneira exata. As linhas93–154 dão o fator de criação `omega_i exp(-rho_i) P_X(rho_i)^2` e a integral da tau. A comutatividade dos dressings escalares é suficiente para a troca de ordem registrada; não se deve ler essa igualdade como uma estrutura não abeliana extra já provada.

[Álgebra criação–aniquilação vestida pela métrica de Vandermonde.md](</home/thlinux/Downloads/Álgebra criação–aniquilação vestida pela métrica de Vandermonde.md>), linhas23–49 e81–152, distingue corretamente aniquilador inverso do dressing e adjunto: o primeiro remove a partícula com1/P, o segundo com P. O twist métrico por `Delta²` é uma peça útil para transportar energia. Precisa de configurações distintas para usar `Delta^-1`; a análise de domínios em uma realização Hilbert infinita não aparece concluída nesse texto. A marca “CLOSED” ali é uma marca de derivação da nota, não nome de teorema Lean.

## 6. Correção exata do rank do defeito de criação

Fonte das definições: [Álgebra de operadores de criação da tau holonômica 3–4–6.md](</home/thlinux/Downloads/Álgebra de operadores de criação da tau holonômica 3–4–6.md>), linhas11–58,151–190.

O setor `a=(p,q,r)` tem base `|a;k>` para `0≤k≤d(a)=2(pq+pr+qr)`. O criador `C_i` incrementa a coordenada i e preserva k. A base é declarada ortonormal. Para i diferente de j,

$$
D_{ij}^{(n)}=C_i^{(n)*}C_j^{(n)}-C_j^{(n-1)}C_i^{(n-1)*}.
$$

Ponha `a=t+e_i`, com `|t|=n-1`. O defeito leva `|a;k>` para `|t+e_j;k>` exatamente nos graus

$$
d(t)<k\le\min(d(t+e_i),d(t+e_j)).
$$

Logo sua contribuição é `2(n-1-max(t_i,t_j))`, e imagens de bases diferentes são diferentes. Portanto

$$
\boxed{\operatorname{rank}D_{ij}^{(n)}=
2\binom{n+1}{3}+2\sum_{k=1}^{\lfloor(n-1)/2\rfloor}\binom{n+1-2k}{2}.}
$$

Cálculo exato, sem arredondamento:

| n | Dimensão do nível | Rank pelas definições | Fórmula antiga2(n−1)n(n+1)/3 |
|---:|---:|---:|---:|
|1|3|0|0|
|2|12|2|4|
|3|40|10|16|
|4|105|26|40|
|5|231|54|80|
|6|448|96|140|
|7|792|156|224|
|8|1305|236|336|

A diferença é uma matriz de permutação parcial com entradas1, permitindo contar o rank exatamente. A fórmula antiga é repetida em `Álgebra criação–aniquilação vestida...:202–205`; não deve ser importada para Lean tal como está. Isso corrige a identificação com o “bulk thickening”; não invalida a positividade da medida, a fatoração Vandermonde nem os criadores definidos.

## 7. Fórmulas e arquivos que precisam de cuidado antes de qualquer formalização

- `Derivação sigma-tau — modo misto 3–4–6.md:43–52` tem chaves/exponentes quebrados. Pela integral das linhas33–36, a fórmula correta é `(33-8 exp(-(s+1)t1)-9 exp(-(s+1)t2))/(s+1)` para `Re(s)>-1`. É uma correção sintática recuperável pela definição; não uma nova hipótese.
- A mesma nota tem outras chaves ausentes na sigma e Toda. `REALIZACAO_JACOBI_COMPLETA_MODO_MISTO_3_4_6.md` contém caracteres de controle oriundos de escapes, incluindo `\\b`, `\\r`, `\\a` interpretados antes de salvar. As fórmulas devem ser confrontadas com o peso ou com os arquivos próximos, sem confundir falha do texto com falha matemática. Nenhum desses arquivos foi alterado.
- As quatro variantes diretas `MODO_MISTO...md`, `(1)`, `(2)`, `(3)` são byte-idênticas; não constituem quatro evidências ou estágios cronológicos diferentes.
- O laboratório antigo de alturas `Wayl/native_carry_height_moment_jacobi_operator_audit.json` contém h0,h1,h2 de uma construção por valores de F. O invariante de escala `h0*h2/h1²` registrado é aproximadamente2.41071974; para os momentos compactos crus acima, o valor exato é3543388/2875323≈1.23234433. Isso é apenas um diagnóstico para evitar tentar ajustar somente massa e escala; o dado de altura é um registro numérico antigo e não uma refutação Lean de todos os possíveis observáveis, bordos ou transportes. A rota deve buscar a identificação adicional, não declarar que o modelo cru já é o nativo.

## 8. Próximas peças exatas a procurar/formalizar

1. **Source → medida3–4–6 no mesmo limite:** recuperar uma demonstração escrita, além da auditoria de cutoff, de que o projetor misto e o POVM convergem com os produtos cruzados preservados.
2. **Transporte do observável:** explicitar no mesmo carrier a função do gerador geométrico que produz a variável de momentos nativa. A escolha v=exp(-xi) demonstra que existe uma alternativa compacta, mas a fonte tem de determinar o observável correto.
3. **Readout/bordo completo:** localizar a identidade que transporte a igualdade escalar `A_inf-L_odd-ell2` para o Gram dos estados normalizados. É o lugar concreto para comparar os termos da completação com a métrica de retorno.
4. **Identidade de momentos ou recorrência:** provar, para a realização encontrada, `IsCompletedNativeLogDerivativeMomentSequence`; aplicar a unicidade já formalizada. Alternativamente, provar diretamente o kernel `a=-F'/2F`.
5. **Independência:** a construção polinomial com uma medida de suporte infinito dá os dois setores e todos os N; na rota C3 concreta, aproveitar os construtores de certificado e os readouts já existentes em vez de recriar a infraestrutura.

## Precisões da revisão independente

A curva $\Psi_\rho$ é uma nova realização por cálculo funcional, ainda não identificada como transporte da curva C3/TFVD existente. A identidade local $Q_\rho=Q_{\rm nat}$ pode fornecer diretamente os Grams e um certificado HP nessa realização; não prova automaticamente a costura do estado C3 já fixado. A interface vetorial `HasCompletedNativeRealAxisNormalizedGreenKernel` quantifica todos os reais regulares, enquanto o kernel acima foi construído inicialmente em $|t|<1$.

Para testar a igualdade literal da medida crua, sua massa 1 exige $h_0=1$, isto é, $a_1=-a_0$ para os coeficientes pares da característica. O próximo passo é comparar a recorrência e os coeficientes da realização geometricamente determinada; não presumir que a medida crua seja a candidata correta. Derivadas de ordem $n$ da curva têm fator $n!$; os vetores utilizados no Gram são coeficientes Taylor normalizados.

## Manifesto das fontes locais

Os hashes abaixo identificam os bytes inspecionados; não se infere a ordem histórica a partir do número da cópia ou do mtime.

| Arquivo em Downloads | Linhas físicas | SHA256 |
|---|---:|---|
| [Ponte C2 pushforward → tau-sigma do modo misto.md](</home/thlinux/Downloads/Ponte C2 pushforward → tau-sigma do modo misto.md>) | 119 | `370f0ba785460afa1d2defb8694f4059083da994ce0c46bd6d255cb36b513be7` |
| [Derivação sigma-tau — modo misto 3–4–6.md](</home/thlinux/Downloads/Derivação sigma-tau — modo misto 3–4–6.md>) | 222 | `4225ce3428c3e38da20c10749dbebb8b4e1e93cd1e2d4d0e530fd2ca1bbc20b1` |
| [REALIZACAO_JACOBI_COMPLETA_MODO_MISTO_3_4_6.md](</home/thlinux/Downloads/REALIZACAO_JACOBI_COMPLETA_MODO_MISTO_3_4_6.md>) | 415 | `40cfab6fcd1e45311f6c696d9ecb89dbb4d28b4d32925b76dcdc8a00edbb6c33` |
| [MODO_MISTO_3_4_6_COUPLED_PV_SISTEMA_DISCRETO.md](</home/thlinux/Downloads/MODO_MISTO_3_4_6_COUPLED_PV_SISTEMA_DISCRETO.md>) | 458 | `dbf70d7e4727dd7e3c5c4ad6e9cb90b885533faf16efd3cea1ef5aabf498594f` |
| [Álgebra de operadores de criação da tau holonômica 3–4–6.md](</home/thlinux/Downloads/Álgebra de operadores de criação da tau holonômica 3–4–6.md>) | 223 | `5bb309e4c6a667c673769432f0672142146d4614a4c264bc01a028376a1b91af` |
| [Álgebra criação–aniquilação vestida pela métrica de Vandermonde.md](</home/thlinux/Downloads/Álgebra criação–aniquilação vestida pela métrica de Vandermonde.md>) | 228 | `8376a43233a34063654df39714687192e7846ba33a24c7456d3926cd9a3c9778` |
| [Dressing de Vandermonde por resultantes e operadores de criação vestidos.md](</home/thlinux/Downloads/Dressing de Vandermonde por resultantes e operadores de criação vestidos.md>) | 192 | `809c52e787a4e382d99bfe354e7d668dcfbed5bd0199c401847d2e429e3a9188` |
| [C2_DISCRETE_JACOBIAN_HEIGHT_JACOBI_BRIDGE.md](</home/thlinux/Downloads/C2_DISCRETE_JACOBIAN_HEIGHT_JACOBI_BRIDGE.md>) | 302 | `a8f54b6b0ac8798aa1b4538bd68365911e456d5ee39238b825ba093a5dc6affb` |
| [TRANSFORMADA_CAUCHY_STIELTJES_POVM_E_WEYL_CAMERAS.md](</home/thlinux/Downloads/TRANSFORMADA_CAUCHY_STIELTJES_POVM_E_WEYL_CAMERAS.md>) | 746 | `68150d022a98d21502dbb5fea4a4ac4e1851523858e14aba3b322d375aa06545` |
| [NATIVE_CARRY_PRIMITIVE_TO_SPECTRAL_BRIDGE_AUDIT.md](</home/thlinux/Downloads/NATIVE_CARRY_PRIMITIVE_TO_SPECTRAL_BRIDGE_AUDIT.md>) | 305 | `c051b786def972e737dd36d898665d17659cfc208cee5f2e527fdd609be117bc` |
| [Wayl/native_carry_height_moment_jacobi_operator_audit.json](</home/thlinux/Downloads/Wayl/native_carry_height_moment_jacobi_operator_audit.json>) | 591 | `9d737a1fd11a4d8dd89cfb11e3f73727f668ad351e75626a90cfced06a34dc03` |

[Voltar ao mapa principal](../mapa-notas-costura-energia-momentos-carry.md).
