# Ataque à positividade: oitava fonte e limite das caixas theta

## Resultado

O sinal nativo em todas as ordens **não foi demonstrado**. Esta investigação
produziu dois resultados formais que tornam o próximo passo verificável:

1. A forma original de oito fontes foi decomposta exatamente, mantendo todos
   os cruzamentos. Sua positividade estrita equivale a um escalar novo, e este
   equivale a uma cota explícita para o coeficiente `c₈` da característica original.
2. As caixas theta atualmente certificadas são insuficientes para concluir o
   próximo teste por uma implicação algébrica válida em todo o retângulo.
   Há um contramodelo racional dentro delas que também tem os Grams theta
   brutos relevantes positivos, mas uma direção logarítmica negativa.

O segundo resultado é uma limitação do método de cotas. **Não é um
contraexemplo à positividade da fonte nativa.** O contramodelo não é identificado
com a fonte nem com a sequência completa de momentos de algum kernel theta.

## A forma nativa completa de oito fontes

Escreva `aⱼ = nativeSourceOddBoundaryCoefficient j`, os coeficientes reais
normalizados da derivada logarítmica original. Não são escolhidos para ajustar
um Gram. A decomposição é

\[
E_8(x)=2\{Q_{\mathrm{par},4}(x_0,x_2,x_4,x_6)
                 +Q_{\mathrm{ímpar},4}(x_1,x_3,x_5,x_7)\}.
\]

O primeiro bloco já tem sinal estrito certificado. O segundo é

\[
\begin{aligned}
Q_{\mathrm{ímpar},4}(u,v,w,t)
={}&Q_{\mathrm{ímpar},3}(u,v,w)
-2a_4\operatorname{Re}(\bar u t)
+2a_5\operatorname{Re}(\bar v t)\\
&-2a_6\operatorname{Re}(\bar w t)+a_7|t|^2.
\end{aligned}
\]

Com o divisor antigo `δ = nativeSourceSixOddDiscriminant > 0` e os três
acoplamentos `C₀,C₁,C₂` definidos dos mesmos coeficientes, a identidade exata é

\[
Q_{\mathrm{ímpar},4}(u,v,w,t)=
Q_{\mathrm{ímpar},3}(u+C_0t/\delta,v+C_1t/\delta,w+C_2t/\delta)
+\frac{\Delta_8}{\delta}|t|^2,
\]

onde

\[
\Delta_8=\delta a_7+a_4C_0-a_5C_1+a_6C_2.
\]

Isto fornece, em Lean,

\[
\forall x\ne0,\ E_8(x)>0\quad\Longleftrightarrow\quad\Delta_8>0.
\]

A direção crítica explícita é `(-C₀/δ,-C₁/δ,-C₂/δ,1)` no bloco ímpar. Sua
energia nesse bloco é exatamente `Δ₈/δ`; não houve descarte de cruzamentos
ou introdução de outra métrica.

## Uma cota analítica concreta

Escreva `cⱼ = completedNativeRealEvenCharacteristicCoefficient j`. A nova
recorrência, válida em todas as ordens e derivada da resposta da própria fonte,
é

\[
c_0a_n+\sum_{k<n}a_kc_{n-k}=-2(n+1)c_{n+1}.
\]

Ela não usa positividade nem o operador de alturas. Defina

\[
R_7=\sum_{k<7}a_kc_{7-k},\qquad
B_8=a_4C_0-a_5C_1+a_6C_2.
\]

O Lean verifica a identidade e a equivalência

\[
c_0\Delta_8=c_0B_8-\delta R_7-16\delta c_8,
\qquad
\boxed{\Delta_8>0\iff
c_8<\frac{c_0B_8-\delta R_7}{16\delta}.}
\]

O lado direito usa somente dados anteriores ao coeficiente novo. Os divisores
`c₀` e `δ` têm sinais positivos já demonstrados. Provar essa cota para a fonte
original fecharia oito fontes; a implicação para contratibilidade eventual do
retorno também foi formalizada, com a hipótese explícita.

Não foi acrescentada uma prova de `Δ₈>0`, nem uma indução de sinal em `N`.

## O que a aritmética exata exclui

`CompletedNativeThetaBoxEighthObstruction.lean` fixa um ponto racional nas
oito caixas existentes para os momentos theta de ordens `0,2,…,14`, com uma
nona coordenada positiva. O Lean verifica:

- A fonte nativa satisfaz essas mesmas oito caixas.
- O ponto racional pertence a todas elas.
- Seus coeficientes são calculados pela fórmula theta–característica, através
  de `c₈`, e a recorrência sem divisão vale em cada ordem `n<8`.
- O divisor central e o prefixo dos nove momentos de cosseno têm sinal positivo.
- O Gram theta bruto `5×5`, de entradas `A_(i+j)`, e o deslocado `4×4`, de
  entradas `A_(i+j+1)`, são positivos definidos, certificados por fatorações
  racionais exatas e diagonais estritamente positivas.
- Há um vetor racional fixo cujo valor no bloco logarítmico ímpar `4×4` é
  estritamente negativo, aproximadamente `−2,22838×10⁻²²`.

O teorema `thetaFourteenthBox_and_raw_positivity_insufficient` refuta a
implicação universal que tentaria obter o sinal logarítmico apenas dessas
condições. As tabelas racionais e suas relações são verificadas pelo kernel;
nenhum resultado de ponto flutuante entra nessa prova.

Isso exige, para esse caminho de ataque, cotas nativas mais fortes ou relações
adicionais da integral theta específica. Positividade de matrizes brutas nessa
ordem não preenche a obrigação. A obstrução não exclui uma prova com outras
informações preservadas da fonte.

## Exploração numérica da fonte original — separada da prova

O script `scripts/probe_native_boundary_eighth_pivot.py` lê o cache preservado
de integrais theta a 1.600 dígitos e usa a recorrência original. O replay foi
feito a 100 e 180 dígitos; não foi executada nova quadratura nem usada uma
tabela de zeros, ajuste de momentos ou extração de alturas.

Para o bloco normalizado de momentos `h=a/2`, o novo pivô numérico é

\[
\sigma=h_7-v^TH_3^{-1}v\simeq2,9622617277\times10^{-23}>0,
\quad H_3=(h_{i+j+1}),\quad v_i=h_{i+4}.
\]

O teto de `c₈` fica aproximadamente `1,8407523191×10⁻²⁴` acima de seu valor
numérico. São leituras numéricas, não intervalos certificados da integral nem
uma prova de sinal.

Mantendo a nona coordenada no valor do cache e variando os 256 vértices das
caixas antigas, o pivô passa de aproximadamente `−2,22838×10⁻²²` a
`2,79800×10⁻²²`. Até a variação isolada do momento theta de ordem zero muda o
sinal nesse ensaio. A certificação racional acima substitui a sondagem de
vértices como prova da insuficiência da implicação.

## Estado final do ataque

O alvo nativo seguinte é a cota exibida para `c₈`, com todos os seus
acoplamentos. O estudo não autoriza escolher momentos dentro de caixas para
definir a fonte ou usar o valor de alta precisão como certificado integral.

Uma prova dessa primeira cota ainda seria finita. Para alcançar `N` arbitrário,
seria necessário um argumento que controle os novos pivôs em todas as ordens,
ou uma identidade positiva da fonte que implique esse controle. A equivalência
all-order já formalizada com os dois blocos nativos de Stieltjes permanece uma
equivalência, sem nova prova do antecedente nesta entrega.
