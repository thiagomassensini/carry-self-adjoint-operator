# Porto de energia derivado do retorno quiral completo

Base: `0321d4eb3b79926f0de725ddc5a36fbe4dfafd69`, execução no servidor `llm`.

Esta construção parte do retorno físico completo já existente. Seu primeiro resultado incondicional é uma realização positiva do kernel canônico na grade radial de sete fontes, e a convergência dos produtos internos dos jets de ordens 0 a 6 para o bloco canônico de coeficientes. Ela não é uma realização global do operador das alturas.

## 1. Construção a partir da fonte

Para cada profundidade radial k e tamanho N, o domínio é o span incidente original `RadialIncidentSpan k N`, com o produto interno herdado do L² Cauchy existente. O operador `T = radialReturnTransfer k N` já recupera os coeficientes da fonte incidente e aplica a síntese retornada com o quociente completado original.

Definimos o defeito de energia e seu canal positivo:

\[
D_{k,N}=I-T_{k,N}^*T_{k,N},\qquad
P_{k,N}=\iota_{k,N}\sqrt{D_{k,N}},
\]

onde a inclusão \(\iota\) devolve o vetor ao L² físico original. O defeito é autoadjunto independentemente de seu sinal. Sob a cota efetiva \(\|T\|\le1\), ele é positivo e o cálculo funcional fornece

\[
\boxed{\langle Px,Py\rangle
=\langle x,y\rangle-\langle Tx,Ty\rangle.}
\]

O adjunto é tomado na norma Cauchy original, na qual as colunas não são ortogonais. Portanto este porto conserva a interferência entre fontes; não é a multiplicação separada de cada coluna por uma raiz escalar.

Os dois inputs são independentes. A igualdade conserva os cruzamentos da fonte completa, o companheiro nativo, a completação e as orientações incident/returned presentes no retorno original. Nenhuma matriz de momentos define D ou P, e o produto interno incidente não foi modificado.

O cálculo funcional de Mathlib é total mesmo fora do cone positivo. Por isso, a definição sozinha não autoriza usar essa igualdade quando falta a cota de contração. As leis de Gram de tamanho N geral mantêm essa hipótese explícita.

Na diagonal da síntese incidente original I(c),

\[
\|P I(c)\|^2=\operatorname{Re}\mathrm{storage}(k,c,1).
\]

Assim o porto representa a energia corrigida efetiva da fonte. O novo D é um operador de defeito de energia da seção finita; não foi identificado com o operador espectral das alturas.

## 2. Sete fontes sem assumir positividade nativa

A fonte atual já prova `radialReturnTransfer_seven_eventually_norm_le_one` e `storage_one_original_sevenSample_eventually_pos`. Elas fornecem, para k suficientemente grande, simultaneamente para todos os coeficientes das sete fontes:

- o Gram positivo de P é o balanço polarizado original;
- o porto tem energia estritamente positiva para toda fonte incidente não nula;
- não é preciso inserir uma hipótese de positividade dos momentos ou do kernel desejado.

Essa positividade de sete fontes é reaproveitada de um resultado anterior. A contribuição nova é o porto vetorial obtido do retorno, sua igualdade polarizada com a fonte e sua ligação aos estados e jets canônicos.

## 3. Kernel canônico na grade, com duas variáveis

Para o ponto radial \(z_{k,i}\), tomamos a fonte incidente unitária da coluna i multiplicada pela amplitude projetiva completada já existente, \(a(z_{k,i})\). O estado de energia é

\[
W_{k,N,i}=\frac1{\sqrt2}P_{k,N}I\bigl(a(z_{k,i})e_i\bigr).
\]

O fator \(1/\sqrt2\) implementa exatamente o fator \(1/2\) da definição anterior `canonicalCompletedNativeProjectiveChiralForm`. Não foi escolhido para ajustar h₀ ou qualquer momento.

Sob regularidade e contração da fonte, o teorema `radialReturnSampleEnergyPort_inner` prova

\[
\boxed{\langle W_{k,N,i},W_{k,N,j}\rangle
=\mathrm{canonicalCompletedNativeRadialDslopeSampleMatrix}(k,N)_{ij}.}
\]

Para N=7, as condições são satisfeitas eventualmente por teoremas existentes. Portanto todos os 49 pareamentos representam exatamente o kernel canônico nessa grade radial. Isso não afirma uma identidade para pontos complexos arbitrários, nem para duas grades de profundidades independentes.

## 4. Jets físicos e momentos recuperados no limite

As fontes dos jets usam os pesos de diferença, o passo e a normalização fatorial antigos:

\[
c_{k,N,p}(i)=\frac{\mathrm{forwardWeight}(p,i)}{p!\,h_k^p}\,a(z_{k,i}),
\qquad p<N.
\]

Foi demonstrado antes de qualquer pareamento que suas duas sínteses originais recuperam o par `projectiveChiralDifferenceJet k p` inteiro. Os vetores positivos novos são

\[
V_{k,N,p}=\frac1{\sqrt2}P_{k,N}I(c_{k,N,p}).
\]

Quando o retorno é contrativo, seu Gram coincide com a forma projetiva assinada dos dois jets originais. Para N=7, isso vale eventualmente sem hipótese nova e dá

\[
\langle V_{k,7,p},V_{k,7,q}\rangle
\longrightarrow \mathrm{polarizedGreenMomentCoefficient}(h;p,q),
\qquad 0\le p,q\le6.
\]

Concretamente:

\[
\langle V_{k,7,2i},V_{k,7,2j}\rangle\to h_{i+j}\quad(0\le i,j<4),
\]

\[
\langle V_{k,7,2i+1},V_{k,7,2j+1}\rangle\to h_{i+j+1}\quad(0\le i,j<3).
\]

Os cruzamentos de paridades diferentes estão presentes em cada passo e tendem a zero pelo limite provado. Em particular,

\[
\boxed{\|V_{k,7,0}\|^2\longrightarrow h_0.}
\]

Isso supera o teste central que excluía o porto direto de valor de massa 1/2. O novo porto inclui o retorno completo e seus jets. O enunciado é um limite das energias, não a afirmação de que a energia em cada k finito já é h₀.

## 5. A correção Green permanece contabilizada

A mesma construção dá a igualdade

\[
2\operatorname{Im}\mathcal B(c,c)+\|P I(c)\|^2=2\|S(c)\|^2.
\]

Logo, no setor em que a contração foi provada, o sinal da desigualdade do estudo segue de um canal positivo efetivo. O balanço não é apagado nem substituído por uma energia escolhida de fora.

## 6. Limites precisos

O porto é definido para cada N, com dimensões disponíveis que crescem com N. A identidade positiva geral ainda depende de controlar o retorno original nesse N. A aplicação sem premissas novas desta formalização é N=7, para k suficientemente grande.

Ainda faltam:

1. controlar o retorno/correção para dimensões arbitrárias, preservando os mesmos quantificadores;
2. construir e justificar uma realização global coerente dos estados, com os limites necessários;
3. obter o kernel positivo inteiro e a identificação com o operador autoadjunto das alturas.

A convergência dos Grams aqui não prova convergência dos vetores no L², compatibilidade vetorial entre diferentes N ou entre grades independentes, nem convergência de resolventes Jacobi de `momentos`. Não foram inseridas hipóteses escondidas para fechar esses pontos.

## Verificação

A API principal contém seis definições e 21 teoremas. O build focado do audit com `--wfail` passou com 9.825 jobs; o guard percorreu 27 raízes e 7.294 dependências de tipos/corpos, aceitando apenas `propext`, `Classical.choice` e `Quot.sound`. A execução direta do módulo com `-E warning` passou. O build raiz com `--wfail` passou com 10.182 jobs, e o Audit global passou com 10.319 jobs. Os logs e hashes estão em `audit/chiral-return-energy-port/`. Não houve campanha numérica nova.
