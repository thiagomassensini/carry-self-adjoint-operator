# Ataque à margem uniforme: cofatores, válvula e obrigação restante

Data: 2026-10-15. Repositório canônico: `llm:/home/thlinux/carry-self-adjoint-operator`. Base: `63d8f2d759dbfc0422c4eb1e7a96ed093641c304` (PR #103).

**Esta tentativa não demonstrou A_{s,n,n+2}≥L_{s,n} para todo n.** Obtivemos uma formulação exata sem inverso matricial do prefixo, uma ligação de coeficientes com a válvula projetiva e uma obstrução incondicional ao uso da massa bruta da válvula como Gram de Hankel positivo. A equivalência de sinal em todas as ordens com a porta de Stieltjes foi formalizada; a validade desse sinal permanece aberta.

## 1. Eliminar o inverso sem mudar o problema

Escreva H=H_{s,n}=(m_{i+j+s}), b=(m_{i+n+s}), d=m_{2n+s}, D=det H. A direção crítica original é v=(−H⁻¹b,1). Definimos diretamente pelos cofatores,

\[
a=(-\operatorname{adj}(H)b,D),\qquad
\widehat Q_{s,n}=c_0\sum_{i,j=0}^n a_i a_jP_{i+j+s}.
\]

Essa definição não contém H⁻¹. Os momentos, os polinômios P, o peso Φ e todas as somas ordenadas são os originais. Não se constrói um portador positivo a partir de um Gram alvo. É a mesma energia homogênea testada numa direção multiplicada por D; não é uma troca de métrica ou de amplitudes da fonte.

Quando H é invertível, Cramer fornece exatamente

\[
a=Dv,\quad \widehat Q=D^2Q,\quad
\mathcal I(\widehat Q)=D^2R,
\]
\[
M(\widehat Q)=D^2M(Q),\qquad
\widehat L:=e^{-(n+3)^2}M(\widehat Q)=D^2L>0.
\]

`NativeThetaCofactorMargin.lean` formaliza essas igualdades. Multiplicar ambos os lados da estimativa por D²>0 não cria o sinal procurado.

## 2. Identidade de borda válida inclusive em prefixos singulares

Defina a expressão escalar

\[
B=Dd-b^T\operatorname{adj}(H)b.
\]

Usando H adj(H)=D I, temos H(adj(H)b)=Db. A expansão completa da forma na direção (−adj(H)b,D) dá

\[
a^TH_{s,n+1}a=D\bigl(Dd-b^T\operatorname{adj}(H)b\bigr)=DB.
\]

Após aplicar o funcional theta original,

\[
\boxed{\mathcal I(\widehat Q_{s,n})=c_0D B.}
\]

Essa identidade está formalizada **sem hipótese de invertibilidade ou de sinal**. Ela conserva os termos cruzados. A anulação em D=0 é consequência da expansão, não um residual descartado. A expressão B é a expansão por cofatores do determinante da matriz de borda; essa identificação com o determinante de tamanho n+1 é a identidade algébrica usual. A declaração Lean usa a expressão explícita B e não depende dessa nomenclatura.

## 3. A margem quantitativa ficou como uma desigualdade polinomial da fonte

No trabalho anterior, K(n)=n+2 e o erro integral satisfaz E≤L/2. Multiplicando a identidade e o erro por D², para prefixos invertíveis, uma condição suficiente para A≥L é

\[
\boxed{\frac32\widehat L_{s,n}
\le (4n+2s+3)\,c_0D_{s,n}B_{s,n},\quad s\in\{0,1\}.}
\]

Com efeito, o termo principal multiplicado por D² é pelo menos (4n+2s+3)𝓘(\widehat Q)−D²E, logo é ≥(3/2)\widehat L−(1/2)\widehat L=\widehat L.

Reciprocamente, A≥L exige (4n+2s+3)𝓘(\widehat Q)≥\widehat L/2 sob o mesmo limite de erro. A margem original está, portanto, entre esses dois limiares quantitativos da mesma expressão de fonte. O fator 3/2 vem da margem 1 somada ao erro 1/2; não foi ajustado a experimentos.

`nativeSourceCofactor_margin_iff` formaliza a equivalência, para qualquer fator real α, entre

\[
\alpha\widehat L\le(4n+2s+3)\mathcal I(\widehat Q)
\quad\text{e}\quad
\alpha L\le(4n+2s+3)R
\]

quando H é invertível. A passagem do limite do erro integral à condição suficiente acima continua sendo a derivação matemática já registrada, não uma nova formalização daquela estimativa integral.

**O limite inferior para DB não foi provado em todas as ordens.** O inverso desapareceu da definição a atacar, mas a necessidade de uma nova desigualdade da fonte permanece. Uma estimativa não estrita com \widehat L=0 em um prefixo singular não basta: a aplicação por indução usa a positividade do prefixo anterior para garantir D≠0.

## 4. O que a válvula realmente entrega

Seja A(t)=c₀/F(t)=∑a_jt^j a massa da válvula projetiva nativa, com t=z². Sua curvatura satisfaz A′=mA, já formalizada no repositório. Aqui os a_j são **coeficientes da massa**, não os momentos m_j da curvatura.

A recorrência fornece

\[
a_0=1,\quad a_1=m_0,\quad a_2=\frac{m_0^2+m_1}{2}.
\]

A recorrência original da característica também fornece

\[
\boxed{a_0a_2-a_1^2=-\frac{c_2}{c_0}<0.}
\]

O sinal é incondicional: c₀>0 e c₂=𝓘(u⁴)/4!>0 vêm da fonte theta original. `NativeThetaValveCentralKernel.lean` demonstra essa identidade, o sinal estrito e que a matriz de Hankel 2×2 da massa da válvula não é semidefinida positiva. A direção (−a₁,1) lê exatamente o menor negativo.

O menor com orientação Toeplitz a₁²−a₀a₂ é positivo. Isso não demonstra positividade total de Toeplitz; apenas distingue os dois menores de ordem dois. A curvatura da válvula continua sendo exatamente m, conforme a identificação existente. O resultado não refuta a válvula nem a positividade da forma dos momentos nativos. Ele impede a etapa específica de tratar a **massa bruta** como uma sequência positiva de momentos de Hankel.

Há ainda uma ligação exata, em todas as ordens, com os polinômios que estamos integrando:

\[
[u^2]P_j=\frac{a_j}{2c_0},
\qquad
\boxed{[u^2]Q_{s,n}=\frac12\sum_{i,j=0}^n v_i v_j a_{i+j+s}.}
\]

As somas mantêm todos os cruzamentos. A válvula aparece, portanto, como um núcleo de Hankel **assinado** no coeficiente central do integrando. Não podemos obter a margem positiva supondo que esse núcleo seja positivo sobre todos os vetores.

## 5. Verificação de direções críticas da fonte, sem ampliar o canário

O pequeno script `audit_valve_central_signs.py` apenas audita os intervalos de fonte já publicados no PR #103. Não calcula novos momentos nem amplia a faixa de positividade. Confirma:

- em s=1,n=2, o coeficiente de u² de Q é estritamente negativo, enquanto R é estritamente positivo;
- em s=0,n=3, ocorre a mesma combinação de sinais.

Isso mostra, nas próprias direções críticas, que o sinal integrado não coincide com o sinal desse coeficiente central. Os dados são intervalos externos reutilizados, não premissas Lean; o JSON registra o hash do certificado de origem. A identidade geral com a válvula e o menor negativo da massa, na seção anterior, são provas Lean sem dependência desses dados.

## 6. Força lógica exata do sinal que continua faltando

`NativeThetaCofactorSignGate.lean` define a condição explícita

\[
\forall n,\quad \mathcal I(\widehat Q_{0,n})>0
\quad\text{e}\quad \mathcal I(\widehat Q_{1,n})>0.
\]

Demonstra que essa condição é **equivalente** a `CanonicalCompletedNativeStieltjesPositivity`. Não foi demonstrado que a condição vale.

Na direção que poderia preocupar quanto a degenerescência, a identidade c₀DB mostra que uma integral estritamente positiva força D≠0. A identidade com D²R então dá R>0, e a equivalência de Schur existente promove isso às duas torres. Na direção contrária, as torres positivas dão prefixos invertíveis e R>0, logo suas integrais de cofatores são positivas.

A consequência formal

`completedNative_zero_im_eq_zero_of_thetaCofactorSign`

é explicitamente **condicional** a esse sinal em todas as ordens. Reutiliza o teorema já existente de Stieltjes para o resolvente positivo de Jacobi e o confinamento dos zeros nativos dentro de `completedNativeHeightDomain`. Não é uma prova incondicional de confinamento, de positividade ou de RH, nem identifica uma energia física ainda não transportada.

Essa força é coerente com o critério clássico de Grommer, que impõe positividade de toda uma família de determinantes derivados do logaritmo de Ξ. O panorama e a normalização clássica podem ser conferidos na seção 11 do [artigo de Brian Conrey](https://aimath.org/~kaur/publications/90.pdf). Essa referência serve para comparação; nenhum resultado externo é uma premissa das novas provas Lean.

## 7. Resultado da tentativa

Foram provados: o transporte por cofatores, a identidade de borda em todas as ordens inclusive no caso singular, a escala exata da massa de coeficientes e do alvo L, a ligação central com a válvula e a obstrução da massa bruta. A equivalência entre a condição de sinal e a porta de Stieltjes é um teorema incondicional; a validade de cada condição permanece aberta. A consequência espectral é condicional à validade desse sinal.

Não foi obtido um limite inferior positivo uniforme para DB nem para A. Não fizemos uma nova extensão numérica de n≤20 para sugerir essa conclusão. O próximo alvo matemático preciso é o limite inferior da seção 3, que deve usar a recorrência e as relações completas da fonte, sem pressupor o sinal dos novos determinantes ou a positividade da massa da válvula.

Validação e estado de publicação: os comandos, o fecho axiomático, os SHAs, a repetição em main e a preservação dos arquivos C2 estão nos artefatos de entrega em `verification.json`.
