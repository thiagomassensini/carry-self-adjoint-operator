# Dois canais positivos extraídos da fonte completada

Data: 2026-10-15. Repositório: `carry-self-adjoint-operator`, servidor `llm`.

**Resultado:** construímos dois canais de Hilbert positivos a partir da resposta completada, com uma identidade exata para o kernel original e seu residual. A construção é a mesma em todas as dimensões finitas. **A positividade do kernel inteiro em todas as ordens permanece aberta.** Não descartamos o residual nem mudamos a métrica das fontes originais.

## 1. A entrada continua sendo a fonte existente

Seja `sourceVector` a síntese vetorial existente dos quatro setores: cabeça, cauda exata, completação e correção de carta. Aplicamos o funcional fixo somente depois dessa síntese:

\[
r(z)=\ell(\mathrm{sourceVector}(z)).
\]

Em uma vizinhança aberta de zero, a identidade anterior do repositório fornece

\[
r(z)=-\frac{F'(z)}{2F(z)},\qquad F=\mathrm{completedNativeOperatorCharacteristic}.
\]

Logo todos os fatores de completação, as caudas e as correções de carta continuam presentes. A resposta é analítica no centro e \(r(0)=0\).

Definimos o quociente removível pela resposta vetorial já construída:

\[
A(z)=\ell(\mathrm{response}(0,z))
=\begin{cases}r(z)/z,&z\ne0,\\r'(0),&z=0.\end{cases}
\]

A escala da construção é extraída da própria fonte:

\[
\alpha=A(0)=r'(0)=-\frac{F''(0)}{2F(0)}=m_0>0.
\]

Ela não é escolhida para ajustar uma norma. A identificação com \(m_0\) vem depois da definição pela fonte e está demonstrada no Lean.

## 2. Primeira extração positiva

Construímos a resposta reduzida regular

\[
r_1(z)=\frac{\operatorname{dslope}(A,0,z)}{\alpha A(z)}.
\]

Para \(z\ne0\), isso equivale a

\[
r_1(z)=\frac{1}{\alpha z}-\frac1{r(z)}.
\]

A definição por `dslope` fornece o valor removível no centro. Não usamos a inversa de um Gram de momentos. A identidade vetorial anterior fornece a entrada; essa operação é aplicada à sua resposta escalar completa.

Com

\[
\psi_0(z)=\frac{A(z)}{\sqrt\alpha},\qquad
K_f(z,w)=\frac{f(w)-\overline{f(z)}}{w-\bar z},
\]

a álgebra dá exatamente

\[
K_r(z,w)=\overline{\psi_0(z)}\psi_0(w)
+\overline{r(z)}r(w)K_{r_1}(z,w).
\]

O primeiro termo é um Gram positivo. O segundo é o residual original da extração, com suas amplitudes e seus cruzamentos.

Também demonstramos a identidade de numeradores antes da divisão. A fórmula dividida exige \(w\ne\bar z\) e os denominadores locais originais não nulos. No centro, tratado separadamente pelo valor removível, temos

\[
|\psi_0(0)|^2=m_0,\qquad
\overline{\psi_0(0)}\psi_0(w)=A(w).
\]

Portanto o primeiro canal recupera a linha central inteira, além da energia central.

## 3. A segunda extração também tem escala positiva

Da série da própria fonte e das identidades theta já formalizadas:

\[
r_1(0)=0,\qquad
\beta=r_1'(0)=\frac{m_1}{m_0^2}>0.
\]

Essa positividade reaproveita o teorema anterior para o primeiro momento ímpar. Não é uma nova prova de sinais em ordens superiores.

Definimos

\[
B(z)=\operatorname{dslope}(r_1,0,z),\qquad
r_2(z)=\frac{\operatorname{dslope}(B,0,z)}{\beta B(z)},
\]

e um único vetor em \(\mathbb C^2\), com seu produto interno usual:

\[
\Phi(z)=\left(\frac{A(z)}{\sqrt\alpha},
\frac{r(z)B(z)}{\sqrt\beta}\right),\qquad
v(z)=r(z)r_1(z).
\]

Os dois denominadores são não nulos em uma vizinhança aberta de zero, cuja existência foi provada, pois \(A(0)=\alpha>0\) e \(B(0)=\beta>0\).

O resultado central é

\[
\boxed{K_r(z,w)=\langle\Phi(z),\Phi(w)\rangle
+\overline{v(z)}v(w)K_{r_2}(z,w).}
\]

A vizinhança é na topologia de \(\mathbb C\). A fórmula dividida mantém \(w\ne\bar z\).

Além disso,

\[
v(z)=z^2A(z)B(z).
\]

O fator que multiplica o residual tem, portanto, um zero de ordem pelo menos dois em cada perna polarizada. Isso é uma fatoração exata, não uma licença para eliminar o residual. O kernel reduzido também tem resposta analítica no centro; não identificamos sua divisão total por zero com o valor removível.

Verificações de calibração:

\[
\|\Phi(0)\|^2=m_0,\qquad
\left|\left(\frac{rB}{\sqrt\beta}\right)'(0)\right|^2=m_1.
\]

## 4. A identidade conserva todos os cruzamentos para qualquer N

Para qualquer família finita de pontos regulares e quaisquer coeficientes complexos independentes, a formalização conserva a soma completa:

\[
\sum_{i,j}\bar c_i c_jK_r(z_i,z_j)
=\left\|\sum_i c_i\Phi(z_i)\right\|^2
+\sum_{i,j}\overline{c_iv(z_i)}c_jv(z_j)K_{r_2}(z_i,z_j).
\]

Não há truncamento das duas somas nem descarte de termos fora da diagonal. A construção de \(\Phi\), \(v\) e \(r_2\) independe de \(N\). A condição de separação inclui os pares diagonais: por exemplo, pontos no semiplano superior satisfazem \(z_j\ne\bar z_i\).

O teorema `nativeKernel_two_positive_channels_local` identifica o lado esquerdo com a resposta nativa \(-F'/(2F)\) na mesma vizinhança. O teorema `sourceKernel_two_channel_finite_energy` fornece a síntese finita completa.

## 5. O que ainda impede a realização positiva inteira

O primeiro termo da última identidade é positivo. **Não provamos que o residual seja positivo nem que sua contribuição negativa seja dominada pelo primeiro termo.**

Isso importa sobretudo nas combinações que cancelam os dois canais positivos. Quando

\[
\sum_i c_i\Phi(z_i)=0,
\]

a energia inteira é exatamente a soma residual. Formalizamos essa igualdade em `sourceKernel_energy_on_positive_nullspace`. Por dimensão, três ou mais vetores em \(\mathbb C^2\) admitem combinações lineares não triviais que os cancelam. Portanto a existência de dois canais positivos não pode, sozinha, provar o sinal para uma família arbitrária de fontes.

O próximo alvo concreto é a fonte reduzida \(r_2\): investigar seu kernel e repetir a extração com escalas positivas provadas a partir da fonte. A identidade de reconstrução

\[
r(z)\bigl(1-\alpha z r_1(z)\bigr)=\alpha z
\]

também foi formalizada. Ela fornece a primeira relação exata de uma possível expansão por frações contínuas. A relação com um operador de Jacobi ou resolvente autoadjunto ainda exige construir os coeficientes em todas as etapas e controlar domínio e limite. Não afirmamos que essa identificação espectral já esteja feita.

## 6. Escopo formal

Módulos novos:

- `NativeCompletedSourcePositiveReduction.lean`: resposta original, escala, primeiro canal e residual exato.
- `NativeCompletedSourcePositiveReductionJet.lean`: identificação nativa, regularidade, escala reduzida positiva e reconstrução.
- `NativeCompletedSourceTwoPositiveChannels.lean`: segundo canal, vetor positivo fixo, calibrações e síntese completa em qualquer dimensão finita.
- `NativeCompletedSourcePositiveReductionAudit.lean`: auditoria das declarações públicas e de suas dependências.

Não foi assumida positividade do kernel pretendido, existência de uma medida que o realize, localização de zeros ou uma identidade de Gram desejada. O resultado é uma **realização positiva parcial com residual explícito**. A realização positiva completa, a passagem a todas as etapas e a conclusão sobre o operador de alturas continuam abertas.

Os resultados finais de compilação, auditoria e publicação estão em [verification.json](../research/native-source-positive-reduction-2026-10-15/verification.json).
