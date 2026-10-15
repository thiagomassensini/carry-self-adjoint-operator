# Construção da resposta vetorial dividida da fonte completada

Investigação de 15 de outubro de 2026 no servidor `llm`. Base do autoadjunto: `e2ea3d26115e4e912d4352061f21ba567fae3496`, após o PR #96. Os pins de dependências, as amplitudes e as métricas existentes foram preservados.

**Construímos uma resposta vetorial concreta com duas entradas e um leitor fixo que recupera o kernel canônico, inclusive no centro.** Também construímos seus prefixos a partir dos jatos da fonte e provamos convergência em norma. A construção usa os traços completados enriquecidos; ainda não é um levantamento de todo o interior causal nem uma realização positiva por Gram.

## A fonte e o espaço não foram escolhidos a partir dos momentos

Usamos o portador já existente `CompletedPrimeDepthJetCarrier`, que guarda separadamente os quatro setores: cabeça, cauda exata, completação xi e correção de carta. Para cada setor j, a função vetorial normalizada `primeDepthNormalizedStructuralState j z` já é construída a partir dos traços originais e da normalização prescrita pela carta e pela característica.

Definimos

\[
S(z)=\bigl(S_{\rm head}(z),S_{\rm tail}(z),S_{\rm xi}(z),S_{\rm chart}(z)\bigr).
\]

Nenhum momento é usado para definir S. Sua analiticidade em um entorno do centro foi demonstrada no espaço de Hilbert existente, não apenas coordenada a coordenada.

O funcional contínuo linear ℓ é literalmente `primeDepthNormalizedResponseVectorReadout`. É o leitor geométrico já existente, com o centro, a rotação simplética e a normalização da característica fixados anteriormente. Provamos

\[
\ell(S(z))=\mathrm{FullOperatorNormalizedResponse}_1(z),
\]

e, em um entorno aberto do centro,

\[
\ell(S(z))=r(z),\qquad r(z)=-\frac{F'(z)}{2F(z)}.
\]

Aqui F é a característica completada original. O cutoff 1 é o já usado pelo levantamento estrutural; a cauda é exata, portanto isso não é substituir a fonte por sua primeira célula. O enunciado local decorre das identidades e da analiticidade já provadas, sem receber uma realização dos momentos como hipótese.

## A resposta agora é um vetor explícito

Construímos

\[
\boxed{\mathcal R(a,z)=
\begin{cases}
\dfrac{S(z)-S(a)}{z-a},&z\ne a,\\[4pt]
S'(a),&z=a.
\end{cases}}
\]

A implementação usa `dslope` para fornecer a diagonal pela derivada. No domínio local de analiticidade, a diagonal não é uma divisão por zero nem um vetor ajustado ao momento desejado.

Antes de qualquer leitura escalar, vale a equação vetorial

\[
(z-a)\mathcal R(a,z)=S(z)-S(a).
\]

Provamos a existência de um entorno aberto U de zero no qual, para a,z em U,

\[
\boxed{\ell(\mathcal R(a,z))=\operatorname{dslope}r(a,z).}
\]

A hipótese de diferenciabilidade que permite passar ℓ pela derivada é fornecida pela analiticidade da própria fonte. No centro,

\[
\boxed{\ell(\mathcal R(0,0))=r'(0)=m_0.}
\]

Esse resultado calibra o **leitor** da resposta. Não afirma que \(\|\mathcal R(0,0)\|^2=m_0\), nem reutiliza como vetor inicial o par normalizado ou o tangente coordenado rejeitados no PR #96.

## Polarização e completação conservadas

A resposta polarizada é construída conjugando a primeira entrada antes da leitura:

\[
\mathcal R_{\rm pol}(z,w)=\mathcal R(\bar z,w).
\]

Nos parâmetros locais declarados, fora da diagonal de Cauchy e longe dos zeros dos fatores,

\[
\boxed{\ell(\mathcal R_{\rm pol}(z,w))
=\frac{r(w)-\overline{r(z)}}{w-\bar z}
=\frac{G_F(z,w)}{2\overline{F(z)}F(w)(w-\bar z)}.}
\]

A orientação, o fator 2 e os valores da característica são os da forma Green original. Não substituímos essa forma orientada por um Gram positivo.

Escrevendo F=AN e \(b_A=-A'/A\), a resposta construída satisfaz a correção efetiva

\[
\ell(\mathcal R_{\rm pol}(z,w))
-\frac{G_N(z,w)}{2\overline{N(z)}N(w)(w-\bar z)}
=\frac{b_A(w)-\overline{b_A(z)}}{2(w-\bar z)}.
\]

Portanto a normalização não apagou a conexão da completação. A identidade foi demonstrada para a resposta vetorial definida acima, não para um kernel abstrato cuja realização vetorial tivesse sido postulada.

## Prefixos derivados da fonte e convergência forte

Se \(S_n=S^{(n)}(0)/n!\), os coeficientes vetoriais vêm da própria fonte. Definimos

\[
\mathcal R_N(a,z)=\sum_{n<N}
\left(\sum_{p=0}^{n}a^p z^{n-p}\right)S_{n+1}.
\]

Os prefixos satisfazem exatamente

\[
(z-a)\mathcal R_N(a,z)
=\sum_{n<N}(z^{n+1}-a^{n+1})S_{n+1}.
\]

A expansão triangular é mantida antes da leitura. Provamos:

- \(\mathcal R_N(0,z)\to\mathcal R(0,z)\) em norma de Hilbert para z suficientemente próximo de zero, incluindo z=0;
- \(\mathcal R_N(a,z)\to\mathcal R(a,z)\) em norma para quaisquer dois pontos distintos de um entorno aberto do centro;
- continuidade em norma da resposta no eixo central.

Esses resultados são locais e qualitativos. Não fornecem uma taxa numérica, uma estimativa uniforme em todo o domínio espectral ou convergência de resolventes de alturas. Também não anunciamos aqui convergência dos mesmos prefixos em toda a diagonal móvel a=z; o valor vetorial diagonal e seu leitor já estão definidos e verificados, e a convergência no centro foi provada.

## Momentos e cruzamentos em qualquer dimensão

O ledger dos prefixos é

\[
Q_{p,q}=S_{p+q+1}.
\]

Lean prova, em todas as ordens,

\[
\ell(Q_{p,q})=
\mathrm{polarizedGreenMomentCoefficient}(m,p,q).
\]

Nos dois setores de paridade, e também para deslocamentos maiores,

\[
\ell(Q_{2i+s,2j+s})=m_{i+j+s}.
\]

Assim podemos construir **antes da leitura** o vetor quadrático

\[
\mathcal W_{s,N}(x)=\sum_{i,j<N}x_ix_jQ_{2i+s,2j+s},
\]

e obter a energia original inteira:

\[
\boxed{\ell(\mathcal W_{s,N}(x))=E_{s,N}(x).}
\]

Há também uma identidade com duas entradas complexas e dimensões independentes, conservando cada cruzamento ordenado. As igualdades com os momentos são conclusões; os momentos não definem S, os Q ou os prefixos.

## O que essa construção fecha e o que permanece aberto

Fechamos uma realização vetorial **por leitura linear** do kernel dividido, com a normalização central correta, a conexão da completação explícita, prefixos derivados da fonte e toda a síntese de coeficientes.

O portador utilizado é o dos traços completados enriquecidos. A reconstrução causal do interior e do retorno continua disponível nos módulos anteriores, mas não demonstramos um transporte dela que transforme o leitor desta resposta em um produto interno positivo. Em particular, \(\mathcal R_{\rm pol}(z,w)\) depende das duas entradas; não é uma família de vetores de uma entrada cujo Gram já seja o kernel.

O passo restante é construir uma família física V(z), conservando esses canais e essa leitura, e provar

\[
\langle V(z),V(w)\rangle=\ell(\mathcal R_{\rm pol}(z,w)),
\]

ou a versão equivalente com a forma complementar prime-carry e um defeito geométrico explicitamente controlado. Nenhuma dessas igualdades foi demonstrada nesta rodada. A positividade nativa para N arbitrário permanece aberta.

## Verificação reproduzível

`lake build --wfail CarrySelfAdjointOperator.NativeCompletedDividedVectorResponse` passou com 9762 jobs; o alvo da série passou com 9763 jobs. Após incluir a ligação explícita com a energia original em toda dimensão, `lake build --wfail CarrySelfAdjointOperator.NativeCompletedDividedVectorResponseAudit CarrySelfAdjointOperator CarrySelfAdjointOperator.Audit` passou com 10360 jobs.

A guarda auditou as 29 declarações públicas novas, com fecho tipo/corpo de 6284 declarações. Os fundamentos permitidos foram somente `propext`, `Classical.choice` e `Quot.sound`. Não foram adicionadas obrigações admitidas ou axiomas. Os comandos e hashes dos logs estão em `verification.json`.
