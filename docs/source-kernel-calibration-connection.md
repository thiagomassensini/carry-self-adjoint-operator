# Calibração do kernel e conexão da fonte completada

Investigação de 14 de outubro de 2026, no servidor `llm`. Base: `carry-self-adjoint-operator` em `8f791152e9c0f354b3aa399f0e0c3de5c24db1ec`, após o PR #95. Reutilizamos os pins existentes, incluindo `CPFormal` em `65d50f6db1208708e109982ba97e1d51d3039956`. Não atualizamos dependências nem alteramos fontes de outros repositórios.

**O avanço desta rodada é uma calibração exata que descarta duas escolhas simples de vetor e explicita a conexão que a representação correta precisa conservar.** A positividade nativa para N arbitrário permanece aberta. Não construímos ainda os vetores cujo Gram complementar seja o kernel canônico.

## A margem positiva impõe uma condição à fonte

Escrevemos C para `nativeGprePrimeCarryDefectState`. A contração já existente fornece a forma real

\[
\mathfrak d(X,Y)=\langle X,Y\rangle-\langle CX,CY\rangle,
\qquad \mathfrak d(X,X)\geq\frac1{12}\|X\|^2.
\]

Se um vetor U₀ tiver exatamente a energia do momento central, então necessariamente

\[
\mathfrak d(U_0,U_0)=m_0
\quad\Longrightarrow\quad
\boxed{\|U_0\|^2\leq12m_0<\frac34.}
\]

A última desigualdade usa a estimativa analítica já formalizada `canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth`; não usa um valor decimal de m₀. Consequentemente, para qualquer estado X com norma quadrada pelo menos 1,

\[
\boxed{\mathfrak d(X,X)-m_0>\frac1{48}.}
\]

O resultado vale após qualquer isometria real linear para a torre. Não elimina transportes gerais derivados da fonte, nem permite escolher uma constante para ajustar uma norma. Ele elimina a proposta específica de usar o estado bruto de norma pelo menos 1 como vetor do momento zero.

Em `geometry-of-numbers`, recompilamos uma prova executável sobre o estado com seed, interior material e retorno da célula inteira. Sua seed é 1 e sua norma é pelo menos 1. O kernel com duas entradas é exatamente

\[
\langle V(t),V(u)\rangle
=1+\langle \nabla a(t),\nabla a(u)\rangle
+\overline{R(t)}R(u).
\]

Esse resultado usa a versão `e1084b43533255b399b82dc307b536d7dfdca07f` da geometria, mais recente que o pin consumido. Foi compilado separadamente; não afirmamos que o autoadjunto já importa esse módulo nem que seu parâmetro material foi identificado com a altura do operador.

## Normalizar só pelo valor perde a completação escalar

Para um readout linear fixo ℓ, consideramos a normalização pelo próprio valor sintetizado:

\[
\widehat v=(\ell(v))^{-1}v.
\]

Para todo escalar não nulo a,

\[
\widehat{av}=\widehat v.
\]

Logo o Gram de duas entradas normalizadas dessa maneira é invariável sob dressings escalares independentes nas duas entradas. Na fonte geométrica com bordo, isso se especializa à identidade exata

\[
\frac{d(t)V(t)}{d(t)S(t)}=\frac{V(t)}{S(t)},
\]

em que d é o dressing prescrito e S é o sinal completo. Os vetores e os fatores são os existentes, não são escolhidos a partir dos momentos.

Essa invariância não diz que uma realização de momentos seja impossível: mostra que a informação derivativa da completação não pode surgir apenas desse Gram normalizado pelo valor.

## A conexão que precisa sobreviver

Usamos literalmente os fatores do autoadjunto:

\[
F=AN,\qquad
b_A=-\frac{A'}A,\quad b_N=-\frac{N'}N,\quad b_F=-\frac{F'}F.
\]

No domínio declarado e onde os fatores não são nulos, Lean prova

\[
\boxed{b_F=b_N+b_A.}
\]

Se G é a forma de Green do par companheiro/valor, definimos somente para esta comparação

\[
\widetilde G_F(z,w)=\frac{G_F(z,w)}{\overline{F(z)}F(w)},
\qquad
\widetilde G_N(z,w)=\frac{G_N(z,w)}{\overline{N(z)}N(w)}.
\]

A lei exata com duas entradas é

\[
\boxed{\widetilde G_F(z,w)-\widetilde G_N(z,w)
=b_A(w)-\overline{b_A(z)}.}
\]

A correção é efetiva na fonte original: no centro, o lado direito é não nulo. Esse fato reutiliza a prova anterior de que a correção arquimediana cancela uma contribuição nativa também não nula. Não é uma nova hipótese de cancelamento.

A mesma lei conserva o fator da divisão Green:

\[
\frac{\widetilde G_F(z,w)-\widetilde G_N(z,w)}{2(w-\bar z)}
=\frac{b_A(w)-\overline{b_A(z)}}{2(w-\bar z)}.
\]

Interpretamos essa expressão fora da diagonal de Cauchy. A implementação Lean usa inverso total; seu valor algébrico no denominador zero não substitui a extensão por limite removível. A forma Green orientada também não deve ser confundida com um Gram positivo. O mecanismo espectral relevante exige conservar essa divisão e sua normalização antes da extração dos coeficientes.

## O par normalizado conserva a conexão, mas tem a energia errada

Construímos o estado concreto a partir do par original:

\[
W(z)=\frac{(-F'(z),F(z))}{F(z)}=(b_F(z),1).
\]

O produto interno padrão foi calculado sem descartar cruzamentos:

\[
\begin{aligned}
\langle W(z),W(w)\rangle={}&1
+\overline{b_N(z)}b_N(w)+\overline{b_A(z)}b_A(w)\\
&+\overline{b_N(z)}b_A(w)+\overline{b_A(z)}b_N(w).
\end{aligned}
\]

A paridade da característica completada dá b_F(0)=0 e b_N(0)+b_A(0)=0. A compensação é mantida antes de tomar a norma. O estado central é (0,1), com norma quadrada 1. Assim, qualquer transporte isométrico desse estado para a torre falha na calibração \(\mathfrak d(U_0,U_0)=m_0\), com o excesso acima de 1/48 já provado.

Também verificamos a escolha do primeiro tangente coordenado, definido da própria fonte:

\[
T=(b_F'(0),0).
\]

A normalização do readout existente é b_F/2; seu primeiro coeficiente é m₀. Portanto

\[
b_F'(0)=2m_0,\qquad \|T\|^2=4m_0^2<m_0.
\]

A positividade de m₀ e a estimativa m₀<1/16 já estavam demonstradas pela fonte theta. Como \(\mathfrak d(X,X)\leq\|X\|^2\), qualquer transporte isométrico desse tangente também fica estritamente abaixo de m₀. Esse resultado é sobre a derivada escalar e o par de derivadas coordenadas; não anunciamos um teorema novo de diferenciabilidade forte de um estado infinito.

Temos, assim, duas obstruções distintas e delimitadas: o estado de valor normalizado fica grande demais; seu primeiro tangente fica pequeno demais. Elas não descartam uma realização pela resposta Green completa com seus canais de bordo, bulk e retorno.

## Contabilidade exata para qualquer N

Para uma família geométrica U ainda a construir, registramos o defeito de pareamento completo

\[
D^{(s)}_{ij}=\mathfrak d(U_i,U_j)-m_{i+j+s}.
\]

Lean verifica a síntese polarizada com entradas e dimensões independentes. Como consequência, para qualquer N, setor s e entrada real x,

\[
E_{s,N}(x)=\mathfrak d\!\left(\sum_i x_iU_i,\sum_i x_iU_i\right)
-\sum_{i,j<N}x_ix_jD^{(s)}_{ij},
\]

\[
E_{s,N}(x)\geq\frac1{12}\left\|\sum_i x_iU_i\right\|^2
-\sum_{i,j<N}x_ix_jD^{(s)}_{ij}.
\]

Essas são identidades e um orçamento com o defeito completo. **Não fornecem uma estimativa independente para esse defeito**, que contém a comparação com os próprios momentos canônicos. Portanto, não são uma prova disfarçada de positividade nem uma construção da família U. Explicitam o que precisa ser controlado, mantendo todos os cruzamentos.

## O próximo alvo ficou mais específico

A tentativa inicial de transportar diretamente o estado com bordo por uma isometria não basta. O portador dos momentos precisa surgir da resposta Green normalizada, com a conexão da completação e a divisão de Cauchy conservadas. As coordenadas desse portador não podem ser identificadas diretamente nem com o vetor de valor W(0) nem com seu tangente coordenado T.

O próximo passo útil é construir essa resposta vetorial com a geometria de bordo/bulk/retorno e provar sua identidade polarizada com o kernel escalar antes de tomar jatos. Se a igualdade falhar, o residual deve ser decomposto nesses canais e comparado com o orçamento complementar. Não há justificativa para corrigir os dois candidatos rejeitados por um ajuste de constantes.

## Proveniência e validação

Os três módulos novos são `NativePrimeCarryKernelCalibration`, `NativeSourceNormalizedKernelConnection` e `NativeSourceCovariantBoundaryState`. O módulo `NativeSourceKernelCalibrationAudit` verifica todas as suas declarações públicas e é importado pela auditoria global. O arquivo `verification.json` acompanha os comandos, resultados e publicação.

O probe `BoundaryKernelProbe.lean` é preservado como estudo reproduzível, executado no checkout próprio de `geometry-of-numbers`; nenhum módulo dessa versão recente foi portado ou incorporado por mudança de pin. Não alteramos os arquivos C2 preexistentes nem as worktrees de outras tarefas.

A compilação direcionada dos três módulos passou com `lake build --wfail CarrySelfAdjointOperator.NativeSourceCovariantBoundaryState`, 9964 jobs. A raiz e a auditoria global passaram com `lake build --wfail CarrySelfAdjointOperator.NativeSourceKernelCalibrationAudit CarrySelfAdjointOperator CarrySelfAdjointOperator.Audit`, 10356 jobs. A guarda examinou 35 declarações públicas, com fecho tipo/corpo de 5365 declarações, e permitiu somente `propext`, `Classical.choice` e `Quot.sound`. O probe separado da geometria terminou com código 0, sem avisos; os `#print axioms` mostraram os mesmos fundamentos usuais. Não há obrigações admitidas nos módulos novos.
