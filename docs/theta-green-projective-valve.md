# Fonte theta, fluxo de Green, TFVD e válvula projetiva

Investigação de 14 de outubro de 2026, sobre `carry-self-adjoint-operator`, base `58455d703e311d02118de8c4658316bc176edc08` (PR #93).

A sugestão da válvula projetiva forneceu uma ligação exata e utilizável: os polinômios da fonte são uma convolução com a massa da válvula já definida no repositório. Essa convolução comuta com a transferência diferencial de Green. Formalizamos também um fluxo explícito que transfere a integral original para a cauda theta, com as duas fronteiras controladas, em toda ordem e para a forma quadrática inteira.

A transferência direta não produz uma densidade positiva. Seu coeficiente superior é negativo em todo o setor par, e o primeiro caso par já apresenta um valor negativo exato. O TFVD fornece a reconstrução completa de estado, mas os resultados atuais ainda não identificam seu Gram positivo com a energia nativa requerida. Portanto, a positividade para todo N continua aberta.

Escrevemos \(A=\mathrm{XiThetaCosine.thetaTail}\). Esta função já pertence à construção original, é não negativa e satisfaz

\[
\Phi=A''-\frac14 A.
\]

Sua normalização é \(A(u)=2\sum_{j\geq1}e^{u/2-\pi j^2e^{2u}}\); o fator 2 importa. Não se escolheu uma nova medida para ajustar momentos. O peso \(A(u)\,du\) que aparece abaixo é derivado da própria fonte pela identidade diferencial. O valor da energia e os coeficientes originais são preservados.

Para qualquer polinômio real \(P\), definimos

\[
\mathscr L P=P''-\frac14P,
\qquad
J_P=P A'-P'A.
\]

O cálculo exato dá

\[
\boxed{P\Phi=(\mathscr L P)A+J_P'.}
\]

Lean verifica a derivada, a integrabilidade e \(J_P(u)\to0\) no infinito. A identidade integrada conserva todos os termos do centro:

\[
\int_0^\infty P(u)\Phi(u)\,du
=\int_0^\infty(\mathscr L P)(u)A(u)\,du
+\frac{P(0)}2+P'(0)A(0).
\]

Aqui usamos o valor já formalizado \(A'(0)=-1/2\). A identidade não foi obtida supondo o sinal da integral.

Os polinômios \(P_j\) do PR #93 têm coeficientes de graus zero e um nulos. A recorrência da característica preserva essa propriedade em toda ordem. Portanto, tanto o polinômio crítico \(\mathcal R_{s,n}\) quanto a síntese completa

\[
Q_{s,N,x}(u)=\sum_{i,j<N}x_ix_jP_{i+j+s}(u)
\]

têm as duas coordenadas centrais nulas. Obtemos os teoremas incondicionais

\[
\boxed{R_{s,n}=\int_0^\infty(\mathscr L\mathcal R_{s,n})(u)A(u)\,du,}
\]

\[
\boxed{x^T H_{s,N}x=\int_0^\infty(\mathscr L Q_{s,N,x})(u)A(u)\,du.}
\]

A segunda identidade vale para todo N e toda entrada real x. Mantém cada cruzamento ordenado \(x_ix_j\); não se limita à direção crítica de Schur. A identificação anterior da energia complexa com os dois setores continua sendo a do repositório.

A primeira tentativa de obter quadrados por essa transferência falha de forma explícita:

\[
\mathcal R_{0,0}(u)=\frac{u^2}{2},\qquad
\mathscr L\mathcal R_{0,0}(u)=1-\frac{u^2}{8},\qquad
(\mathscr L\mathcal R_{0,0})(3)=-\frac18.
\]

Logo, o polinômio transferido não é um quadrado pontual nem uma soma de quadrados pontuais. Isso não contradiz a positividade de sua integral, já conhecida nesse caso.

A obstrução tem uma forma em toda ordem:

\[
[u^{4n+2s+2}]\mathscr L\mathcal R_{s,n}
=-\frac14\frac{(-1)^s(2n+s+1)}{(4n+2s+2)!}.
\]

O termo \(P''\) baixa o grau e não altera o coeficiente superior; quem o determina é \(-P/4\). Lean prova que o polinômio transferido tende a menos infinito em todo o setor par. Assim, essa transferência troca o setor com cauda polinomial negativa. Não demonstramos impossibilidade de outras integrações por partes, de identidades não locais ou de uma construção vetorial completa.

Também isolamos mais precisamente a origem do primeiro sinal ímpar. Se

\[
T_j=\int_0^\infty u^j A(u)\,du,
\qquad c_0=\frac12-\frac14T_0>0,
\]

então a fonte satisfaz a decomposição exata

\[
\boxed{R_{1,0}
=\frac{2T_0^2-T_2}{2c_0}
+\frac{T_2^2}{64c_0}
+\frac{T_4}{48}.}
\]

As duas últimas parcelas são não negativas. A desigualdade específica da fonte

\[
T_2<2T_0^2
\]

torna a primeira estritamente positiva e fornece uma cota inferior explícita para \(R_{1,0}\). A prova reaproveita os limites theta já verificados em Lean: \(T_0>113/10000\) e \(T_2<51/200000\). Não usa a positividade desejada do resto como premissa.

Este resultado explica uma dificuldade da extensão: o primeiro sinal usa uma relação **não linear** entre integrais da fonte, além da integração por partes. A positividade isolada de A não fornece \(2T_0^2-T_2>0\). O quadrado \(T_0^2\) também sugere conservar pareamentos entre duas cópias da fonte. Uma hierarquia adequada dessas relações para os blocos seguintes ainda precisa ser construída.

A válvula entra de forma literal. Se

\[
C(z)=\sum_{j\geq0}c_jz^j,\quad M(z)=\sum_{j\geq0}m_jz^j,
\quad V(z)=\mathrm{projectiveValveMass}(M)(z),
\]

o teorema existente fixa \(V=(C/c_0)^{-1}\). A nova ligação é

\[
\boxed{
\sum_{n\geq0}P_n(u)z^n
=\frac{V(z)}{c_0}
\sum_{j\geq0}\frac{(-1)^j(j+1)}{(2j+2)!}u^{2j+2}z^j.}
\]

É uma identidade de séries formais. Em cada coeficiente há uma soma finita, sem intercâmbio de integrais com uma soma infinita. Se \(v_k=[z^k]V\) e \(D_j(u)=(-1)^j(j+1)u^{2j+2}/(2j+2)!\), isso equivale a

\[
P_n=\frac1{c_0}\sum_{k=0}^n v_kD_{n-k},\qquad
\mathscr LP_n=\frac1{c_0}\sum_{k=0}^n v_k\mathscr LD_{n-k}.
\]

Logo, há uma regra uniforme que transporta a válvula pelo cálculo de Green. Nenhum sinal dos coeficientes da válvula foi suposto. Massa formal, completude da reconstrução e positividade métrica são obrigações distintas.

Conferimos também cinco interfaces existentes, incluídas na auditoria desta investigação:

| Interface | O que fornece | Limite atual |
|---|---|---|
| `TfvdBoundaryCompletedTransport` | Análise em bracket ponderado e traço de duas coordenadas; síntese Green + retorno recompõe o estado inteiro. | A reconstrução não identifica por si só o produto interno com a forma da fonte. |
| `NativeMomentProjectiveValveBridge` | Massa da válvula igual ao recíproco da característica normalizada. | Identidade escalar formal; não é certificado de Gram. |
| `ProjectiveValveFirstColumnMomentGate` | Se o transporte polarizado interior de um candidato já foi provado, a igualdade do kernel reduz-se à calibração da primeira coluna. | A coluna e o transporte precisam vir do candidato; não são consequências automáticas do readout. |
| `CompletedNativeCameraTfvdGreenFrameDefectCrosswalk` | O Gram bruto da incidência projetiva já difere do momento nativo na entrada zero. | Exclui essa identificação literal; não exclui a realização completa com retorno e correções. |
| `CompletedNativePolarizedTfvdGreenMomentKernel` | Ledger com proveniência Green, cruzamentos, residual de readout e completação; equivalência exata com o defeito limite pertinente. | A convergência a zero do defeito não está provada em geral. |

A válvula formal mencionada acima não deve ser confundida com a realização projetiva quiral em dois canais. Esta última fornece uma forma assinada, diferença entre dois produtos internos; sua positividade geral continua ligada à contratividade do multiplicador correspondente. Nenhuma dessas condições foi introduzida como premissa nova.

O uso produtivo do TFVD é preservar bracket **e** traço durante a construção de uma identidade polarizada que compare o estado reconstruído com a fonte. Ainda falta um transporte concreto entre esses dados vetoriais e o kernel que representa a energia nativa. Não foi identificada a variável contínua u com o índice vertical, nem o parâmetro formal da válvula com uma altura espectral.

O próximo ataque fica mais delimitado: procurar uma identidade polarizada, derivada do estado TFVD completado e compatível com a válvula, que controle os defeitos restantes e reproduza as relações não lineares dos momentos theta. Qualquer candidato deve passar primeiro pelo centro e pelos termos fora da diagonal. A transferência diferencial simples já foi testada e preserva densidades assinadas; não basta repeti-la para declarar positividade.

Os novos módulos são `NativeSourceThetaGreenTransport.lean`, `NativeSourceThetaProjectiveValve.lean` e `NativeSourceThetaGreenValveAudit.lean`. Não houve nova quadratura externa nesta etapa. Validação em `llm`: compilação dirigida dos dois módulos de produção com `--wfail` concluída em 9.834 tarefas; módulo de auditoria dedicado, raiz e auditoria global concluídos em 10.351 tarefas. As 36 declarações públicas novas passaram pelo bloqueio fundacional, com 5.886 dependências de tipos e corpos. Cinco raízes das interfaces existentes também passaram, com 6.233 dependências. A auditoria inclui `#print axioms`: somente as fundações usuais `propext`, `Classical.choice` e `Quot.sound`, sem axiomas de pesquisa novos ou provas admitidas. `git diff --check` também passou. Os dados da publicação acompanham a entrega final.
