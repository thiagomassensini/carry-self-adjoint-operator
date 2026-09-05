# O estado que continua observável quando o carry evolui

Pesquisa de 2026-09-05. Base de código: `3674c8feeb0e2b2ef26afe6a0cd9df786ce790fe`.

## Leitura da teoria

A estrutura que reaparece nas notas é um estado reconstruível, com bordo,
evolução e leituras em diferentes cartas. A resultante escalar é uma dessas
leituras. Seu cancelamento não apaga automaticamente o estado nem sua energia.
Essa interpretação é compatível com os resultados existentes de reconstrução
por curvatura e dados iniciais, com a válvula multiplicativa e com os exemplos
recentes de direções invisíveis ao retorno misto.

Uma pergunta surge antes de escolher uma métrica: **quais direções permanecem
invisíveis quando o próprio estado evolui?** A presente construção segue essa
pergunta. Não toma os zeros desejados como dados e não escolhe uma energia para
ajustar os momentos. O procedimento algébrico é a observabilidade usual de um
sistema linear; não se reivindica novidade desse conceito na literatura.

## O que os resultados anteriores permitem distinguir

| Construção | Informação que fornece |
| --- | --- |
| Carry, profundidade e massa | Geometria e pesos de partida; a amplitude L² é a raiz da massa |
| Reconstrução discreta | A curvatura, acompanhada dos dois dados iniciais, determina o estado |
| Válvula formal | A curvatura determina uma massa multiplicativa normalizada |
| Atlas e completação | A leitura escalar nativa pode ser comparada entre câmeras |
| Retorno e trace C3 | Leituras diferentes perdem direções diferentes |
| Gram/Hankel/Jacobi | Uma realização positiva exige identificar a forma correta com os momentos nativos |

A existência de uma norma positiva no carrier não identifica essa norma com
o defeito nativo. O no-go do Gamma bruto permanece válido. A presente pesquisa
também não transforma a identidade escalar da válvula em uma representação
de Gram dos momentos.

## A construção algébrica

Sejam um espaço vetorial X, um endomorfismo L e uma leitura linear Q. Defina

\[
U=\bigcap_{k\geq0}\ker(QL^k),\qquad X_{\mathrm{obs}}=X/U.
\]

U é o maior subespaço L-invariante contido em ker Q. Por isso tanto L quanto
Q passam ao quociente. Além disso,

\[
U=\ker Q\quad\Longleftrightarrow\quad L(\ker Q)\subseteq\ker Q.
\]

Essa equivalência explicita quando é lícito esquecer tudo que uma leitura
instantânea não vê, mantendo uma evolução bem definida. No caso geral, é
necessário conservar parte dessa informação para prever leituras posteriores.

Esse estado observável é relativo ao par (L,Q). Ele não redefine o zero nativo
nem identifica o estado completo com sua resultante. Uma direção descartada
pelo quociente pode continuar tendo energia no espaço original. A escolha de
um atlas conjunto de leituras, e de uma eventual norma no quociente, exige
informação adicional.

`ObservableJetQuotient.lean` contém a definição, a maximalidade, a invariância
e os mapas induzidos. Tudo é algébrico sobre um domínio invariante fornecido.
Para um gerador ilimitado, a escolha desse domínio e o controle analítico
continuam sendo questões separadas. Não se afirma que todos os jets nulos
impliquem uma função identicamente nula sem hipótese de analiticidade.

## O cálculo que motivou a construção: nós 2, 3, 4

Considere variações nodais x=(δf₂,δf₃,δf₄), mantendo δf₁=0. As coordenadas de
gradiente e sua reconstrução são

\[
g=(x_0,x_1-x_0,x_2-x_1),\qquad
x=(g_0,g_0+g_1,g_0+g_1+g_2).
\]

O relógio material é D=diag(a,b,c), com a=log 2, b=log 3, c=log 4.
Transportá-lo para os gradientes produz exatamente

\[
L_g=\begin{pmatrix}
a&0&0\\
b-a&b&0\\
c-b&c-b&c
\end{pmatrix}.
\]

O trace de variação que aparece na cabeça C3 de cutoff 1 é
Q(g)=g₂−g₁=x₀−2x₁+x₂. Para o pulso g=(u,0,0),

\[
Q(g)=0,\qquad Q(L_gg)=(a-2b+c)u=\log(8/9)u.
\]

Logo, se u≠0, esse pulso é invisível ao valor, mas visível ao primeiro
log-jet consistente com o mesmo estado. A prova do sinal usa log 8 < log 9,
sem tolerância numérica. Na evolução em altura, os fatores −i das derivadas
apenas multiplicam as leituras por escalares não nulos.

Há um resultado finito mais forte. As três leituras Q, QD, QD² nas coordenadas
nodais separam todos os estados desse bloco. A matriz de observação tem linhas

\[
(1,-2,1),\quad(a,-2b,c),\quad(a^2,-2b^2,c^2),
\]

e determinante −2(b−a)(c−a)(c−b). A implementação Lean usa identidades de
reconstrução sem divisões; o teste Python verifica também o determinante.
Assim, conhecer o valor e os dois primeiros log-jets basta para recuperar
as três variações nodais. Isso é um resultado de dimensão três, não uma
afirmação de recuperação do estado infinito por três números.

Como corolário matemático, esse cálculo identifica o subespaço invisível
da construção geral: nesse bloco, U={0}. Esquecer as direções apagadas apenas pelo valor
perderia informação que os jets subsequentes recuperam.

## A ligação com as definições nativas e o papel do bordo

No código existente, fₙ=(n+1)^(−s), gₙ=fₙ₊₁−fₙ e
ℓₙ=log(n+2)fₙ₊₁−log(n+1)fₙ. Os três primeiros gradientes nativos satisfazem

\[
(\ell_0,\ell_1,\ell_2)
=L_g(g_0,g_1,g_2)+f_0(a,b-a,c-b).
\]

Aqui f₀ é a entrada material de índice 1, o dado inicial. Portanto, no estado
nativo, valor e log-jet vivem num **grafo afim com bordo**, e não são duas
escolhas independentes. A identidade é escrita diretamente com
`positiveDirichletGradient` e `positiveLogDirichletGradient` em
`C3NativeTraceDynamics.lean`.

Os testes anteriores no carrier ambiente ordinary ⊕ log continuam corretos:
é possível variar o canal ordinary mantendo o canal log fixo naquele espaço.
O novo cálculo mostra o que acontece quando se exige que os dois canais
provenham do mesmo estado nodal. Não é apresentado um segundo estado da família
canônica de Dirichlet com a mesma cauda, nem se elimina o contraexemplo canônico
à identificação do Gamma. Uma restrição de proveniência muda quais variações
são admissíveis; ela não muda o valor do Gamma na família original.

## O que segue naturalmente, ainda sem teorema analítico global

A direção sugerida por esta leitura é estudar juntos o estado causal, seus
dados de bordo, o relógio material e o conjunto de leituras compatíveis entre
câmeras. O quociente observável registra a informação indispensável à evolução
das leituras. Depois disso se pode perguntar quais formas de Green, normas e
completações são compatíveis com esse objeto.

Isso continua duas peças já presentes. O dossiê
`carry-geometric-graph-investigation.md` preserva duas leituras para reparar
uma perda de proveniência num pequeno módulo livre; a nota do coequalizador
J/H verifica a descida de um operador que atua num fator tensorial diferente.
Aqui a segunda leitura não é acrescentada livremente: ela é QL, imposta pelo
relógio do mesmo estado C3. A independência de famílias de jets por Vandermonde
também já aparece em `CompletedNativeTfvdCoefficientJets.lean`. O cálculo
presente a aplica a uma leitura C3 concreta e explicita seu quociente observável.

No caso infinito, a sequência logarítmica exige domínio, convergência e caudas.
No caso multibase, é preciso verificar que as mudanças de câmera transportam
também os jets e o bordo. Uma realização positiva dos momentos nativos exige
uma identidade adicional com esses momentos. Nenhuma dessas conclusões é
assumida nas proposições novas.

## Proveniência e validação

A leitura desta sessão cobriu os 16 anexos fornecidos e consultou diretamente
os módulos e notas pertinentes nos repositórios. O inventário do autoadjunto
na base acima contém 73 arquivos Markdown. Não se afirma leitura integral de
todas as centenas de notas originais e ZIPs mencionados pelos mapas; os anexos
incluem auditorias desse acervo, mas não são o acervo inteiro.

Os nomes e hashes SHA-256 dos 16 anexos constam de
`research/observable-jet-2026-09-05/source_manifest.json`.

Fontes especialmente relevantes no repositório:

- `docs/causal-bracket-state-uniqueness.md`;
- `docs/discrete-projective-reconstruction.md`;
- `docs/c3-projective-hilbert-readout-kernel.md`;
- `CarrySelfAdjointOperator/NativeLogEvolution.lean`;
- `CarrySelfAdjointOperator/CompletedNativeTfvdCoefficientJets.lean`;
- `CarrySelfAdjointOperator/C3ReturnCompletedTraceChannels.lean`;
- `CarrySelfAdjointOperator/CompletedC3DirichletGradientBracketSource.lean`;
- `CPFormal/Analytic/CpFiniteLogJetCommutator.lean` no crosswalk.

O script `research/observable-jet-2026-09-05/exact_check.py` verifica 11
identidades por aritmética polinomial racional exata e grava `exact_check.json`.
Ele não valida a elaboração ou o kernel Lean. Não há toolchain Lean instalada
no ambiente local desta sessão. Os arquivos Lean são submetidos ao workflow
existente do repositório, com `--wfail` e impressão dos axiomas dos resultados
centrais via `ObservableJetAudit`. Até haver uma execução bem-sucedida desse
workflow, a formalização deve ser tratada como proposta pendente de compilação.

Há ainda um workflow separado, `Observable jet core audit`, que compila
`ObservableJetCoreAudit` para dar retorno rápido sobre os dois módulos
algébricos e depois compila `ObservableJetAudit`, incluindo a integração com
as definições nativas. Essa integração importa diretamente o módulo CPFormal
que fornece os gradientes, sem puxar toda a cadeia do autoadjunto. O workflow
completo do repositório continua verificando a integração da biblioteca inteira.
