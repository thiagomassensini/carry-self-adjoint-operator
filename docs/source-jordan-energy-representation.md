# Representação da energia a partir da fonte: canais de Jordan e limite físico

## Resultado e limite da investigação

Construímos dois canais físicos a partir do **retorno original da fonte**, sem escolher momentos positivos nem uma medida nova. Eles vivem no mesmo `L²([0,1], volume)` usado pelo carrier de Cauchy. Sua diferença recupera a energia original, inclusive os pareamentos entre inputs independentes.

Isso **não prova a positividade geral**. A separação de Jordan existe para qualquer defeito autoadjunto; sua existência não explica o sinal. O avanço é uma construção explícita e auditável dos canais e um alvo geométrico suficiente: eliminar o canal negativo nos jets da fonte e obter limites físicos coerentes para o positivo.

Também há uma restrição nova sobre uma candidata específica: o carrier de cada vetor comprimido `U_n` tem dimensão complexa 24. Um mapa complexo-linear fixo aplicado individualmente a esses vetores não pode produzir 25 colunas independentes. Essa restrição não se aplica à fonte infinita ou à torre inteira de jets considerada como um estado infinito.

## 1. Construção sem supor o sinal

Seja `T = radialReturnTransfer k N` o retorno finito já construído com os inputs incidentes originais, sua métrica herdada e a fonte completada. No seu domínio finito de Hilbert, definimos

\[
D=I-T^*T,\qquad D_+=\max(D,0),\qquad D_-=\max(-D,0).
\]

O cálculo funcional contínuo fornece

\[
D=D_+-D_-,\qquad P_+=\iota\sqrt{D_+},\qquad P_-=\iota\sqrt{D_-},
\]

onde `ι` é a inclusão do span incidente no `L²` físico original. A medida é o volume do intervalo unitário, já presente na definição do carrier. Nenhum Gram de momentos desejado define esses mapas.

Para quaisquer inputs independentes `u,v`, a identidade formalizada é

\[
\langle P_+u,P_+v\rangle-\langle P_-u,P_-v\rangle
=\langle u,v\rangle-\langle Tu,Tv\rangle.
\]

Portanto, para a síntese incidente original `I(c)`,

\[
\operatorname{Re}\mathrm{storage}(c,1)
=\|P_+I(c)\|^2-\|P_-I(c)\|^2.
\]

Todos os cruzamentos permanecem nessa identidade polarizada. Não substituímos a diferença pela soma nem descartamos a parcela negativa.

Declarações centrais em `CompletedNativeChiralReturnEnergyPort.lean`:

- `radialReturnDefect_jordan`;
- `radialReturnJordanPorts_pairing`;
- `radialReturnJordanPorts_storage`.

Sob uma contração já demonstrada independentemente, `P_- = 0` e `P_+` coincide com o porto de energia anterior. Sem contração, a raiz do defeito bruto anterior não deve ser confundida com a raiz da sua parte positiva.

## 2. O que zerar o canal negativo significa

O teorema `radialReturnJordanNegativePort_zero_iff_contractive` prova

\[
P_-=0\quad\Longleftrightarrow\quad\|T\|\leq1.
\]

Logo, anular o porto inteiro em cada dimensão finita apenas reformula a estimativa original. Isso impede apresentar a decomposição como solução automática da positividade.

Há, porém, uma condição suficiente para a energia de borda que não exige essa contração em cada etapa finita: a energia negativa desaparecer **nos estados efetivamente produzidos pelos jets** quando o parâmetro da fonte tende ao limite.

O setor de sete fontes é um teste de compatibilidade: pela contração já formalizada para esse setor, `radialReturnJordanNegativePort_seven_eventually_zero` mostra que o porto negativo inteiro é eventualmente nulo. Nenhuma estimativa nova para oito ou para todas as ordens é deduzida desse caso.

## 3. Transporte da fonte inteira ao limite

Para ordem par `2n`, escrevemos `J_(n,k)x` para a síntese incidente do input `nativeSourceChiralJetInput n k x`. É o chart original da fonte inteira, anterior ao readout escalar. Definimos

\[
v^\pm_{n,k}(x)=P^\pm_{k,2n}J_{n,k}x.
\]

O teorema **incondicional** `nativeSourceJordan_signed_energy_tendsto` prova

\[
E_{2n}(x)=\lim_{k\to\infty}
2\bigl(\|v^+_{n,k}(x)\|^2-\|v^-_{n,k}(x)\|^2\bigr).
\]

O fator 2 é a normalização já existente do transporte da fonte à borda; ele não foi ajustado para fabricar o sinal.

Se demonstrarmos

\[
\|v^-_{n,k}(x)\|\longrightarrow0,
\]

então a energia positiva tende a `E_(2n)(x)`, o que implica sua não negatividade. Essa implicação está formalizada; **a condição de desaparecimento não está demonstrada em ordem geral**.

Basta demonstrar o desaparecimento nas colunas da base, para cada dimensão fixa: a síntese linear já formalizada transporta esse controle para todos os inputs e preserva os cruzamentos. Na versão polarizada dos jets, o produto interno de duas colunas negativas tende a zero se suas normas tendem a zero; o Gram positivo então tende aos coeficientes nativos canônicos sem uma hipótese de contração em cada etapa finita.

## 4. Uma única família de funções para qualquer N

A formulação forte solicitada pelo usuário requer mais que convergência de números ou de Grams. Considere **uma única família física** `phi : ℕ → L²([0,1])`. As hipóteses explícitas são, para cada `n` e `i < 2n`,

\[
v^+_{n,k}(e_i)\longrightarrow\phi_i
\quad\text{fortemente no mesmo }L^2,
\qquad
\|v^-_{n,k}(e_i)\|\longrightarrow0.
\]

A família `phi_i` é independente da dimensão. A compatibilidade entre prefixos é parte da hipótese, não uma conclusão extraída de Grams finitos.

Sob essas hipóteses, `nativeSourceBoundary_integral_all_N_of_coherent_columns` prova, **para todo N**, inclusive ímpar,

\[
E_N(x)=2\int_{[0,1]}
\left|\sum_{j<N}x_j\phi_j(t)\right|^2\,dt.
\]

Ordens ímpares são transportadas pela identidade exata de extensão por uma coordenada final zero, também formalizada. A avaliação do vetor soma é entendida como uma função de `L²`, definida quase em toda parte. Não se pressupõe uma avaliação pontual canônica para cada representante.

A forma do pedido, sem o fator externo 2, resulta de escrever `psi_j = sqrt(2) phi_j`; essa é uma mudança explícita de notação das features da representação, não uma mudança da energia ou dos inputs originais. A formalização mantém o fator 2 visível.

**O que falta:** construir/provar esses limites coerentes a partir da fonte. Não demonstramos a existência dessa família, nem afirmamos que esta escolha de ports necessariamente admita convergência forte. Convergência de Grams não basta para impedir escape ou oscilação dos vetores no carrier físico. Trata-se de um caminho suficiente, ainda aberto; uma realização positiva abstrata não resolve essa exigência de proveniência.

Para positividade estrita falta também não colapso: para `x ≠ 0`, a síntese física limite deve ser não nula. O teorema `nativeSourceBoundary_pos_of_state_limits` mantém essa hipótese visível.

## 5. Por que o readout de U_n não identifica uma energia de todas as ordens

O levantamento `primeDepthNormalizedResponseVectorJet n` preserva quatro rótulos de setores, mas cada setor já foi comprimido a três pares complexos de traços:

\[
\dim_{\mathbb C}(\text{FullWronskianTrace})=6,
\qquad \dim_{\mathbb C}(\text{CompletedPrimeDepthJetCarrier})=4\cdot6=24.
\]

Para qualquer espaço complexo `H`, inclusive infinito, e qualquer mapa complexo-linear fixo `A` desse carrier para `H`, existem coeficientes complexos `c_0,...,c_24`, não todos nulos, tais que

\[
\sum_{j<25}c_j A(U_j)=0.
\]

Isso foi provado sem assumir sinal de momentos ou igualdade com um Gram. Consequentemente, essa candidata não pode representar uma energia **estritamente** positiva em todas as combinações complexas não nulas. O teorema não exclui uma energia semidefinida nem demonstra que a energia nativa tenha posto infinito.

O resultado de readout `ell(U_n)=h_n` continua válido em todas as ordens. Ele não fornece produtos internos: infinitos valores escalares podem ser obtidos de uma sequência de vetores em um espaço finito.

A restrição vale apenas para aplicar **o mesmo mapa linear a cada vetor comprimido individual**. Ela não impede trabalhar com o estado da fonte antes da compressão, com a torre de jets inteira em um carrier infinito, ou com uma construção que não tenha essa forma.

## 6. Próximo alvo matemático preciso

1. Estimar a parte negativa do defeito original nos inputs do chart da fonte, por exemplo `⟨Jx, D_- Jx⟩`, até provar que tende a zero. A igualdade com a norma do canal negativo já está disponível.
2. Controlar a família positiva no `L²` original para obter limites vetoriais e compatibilidade entre dimensões. Não substituir essa etapa por uma fatoração do Gram alvo.
3. Provar injetividade da síntese limite se o objetivo for positividade estrita.

O fluxo de Euler local já tem exemplos de sinal negativo no repositório, mesmo em um setor com storage integrado não negativo. Portanto não basta declará-lo uma densidade positiva. As identidades de borda, retorno e correção continuam necessárias.

Não foi provada nesta investigação a identificação com um operador autoadjunto global de alturas, uma medida espectral de alturas, positividade em todas as ordens ou qualquer consequência sobre RH.

## Arquivos de implementação

- `CarrySelfAdjointOperator/CompletedNativeChiralReturnEnergyPort.lean`: dois canais do defeito original e identidade polarizada incondicional.
- `CarrySelfAdjointOperator/CompletedNativeChiralReturnJordanEnergy.lean`: transporte à borda, condição de desaparecimento, limites físicos e representação integral condicional para todo N.
- `CarrySelfAdjointOperator/PrimeDepthEnergyCarrierRank.lean`: dimensão 24 e restrição da transformação linear fixa dos vetores comprimidos.
- `CarrySelfAdjointOperator/SourceJordanEnergyAudit.lean`: assinaturas, axiomas e fechamento transitivo de dependências de todas as novas declarações públicas.

## Validação Lean desta alteração

- `lake build --wfail CarrySelfAdjointOperator.SourceJordanEnergyAudit`: passou, 9.828 jobs; 41 novas raízes públicas, fechamento de 7.029 dependências e guarda axiomática aprovada.
- `lake build --wfail`: passou, 10.187 jobs.
- `lake build --wfail CarrySelfAdjointOperator.Audit`: passou, 10.327 jobs.
- A auditoria das novas raízes admite somente os fundamentos usuais `propext`, `Classical.choice`, `Quot.sound`. Nenhum `sorry`, `admit` ou axioma novo foi adicionado às fontes de prova tocadas.
- `git diff --check` passou. Os dois arquivos C2 preexistentes e `lake-manifest.json` conservaram os hashes iniciais.

Esses comandos validam as identidades e as implicações condicionais descritas acima; não validam como verdadeiras as hipóteses matemáticas ainda abertas. Nenhuma nova varredura numérica de pivôs foi feita nesta investigação.
