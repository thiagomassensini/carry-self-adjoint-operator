# Mapa das notas — energia de retorno, modo misto e momentos nativos

**Data:** 4 de setembro de 2026. **Objetivo:** recuperar nas notas de Downloads mecanismos e derivações que possam alimentar as obrigações do `carry-self-adjoint-operator`, confrontando cada pendência histórica com os fontes atuais.

## 1. O que mudou com este garimpo

**As notas acrescentam mecanismos concretos e corrigem a avaliação anterior de duas rotas.**

1. **Métrica de retorno:** a igualdade finita que conserva a energia e suas covariâncias já tem declarações no Weyl. O kernel com dois resolventes é uma consequência algébrica precisa; o trabalho restante é especializá-lo ao readout e aos parâmetros nativos corretos. A passagem ao limite precisa respeitar os tipos/dimensões que variam com o cutoff.
2. **Modo misto 3–4–6:** a mudança para um observável limitado já aparece nas notas. Ela produz momentos limitados, em particular de crescimento no máximo exponencial e permite construir explicitamente os dois blocos de Gram exigidos pela forma da rota HP. O argumento antigo “os momentos crescem fatorialmente” continua correto na variável logarítmica, mas não exclui essa realização transportada.
3. **Cumulantes e bordo:** o documento estendido tem fórmulas ausentes nas cópias resumidas: transporte covariante em altura antes da redução de razões, canais somáveis por diferenças e reformulação da exigência de contração. Outras notas fornecem a métrica matricial dos dois traços e uma fórmula explícita de correção de bordo com residual comprimido.

**A identificação com a sequência nativa ainda precisa ser demonstrada.** O ganho desta rodada é tornar a próxima tentativa mais concreta: agora existem fórmulas candidatas para a métrica, para o retorno e para um estado positivo com ambas as paridades. A igualdade de readout com `−F′/(2F)` permanece localizada; nenhum aviso histórico foi usado como substituto dessa verificação.

### Convenções de status

- **Fonte Lean:** declaração e hipóteses conferidas no snapshot indicado. Uma implicação formalizada não significa que sua hipótese foi construída.
- **Derivação da nota:** argumento matemático presente no documento; os rótulos históricos “fechado” ou “proved” não foram convertidos automaticamente em auditoria Lean.
- **Dedução verificada nesta rodada:** consequência algébrica ou analítica explicitada aqui, distinguida de uma declaração já existente.
- **Evidência numérica:** cálculo finito/experimental; seu alcance é o cálculo executado.
- **Pendente de identificação:** os objetos de origem e destino estão escritos, mas a igualdade necessária ainda não foi localizada/provada.

Um resultado negativo demonstrado para uma escolha específica continua informativo nessa escolha. Uma construção posterior pode mudar o carrier, a variável, a métrica ou o domínio e sair daquele escopo. Foi esse critério, e não o título “no-go” ou “firewall”, que orientou a triagem.

## 2. Cobertura e como localizar as versões

O inventário inicial percorreu Downloads recursivamente e encontrou **564 arquivos `.md`/`.txt`**, com **409 conteúdos distintos byte a byte** e **116 grupos de cópias exatas**. A leitura de **562 entradas textuais em ZIPs encontrados no disco** recuperou **200 conteúdos distintos adicionais**, cerca de 1,67 MB. Houve busca textual nesse corpus, seguida de leitura dirigida das notas matemáticas relevantes e suas versões/remissões. Esses números medem a triagem, não uma revisão matemática linha a linha de todos os documentos.

Os links absolutos de Downloads apontam para o notebook; os links relativos conectam o mapa aos dossiês. Os inventários preservam os caminhos, tamanhos e hashes:

- [Inventário dos documentos soltos](</home/thlinux/Downloads/Garimpo_notas_carry_2026-09-04/inventario_documentos.csv>).
- [Inventário de notas nos ZIPs](</home/thlinux/Downloads/Garimpo_notas_carry_2026-09-04/inventario_notas_em_zip.csv>).
- [Origem das cópias recuperadas](</home/thlinux/Downloads/Garimpo_notas_carry_2026-09-04/proveniencia_recuperacoes.json>).

Notas originais e ZIPs foram preservados. PDFs receberam apenas triagem de títulos/resumos quando pertinente; documentos pessoais sem relação com a teoria não foram usados. Não foi feita extração recursiva de arquivos ZIP contidos dentro de outros ZIPs. As referências matemáticas centrais deste mapa são textuais.

**Pontos importantes de versão:**

| Família | O que a comparação mostrou | Como usar |
| --- | --- | --- |
| Registros de sondas | O PT na raiz, a cópia de `hp` e a de `Wayl` têm comprimentos/conteúdos diferentes; as últimas têm material adicional sobre a Weyl de alturas. | Usar as seções e versões apontadas no dossiê de retorno; não deduplicar somente pelo título. |
| Cumulantes Mellin | As cópias soltas de `DEFEITO_GREEN_CUMULANTES_MELLIN` têm 353 linhas; a versão em `teoria_defeitos_pack` tem 2.142 linhas. | Priorizar a versão estendida e ler as correções posteriores da mesma nota. |
| Geradora das câmeras | A expressão equivocada do resumo dos registros tem uma versão correta em `CONVERGENCIA_FUNCIONAL_DEFECT_PROBES_POVM`. | Registrar a correção com as duas fontes, sem atribuí-la a uma conjectura nova. |
| Notas antigas de agosto sobre jets e ordem Jacobi | Parte das tarefas sugeridas já possui fontes no autoadjunto atual, incluindo compatibilidade da torre e limite do Gram C3 bruto. | Reutilizar esses teoremas sob suas hipóteses; concentrar trabalho na identificação métrica restante. |

A referência formal continua sendo o [mapa dos repositórios](</home/thlinux/Downloads/Mapa_garimpo_repositorios_obrigacoes_carry_2026-09-04.md>). O workspace foi conferido em `b39f4e7643d81295201626430dab15dd55da7c31`, branch `agent/projective-valve-moment-frontier`; seus fontes Lean são os da tentativa já registrada, e esta rodada não alterou dependências nem recompilou as bibliotecas.

## 3. Alvo que organiza a leitura

Se

$$
F(t)=\texttt{completedNativeOperatorCharacteristic}(t),\qquad
F(t)=F(0)\Phi(t^2),\qquad
Q_{\rm nat}(u)=-\frac{\Phi'(u)}{\Phi(u)},
$$

então, perto da origem,

$$
a(t)=-\frac{F'(t)}{2F(t)}=tQ_{\rm nat}(t^2),\qquad
Q_{\rm nat}(u)=\sum_{k\ge0}h_ku^k.
$$

A rota vetorial quer o Gram `dslope a` de duas alturas reais regulares; os jets fornecem

$$
G_N=(h_{i+j})_{i,j<N},\qquad K_N=(h_{i+j+1})_{i,j<N}.
$$

Na especialização do estado C3 ordinário/logarítmico/residual, o construtor `completedNativeRealHPCarrierCertificate_of_concreteC3Sewing` recebe a costura concreta e dela deriva o kernel; `completedNativeRealHPCarrierCertificate_of_concreteC3Kernel` recebe esse kernel diretamente. Ambos produzem o certificado com independência das duas paridades. Para outro estado positivo recuperado das notas, é preciso demonstrar a identidade com `Q_nat`/`h` e usar seus próprios jets/readouts. Fonte: [CompletedNativeTfvdCoefficientJetHPCarrier.lean:665–703](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/b39f4e7643d81295201626430dab15dd55da7c31/CarrySelfAdjointOperator/CompletedNativeTfvdCoefficientJetHPCarrier.lean#L665-L703).

A rota projetiva alternativa continua sendo:

$$
c(p,0)=\operatorname{oddMomentResponseCoefficient}(h,p+1),\qquad
c(p,q+1)=c(p+1,q).
$$

Sua construção do certificado exige também mapa injetivo, base suportada e raio admissível. A busca nas notas procurou fórmulas capazes de alimentar essas igualdades, além de resultados de positividade de outros Grams.

## 4. Inventário das peças recuperadas


O detalhamento está dividido em três dossiês, com equações, hipóteses, versões, hashes e referências formais:

- [1 — Retorno, sondas e Green em duas variáveis](garimpo-notas-2026-09-04/01_retorno_sondas.md).
- [2 — Modo misto, observável compacto e Vandermonde](garimpo-notas-2026-09-04/02_modo_misto_vandermonde.md).
- [3 — Cumulantes, traço TFVD, Möbius e residual](garimpo-notas-2026-09-04/03_cumulantes_bordo.md).

| Peça | Abrir primeiro | O que entrega | Ligação a fazer |
| --- | --- | --- | --- |
| N1. Retorno polarizado | [Unicidade das covariâncias, L149–270](</home/thlinux/Downloads/UNICIDADE_LIMITE_COVARIANCIA_DEFECT_PROBES.md:149>) e [transformada/POVM, L238–485](</home/thlinux/Downloads/TRANSFORMADA_CAUCHY_STIELTJES_POVM_E_WEYL_CAMERAS.md:238>) | Métrica de retorno que conserva todos os cruzamentos; resolvente comprimido. | Identificar fonte, observável, sinal e parâmetro com a resposta nativa completada. |
| N2. Modo misto positivo | [Ponte C2 → tau/sigma, L29–59](</home/thlinux/Downloads/Ponte C2 pushforward → tau-sigma do modo misto.md:29>) e [medida original, L12–81](</home/thlinux/Downloads/REALIZACAO_JACOBI_COMPLETA_MODO_MISTO_3_4_6.md:12>) | Densidade positiva; dois Hankels estritos em toda ordem. Na variável compacta, estado explícito com kernel da forma desejada. | Determinar o observável/readout nativo; provar a igualdade de séries ou a recorrência concreta. |
| N3. Fonte geométrica do modo | [Primitive → spectral, L118–200](</home/thlinux/Downloads/NATIVE_CARRY_PRIMITIVE_TO_SPECTRAL_BRIDGE_AUDIT.md:118>) | Massas por projeção da geometria branqueada; comparação numérica de cutoffs com a densidade 3–4–6. | Recuperar/formalizar a identidade e o limite desse projetor; a seção citada é evidência numérica. |
| N4. Métrica dos dois traços | [Derivações exatas V2, L276–336](</home/thlinux/Downloads/PRIMOS_TFVD_HILBERT_COVARIANT_MASS_GAP_DEEP_DIVE_V2/DERIVACOES_EXATAS.md:276>) | Matriz positiva $M_q$ e Gram completo da análise bracket+traço. | Transportar a métrica ao estado completado e preservar os cruzamentos da síntese. |
| N5. Bordo visível e oculto | [Canal oculto, L499–620](</home/thlinux/Downloads/RELATORIO_CANAL_OCULTO_GREEN_NAIMARK_MOBIUS.md:499>) | Decomposição exata $D=\Psi_0^*\Gamma-\Gamma^*\Psi_0+QDQ$. | Instanciar os mesmos mapas e comparar $QDQ$ com os defeitos concretos do autoadjunto. |
| N6. Cumulante vestido | [Teoria C2, L277–442](</home/thlinux/Downloads/teoria_defeitos_c2_unificada.md:277>) e [teorema geral](</home/thlinux/Downloads/teoria_de_defeitos/teoria_defeitos_pack/09_teorema_geral_cumulantes.md:1>) | Equação deconvolutiva e recorrência triangular; partes já formalizadas em CPFormal. | Calcular a coluna inicial com a completação correta e verificar a recorrência nativa. |
| N7. Altura e cauda covariantes | [Mellin extenso, §§39–40, L1663–1803](</home/thlinux/Downloads/teoria_de_defeitos/teoria_defeitos_pack/DEFEITO_GREEN_CUMULANTES_MELLIN.md:1663>) | Transporte de fase antes da redução por gcd; três canais por diferenças com energia somável. | Alinhar os pesos e os canais da nota aos estados efetivos; provar o limite no mesmo carrier. |
| N8. Gram aritmético residual | [Möbius log-clock, L259–473](</home/thlinux/Downloads/MOBIUS_LOG_CLOCK_CONNECTED_DRESSING_THEOREM.md:259>) | Funções-cauda de Möbius, positividade e independência por suporte. | Construir o mapa dos índices de câmera/cofator para os jets nativos. |
| N9. Independência/Vandermonde | [Dressing por resultantes, L25–154](</home/thlinux/Downloads/Dressing de Vandermonde por resultantes e operadores de criação vestidos.md:25>) | Fatoração dos cruzamentos entre cores e integral de determinantes. | Transportar a medida correta; tratar o domínio do adjunto e corrigir o rank do defeito. |
| N10. Molécula completa de bordo | [Relatório Haar recuperado do ZIP, L53–108](</home/thlinux/Downloads/Garimpo_notas_carry_2026-09-04/notas_recuperadas/07e235b0a923_C2_GREEN_HAAR_RIGGED_VECTOR_PORT_REPORT.md>) | Cancelamento dos dois primeiros momentos e norma molecular que retém quatro cantos. | Identificar o fluxo completo e os pesos; a convergência escrita não constrói sozinha a porta nativa. |

## 5. A primeira rota: retorno → readout → kernel nativo

Com $L=L^*$, $PE=D$ e $E^*E+D^*D=I$, temos

$$
G_E=I+P^*P,\qquad E^*G_EE=I.
$$

Para $R_z=(zI-L)^{-1}$, $S(z)=CR_zE^*$ e $B(z)=CR_zC^*$, com os mapas fixos,

$$
S(z)G_ES(w)^*=CR_zR_w^*C^*,
$$

$$
(\bar w-z)S(z)G_ES(w)^*=B(z)-B(w)^*.
$$

**Essa forma sem divisão é a primeira candidata de lema.** Nos pontos reais do resolvente, a diagonal é $-B'(x)$; portanto, para fonte fixa $u$ e $b(z)=u^*B(z)u$, o sinal que coincide com a obrigação é

$$
\boxed{a(z)=-b(z)+c},\qquad c\in\mathbb R.
$$

As primeiras duas etapas algébricas já têm apoio formal, inclusive no pin consumido do Weyl:

- [ReturnMetric.lean:84–131](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/298d83c9351e308a5213b9f5ac32e44087f98a9f/NativeCarrySpectralWeyl/Finite/ReturnMetric.lean#L84-L131): `endpointMap_conjTranspose_mul_returnMetric_mul_endpointMap` e `returnMetricCovariance_eq_directResolventCovariance`.
- [FunctionalReturnMetric.lean:50–81](https://github.com/thiagomassensini/native-carry-spectral-weyl/blob/298d83c9351e308a5213b9f5ac32e44087f98a9f/NativeCarrySpectralWeyl/Finite/FunctionalReturnMetric.lean#L50-L81): `functionalReturnMetricCrossCovariance_eq_direct`, para observável arbitrário, sem comutação postulada.

O teorema atual de limite da covariância de retorno fixa tipos finitos de endpoint e bulk enquanto a janela espectral cresce. Para realizar literalmente as coligações das notas, deve-se usar tipos dependentes do cutoff, cancelar em cada corte e aplicar o limite direto já existente. Isso evita pedir uma isometria de dimensões arbitrariamente grandes para um espaço fixo. A convergência funcional analítica de grau arbitrário ainda não está fornecida por aquela API: o README do snapshot registra conclusão até grau oito. Os enunciados e as hipóteses estão transcritos no dossiê 1.

**O que procurar na próxima tentativa:** uma fórmula explícita para $C,E,P,L$, a fonte $u$ e o mapa de parâmetro. Se $u(t)$ ou $C(t)$ variar com a altura, os termos dessa variação precisam entrar na identidade; a conta acima com fonte fixa não os absorve. O limite normalizado de uma sonda em âncora fixa, que perde o parâmetro e entrega apenas $G_C$, também não é ainda o kernel em duas alturas.

Se o parâmetro do resolvente for $\lambda(t)$, a igualdade $a(t)=-b(\lambda(t))+c$ dá

$$
\operatorname{dslope}a(x,z)
=\operatorname{dslope}\lambda(x,z)\,K_{\rm res}(x,z).
$$

Para $\lambda(t)=\alpha t+\beta$, $\alpha>0$, basta multiplicar os vetores por $\sqrt\alpha$. Uma mudança não linear exige outra identidade ou fatoração, que ainda precisa ser demonstrada. Também é necessário provar que os parâmetros considerados pertencem ao resolvente geométrico: $F(t)\ne0$ sozinho não estabelece esse domínio comum.

A [ponte C2 → alturas, L142–208](</home/thlinux/Downloads/C2_DISCRETE_JACOBIAN_HEIGHT_JACOBI_BRIDGE.md:142>) explicita um readout escalar com os sinais conferidos:

$$
\frac{\xi'(w)}{\xi(w)}=A_\infty(w)-L_{\rm odd}(w)-\ell_2(w),
$$

$$
L_{\rm odd}=-Z_{\rm odd}'/Z_{\rm odd},\quad
\ell_2(w)=\frac{\log2\,2^{-w}}{1-2^{-w}},\quad
A_\infty=\frac1w+\frac1{w-1}-\frac12\log\pi+\frac12\psi(w/2).
$$

É uma localização concreta dos canais aritmético, local 2 e arquimediano. Sua aplicação ao fonte atual exige identificar a completação e a mudança $w=1/2+it$ com [CompletedOperatorCharacteristic.lean:29–41](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/b39f4e7643d81295201626430dab15dd55da7c31/CarrySelfAdjointOperator/CompletedOperatorCharacteristic.lean#L29-L41). A igualdade escalar escrita não é, por si, uma isometria dos estados.

## 6. A segunda rota: um estado positivo explícito para os dois Hankels

Na nota 3–4–6, $x\in(0,6]$, $\xi=\log(6/x)$ e $y=1+\log x$ são coordenadas distintas. Os momentos em $\xi$ crescem fatorialmente. Usando o observável **já recuperável da mesma medida**

$$
v=e^{-\xi}=x/6\in(0,1],
$$

obtemos

$$
d\rho_*(v)=\frac6{139}\left(33-8\mathbf1_{v\le2/3}-9\mathbf1_{v\le1/2}\right)dv,
$$

$$
m_k=\int v^k\,d\rho_*(v)
=\frac6{139(k+1)}\left[33-8(2/3)^{k+1}-9(1/2)^{k+1}\right].
$$

São **valores da transformada de Laplace nos inteiros**, não suas derivadas na origem: $m_0=1$, $m_1=979/1668$, $m_2=6373/15012$, e $0<m_k\le1$. A densidade é estritamente positiva em todo o intervalo. Portanto, para todo polinômio real não nulo, tanto $\int p^2d\rho_*$ quanto $\int vp^2d\rho_*$ são positivos; isso prova os dois Hankels em toda ordem, sem uma cota inferior uniforme em $N$.

**Dedução desta rodada:** para uma medida positiva finita $\rho$ em $[0,1]$, ponha

$$
Q_\rho(u)=\int\frac{d\rho(v)}{1-uv},\qquad a_\rho(t)=tQ_\rho(t^2),
$$

$$
\Psi_\rho(t)(v)=\left(\frac1{1-t^2v},\frac{t\sqrt v}{1-t^2v}\right)
\in L^2(\rho)\oplus L^2(\rho),\qquad |t|<1.
$$

Então, para alturas reais nesse intervalo,

$$
\boxed{\langle\Psi_\rho(x),\Psi_\rho(z)\rangle
=\frac{a_\rho(z)-a_\rho(x)}{z-x}},
$$

com valor $a_\rho'(x)$ na diagonal. A prova é integrar a identidade

$$
\frac{z/(1-z^2v)-x/(1-x^2v)}{z-x}
=\frac{1+xzv}{(1-x^2v)(1-z^2v)}.
$$

Os coeficientes vetoriais pares são $(v^i,0)$ e os ímpares $(0,\sqrt v\,v^i)$. Seus Grams são exatamente $m_{i+j}$ e $m_{i+j+1}$, e os cruzamentos entre paridades são zero. Para $\rho_*$, a positividade da densidade garante independência de ambas as famílias em toda ordem. Para uma medida geral de suporte finito, essa última afirmação não vale em todas as ordens.

Temos, assim, uma construção que reproduz a **forma exata** da obrigação em um intervalo. Falta identificar sua resposta com a característica concreta:

$$
\boxed{Q_\rho(u)=Q_{\rm nat}(u)=-\Phi'(u)/\Phi(u).}
$$

Para a medida crua $\rho_*$, o lado esquerdo é conhecido:

$$
Q_*(u)=\frac6{139u}\left[-33\log(1-u)+8\log(1-2u/3)+9\log(1-u/2)\right],
\quad Q_*(0)=1.
$$

Não foi encontrada uma prova de que esse readout cru seja o nativo. A geometria pode determinar outro observável, medida transportada ou estado com bordo. Uma igualdade local de séries pode servir à rota dos coeficientes e seus Grams; a interface que exige o kernel em **todos** os reais regulares precisa ainda de extensão apropriada. O estado local acima não foi apresentado como uma instância automática dessa interface global.

A curva $\Psi_\rho$ é uma **nova construção por cálculo funcional do observável**. O pushforward da medida está explícito; não foi demonstrado que ele transporte a curva C3/TFVD já fixada para essa nova curva. Uma identificação local de $Q_\rho$ com $Q_{\rm nat}$, acompanhada da independência, pode alimentar diretamente [CompletedNativeRealHPCarrierCertificate, L67–76](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/b39f4e7643d81295201626430dab15dd55da7c31/CarrySelfAdjointOperator/CompletedNativeHPGateAudit.lean#L67-L76) em outra realização de jets. Isso não provaria automaticamente a costura do estado C3 específico.

Antes de propor a igualdade literal para a medida crua, o primeiro teste é a ordem zero: $m_0=1$, enquanto $h_0=-a_1/a_0$, para $a_j$ os coeficientes pares da característica. Portanto ela já exigiria $a_1=-a_0$. Massa e escala devem ser determinadas pela construção; o modelo explícito não foi escolhido presumindo que essa igualdade seja verdadeira.

Uma alternativa concreta à comparação direta de kernels é provar que a sequência candidata satisfaz a recorrência de convolução de $F$ e usar [a unicidade dos momentos, CompletedNativeRealWeylMoments.lean:208–266](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/b39f4e7643d81295201626430dab15dd55da7c31/CarrySelfAdjointOperator/CompletedNativeRealWeylMoments.lean#L208-L266). Construir uma medida assumindo de antemão a positividade desses mesmos $h_k$ não descarregaria a obrigação; a rota útil parte da medida/estado geométrico efetivamente construído.

## 7. Bordo, cumulantes e ganho de cauda: peças para a identificação

### 7.1 A métrica explícita de análise TFVD

Para $0<q<1$, $A_q=q^{-1}(I-qU)^2$ e $t_q(x)=(x_0,q^{-1}x_1-x_0)$, a nota fornece

$$
M_q=\begin{pmatrix}q^{-2}+1&-1\\-1&1\end{pmatrix},\qquad
\langle A_qx,A_qy\rangle=\langle B_qx,B_qy\rangle+t_q(x)^*M_qt_q(y).
$$

Temos $M_q=J_q^*J_q$, com $J_q=\left(\begin{smallmatrix}q^{-1}&0\\-1&1\end{smallmatrix}\right)$, e $\det M_q=q^{-2}>0$. É uma métrica concreta dos dois traços. A norma de síntese $x=G_qB_qx+R_qt_q(x)$ conserva também seus termos cruzados; a separação ortogonal das coordenadas de **análise** não elimina esses cruzamentos da **síntese**. A expansão atual em quatro canais está em [ProjectiveValveCarryEnergyFrontier.lean:66](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/b39f4e7643d81295201626430dab15dd55da7c31/CarrySelfAdjointOperator/ProjectiveValveCarryEnergyFrontier.lean#L66).

### 7.2 O residual tem uma fórmula, não apenas um nome

Para uma análise finita sobrejetiva $\Gamma$, sejam $P=\Gamma^*(\Gamma\Gamma^*)^{-1}\Gamma$, $Q=I-P$ e $D^*=-D$. A escolha

$$
\Psi_0=-(\Gamma\Gamma^*)^{-1}\Gamma D(I-P/2)
$$

dá

$$
\boxed{D=\Psi_0^*\Gamma-\Gamma^*\Psi_0+QDQ.}
$$

A diferença de traços é $PD+DP-PDP$; somando $QDQ$ recupera-se $D$. Essa identidade conserva o residual bilinear $\langle Qx,DQy\rangle$. O destino concreto para a comparação é a soma de defeitos de proveniência, cruzamento e correção de readout em [CanonicalEnrichedBoundaryResidualIdentity.lean:82–155](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/b39f4e7643d81295201626430dab15dd55da7c31/CarrySelfAdjointOperator/CanonicalEnrichedBoundaryResidualIdentity.lean#L82-L155). Não foi localizada a instanciação que identifica essa soma com o $QDQ$ da nota. Uma norma residual não nula isolada tampouco decide seu cancelamento com os demais termos.

### 7.3 A conexão cumulante já tem parte concreta formalizada

Para massa escalar com termo constante 1, $BA=EA$ e $E=\sum_p\log(p)x_p\partial_p$ dão $b(p^\alpha)=\log(p^\alpha)[x^\alpha]\log A$. No pin CPFormal consumido, a massa de cutoff concreta satisfaz a deconvolução, e a conexão vestida é identificada ao log-jet:

- [CpC2OddCorePushforwardTfvd.lean:239–291](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpC2OddCorePushforwardTfvd.lean#L239-L291), `c2OddCoreLogCoefficientArithmetic_mul_mass`.
- [Mesmo módulo:456–490](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpC2OddCorePushforwardTfvd.lean#L456-L490), `c2OddCoreLogCoefficient_mul_positiveDirichletValue` e `positiveLogDirichletValue_eq_sum_range_gradient`.
- [CpC2DirichletJetTfvd.lean:95](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpC2DirichletJetTfvd.lean#L95) e [L169](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpC2DirichletJetTfvd.lean#L169), células ordinary/log como cumulante conectado vezes o termo Dirichlet apropriado.

Isso sugere calcular uma coluna inicial efetiva e verificar a convolução nativa, usando a unicidade já disponível. A identidade escalar não implica automaticamente a simetria de deslocamento $c(p,q+1)=c(p+1,q)$; essa parte pede a métrica ou um operador simétrico sobre os jets.

### 7.4 A diferença pode tornar somável a energia que a amplitude nua não torna

Na versão extensa, os três canais são

$$
Y_{n,\alpha,d}(s)=\sqrt{h_n}\,V_{n+1}(d)\,
\Delta\bigl((\log n)^\alpha n^{-s}\bigr),\qquad \alpha\in\{0,1/2,1\}.
$$

Com $\sum_d|V_{n+1}(d)|^2=1$, a nota estima a energia por $C_s n^{-2\sigma-1}(1+\log n)^{2\alpha+2}$, somável para $\sigma>0$. Aqui **$h_n$ é o peso da nota, não a sequência de momentos nativos $h_k$**. A ligação precisa identificar os pesos e estados antes de importar a estimativa.

O mesmo documento conserva as fases antes de reduzir $(ka,kb)$ à razão $a/b$: $K_{N,t}(R)=D_tK_{N,0}(R)D_t$, com $D_t=\operatorname{diag}(n^{-it})$. O kernel é bilinear refletido, justificando a ausência de adjunto nessa fórmula. A redução perde a fase $k^{-2it}$ se não carregar sua multiplicidade. Essa peça ajuda a manter a variável de altura e a energia na mesma construção.

### 7.5 Caudas de Möbius e moléculas completas

Outra realização positiva explícita usa

$$
f_r(u)=\sum_{a\mid r}\mu(r/a)\mathbf1_{[0,\log a)}(u),\qquad Q(r,s)=\int f_r f_s.
$$

A extremidade máxima do suporte prova independência das $f_r$, $r\ge2$. A nota de Möbius constrói daí o Gram da correção conectada no atlas ímpar, com núcleo no setor primo e positividade estrita no setor composto finito. Trata-se de índices de câmeras/cofatores: ainda é necessário um mapa para os jets nativos.

O relatório Haar recuperado do ZIP retém a célula completa de quatro cantos:

$$
\mu_n=\sqrt2 h_n\left[\frac{e_{2n,n}}n-\frac{e_{2n,n+1}}{n+1}
-\frac{e_{2n+2,n}}n+\frac{e_{2n+2,n+1}}{n+1}\right].
$$

Sem o fator comum, os momentos em torno de $1/2$ satisfazem $M_0=M_1=0$ e $M_2=-(2n+1)/(4n^2(n+1)^2)$. A norma molecular usa $b_n=\sqrt2 h_n(2n+1)/(8n^2(n+1)^2)$, declarado $O(\log^2n/n^2)$ no relatório. Isso torna a soma das moléculas Cauchy **nesse modelo, com os pesos e o levantamento escolhidos**; a identificação desses pesos e da porta global permanece uma tarefa. O canto omitido isoladamente podia divergir e a célula completa conservar o cancelamento. O exemplo reforça a utilidade de revisitar antigas obstruções quando o estado ou a métrica mudam.

O relatório também apresenta $\mathcal G(f,g)=\langle L_2df,dg\rangle-\langle df,L_2dg\rangle$. Essa é uma forma Green anti-Hermitiana; sua continuidade/closabilidade não a converte em um Gram positivo. As duas utilidades da nota — controlar a molécula e preservar o fluxo — precisam ser ligadas à forma positiva desejada por uma identidade adicional.

## 8. Outras notas: o que já foi absorvido pelo fonte atual

| Documento | Peça recuperada / status atual |
| --- | --- |
| [TFVD defect jets, L1–180](</home/thlinux/Downloads/hp/TFVD_DEFECT_JETS_GREEN_POSITIVE_CARRY_OPERATOR_AUDIT.md:1>) | Constrói $G=X^*X$, $K=X^*YX$ e jets resolventes **supondo** os Grams positivos. É um esquema útil para comparar os mapas, sem fornecer sozinho a origem da positividade. A própria revisão histórica diz que “crosswalk não localizado no corpus” não significa que ele precise ser importado de fora. |
| [Identidade ordem Jacobi](</home/thlinux/Downloads/IDENTIDADE_EXATA_ORDEM_JACOBI_OPERADOR_ALTURAS_GITHUB_VSCODE.md:1>) e [versão projetiva recuperada do ZIP](</home/thlinux/Downloads/Garimpo_notas_carry_2026-09-04/notas_recuperadas/a0f1afaf5722_IDENTIDADE_PROJETIVA_EXATA_LIMITE_OPERADOR_ALTURAS.md>) | A compatibilidade de prefixos LDL e a torre exata já têm [CanonicalLDLPrefixReduction.lean:141–181](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/b39f4e7643d81295201626430dab15dd55da7c31/CarrySelfAdjointOperator/CanonicalLDLPrefixReduction.lean#L141-L181). O teorema com sufixo `unconditional` ainda recebe a positividade de $G$; remove a hipótese adicional de compatibilidade, não a positividade. |
| [Green reflection/height, L1–210](</home/thlinux/Downloads/hp/GREEN_FRAME_REFLECTION_HEIGHT_WEYL_BRIDGE.md:1>) | A construção Householder traduz um overlap finito em condição espectral. Seu papel é uma equivalência finita de readout; a positividade de Pick do kernel nativo não segue apenas da coincidência dos zeros. |
| [C3 Green em duas variáveis, L496–589](</home/thlinux/Downloads/C3_GREEN_GAMMA_IDENTIDADE_DUAS_VARIAVEIS.md:496>) | A própria nota revisa a tarefa “construir Gamma”. O fonte atual já possui Gamma completado e [limite do Gram C3 bruto, CompletedC3RawGreenGamma.lean:65–98](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/b39f4e7643d81295201626430dab15dd55da7c31/CarrySelfAdjointOperator/CompletedC3RawGreenGamma.lean#L65-L98). O coeficiente da Green bruta continua sendo o autovalor da câmera; deve-se mostrar como chega à resposta completada nativa. |

## 9. Correções e reclassificação dos avisos antigos

| Registro anterior | Resultado do confronto | Consequência prática |
| --- | --- | --- |
| “Ainda não localizei o cancelamento da métrica em Lean” | A igualdade finita e a covariância funcional existem no Weyl, inclusive no pin consumido. | Reutilizar os lemas; acrescentar a especialização polarizada e a identificação do readout. |
| “Momentos fatoriais impedem a ponte” | Correto para identificar diretamente os momentos em $\xi$. O observável $v=e^{-\xi}$ da mesma medida tem momentos limitados. | Investigar transporte explícito; não descartar a medida pelo crescimento da coordenada antiga. |
| “Não há Gamma” | A nota já traz revisão; o crosswalk atual tem o estado completado. | Trabalhar a compatibilidade do readout e do bordo desse estado. |
| “O quociente destrói a proveniência” | O witness antigo vale para aquele quociente; [minimalProvenance_factorization](https://github.com/thiagomassensini/primos/blob/e2a723b4ec3e645539de0b9ca881951d93259cda/CPFormal/Analytic/CpMinimalProvenanceQuotient.lean#L93-L102) retém os dois mapas por $\ker Q\cap\ker A$. | Reaproveitar o reparo formal e verificar sua realização no estado escolhido. |
| “Todo retorno deve ser contrativo” | A versão extensa troca a meta por limitação uniforme e controle da passagem ao limite; modelos reduzidos posteriores têm novos resultados finitos. | Não fazer do bound 1 uma obrigação universal sem necessidade matemática demonstrada. |
| “A janela rígida falhou” | O insucesso par a par e o sucesso experimental após agregação por razão estão no mesmo §43; são problemas distintos. | Preservar as fases/multiplicidades e procurar cota simbólica da família adequada. |
| “O canto de bordo diverge” | O relatório molecular retém quatro cantos e apresenta norma/ganho de cancelamento próprios. | Comparar a célula completa; a segunda ordem em uma coordenada não autoriza substituir a primeira diferença do fluxo em outra. |

Duas fórmulas anteriores foram corrigidas no dossiê, sem editar os originais:

1. **Geradora das câmeras.** A nota detalhada já fornece

   $$
   (F_C(s))_{bc}=(G_C)_{bc}\frac{e^{s(1+\log\ell_{bc})}}{1+s},\qquad \Re s>-1.
   $$

   É a integral da medida declarada; na origem vale $G_C$. A expressão resumida falhava nessa ordem zero. Ver [convergência funcional, L411–422](</home/thlinux/Downloads/CONVERGENCIA_FUNCIONAL_DEFECT_PROBES_POVM.md:411>).

2. **Rank criação–aniquilação.** Pelas bases e criadores definidos na [nota, L11–58 e L151–190](</home/thlinux/Downloads/Álgebra de operadores de criação da tau holonômica 3–4–6.md:11>),

   $$
   \operatorname{rank}D_{ij}^{(n)}=2\binom{n+1}{3}
   +2\sum_{k=1}^{\lfloor(n-1)/2\rfloor}\binom{n+1-2k}{2}.
   $$

   Em $n=2,3$ dá **2 e 10**, contra **4 e 16** da fórmula antiga. A contagem exata e a derivação por permutação parcial estão no dossiê 2. A correção não elimina a medida positiva nem a fatoração de Vandermonde.

## 10. Ordem proposta para a próxima tentativa

| Etapa | Trabalho concreto | Saída que permite avançar |
| --- | --- | --- |
| E1 — retorno polarizado | Reutilizar $E^*G_EE=I$ e escrever a identidade sem divisão com dois resolventes; fixar tipos e convenção de produto interno. | Um lema verificável independente da característica, mais a lista exata dos mapas a instanciar. |
| E2 — mesma fonte e bordo | Instanciar as coordenadas de análise/retorno para os canais ordinário, logarítmico e residual. Calcular a diferença entre o readout completo e o Gram. | Fórmula explícita da diferença; conexão de $M_q$ ou $QDQ$ com os defeitos concretos, se existir. |
| E3 — momentos pela conexão | Usar a conexão cumulante vestida para calcular a coluna inicial; demonstrar sua convolução com os coeficientes da característica completada. | `IsCompletedNativeLogDerivativeMomentSequence` para a sequência candidata e aplicação da unicidade. |
| E4 — observável e ordem | Determinar o observável geométrico que gera os jets; o modelo compacto dá um exemplo explícito a comparar. Demonstrar a simetria de deslocamento ou diretamente os dois Grams. | Igualdade com $h_{i+j}$ e $h_{i+j+1}$, conservando ambos os setores. |
| E5 — limite compatível | Usar isometrias para um Hilbert comum, controle de caudas e convergência dos readouts nas duas alturas. Manter todo o bordo da construção selecionada. | Identidade do kernel nativo, ou construção direta dos coeficientes com a mesma identificação. |
| E6 — consumir a infraestrutura | Na rota C3 concreta, aplicar o construtor já existente; em outra realização, fornecer seus jets e independência de acordo com a interface escolhida. | Certificado HP. A extração por diferenças finitas e o caminho de certificado não precisam ser reconstruídos depois de suas hipóteses serem satisfeitas. |

E1 é pequena e isolável. **E2/E3 são o conteúdo decisivo**: provar a igualdade nativa, em vez de apenas acumular novos kernels positivos. A proposta é usar a métrica de retorno como eixo principal, com o modo misto compacto como realização explícita para testar o mecanismo de observável/paridade, e cumulantes/bordo para determinar a identificação correta.

Se a próxima tentativa deixar uma igualdade aberta, registrar seus mapas e termos exatos, incluindo o resíduo calculado. As próximas peças a procurar em notas adicionais são: o readout de retorno com a completação incorporada; a fórmula da projeção para o mesmo estado C3; uma identidade da conexão vestida nesse estado; e uma cota de cauda/retorno válida em todos os cutoffs do modelo escolhido.

## 11. Evidência e preservação

- As referências Lean foram conferidas nos fontes indicados por commit/pin. Esta rodada é de pesquisa e documentação; não executou um novo build nem formalizou os lemas derivados aqui.
- As identidades de retorno e $D=\text{traço}+QDQ$ tiveram exemplos matriciais verificados com aritmética racional exata, além da derivação geral escrita. A contagem do rank foi conferida exatamente nos primeiros níveis; a prova geral é a contagem apresentada no dossiê.
- O kernel compacto foi derivado da identidade racional exibida; positividade e independência foram justificadas pela medida e pelo argumento polinomial. Isso ainda não identifica o readout com $F$.
- Os dossiês incluem hashes das notas centrais; os CSVs abrangem o corpus textual inventariado. As duas notas recuperadas dos ZIPs estão identificadas por arquivo de origem, membro e SHA256 em `proveniencia_recuperacoes.json`.
- Os originais foram preservados. As fórmulas problemáticas foram anotadas nos novos documentos, sem reescrever retroativamente as notas históricas.

Validação estática concluída: 114 links locais, 45 hashes das fontes dos dossiês e 26 links de fonte Git por commit, sem erros encontrados. Os 564 documentos do inventário inicial mantiveram seus hashes. Registros: [documentação](</home/thlinux/Downloads/Garimpo_notas_carry_2026-09-04/validacao_documentacao.json>) e [fontes Lean](</home/thlinux/Downloads/Garimpo_notas_carry_2026-09-04/validacao_fontes_lean.json>). Não foi executada verificação visual de preview.
