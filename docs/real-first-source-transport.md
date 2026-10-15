# Fonte Carry, duas quadraturas reais e o pareamento que falta

Investigação em `llm`, 15/10/2026. Base do autoadjunto: `bde8af97a34923563965128b7748e8ac088d7d9b`, merge do PR #105. Este estudo reúne a auditoria da rota real solicitada e a leitura crítica do texto anexado sobre meia escala, contração prime-carry e kernel dividido.

**O texto propõe uma ligação matematicamente coerente, mas sua igualdade principal continua aberta. A geometria fornece uma forma coerciva; ainda não está demonstrado que a fonte completada determina estados cujo pareamento nessa forma seja o kernel canônico. Nesta rodada formalizamos o transporte das duas quadraturas, dos domínios e das correções, sem modificar esse kernel nem eliminar seu defeito.**

O [mapa de declarações](real-first-declaration-map.md) foi entregue antes dos módulos novos. Ele separa resultados existentes, hipóteses, ligações não construídas e obstruções de candidatos específicos.

## 1. O que o texto acerta e onde é necessário precisar o alcance

| Afirmação do texto | Resultado da conferência |
|---|---|
| A massa de profundidade e a compatibilidade quadrática selecionam a meia escala. | **PROVADO**, com a compatibilidade quadrática como requisito explícito. `foundational_half_scaling_capstone` trabalha com expoentes formais racionais representados por naturais `p,q`, capacidade emergente e profundidade positiva. A expressão com potências reais de `sigma` explica uma realização analítica; não é literalmente o enunciado discreto desse teorema. Não determina a norma central da resposta Green. |
| O operador prime-carry tem orçamento `11/12`, e a forma complementar tem margem `1/12`. | **PROVADO** nas fontes consumidas. O mapa vai de `NativeGpreTowerHilbert` a `PrimeCarryDefectGlobalHilbert`; não é necessário tratá-lo como endomorfismo. A margem vale na norma da torre, para combinações efetivamente sintetizadas nela. |
| Leitura linear de momentos não determina seu Gram. | Correto. `NativeCompletedDividedVectorResponse` já constrói uma resposta vetorial dividida da fonte, com quatro setores e readout fixo que recupera o kernel escalar localmente. O próprio módulo distingue esse readout de uma realização positiva por produtos internos. Não recriamos esse resultado. |
| O Gram vertical completo é positivo e não é Hankel. | **PROVADO para a família indicada.** As entradas `(0,2)` e `(1,1)` são `1` e `4+eta²+eta⁻²`. `completeVerticalObservabilityGram_not_hankel` descarta sua identificação direta com qualquer sequência Hankel, para `eta≠0`. Não descarta outra família derivada da fonte. |
| A diferença material tem uma correção logarítmica. | **PROVADO** em `BaseTwoCompletedBoundaryDynamics`, como lei de derivadas coordenadas. O arquivo não anuncia diferenciabilidade forte da órbita em `ℓ²` nem um gerador autônomo nesse Hilbert. |
| A leitura interior bruta não é fechável. | **PROVADO** para operadores parciais que concordam com os coeficientes brutos especificados em todos os probes finitos. O limite vertical do gráfico impede esse fechamento. Não proíbe uma realização com semente, interior e retorno, nem toda leitura interior possível. |
| Parseval transporta os jets e resolveria a calibração. | Transporta os jets reais e seus pareamentos; **não resolve a calibração**. `baseTwoCanonicalGreenFirstColumnResidual_eq_material` conserva exatamente o residual anterior. Na ordem zero, ele é a norma real do core ao quadrado menos o momento central. |
| Uma representação positiva regular do kernel daria os dois blocos de Hankel. | Correto **condicionalmente** à identidade exata, à regularidade adequada e à extração dos coeficientes. Positividade estrita exige independência das famílias, não apenas vetores individuais não nulos. |

As quatro últimas fontes de análise da geometria foram conferidas e recompiladas no commit `e1084b43533255b399b82dc307b536d7dfdca07f`, que difere do pin consumido pelo autoadjunto. O capstone discreto é idêntico ao pin. Nenhum pin foi atualizado e nenhum desses módulos mais recentes foi importado por alteração de dependência.

## 2. Duas quadraturas antes de escolher escalares complexos

`RealQuadratureDomainTransport.lean` usa o produto Hilbert real existente

\[
\mathcal Q(E)=\operatorname{WithLp}_2(E\times E),\qquad
\mathcal J(x,y)=(-y,x).
\]

Não se usa a norma sup do produto bruto. Foram verificados `J_squared`, `J_inner`, `J_skew` e `J_norm`. Para a métrica real `g`, o packaging posterior satisfaz exatamente

\[
\langle\operatorname{pack}u,\operatorname{pack}v\rangle_{\mathbb C}
=g(u,v)+i\,g(\mathcal Ju,v).
\]

Essa é a convenção do produto interno Lean, antilinear na primeira entrada. A identidade `pack_inner` mantém dois argumentos independentes. `pack_inner_of_rotation_intertwining` torna explícita a exigência adicional: uma isometria real preserva esse pareamento complexo se também entrelaçar `J`. Isometria real sozinha não implica linearidade complexa.

Para um operador parcial real `T`, potencialmente não limitado, a construção começa sobre o real:

\[
D(T^{(2)})=D(T)\times D(T),\qquad
T^{(2)}(x,y)=(Tx,Ty).
\]

`J_mem_doubleDomain_iff` e `double_domainJ` provam invariância do domínio e comutação da ação com `J`. `double_realAdjoint_pairing` transporta o pareamento com o adjunto real nos dois domínios naturais. Depois, `pack_double_domain_iff` e `pack_double_action` comparam literalmente essa construção com a complexificação já existente. A igualdade maximal dos adjuntos complexificados é reutilizada de `LinearPMap.complexification_adjoint_eq_realAdjoint`; não foi substituída por uma identidade apenas formal de pareamentos.

O bloco real par/ímpar do operador de alturas tem carrier `E_even ⊕ E_odd`. Essa decomposição não é a duplicação de quadraturas `E ⊕ E`. Para complexificar o bloco, dobra-se o carrier inteiro; não se pressupõe uma rotação entre dois espaços de paridades diferentes.

## 3. A fase conserva a energia, mas a diferença conserva uma conexão

`RealMaterialPhaseConnection.lean` define

\[
R_\theta u=\cos\theta\,u+\sin\theta\,\mathcal Ju,
\qquad U_t(n)=R_{-t\log n}.
\]

`rotation_inner` conserva o pareamento real completo sob a mesma rotação nas duas entradas; `rotation_norm` e `materialPhase_norm` conservam a norma. Isso não autoriza usar frequências distintas como se fossem a mesma rotação.

Para o relógio de fase `L_a u=-a\mathcal Ju`, a identidade nova é

\[
\boxed{L_a u-L_b v=L_b(u-v)-(a-b)\mathcal Ju.}
\]

`materialLogClock_edge_connection` especializa `a=log(n+2)`, `b=log(n+1)`. `materialLogClock_first_edge_not_diagonal` dá um contraexemplo real explícito, já nos pontos materiais `2,1`, à exclusão desse segundo termo. Essa formalização algébrica não depende de afirmar diferenciabilidade forte de uma fonte infinita.

Outra distinção necessária aparece no sinal:

\[
L_a^2u=-a^2u,\qquad g(L_a^2u,u)=-a^2\|u\|^2\leq0.
\]

Essas duas identidades também foram formalizadas. Portanto não podemos tomar automaticamente as potências do gerador de tempo material como os jets normalizados de Green que devem ter cruzamento `h1>0`. É necessária uma conversão tipada de parâmetro, ordem e normalização. Não é um no-go contra uma realização real; é uma restrição à identificação ingênua dos jets.

A conexão material `log(n+2)-log(n+1)` e a conexão da completação `-A'/A` permanecem distintas. Nenhuma igualdade entre elas foi encontrada ou assumida. A segunda já possui uma lei normalizada exata, derivada de `F=AN`, em `NativeSourceNormalizedKernelConnection`; transportá-la exige conservar seu termo derivativo e sua normalização.

## 4. Os três setores e o residual do PR #105 sobrevivem integralmente

`NativeRealFirstQuadratureNaturality.lean` demonstra primeiro a decomposição polarizada dos operadores **reais preexistentes**: observado, halo e escape. O levantamento nas duas quadraturas preserva tanto `g(u,v)` quanto `g(Ju,v)`.

`pr105_full_pairing_comparison` compara literalmente a soma dos três pareamentos com o PR #105. A comparação é da soma completa; não afirma novas fórmulas de igualdade individual para todas as coordenadas da projeção das seis câmeras. Para o escape global, `pack_escape` reutiliza a identificação individual já existente com sua complexificação real.

A resposta `R` dessa parte do módulo é a decomposição em quadraturas da resposta complexa já definida. **Isso ainda é uma realificação fiel da resposta existente, não uma nova derivação física de `R` anterior ao packaging.** Nessa representação, foram verificados

\[
R=\Gamma+Q,\qquad ER=0,\qquad EQ=-E\Gamma,
\]

e o cancelamento dos quatro cruzamentos do escape nas duas formas reais. A energia de `Gamma` isolada não é promovida a energia da resposta: os termos de `Q` continuam presentes.

Se `a+ib=w-conj(z)`, `g=g(R_z,R_w)` e `omega=g(JR_z,R_w)`, `nativeDefect_real_components` prova

\[
\operatorname{Re}D_4=ag-b\omega-\operatorname{Re}W_F(w,z),
\qquad
\operatorname{Im}D_4=a\omega+bg-\operatorname{Im}W_F(w,z).
\]

São as duas componentes da **mesma** identidade

\[
D_4=(w-\bar z)K_R-W_F(w,z).
\]

O defeito não foi anulado, estimado por uma quantidade positiva nem dividido pela separação. Não identificamos esse defeito não normalizado com o defeito complementar proposto no texto sem demonstrar os fatores de passagem entre eles.

## 5. A margem geométrica funciona nas duas quadraturas

`NativeRealComplementTransport.lean` reaproveita a contração `C` e a forma complementar já existente, levantando-as coordenada a coordenada. Sem introduzir outra métrica,

\[
d(u,v)=g(u,v)-g(C^{(2)}u,C^{(2)}v),\qquad
\boxed{d(u,u)\geq\frac1{12}\|u\|^2.}
\]

`towerComplement_eq_original_quadratures` identifica essa forma com a soma das duas formas originais. `towerComplement_pack_pairing` conserva também o cruzamento orientado:

\[
d_{\mathbb C}(\operatorname{pack}u,\operatorname{pack}v)
=d(u,v)+i\,d(\mathcal Ju,v).
\]

A calibração continua restritiva:

\[
d(u_0,u_0)=h_0\Longrightarrow\|u_0\|^2\leq12h_0<3/4.
\]

O teorema é necessário e condicional nessa igualdade central. Não escolhe `u0` nem ajusta sua norma. Os estados brutos de norma quadrada pelo menos um continuam excluídos pelos no-gos de calibração anteriores.

Para uma família realmente construída da fonte, a estimativa necessária é **após a síntese inteira**. Se

\[
D_{ij}^{(s)}=d(U_i,U_j)-h_{i+j+s},
\]

o resultado anterior `native_energy_lower_bound_with_discrepancy`, já existente, fornece

\[
E_{s,N}(x)\geq\frac1{12}\left\|\sum_i x_iU_i\right\|^2
-\sum_{i,j}x_ix_jD_{ij}^{(s)}.
\]

Não basta controlar apenas os defeitos diagonais. Para concluir positividade estrita por essa rota, seria suficiente controlar o termo completo de defeito por `theta` vezes a norma sintetizada ao quadrado, com `theta<1/12`, e excluir combinações não nulas com síntese zero. Essa estimativa da fonte não foi demonstrada aqui. A margem da torre não se torna automaticamente uma margem uniforme dos pivôs de Hankel.

## 6. Os dois Hankel e a primeira identidade que ainda falta

Com `r(z)=sum h_n z^(2n+1)` na normalização canônica já fixada, o desenvolvimento do kernel dividido realmente tem coeficientes

\[
K_{2p,2q}=h_{p+q},\quad K_{2p+1,2q+1}=h_{p+q+1},\quad K_{2p,2q+1}=0.
\]

Aqui jets de coeficientes significam derivadas divididas pelo fatorial. A extração por um Gram de estados exigiria regularidade apropriada nas duas entradas; uma derivada real direcional não é por si um jet holomorfo. Onde `w=conj(z)`, a divisão deve ser substituída por uma extensão demonstrada, como o `dslope` da fonte, e não pelo inverso total de Lean nesse ponto.

A obrigação decisiva proposta no texto pode ser escrita como

\[
\boxed{d(U_z,U_w)+i\,d(JU_z,U_w)
=\frac{r(w)-\overline{r(z)}}{w-\bar z}.}
\]

**Falta construir a família `U` a partir da síntese posicional completada e provar essa igualdade, ou uma estimativa do seu defeito, com dinâmica e domínios compatíveis.** Valores escalares corretos, Parseval e coerção não a fornecem. A família não pode ser definida pela fatoração do Hankel que queremos justificar.

Antes de qualquer argumento geral, seus jets precisam passar simultaneamente por

\[
g(v_{e0},v_{e0})=h_0,\quad g(v_{e0},v_{o0})=0,
\quad g(v_{e1},v_{e0})=h_1,\quad g(v_{o0},v_{o0})=h_1.
\]

Para uma proposta complementar, substitui-se `g` pela forma complementar correspondente. As quatro identidades não foram obtidas para uma nova família física nesta rodada. Semente/interior/retorno não foram identificados automaticamente com cabeça/cauda/correção; câmera não foi identificada com voz prima, profundidade com ordem de jet ou relógio material com altura.

Na infraestrutura efetiva, a primeira ponte utilizável já tem nome: `HasCanonicalCompletedNativeTfvdGreenCenterLegReadout`, instanciada para os mesmos vetores e o transporte de incidência efetivo, ou a realização normalizada equivalente por limites de Green. A interface real corrigida `CompletedNativeRealHPCarrierCertificate` recebe o Gram e as independências e alimenta o construtor real reduzido autoadjunto existente.

Há uma correção importante ao alvo original: **o antigo `CompletedNativeGreenWeylReducedHeightCertificate` está formalmente refutado**, pois o primeiro jet ímpar Taylor complexo do ledger radial é zero. `not_completedNativeGreenWeylReducedHeightCertificate` já estava em `CompletedNativeHPGateAudit.lean`. Não tentamos preencher essa interface; reutilizamos a interface real corrigida do mesmo arquivo. A existência da maquinaria autoadjunta, a pertinência do estado físico ao domínio, a identificação de seu Gram e a identificação espectral continuam obrigações diferentes.

## 7. Verificação e resultado da investigação

- Os três módulos reais e os dois módulos de packaging upstream pedidos inicialmente foram recompilados nos pins consumidos: **3.171 jobs**, sem falha.
- Os cinco módulos adicionais do texto foram recompilados no checkout atual de geometria, separadamente: **8.779 jobs**, sem falha. Uma auditoria independente de sete declarações verificou o capstone discreto sem axiomas e as declarações analíticas apenas com `propext`, `Classical.choice`, `Quot.sound`.
- Os quatro módulos novos passaram em `lake build --wfail` (**9.916 jobs**); o módulo de auditoria passou com **9.920 jobs**.
- `RealFirstSourceTransportAudit` audita **67 declarações públicas**, com fecho de **7.510 dependências de tipos/corpos** e o guard físico existente. Onze raízes de regressão cobrem PR #105, calibrações, no-go radial, construtor real e adjunto complexificado.
- A compilação integrada dos alvos `CarrySelfAdjointOperator` e `CarrySelfAdjointOperator.Audit` passou com `lake build --wfail`: **10.389 jobs**. Não foram adicionados `sorry`, `admit` ou axiomas. Os logs e hashes acompanham a publicação.

**Resposta à pergunta final:** os resultados inspecionados ainda não demonstram que a síntese física real completa determina o pareamento polarizado dos jets completados. Demonstramos que as duas quadraturas, o domínio dobrado, a fase e os três setores podem ser conservados fielmente nas etapas indicadas. Isso mantém o defeito e a obrigação de positividade inalterados. O próximo alvo natural é construir a família física normalizada e calcular seu defeito de pareamento, começando pelas quatro calibrações acima; não começar outra campanha de discriminantes antes dessa identificação.

## Fontes verificadas

- [Capstone discreto](https://github.com/thiagomassensini/geometry-of-numbers/blob/e1084b43533255b399b82dc307b536d7dfdca07f/GeometryOfNumbers/Foundation/FoundationalHalfScalingCapstone.lean), [Gram vertical completo](https://github.com/thiagomassensini/geometry-of-numbers/blob/e1084b43533255b399b82dc307b536d7dfdca07f/GeometryOfNumbers/Analysis/CompleteVerticalObservationGram.lean), [dinâmica de bordo](https://github.com/thiagomassensini/geometry-of-numbers/blob/e1084b43533255b399b82dc307b536d7dfdca07f/GeometryOfNumbers/Analysis/BaseTwoCompletedBoundaryDynamics.lean), [não fechabilidade bruta](https://github.com/thiagomassensini/geometry-of-numbers/blob/e1084b43533255b399b82dc307b536d7dfdca07f/GeometryOfNumbers/Analysis/BaseTwoRawL2ReadoutNonclosable.lean), [Parseval e residual](https://github.com/thiagomassensini/geometry-of-numbers/blob/e1084b43533255b399b82dc307b536d7dfdca07f/GeometryOfNumbers/Analysis/CanonicalGreenMomentJetSeam.lean).
- [Contração prime-carry no pin consumido](https://github.com/thiagomassensini/primos/blob/65d50f6db1208708e109982ba97e1d51d3039956/CPFormal/Analytic/CpNativeGprePrimeCarryContraction.lean).
- [Costura dos três setores, PR #105](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/bde8af97a34923563965128b7748e8ac088d7d9b/CarrySelfAdjointOperator/CompletedNativeSourceThreeSectorSewing.lean), [readout vetorial dividido](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/bde8af97a34923563965128b7748e8ac088d7d9b/CarrySelfAdjointOperator/NativeCompletedDividedVectorResponse.lean), [calibração complementar](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/bde8af97a34923563965128b7748e8ac088d7d9b/CarrySelfAdjointOperator/NativePrimeCarryKernelCalibration.lean), [interface real corrigida e no-go anterior](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/bde8af97a34923563965128b7748e8ac088d7d9b/CarrySelfAdjointOperator/CompletedNativeHPGateAudit.lean).
