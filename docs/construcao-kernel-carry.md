# Construção do kernel carry — resultado da tentativa

**4 de setembro de 2026.** Continuação do mapa dos repositórios e das notas. Base de trabalho: `07d5821803c2093e7c9d205ceac1156634daeea4`; implementação desta rodada: `7c778e4a49409f51fd6742fc30ffe2d5045c300a`. Branch `agent/projective-valve-moment-frontier`.

## 1. Resultado

**Foi construído e formalizado um kernel positivo de diferença dividida em um Hilbert real de dimensão arbitrária, com resolvente existente em domínio local explícito, diagonal igual à derivada e séries dos mesmos momentos que aparecem nos dois Grams.** A identificação desse kernel com a característica nativa permanece aberta.

A tentativa também decidiu uma questão que antes estava apenas listada como pendência: **o estado C3 concreto com o produto interno ortogonal padrão não pode realizar a costura nativa**. A prova compara o Gram completo com o momento nativo, usando estimativas analíticas formais. Isso muda a escolha da próxima métrica; não elimina as rotas com outro operador métrico, observável ou estado.

Foram acrescentados sete módulos de construção e um módulo de auditoria. As notas originais, a característica nativa e as dependências foram preservadas.

## 2. O kernel que agora existe no Lean

Seja $H$ um Hilbert real completo, $S:H\to H$ linear contínuo e simétrico, e $u\in H$. No domínio

$$
|t|\,\|S\|<1,
$$

defina

$$
r_t=(I-t^2S^2)^{-1}u,\qquad
\Psi(t)=(r_t,tSr_t)\in H\oplus H,
\qquad a_{S,u}(t)=t\langle u,r_t\rangle.
$$

O inverso foi construído por `Ring.inverse`, e sua propriedade de inverso foi demonstrada pela cota de Neumann. Portanto $r_t$ não é apenas uma variável cuja existência se supõe. O Lean prova

$$
r_t-t^2S^2r_t=u
$$

e a identidade polarizada

$$
(z-x)\langle\Psi(x),\Psi(z)\rangle=a_{S,u}(z)-a_{S,u}(x).
$$

Além disso, a continuidade do inverso e o limite das diferenças divididas fornecem a diagonal efetiva:

$$
a_{S,u}'(x)=\|\Psi(x)\|^2.
$$

Assim, **incluindo pontos iguais**,

$$
\boxed{\langle\Psi(x),\Psi(z)\rangle=\operatorname{dslope}a_{S,u}(x,z).}
$$

Todas as seções finitas desse kernel são positivas semidefinidas, inclusive com parâmetros repetidos. Não foi imposta dimensão finita a $H$. A simetria de $S$ faz de $V=S^2$ um observável positivo; não foi suposto um operador positivo construído previamente a partir dos momentos nativos.

**Fontes:** [positiveObservableResolventParityState_polarized](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7c778e4a49409f51fd6742fc30ffe2d5045c300a/CarrySelfAdjointOperator/PositiveObservableParityKernel.lean#L123); [positiveObservableResolventParityState_inner_eq_dslope](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7c778e4a49409f51fd6742fc30ffe2d5045c300a/CarrySelfAdjointOperator/PositiveObservableKernelDiagonal.lean#L100); [positiveObservableResolventResponse_dslope_posSemidef](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7c778e4a49409f51fd6742fc30ffe2d5045c300a/CarrySelfAdjointOperator/PositiveObservableKernelDiagonal.lean#L117).

## 3. As séries e os Grams são da mesma construção

Também foram provadas como `HasSum` as séries convergentes

$$
r_t=\sum_{n\ge0}t^{2n}S^{2n}u,
\qquad a_{S,u}(t)=\sum_{n\ge0}t^{2n+1}m_n,
\qquad m_n=\langle u,S^{2n}u\rangle=\|S^n u\|^2.
$$

Os dois canais têm coeficientes

$$
\psi_{2n}=(S^{2n}u,0),\qquad
\psi_{2n+1}=(0,S^{2n+1}u),
$$

e a série pareada desses vetores soma exatamente a $\Psi(t)$. Seus produtos internos são

$$
\langle\psi_{2i},\psi_{2j}\rangle=m_{i+j},\qquad
\langle\psi_{2i+1},\psi_{2j+1}\rangle=m_{i+j+1},\qquad
\langle\psi_{2i},\psi_{2j+1}\rangle=0.
$$

**Independência:** o teorema de positividade estrita recebe `LinearIndependent ℝ (fun n => S^n u)`. Isso significa ausência de relação polinomial finita sobre a fonte; não significa apenas que o span da órbita seja denso no seu fechamento. Sob essa condição explícita, os dois Hankels são definidos positivos em toda ordem. As séries foram formalizadas diretamente; não foi necessário acrescentar teoremas com `iteratedDeriv` e fatores fatoriais para construir o certificado por coeficientes.

**Fontes:** [positiveObservableResolventParityState_hasSum](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7c778e4a49409f51fd6742fc30ffe2d5045c300a/CarrySelfAdjointOperator/PositiveObservableKernelSeries.lean#L94); [positiveObservableResolventResponse_hasSum](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7c778e4a49409f51fd6742fc30ffe2d5045c300a/CarrySelfAdjointOperator/PositiveObservableKernelSeries.lean#L71); [positiveObservableMoment_hankelPair_posDef_of_cyclic](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7c778e4a49409f51fd6742fc30ffe2d5045c300a/CarrySelfAdjointOperator/PositiveObservableParityKernel.lean#L253).

## 4. Como o retorno e o bordo entram

### 4.1 Retorno polarizado

No módulo matricial, $PE=D$ e $E^*E+D^*D=I$ fornecem $E^*G_EE=I$, com $G_E=I+P^*P$. Para duas pernas independentes,

$$
S(z)G_ES(w)^*=CR_zR_w^*C^*.
$$

Se $L=L^*$ e as matrizes satisfazem as equações de resolvente, temos

$$
(\bar w-z)S(z)G_ES(w)^*=B(z)-B(w)^*,\qquad B(z)=CR_zC^*.
$$

Foram provadas a fatoração de Gram, a positividade com todos os cruzamentos de uma seção finita e o sinal $-\operatorname{Im}B(z)=\operatorname{Im}(z)K(z,z)$. As câmeras e os mapas de retorno permanecem os mesmos nas duas pernas. Uma fonte dependente da altura ou uma mudança não linear de parâmetro exigem suas identidades de transporte; elas não foram identificadas silenciosamente com $t$.

**Fonte:** [compressedReadout_sub_adjoint_eq_separation_smul_covariance](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7c778e4a49409f51fd6742fc30ffe2d5045c300a/CarrySelfAdjointOperator/ReturnMetricPolarizedKernel.lean#L159).

### 4.2 Métrica de traço no espaço carry efetivo

No $\ell^2(\mathbb N,\mathbb C)$ já utilizado pelo projeto, foi construído o stencil causal

$$
A_q=q^{-1}I-2U+qU^2,
$$

que para $q\ne0$ corresponde algebricamente a $q^{-1}(I-qU)^2$. As primeiras coordenadas são $q^{-1}x_0$ e $q^{-1}x_1-2x_0$; a cauda é o bracket existente, deslocado uma posição. A decomposição da soma do produto interno em cabeça e cauda prova

$$
\boxed{\langle A_qx,A_qy\rangle
=\langle B_qx,B_qy\rangle+t_q(x)^*M_qt_q(y)},
$$

$$
t_q(x)=(x_0,q^{-1}x_1-x_0),\qquad
M_q=\begin{pmatrix}q^{-2}+1&-1\\-1&1\end{pmatrix}.
$$

Esse Gram foi realizado por um estado de um ponto, com bracket e traço em coordenadas Hilbert. Para $0<q<1$, sua injetividade foi provada usando a reconstrução TFVD já existente. Portanto ele conserva informação. A igualdade é da **métrica de análise**; não elimina os cruzamentos da reconstrução $x=G_qB_qx+R_qt_q(x)$. Tampouco identifica $A_q$ com o operador simétrico $S$ da seção 2.

**Fontes:** [carryTfvdCausalSecondDifference_inner_eq_bracket_add_trace](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7c778e4a49409f51fd6742fc30ffe2d5045c300a/CarrySelfAdjointOperator/CarryTfvdTraceMetricKernel.lean#L89); [carryTfvdMetricState_injective](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7c778e4a49409f51fd6742fc30ffe2d5045c300a/CarrySelfAdjointOperator/CarryTfvdTraceMetricKernel.lean#L118).

## 5. A calibração nativa que mudou a rota

Para o estado fixado em `canonicalCompletedC3RealAxisPositiveState`, Parseval e complexificação conservam o produto ortogonal dos canais ordinário, logarítmico e residual. Sua energia central é

$$
K_{\rm C3}(0,0)=E+L+E^2,
$$

$$
E=\sum_{m\ge1}\left((m+1)^{-1/2}-m^{-1/2}\right)^2,
\quad
L=\sum_{m\ge1}\left(\frac{\log(m+1)}{\sqrt{m+1}}-\frac{\log m}{\sqrt m}\right)^2.
$$

Na origem, o readout desejado é $a_{\rm nat}'(0)=h_0$. O novo módulo prova

$$
\boxed{h_0<\frac1{16}<E\le E+L+E^2.}
$$

A estimativa de $h_0$ usa a representação cosseno já formalmente identificada à característica nativa. Para $A_j=\int_0^\infty u^j\operatorname{thetaTail}(u)du$, foi demonstrado

$$
\operatorname{thetaTail}(u)\le\frac17e^{-5u},\qquad A_0\le\frac1{35},\qquad A_2\ge0.
$$

As identidades formais existentes $\mu_0=1/2-A_0/4$, $\mu_2=2A_0-A_2/4$ e $\mu_0h_0=\mu_2/2$ dão a cota racional. Do lado carry, basta a primeira coordenada: $(1/\sqrt2-1)^2>1/16$. Nenhuma aproximação numérica entrou nessa prova.

O defeito completo agora está decidido:

$$
\Delta_0=E+L+E^2-h_0>0.
$$

Consequentemente, `CanonicalCompletedC3ConcreteRealAxisPositiveSewing` e o kernel normalizado daquele estado específico foram refutados. Os antigos construtores que recebem essa hipótese continuam implicações formais, mas **essa hipótese não deve continuar sendo a meta de construção**.

Isso não é uma proibição geral à rota geométrica. Uma mudança isométrica do estado inteiro preservaria o defeito; é necessário modificar de fato a métrica/observável ou a realização da fonte. Para uma métrica positiva $M$ sobre o mesmo carrier, uma condição necessária seria $\langle\Psi_0(0),M\Psi_0(0)\rangle=h_0$, junto das igualdades em todas as demais alturas. Ajustar apenas essa entrada não prova o kernel.

**Fontes:** [canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7c778e4a49409f51fd6742fc30ffe2d5045c300a/CarrySelfAdjointOperator/CompletedC3KernelMetricCalibration.lean#L115); [canonicalCompletedC3ConcreteDressedCentralMomentDefect_pos](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7c778e4a49409f51fd6742fc30ffe2d5045c300a/CarrySelfAdjointOperator/CompletedC3KernelMetricCalibration.lean#L181); [not_canonicalCompletedC3ConcreteRealAxisPositiveSewing](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7c778e4a49409f51fd6742fc30ffe2d5045c300a/CarrySelfAdjointOperator/CompletedC3KernelMetricCalibration.lean#L202). [Investigação detalhada da calibração](garimpo-kernel-2026-09-04/calibracao_metrica.md).

## 6. A obrigação nativa ficou explícita no código

Escreva $F(t)=\sum_{n\ge0}f_nt^{2n}$ para a característica concreta já definida, com $f_0\ne0$. Para o operador e a fonte da seção 2, foi definido

$$
D_n(S,u)=f_0m_n+\sum_{k<n}m_k f_{n-k}+(n+1)f_{n+1}.
$$

O Lean prova que

$$
\bigl(\forall n,\ D_n(S,u)=0\bigr)
\iff \texttt{IsCompletedNativeLogDerivativeMomentSequence}(m).
$$

Pela unicidade nativa já existente, isso identifica todos os $m_n$ com os $h_n$. A construção de Gram e a independência das potências então produzem `CompletedNativeRealHPCarrierCertificate` diretamente. Não é preciso primeiro estender o kernel local para toda a reta para usar essa interface de coeficientes.

A primeira equação serve de calibração imediata:

$$
D_0(S,u)=f_0\|u\|^2+f_1,
\qquad \|u\|^2=h_0\ \text{se toda a recorrência valer}.
$$

**O defeito não foi provado nulo.** A equivalência o torna uma obrigação verificável; não reduz automaticamente sua dificuldade. Falta construir a partir da geometria o par $S,u$ — ou uma métrica equivalente sobre a fonte completa — e demonstrar a independência polinomial e essas identidades em todas as ordens. Não escolhemos $S$ a partir de um Jacobi cuja positividade nativa seria justamente a hipótese em discussão.

**Fontes:** [positiveObservableNativeConvolutionDefect](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7c778e4a49409f51fd6742fc30ffe2d5045c300a/CarrySelfAdjointOperator/PositiveObservableNativeMomentBridge.lean#L46); [positiveObservable_isNativeMomentSequence_iff_defect_zero](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7c778e4a49409f51fd6742fc30ffe2d5045c300a/CarrySelfAdjointOperator/PositiveObservableNativeMomentBridge.lean#L54); [completedNativeRealHPCarrierCertificate_of_positiveObservable](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/7c778e4a49409f51fd6742fc30ffe2d5045c300a/CarrySelfAdjointOperator/PositiveObservableNativeMomentBridge.lean#L110).

## 7. Próxima tentativa concreta

1. **Métrica e fonte:** extrair das portas de retorno completas um operador positivo ou uma transformação da análise, mantendo o bordo e os cruzamentos. A energia na direção central precisa mudar conforme a calibração provada.
2. **Observável simétrico:** determinar o $S$ limitado na realização escolhida e verificar a mesma variável de altura. A métrica $M_q$ isolada e a energia preservada de retorno não fazem essa escolha automaticamente.
3. **Readout:** provar $D_n(S,u)=0$ por uma identidade de conexão cumulante/Green com a completação. Conferir as primeiras ordens serve para rejeitar uma identificação errada cedo; o resultado final exige todo $n$.
4. **Independência e certificado:** demonstrar ausência de relação polinomial da fonte; consumir o construtor pronto. As séries, o kernel, a diagonal e os dois Grams já estão formalizados.

O ganho é uma mudança verificável de trabalho: há agora um kernel operacional com provas completas das propriedades locais, e uma realização concreta anterior cuja incompatibilidade foi demonstrada. A tarefa restante é a identificação geométrica específica, com a métrica correta.

## 8. Verificação e arquivos

- A auditoria estática do projeto, a compilação completa e os audits prescritos por `scripts/audit.sh` foram executados no servidor.
- O novo `KernelConstructionAudit.lean` verifica o uso de axiomas dos 68 teoremas públicos desta rodada. Os resultados usam somente `propext`, `Classical.choice` e `Quot.sound`.
- O script de auditoria do repositório agora inclui esse módulo; os sete módulos de construção estão no import principal.
- Os logs e hashes estão em [registro de validação](garimpo-kernel-2026-09-04/validacao.json). Há cópias dos fontes Lean no diretório `Garimpo_kernel_carry_2026-09-04/fontes_lean` do notebook.
- Não houve atualização de dependências nem alteração das notas originais. Esta tentativa não concluiu o kernel nativo e não foi mergeada ao `main`.
