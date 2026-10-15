# Redução iterada do residual do PR #98

Data: 2026-10-15. Fonte canônica: `carry-self-adjoint-operator`, servidor `llm`.

**Sim: a redução fecha sob a mesma operação e produz uma cadeia definida pela fonte.** Formalizamos a identidade para qualquer comprimento finito, mantendo o residual completo. Também construímos a terceira etapa positiva, identificando sua escala com uma expressão cujo sinal já estava certificado por integrais theta. **A positividade de todas as etapas e a realização infinita completa continuam abertas.**

## A mesma operação em cada etapa

A entrada é a resposta da fonte completada já sintetizada com cabeça, cauda, completação e correção de carta. Localmente,

\[
r_0(z)=-\frac{F'(z)}{2F(z)}.
\]

Para cada etapa, definimos

\[
A_j(z)=\operatorname{dslope}(r_j,0,z),\qquad
a_j=\operatorname{Re}A_j(0),
\]

\[
r_{j+1}(z)=\frac{\operatorname{dslope}(A_j,0,z)}{a_jA_j(z)}.
\]

Essas definições não dependem da dimensão de uma síntese finita nem de uma matriz de momentos. O valor no centro é dado por derivadas, pela definição de `dslope`.

Nos estágios regulares com \(r_j(0)=0\), \(A_j(0)=a_j\in\mathbb R\) e \(a_j>0\), temos exatamente

\[
r_j(z)=zA_j(z),\qquad
r_j(z)r_{j+1}(z)=\frac{A_j(z)}{a_j}-1.
\]

Fora do centro e dos zeros dos denominadores, a mesma operação se escreve

\[
\boxed{r_{j+1}(z)=\frac1{a_jz}-\frac1{r_j(z)}.}
\]

A reconstrução é

\[
r_j(z)\bigl(1-a_jzr_{j+1}(z)\bigr)=a_jz.
\]

Ambas as identidades estão formalizadas. A recorrência fornece uma expansão por frações contínuas com o residual terminal preservado. Sua definição total no Lean não certifica regularidade ou positividade quando uma escala é zero ou negativa.

## A cadeia de canais e a identidade em qualquer profundidade finita

Definimos uma única família, independente do ponto onde se interrompe a expansão:

\[
W_0(z)=1,\qquad W_n(z)=\prod_{k<n}r_k(z),\qquad
\phi_j(z)=\frac{W_j(z)A_j(z)}{\sqrt{a_j}}.
\]

Para

\[
K_j(z,w)=\frac{r_j(w)-\overline{r_j(z)}}{w-\bar z},
\]

a identidade de uma etapa e sua indução dão

\[
\boxed{
K_0(z,w)=\sum_{j<n}\overline{\phi_j(z)}\phi_j(w)
+\overline{W_n(z)}W_n(w)K_n(z,w).
}
\]

O teorema `chainKernel_prefix` vale para qualquer \(n\), com as condições das etapas anteriores expostas: centro nulo, escala central real e positiva e eixos não nulos nos pontos de entrada. Não pressupõe positividade do kernel pretendido nem uma igualdade de Gram desejada. A fórmula dividida mantém a restrição \(w\ne\bar z\).

Os dois primeiros canais coincidem exatamente com os do PR #98. Essa identificação está provada em `chainChannel_zero_eq`, `chainChannel_one_eq` e `chainPrefix_two_eq_existing`.

Para qualquer número finito \(N\) de entradas e quaisquer coeficientes complexos, `chainKernel_finite_energy` conserva todos os cruzamentos:

\[
\sum_{i,k}\bar c_i c_kK_0(z_i,z_k)
=\sum_{j<n}\left|\sum_i c_i\phi_j(z_i)\right|^2
+\sum_{i,k}\overline{c_iW_n(z_i)}c_kW_n(z_k)K_n(z_i,z_k).
\]

O primeiro termo é uma energia positiva em \(\mathbb C^n\), com seu produto interno usual. O segundo continua sendo a contribuição residual inteira. Os índices \(n\), profundidade de extração, e \(N\), quantidade de entradas, são independentes.

## A terceira etapa positiva já foi construída

No PR #98 estavam fornecidas pela fonte as duas primeiras escalas:

\[
a_0=m_0>0,\qquad a_1=\frac{m_1}{m_0^2}>0.
\]

Nesta etapa identificamos a derivada da resposta residual \(r_2\), em vez de definir a escala por uma expressão de momentos:

\[
\boxed{
a_2=r_2'(0)=\frac{m_0(m_0m_2-m_1^2)}{m_1^2}>0.
}
\]

A identificação usa o produto analítico exato da fonte

\[
A_0r_1=\frac{\operatorname{dslope}(A_0,0,\cdot)}{a_0}
\]

e suas identidades de Taylor. Obtivemos

\[
[z^2]r_1=0,\qquad
[z^3]r_1=\frac{m_2}{m_0^2}-\frac{m_1^2}{m_0^3}.
\]

O sinal de \(m_0m_2-m_1^2\) vem do teorema existente `nativeSourceMixedDiscriminants_pos`, demonstrado a partir dos integrais da fonte. Assim, a positividade da terceira escala não é uma hipótese nova sobre o kernel.

Formalizamos também \(r_2(0)=0\), a realidade da sua derivada central e a analiticidade da resposta seguinte \(r_3\). Há uma vizinhança aberta de zero, fornecida pela fonte, na qual os três primeiros eixos são não nulos. Nela,

\[
K_0(z,w)=\sum_{j<3}\overline{\phi_j(z)}\phi_j(w)
+\overline{W_3(z)}W_3(w)K_3(z,w).
\]

`nativeKernel_three_positive_channels_local` identifica essa igualdade com o kernel original de \(-F'/(2F)\). Não houve troca da fonte nem descarte da completação.

## O que falta para a cadeia inteira ser positiva

O passo algébrico pode ser repetido. O sinal da próxima escala precisa vir de uma propriedade adicional da fonte. Conhecer duas ou três escalas positivas não fornece uma indução que prove todas as seguintes.

Um exemplo algébrico mostra por que a operação, isoladamente, não preserva esse sinal: começando com \(r_0(z)=z+z^3\), ela produz

\[
a_0=1,\quad r_1(z)=\frac{z}{1+z^2},\quad
a_1=1,\quad r_2(z)=-z,\quad a_2=-1.
\]

Esse exemplo é uma derivação algébrica sobre outra função, não um contraexemplo para a fonte nativa. Ele apenas impede concluir positividade infinita pela forma da recorrência.

Na cadeia nativa, o alvo de sinal agora pode ser escrito diretamente:

\[
\forall j,\quad a_j>0,
\]

com as condições de regularidade e simetria preservadas. Para os três primeiros índices, essas condições foram fornecidas sem hipóteses de positividade do kernel. Para todos os índices, a obrigação permanece aberta.

## O fator de ordem crescente não elimina o residual sozinho

Também provamos exatamente

\[
W_n(z)=z^n\prod_{j<n}A_j(z)
\]

quando os centros anteriores são nulos. Isso explicita a profundidade do fator residual. Para cada prefixo finito, suas condições e vizinhança são declaradas. Não foi provada uma vizinhança comum a todas as profundidades.

O produto dos eixos pode crescer com \(n\). Portanto o fator \(z^n\), sozinho, não demonstra

\[
\overline{W_n(z)}W_n(w)K_n(z,w)\longrightarrow0.
\]

Uma realização infinita por uma família em \(\ell^2\) precisa justificar essa passagem e a convergência das energias. O presente resultado conserva o residual em cada etapa; não o substitui por zero. A construção de um operador autoadjunto ou a identificação com o operador de alturas também não foi acrescentada nesta etapa.

## Fontes formais e evidências

- `NativeCompletedSourceReductionChain.lean`: recorrência, reconstrução, compatibilidade com o PR #98, identidade para qualquer prefixo e síntese finita completa.
- `NativeCompletedSourceThirdPositiveChannel.lean`: identificação da terceira escala, prova de seu sinal e terceiro canal nativo com residual.
- `NativeCompletedSourceReductionChainAudit.lean`: auditoria das novas declarações públicas, incluindo tipos e corpos das dependências.

Os resultados finais de build, auditoria e publicação estão no registro de verificação que acompanha esta entrega.
