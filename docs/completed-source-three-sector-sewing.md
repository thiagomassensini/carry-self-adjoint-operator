# Transporte da fonte completada nos três setores

15/10/2026. Base: `carry-self-adjoint-operator`, `a7c9d03b1b006b2396ab7da624fac63490a2a645`. Continuação do estudo dos mapas históricos, executada no servidor `llm`.

**O resultado é uma comparação exata da mesma fonte com seus setores observados, de halo e de escape global. O escape global da resposta completada é zero e a correção resolvida cancela exatamente o escape Gamma, incluindo os cruzamentos.** Na síntese de ordem finita arbitrária, essa energia também aparece no residual assinado: extraí-la não fornece uma margem positiva adicional. A estimativa geral sobre o residual permanece por demonstrar.

## Fonte e mapas preservados

Utilizamos literalmente os objetos anteriores. Nos pontos radiais `z_i`, as amplitudes são

\[
a_i=\frac{c_i r^{i+1}}{\operatorname{HB}_+(z_i)}.
\]

Os vetores sintetizados são o Gamma completo

\[
\Gamma_c=\sum_i a_i\Gamma(z_i)
\]

e a síntese de câmera coisométrica `S_c = coisometricSourceSynthesis`. Não alteramos pontos, amplitudes, fases, métrica, Gram das seis câmeras ou fatores de completação. As projeções são aplicadas depois da síntese. A polarização mantém `c,d` e `r,s` independentes.

Se `J` é a isometria Naimark ordinária e `P₆` a projeção das seis câmeras no Hilbert global de câmeras, os três mapas utilizados são

\[
O x=P_6J^*x,\qquad Hx=(I-P_6)J^*x,\qquad Ex=(I-JJ^*)x.
\]

`O` e `H` têm valores no Hilbert de câmeras; `E` tem valores no Hilbert Naimark. A promoção por `J` preserva os produtos internos dos dois primeiros setores. Isso fornece a identidade polarizada

\[
\boxed{\langle x,y\rangle
=\langle Ox,Oy\rangle+\langle Hx,Hy\rangle+\langle Ex,Ey\rangle.}
\]

A identidade vale para vetores ambientes arbitrários, permitindo aplicá-la às sínteses inteiras e às correções. O setor `O` conserva o Gram original das seis câmeras: seu produto interno equivale à expressão com as coordenadas e `nativeSixCameraGram`. Não foi substituído por uma norma de coeficientes em outra métrica.

Declarações novas: `nativeNaimarkThreeSector_inner` e `nativeNaimarkThreeSector_norm_sq`.

## Onde a resposta completada realmente está

A resposta ambiente completada já existente é

\[
R(z)=J\,u(z),
\]

onde `u(z)` é a visão complexa de `completedC3SymplecticCameraState`. Portanto

\[
\boxed{ER(z)=0.}
\]

Essa igualdade recupera e transporta uma propriedade existente da resposta específica. O testemunho de halo não nulo dos **perfis logarítmicos centrados** estudados nos mapas é outro resultado; ele não foi aplicado automaticamente a `R(z)`.

A relação vetorial de origem TFVD já provada é

\[
R(z)=\Gamma(z)+Q(z),
\]

com `Q = canonicalCompletedC3AmbientTfvdResolvedCorrectionState`, a correção resolvida da fonte. Ela não é simplesmente o termo escalar `A'` do dressing arquimediano. A projeção produz

\[
\boxed{EQ(z)=-E\Gamma(z).}
\]

Em dois parâmetros independentes, os quatro termos do escape se cancelam:

\[
\begin{aligned}
0={}&\langle E\Gamma(z),E\Gamma(w)\rangle
+\langle E\Gamma(z),EQ(w)\rangle\\
&+\langle EQ(z),E\Gamma(w)\rangle
+\langle EQ(z),EQ(w)\rangle.
\end{aligned}
\]

O cancelamento usa os dois cruzamentos ordenados. Tomar apenas as duas normas positivas perderia a identidade da fonte inteira.

Declarações novas: `nativeCompletedAmbientResponse_globalEscape_zero`, `nativeCompletedResolvedCorrection_globalEscape` e `nativeCompletedGlobalEscape_fourTerms_zero`. As hipóteses são as de domínio das fontes: parte real positiva do parâmetro material e parâmetro espectral não real quando o resolvente é utilizado.

## Comparação direta com o Wronskiano completado

Para a resposta `R`, o Gram é a soma dos dois setores de câmeras:

\[
K_R(z,w)=\langle OR(z),OR(w)\rangle+\langle HR(z),HR(w)\rangle.
\]

Chamando `D₄` ao defeito de quatro canais **já definido** e `W_F(w,z)` ao `completedGreenWronskian` original do par `(F,-F')`, a nova composição formal fornece

\[
\boxed{D_4(z,w)=(w-\bar z)K_R(z,w)-W_F(w,z).}
\]

Essa é a comparação com o alvo completado, com a ordem dos argumentos preservada. O defeito conserva o canal Gamma–Wronskiano e as três correções coisométricas. A separação `w−bar z` foi mantida; não a dividimos na diagonal nem substituímos a extensão removível por um inverso total avaliado em zero.

A positividade de `K_R` vem de seus dois Grams. A igualdade com o kernel nativo normalizado ainda requer controlar `D₄` e conservar a normalização de Green. Este teorema não declara essa igualdade, nem transforma `R(0)` no vetor do momento `h₀`.

Declarações novas: `nativeCompletedAmbientResponse_twoSector_inner` e `nativeCompletedWronskianDefect_eq_twoSectorBoundary`.

## Orçamento da fonte para ordem arbitrária

Escreva `B` para `coisometricFourChannelBalance` e `BΓ` para `rawGammaWronskianBalance`. Essas duas quantidades já existiam e foram construídas com as amplitudes e correções originais. A nova identidade polarizada é

\[
\mathcal P(c,d)=2\bigl(
\langle O\Gamma_c,O\Gamma_d\rangle+
\langle H\Gamma_c,H\Gamma_d\rangle+
\langle E\Gamma_c,E\Gamma_d\rangle\bigr)+2iB_\Gamma(c,d).
\]

Na diagonal, ela dá

\[
\boxed{\operatorname{Re}\mathrm{storage}(c)
=2(\|O\Gamma_c\|^2+\|H\Gamma_c\|^2+\|E\Gamma_c\|^2)
-2\operatorname{Im}B_\Gamma(c,c).}
\]

Nenhuma parcela residual foi descartada. Para cada `N`, a regularidade nativa já provada fornece um corte radial suficientemente grande que torna a identidade válida simultaneamente para todos os coeficientes e raios internos. Não obtivemos um único corte para todas as ordens, nem uma estimativa uniforme do sinal.

O transporte do residual é igualmente explícito, antes da diagonal:

\[
\boxed{B_\Gamma(c,d)-i\langle E\Gamma_c,E\Gamma_d\rangle
=B(c,d)+i\bigl(
\langle O\Gamma_c,O\Gamma_d\rangle+
\langle H\Gamma_c,H\Gamma_d\rangle-
\langle S_c,S_d\rangle\bigr).}
\]

Em particular,

\[
\operatorname{Im}B_\Gamma(c,c)-\|E\Gamma_c\|^2
=\operatorname{Im}B(c,c)+\|O\Gamma_c\|^2+\|H\Gamma_c\|^2-\|S_c\|^2.
\]

Isso demonstra por que a energia do escape global não pode ser contabilizada como uma margem adicional sem transportar também a correção: ela reaparece com o coeficiente exato no orçamento assinado.

No carrier de câmera da resposta completada, o mesmo armazenamento fica

\[
\boxed{\operatorname{Re}\mathrm{storage}(c)
=2(\|P_6S_c\|^2+\|(I-P_6)S_c\|^2)-2\operatorname{Im}B(c,c).}
\]

A desigualdade ainda necessária é, portanto,

\[
\operatorname{Im}B(c,c)
\le\|P_6S_c\|^2+\|(I-P_6)S_c\|^2
\]

para a família efetiva da fonte, em todas as ordens. A reconstrução e a decomposição já provadas não demonstram esse sinal. A decomposição mostra exatamente quais parcelas precisam entrar numa eventual estimativa geométrica.

Declarações novas: `polarizedSourceBalance_eq_threeSectorGamma_add_rawBalance`, `storage_re_eq_threeSectorGammaBudget`, `rawGammaBalance_sub_globalEscapeGram`, `storage_re_eq_completedCameraTwoSectorBudget` e `threeSectorGammaBudget_eventually`.

## Consequência para a investigação

A análise separou duas situações que os mapas poderiam deixar próximas demais: o Gamma pode escapar do Hilbert de câmeras; a resposta completada `R` está nesse Hilbert, porque a correção da fonte cancela o escape. A existência de canais positivos de Gamma, isoladamente, não aumenta o orçamento disponível para o sinal da fonte completada.

O próximo controle precisa usar a relação entre a síntese completa `S`, seus setores observado/halo e a correção de Green. Estimar somente a massa de Gamma ou aumentar o atlas sem transportar `B` deixa esse controle por fazer. O teste da ordem zero e a identidade do kernel normalizado continuam necessários antes de extrair um Gram de momentos.

Essa é uma localização formal da obrigação, com um cancelamento exato e uma comparação de dois argumentos. Não foi produzida uma prova de positividade geral, uma nova identificação espectral, uma estimativa numérica ou uma igualdade nova com o Hankel sem residual.

## Código e validação

O módulo `CarrySelfAdjointOperator/CompletedNativeSourceThreeSectorSewing.lean` contém 21 declarações públicas, auditadas pelo módulo correspondente. As provas reaproveitam as projeções, a isometria Naimark, a correção resolvida e o balanço quiral existentes. A auditoria direcionada passou com `lake build --wfail`, 9.711 jobs, fecho de 7.146 declarações e somente `propext`, `Classical.choice` e `Quot.sound` nas raízes verificadas.

O módulo e sua auditoria foram adicionados às respectivas raízes do projeto. O build conjunto `lake build --wfail CarrySelfAdjointOperator CarrySelfAdjointOperator.Audit` passou, com 10.384 jobs. O registro `research/completed-source-three-sector-2026-10-15/verification.json` contém os comandos, os arquivos preservados e os pins. Os arquivos C2 preexistentes, as amplitudes e o manifesto de dependências foram preservados.
