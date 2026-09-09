# Matriz literal finita e Gram das câmeras

Esta etapa parte do commit `e8996e0209481471404537fdf0dae2033be4bf46`, que
contém o comutador finito e a decomposição visible/blind. O módulo novo
`FiniteNativeDepthRawCameraGram.lean` constrói a camada raw antes do
whitening canônico.

Para uma família finita `camera : index → ℕ`, a matriz real é

\[
C_{M}(i,n)=\texttt{finiteCoefficientAt}(\texttt{camera}\ i,M,n),
\]

com `n` na janela comum `finiteFamilyWindow M camera`. O teorema
`finiteLiteralCameraMatrix_rowGram_apply_eq_literalFiniteCameraGram` prova
entrywise que

\[
(C_MC_M^\top)_{ij}
=\texttt{literalFiniteCameraGram}(M,\texttt{camera}\ i,
  \texttt{camera}\ j).
\]

A prova usa somente a identidade existente
`sum_finiteFamilyWindow_eq_pairFiniteWindow`: a extensão para a janela comum
acrescenta coeficientes nulos fora da sobreposição. Não há troca de métrica
nem normalização escondida.

Para `sixCamera`,
`finiteLiteralSixCameraMatrix_rowGram_apply_eq_literalFiniteCameraGram`
instancia a mesma igualdade para as seis câmeras concretas. Em seguida,
`tendsto_normalizedFiniteLiteralSixCameraRowGram` transporta literalmente o
resultado existente
`tendsto_normalizedLiteralSixCameraGram` e prova

\[
M^{-1}C_MC_M^\top\longrightarrow\texttt{sixCameraGram}.
\]

Esse é o objeto correto para aplicar depois

\[
R_M=(C_MC_M^\top)^{-1/2}C_M,
\]

quando uma hipótese de positividade definida do Gram finito estiver
disponível. Esta etapa ainda não afirma essa positividade para todo cutoff.

## Limite da redução

O módulo não identifica `C_M J_{p,M}` com um readout Cp. A API atual fornece
o comutador finito como uma matriz em `Fin N`, enquanto os coeficientes
literais usam a janela dependente da família de câmeras. O próximo passo
precisará tipar essa aplicação comum e especificar o vetor/estado finito que
será lido. A diferença entre leitura literal e whitening permanece explícita.

Também não há identificação Gamma–Wronskiano, Gram nativo de momentos ou
limite forte no `CarryVerticalL2` nesta rodada.

O audit `FiniteNativeDepthRawCameraGramAudit.lean` imprime os três teoremas
públicos; suas dependências ficam no conjunto padrão `propext`,
`Classical.choice`, `Quot.sound`.
