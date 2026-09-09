# Comutador finito de profundidade e decomposição da câmera

Esta rodada parte da branch `agent/native-depth-cp-logjet-crosswalk`, commit
`234e7c157033aebc9fc5a438ee33cf1e40e65472`. O novo módulo
`FiniteNativeDepthCameraCommutator.lean` mantém o operador finito na camada
real e aplica a reconstrução enriched já existente.

Para `N : ℕ`, o shift `finiteDepthShift N` é o truncamento

\[
S_N e_j = e_{j-1}\quad(j>0),\qquad S_Ne_0=0,
\]

e `finiteDepthIndex N` é a diagonal dos índices `0, ..., N-1`. Definimos

\[
\Delta_{q,N}=q^{-1}S_N-I,
\qquad
L_{p,N}=(\log p)K_N,
\]

e o comutador real `finiteNativeDepthCommutator p q N`.

## Resultados formais

`finiteDepthShift_index_commutator` prova diretamente

\[
S_NK_N-K_NS_N=S_N.
\]

Consequentemente, `finiteDepthDifference_index_commutator` prova, sem exigir
`q ≠ 0`,

\[
[\Delta_{q,N},K_N]=\Delta_{q,N}+I.
\]

O teorema
`finiteDepthDifference_logMultiplication_commutator` entrega a versão de
escala:

\[
[\Delta_{q,N},L_{p,N}]
=(\log p)(\Delta_{q,N}+I).
\]

`finiteNativeDepthCommutator_eq_log_scale` apenas expõe a mesma igualdade
para a definição nomeada do comutador.

## Câmera enriched

`finiteVisibleOperatorReadout C J` e `finiteBlindOperatorReadout C J` são
os dois termos existentes da reconstrução canônica:

\[
J_{\rm vis}=R^\top(RJ),
\qquad
J_{\rm blind}=B^\top(BJ).
\]

`finiteEnrichedCamera_operator_decomposition` reutiliza
`finiteCanonicalEnrichedCamera_reconstruct` e prova

\[
J_{\rm vis}+J_{\rm blind}=J
\]

para toda matriz real `J`. O corolário
`finiteNativeDepthCommutator_visible_blind_decomposition` instancia isso ao
comutador concreto, para qualquer câmera de Gram positivo e qualquer `q`.

O canal blind permanece explícito. A rodada não afirma que o canal visível
é o `cpLogJetCommutator`, nem identifica essa matriz real com o gradiente
complexo horizontal. Essa identificação é o próximo gate e não foi assumida.

Também não há limite de cutoff, positividade do Gram nativo, sewing
Gamma–Wronskiano ou certificado espectral nesta etapa.

## Auditoria e escopo

O arquivo `FiniteNativeDepthCameraCommutatorAudit.lean` imprime os axiomas
dos seis teoremas públicos. O resultado esperado é o conjunto transitivo
padrão do projeto: `propext`, `Classical.choice` e `Quot.sound`.

Os pins, a toolchain e o mathlib foram preservados. Os arquivos temporários
e backups preexistentes do workspace não são incluídos.
