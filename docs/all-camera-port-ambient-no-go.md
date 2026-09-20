# Teste do porto Naimark de todas as câmeras no excesso ambiente

## Escopo exato

Este documento registra um teste de um candidato concreto, já existente no
repositório.  Ele **não** reabre a rota fechada do Gram ambiente literal e
**não** conclui que não exista uma dilatação projectiva/quiral diferente.

O candidato é a projeção histórica global da realização Naimark de
`CameraHilbert`:

\[
 P_{\mathrm{global}}=U U^*,\qquad
 U=\texttt{naimarkIsometry}.
\]

O módulo
`SixCameraGlobalNaimarkHaloDecomposition.lean` já a expõe como
`globalNaimarkCameraProjection`.  No carrier realificado do C3, a projeção
já existente

```lean
canonicalCompletedC3AmbientPortProjection
```

é exatamente a sua aplicação nas duas quadraturas.  Isto é certificado por

```lean
canonicalCompletedC3AmbientPortProjection_fst_eq_globalNaimarkCameraProjection
canonicalCompletedC3AmbientPortProjection_snd_eq_globalNaimarkCameraProjection
```

Portanto o teste usa o `P_global` da API histórica; não introduz uma
projeção auxiliar.

## Entrada e saídas testadas

Para o estado ambiente normalizado já usado pelo no-go literal, foi mantida
a mesma normalização, sem constante ajustada:

\[
 a(z)=(\sqrt 2 F(z))^{-1},\qquad
 x(z)=a(z)\,A(z).
\]

No nível realificado, a transformação testada é

\[
 x(z)\longmapsto
 \bigl(P_{\mathrm{global}}x(z),\;(I-P_{\mathrm{global}})x(z)\bigr).
\]

O primeiro output é chamado `AllCameraPortState`; o segundo é o único
escape/horizontal intrínseco disponibilizado pela mesma coligação
lossless, `AllCameraHorizontalState`.

## Conservação que de fato existe

O bloco port-plus-escape já é uma isometria.  No estado normalizado, o novo
teorema polarizado registra:

\[
 \langle\widehat A(z),\widehat A(w)\rangle
 =\langle V(z),V(w)\rangle+\langle H(z),H(w)\rangle.
\]

Formalmente:

```lean
inner_canonicalCompletedC3NormalizedAmbientResponseState_eq_allCameraPort_add_horizontal
```

Mas a informação decisiva é que o estado completo já está na imagem de
`U`.  Logo, para todos os parâmetros admissíveis,

\[
 P_{\mathrm{global}}x(z)=x(z),\qquad H(z)=(I-P_{\mathrm{global}})x(z)=0.
\]

Isto é provado por:

```lean
canonicalCompletedC3AmbientPortProjection_normalizedAmbientRealifiedState
canonicalCompletedC3NormalizedAmbientAllCameraPortState_eq_response
canonicalCompletedC3NormalizedAmbientAllCameraHorizontalState_eq_zero
```

Assim, a conservação é real, geométrica e all-order, mas é trivial no
segundo canal para esta entrada específica.

## Obstrução central

Defina o excesso ambiente já estabelecido:

\[
 \delta_A=\|\widehat A(0)\|^2-h_0>0.
\]

O residual do candidato é definido sem recorrer a Pick/PSD:

\[
 \varepsilon_{\mathrm{global}}
 =\|H(0)\|^2-\delta_A.
\]

Como `H(0)=0`, o resultado formal é

\[
 \varepsilon_{\mathrm{global}}=-\delta_A<0.
\]

Teoremas:

```lean
canonicalCompletedC3AllCameraHorizontalCentralExcessResidual_eq_neg
canonicalCompletedC3AllCameraHorizontalCentralExcessResidual_neg
canonicalCompletedC3AllCameraHorizontal_central_energy_ne_excess
```

Logo o candidato falha no primeiro sanity-check de energia central:

\[
 \|H(0)\|^2=0\ne\delta_A.
\]

## Classificação da auditoria

| Pergunta | Resultado |
|---|---|
| Projeção derivada de API histórica? | Sim: `globalNaimarkCameraProjection=U U*`. |
| Entrada é o estado ambiente normalizado real? | Sim. |
| Há segundo output intrínseco? | Sim: `(I-P_global)x`. |
| Há conservação polarizada/all-order? | Sim. |
| Segundo output é não trivial nessa entrada? | Não: é identicamente zero. |
| Reproduz \(\delta_A\) no centro? | Não: residual exato \(-\delta_A<0\). |
| Pode ser o canal de defeito desejado? | Não, para esta projeção global específica. |
| Pick virou Gram? | Não; nenhuma identificação com `Qv` foi obtida. |
| N=2/N=3 da meta Pick | Não aplicável: o candidato já falha antes, no output central. |

O resultado é portanto um **no-go específico do escape do porto Naimark
global**.  Ele deixa aberta a ponte que ainda falta: uma projeção finita ou
multibase, construída a partir de `cameraLogVerticalContribution` e
`cameraLogHorizontalContribution`, com uma realização isométrica concreta
no carrier ambiente e uma identificação não trivial com a transformação
projetiva/quiral `Q`.

## Auditoria lógica

`CompletedNativeAllCameraPortAmbientNoGoAudit.lean` executa `#print axioms`
para a identificação com a projeção global, a anulação do segundo output, a
conservação polarizada e a obstrução central.  Os resultados usam somente
`propext`, `Classical.choice` e `Quot.sound`; não usam `sorry`, axiomas
novos, positividades Pick/Stieltjes/Hankel/Jacobi, Herglotz, zeros/RH ou
fatoração abstrata de kernels.
