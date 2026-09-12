# Native Green-inverse trace sewing

Esta branch cria a realização nativa

`CanonicalCompletedC3NativeGreenInverseTraceRealization`.

Para parâmetros não reais `z,w`, ela contém:

- dois candidatos em `RealifiedLogarithmicDomain`;
- a equação de Green right-inverse para a fonte C3 canônica em cada ponto;
- o alvo de trace sem dressing:
  `completedGreenWronskian nativeHeightScalar
    nativeHeightScalarBoundaryCompanion w z`.

Os candidatos TFVD resolvidos disponíveis no repositório são:
`canonicalCompletedC3TfvdResolventDomainVector z hz` e
`canonicalCompletedC3TfvdResolventDomainVector w hw`. Os teoremas de
right-inverse e a unicidade existente mostram que ambos coincidem com os
estados Gamma correspondentes. Assim, não há um segundo resolvente que possa
ser escolhido para ajustar o trace.

A ponte de trace foi deixada como gate explícito. Os resultados principais são:

- `CanonicalCompletedC3NativeGreenInverseTraceRealization.candidateZ_eq_gamma`;
- `CanonicalCompletedC3NativeGreenInverseTraceRealization.candidateW_eq_gamma`;
- `CanonicalCompletedC3NativeGreenInverseTraceRealization.gammaBoundaryReadout_eq_nativeWronskian`;
- `canonicalCompletedC3TfvdNativeBoundaryReadout_iff_mismatch_zero`;
- `canonicalCompletedC3NativeGreenInverseTraceRealization_nonempty_iff_mismatch_zero`;
- `canonicalCompletedC3NativeGreenInverseTraceRealizationExists_iff_mismatch_zero`.

Em particular, para cada par `(z,w)\), a realização nativa é não vazia
exatamente quando o mismatch puro previamente isolado é zero:

```
Nonempty (CanonicalCompletedC3NativeGreenInverseTraceRealization z w hz hw)
  ↔ canonicalCompletedC3PureNativeBoundaryMismatch z w hz hw = 0
```

A definição do mismatch puro usada nessa caracterização é a existente em
`PureNativeBoundaryGreenSewing.lean`; ela é a diferença entre a Green form
Gamma e a Green form escalar nativa e não contém `nativeXiCompletionFactor`.

A geometria finita também permanece explicitamente conectada. O wrapper
`canonicalCompletedC3NativeTrace_cancellation_greenDefect_eq_verticalWronskian`
reutiliza a identidade Gpre colada já provada: o response Green, o boundary
return, a proveniência e a reconstrução TFVD permanecem no carrier, e o Green
defect desse carrier reduz ao Wronskiano vertical. O passo que ainda falta é
identificar esse Wronskiano vertical com o Wronskiano escalar de
`nativeHeightScalar`.

Portanto a branch não declara artificialmente o sewing nem altera Gamma. O
resultado é Outcome B: a realização e o candidato canônico estão tipados, e o
gate restante foi reduzido a um único termo exato,
`canonicalCompletedC3PureNativeBoundaryMismatch`.

Nenhum objeto arquimediano, Hankel, Jacobi, HP, câmera adicional, limite de
atlas/cutoff ou carrier refutado participa da nova prova.
