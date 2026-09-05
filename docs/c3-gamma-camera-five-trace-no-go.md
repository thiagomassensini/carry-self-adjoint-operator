# No-go local do Gamma canônico pelo teste da câmera 5

Data: 2026-09-05. Repositório: `thiagomassensini/carry-self-adjoint-operator`.
Base desta continuação: `b2f2fb9f23fcad3724d774e5187dffa99fd8c13a`.
Essa base tem como pai direto a base solicitada `225a85d9e8e3e0a3b659c5b6ad821458770b3195`.
Branch: `agent/c3-gamma-camera-five-trace`.

**Resultado: a costura Gamma–Wronskiano é falsa, perto do centro, para o source canônico e o Gamma atualmente definidos.** Esta rodada prova a não anulação do defeito existente em pontos não reais arbitrariamente próximos de zero, dentro da faixa Genuine e com característica nativa não nula. Também prova a negação de `CanonicalCompletedC3GammaCauchyScalarization`.

A rodada anterior isolou um complemento do source invisível ao retorno misto. Agora o teste desse complemento controla o **Gamma inteiro**, incluindo os cruzamentos. Portanto o resultado não depende de supor que a norma positiva de uma parcela impeça cancelamento.

## 1. Objetos fixados e escopo

Foram usados sem alteração:

- `canonicalCompletedC3SixCameraSource` e seu empacotamento fiel em `CameraHilbert`;
- `carryGammaSource`, definido como o resolvente do multiplicador logarítmico existente aplicado ao porto Naimark;
- `canonicalCompletedC3NormalizedPolarizedGammaKernel`, com a normalização existente `sqrt 2 * F`;
- `completedNativeOperatorCharacteristic`, seu companion e os momentos nativos;
- `canonicalCompletedC3RawGammaWronskianDefect` e as equivalências de sewing existentes.

A comparação testa a identificação de parâmetros **já escrita nesse endpoint**. Nenhum mapa novo entre altura, índice aritmético e parâmetro de resolvente foi introduzido.

Nenhum pin, mathlib, operador, Jacobi, Gamma ou momento nativo foi substituído. O resultado é sobre esses objetos tipados. Ele não estabelece impossibilidade de toda representação positiva dos momentos nativos.

## 2. Arquivos entregues

| Arquivo | Conteúdo |
|---|---|
| [C3GammaCameraMomentBound.lean](../CarrySelfAdjointOperator/C3GammaCameraMomentBound.lean) | 9 teoremas novos: momento quadrático no domínio Naimark, desigualdade da equação de defeito, teste exato da câmera 5 e limite inferior do Gamma completo |
| [C3GammaCameraTraceObstruction.lean](../CarrySelfAdjointOperator/C3GammaCameraTraceObstruction.lean) | 15 teoremas novos: limite do dslope nativo, normalização, separação local, contraexemplos e negação da scalarization nomeada |
| [CarrySelfAdjointOperator.lean](../CarrySelfAdjointOperator.lean) | Integra os dois módulos |
| [KernelConstructionAudit.lean](../CarrySelfAdjointOperator/KernelConstructionAudit.lean) | Imprime os axiomas dos 24 teoremas novos |
| [Audit.lean](../CarrySelfAdjointOperator/Audit.lean) | Integra os três endpoints principais à auditoria geral |
| [Evidências](../research/c3-gamma-camera-five-trace-2026-09-05/verification.json) | Comandos, hashes, axiomas, declarações e resultado dos 14 estágios |

Ambos os módulos novos usam `set_option autoImplicit false`, para que identificadores ausentes não se tornem parâmetros implícitos.

## 3. Origem → teste no domínio → Gamma completo

Denote por $u(z)$ o source canônico existente, por $V$ a isometria Naimark existente e por $Y$ seu multiplicador logarítmico. A equação já provada é

$$
z\Gamma(z)u=Y\Gamma(z)u+Vu.
$$

Escolha o vetor já existente $v_5=V e_{\text{câmera }5}$, que pertence ao domínio maximal de $Y$. As câmeras estão ordenadas pelos rótulos $2,3,4,5,6,7$. A câmera 5 corresponde à primeira coordenada da segunda perna C3 e tem Gram diagonal 20.

O novo `norm_logarithmic_camera_sq` liga a norma do multiplicador ao momento de câmera existente:

$$
\|Yv_b\|^2=G_{bb}\bigl(1+\log(\ell_b)^2\bigr).
$$

Sua prova usa a realização Naimark por indicadores, `logarithmicMultiplication_coeFn` e `integral_centeredLogSq_zero`. Para a câmera 5:

$$
\|v_5\|^2=20,\qquad
\|Yv_5\|^2=20(1+\log(5)^2).
$$

As estimativas $\|v_5\|\le5$ e $\|Yv_5\|\le10$ são provadas analiticamente; não vêm de ajuste numérico.

A simetria do mesmo $Y$, sua equação de defeito e Cauchy–Schwarz fornecem `carryGammaSource_camera_test_bound`:

$$
\left|\langle v_5,(Vu(z))_{\mathrm{re}}\rangle\right|
\le
\left[(|\Re z|+|\Im z|)\|v_5\|+\|Yv_5\|\right]
\|\Gamma(z)u(z)\|.
$$

Essa desigualdade é aplicada diretamente ao estado Gamma completo. Ela já cobre qualquer cancelamento entre a componente mista e seu complemento.

## 4. Primeiro termo que impede a igualdade

O empacotamento do source e a ortogonalidade da câmera 5 às outras cinco na métrica original dão exatamente:

```lean
canonicalC3CameraFive_source_test
```

$$
\langle v_5,(Vu(z))_{\mathrm{re}}\rangle
=20\Re\!\left(2^{-s(z)}-1\right),
\qquad s(z)=\operatorname{operatorHeightParameter}(z).
$$

É o mesmo termo que a rodada anterior localizou no complemento do retorno misto. O teorema preexistente `canonicalCentralCompletedGradient_firstCoordinate_sq_gt_sixteenth` e a continuidade dão, perto de zero,

$$
\left|\Re(2^{-s(z)}-1)\right|>\frac14.
$$

Com $|\Re z|,|\Im z|\le1$, a desigualdade do domínio resulta em

$$
5<20\|\Gamma(z)u(z)\|,
\qquad
\boxed{\|\Gamma(z)u(z)\|^2>\frac1{16}.}
$$

Este é `canonicalC3Gamma_energy_gt_sixteenth_of_cameraFive`. É uma estimativa do Gamma após o resolvente, obtida do porto inteiro.

## 5. Comparação na normalização correta

A normalização diagonal foi reutilizada de

```lean
canonicalCompletedC3GammaCharacteristicWeight_self_eq_normSq
```

para obter

$$
\Re K_\Gamma^{\mathrm{norm}}(z,z)
=\frac{\|\Gamma(z)u(z)\|^2}{2|F(z)|^2}.
$$

A identidade theta nativa já formalizada dá $|F(0)|\le1/2$. Continuidade e $F(0)\ne0$ dão, perto de zero, $F(z)\ne0$ e $|F(z)|<2/3$. Assim,

$$
\boxed{\Re K_\Gamma^{\mathrm{norm}}(z,z)>\frac1{16}}
$$

em todos os pontos próximos com $\Im z\ne0$.

No lado escalar, sejam $a=-F'/(2F)$ e $z=i\tau$. A paridade já estabelecida de $F$ dá a imparidade local de $a$. Logo

$$
\operatorname{dslope}(a)(-i\tau,i\tau)
=\operatorname{dslope}(a)(0,i\tau)
\longrightarrow a'(0)=h_0.
$$

A prova reutiliza `completedNativeGreenNormalizedResponse_hasDerivAt_h0`. Como `canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth` já fornece $h_0<1/16$, segue, para $\tau$ pequeno,

$$
\boxed{\Re K_{\mathrm{native}}(i\tau,i\tau)<\frac1{16}.}
$$

Portanto os kernels completos diferem nesses pontos. Não se comparou a energia bruta C3 com um momento como se fossem o mesmo objeto; o limite inferior foi transportado pela equação do Gamma e depois pela normalização característica existente.

## 6. Endpoints efetivamente provados

Os dois endpoints centrais são:

```lean
canonicalC3RawGammaWronskianDefect_ne_zero_near_imaginary_center
not_canonicalCompletedC3GammaCauchyScalarization_cameraFive
```

O primeiro afirma, literalmente, que eventualmente para $\tau\to0$, para toda prova de $\Im(i\tau)\ne0$,

```lean
canonicalCompletedC3RawGammaWronskianDefect
  (Complex.I * (t : ℂ)) (Complex.I * (t : ℂ)) hz hz ≠ 0
```

O segundo prova:

```lean
¬ CanonicalCompletedC3GammaCauchyScalarization
```

Também foram provados:

- `canonicalC3GreenInverseTraceRealization_empty_near_imaginary_center`: a estrutura de realização do trace existente é vazia nesses pares. Os vetores de right inverse continuam sendo os mesmos; a contradição ocorre em seu campo de trace.
- `canonicalC3RawDefect_counterexamples_arbitrarily_close`: para todo $\varepsilon>0$, existe $0<\tau<\min(\varepsilon,1/2)$ com $s(i\tau)$ dentro da faixa Genuine, $F(i\tau)\ne0$ e defeito não nulo.

O testemunho é existencial em toda vizinhança, verificado no kernel; esta rodada não fixa um numeral para $\tau$. Não foram usados testes numéricos nem uma lista de zeros.

## 7. Cadeia exata reutilizada

```text
naimarkCameraVector_mem_logarithmicMultiplicationDomain
+ logarithmicMultiplication_coeFn
+ integral_centeredLogSq_zero
  → norm_logarithmic_camera_sq

carryGammaSource_defect_equation
+ logarithmicMultiplication_isFormalAdjoint
+ abs_real_inner_le_norm
  → carryGammaSource_camera_test_bound

canonicalCompletedOperatorC3State_eq_greenBoundaryPair
+ finiteC3GenuineBracketGreenBoundaryPair_snd_apply
+ canonicalCentralCompletedGradient_firstCoordinate_sq_gt_sixteenth
  → canonicalC3Gamma_energy_gt_sixteenth_of_cameraFive

canonicalCompletedC3GammaCharacteristicWeight_self_eq_normSq
+ completedNativeXiCosineMoment_zero_eq_thetaTailMoments
+ completedNativeOperatorCharacteristic_differentiableAt_zero
+ completedNativeOperatorCharacteristic_zero_ne_zero
  → canonicalC3NormalizedGamma_diagonal_eventually_gt_sixteenth

completedNativeOperatorCharacteristic_eventually_even
+ completedNativeGreenNormalizedResponse_zero
+ completedNativeGreenNormalizedResponse_hasDerivAt_h0
+ canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  → completedNativePolarizedDslope_imaginaryAxis_eventually_lt_sixteenth

as duas desigualdades
+ canonicalCompletedC3NormalizedPolarizedGammaKernel_eq_dslope_iff_rawWronskian
  → canonicalC3RawGammaWronskianDefect_ne_zero_near_imaginary_center

+ CanonicalCompletedC3GreenInverseTraceRealization.rawGammaWronskianDefect_eq_zero
  → canonicalC3GreenInverseTraceRealization_empty_near_imaginary_center

+ canonicalCompletedNativeGammaCauchyScalarization_iff_energy
+ totalCarryGammaState_of_im_ne_zero
+ canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel
  → not_canonicalCompletedC3GammaCauchyScalarization_cameraFive
```

A equivalência da rodada anterior,
`canonicalC3RawGammaWronskianDefect_eq_zero_iff_returnBalance`, mostra então que a compensação dos três termos residuais também falha nesses pontos. Não sobra um goal aberto nos módulos desta rodada: foi provada a não anulação do defeito solicitado.

## 8. Verificação e consequência para a investigação

Nenhuma hipótese matemática nova foi usada nos endpoints. As hipóteses auxiliares de domínio e os limites locais foram demonstrados. A negação da scalarization é um teorema fechado.

O [registro de verificação](../research/c3-gamma-camera-five-trace-2026-09-05/verification.json) contém os resultados do workflow de 14 estágios, `git diff --check`, hashes dos módulos e configuração, e os axiomas transitivos dos 24 teoremas. A [saída de declarações](../research/c3-gamma-camera-five-trace-2026-09-05/theorem-statements.txt) conserva o texto emitido pelo Lean para os endpoints.

A identidade escalar TFVD → resposta → momentos continua sendo uma peça disponível. Esta prova determina que o Gamma com este source não fornece sua realização Gram pela costura proposta. O certificado HP e a equivalência espectral posterior não foram reconstruídos nem invocados com essa hipótese falsa.

Sem merge: o Gram nativo não foi identificado.
