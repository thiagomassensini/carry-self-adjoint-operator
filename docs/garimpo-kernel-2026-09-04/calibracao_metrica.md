# Investigação do kernel nativo: calibração exata da métrica C3 concreta

2026-09-04. Fontes verificadas no servidor `llm`. Implementação auditada no commit `7c778e4a49409f51fd6742fc30ffe2d5045c300a` do `carry-self-adjoint-operator`. Este documento detalha a calibração demonstrada durante a construção do kernel.

## Resultado formal

O estado C3 concreto atualmente chamado `canonicalCompletedC3RealAxisPositiveState`, com seu produto interno ortogonal padrão, **não realiza o kernel nativo**. O defeito já é estritamente positivo no centro, e isso agora está demonstrado no Lean usando a característica nativa real e sua representação cosseno já formalizada:

$$
h_0<\frac1{16}<E\le E+L+E^2=K_{\rm concreto}(0,0).
$$

Aqui

$$
E=\sum_{m\ge1}\left((m+1)^{-1/2}-m^{-1/2}\right)^2,
\qquad
L=\sum_{m\ge1}\left(\frac{\log(m+1)}{\sqrt{m+1}}-\frac{\log m}{\sqrt m}\right)^2.
$$

O resultado é sobre essa escolha de estado e produto interno. Ele não exclui uma métrica positiva transportada, um observável distinto ou outra realização nativa. A igualdade quebrada não deve continuar sendo usada como próxima hipótese a tentar instanciar literalmente.

## Onde a normalização atual cancela

`CompletedC3ConcreteRealAxisKernelCarrier.lean:242–260` define

$$
\Psi_{\rm raw}(t)=\sqrt2 F(t)\,S(t),
$$

e prova que a normalização por `√2 F` devolve exatamente `S(t)`. Portanto a normalização não repondera o Gram das coordenadas. O vetor `S(t)` é a soma ortogonal de:

1. gradiente Dirichlet ordinário `g(t)`;
2. gradiente logarítmico `ℓ(t)`;
3. coeficiente real `E(t)` vezes um gerador residual unitário.

Parseval e complexificação preservam esses produtos. Por isso, para duas alturas,

$$
K_0(x,z)=\langle g(x),g(z)\rangle+
\langle\ell(x),\ell(z)\rangle+E(x)E(z).
$$

No centro, `E(0)=‖g(0)‖²=E`, dando `K₀(0,0)=E+L+E²`.

O readout C3 normalizado já é `dslope a`, com `a=−F′/(2F)`. O lema existente `completedNativeGreenNormalizedResponse_hasDerivAt_h0` liga sua diagonal central ao **mesmo** `canonicalCompletedNativeLogDerivativeMoment 0`. Assim a comparação não introduz uma característica substituta.

## Como a desigualdade nativa foi provada

Os fontes `CompletedNativeXiCosineMoments` e `CompletedNativeXiThetaMoments` já identificam os coeficientes da característica nativa com os momentos do kernel cosseno. Escreva `A_j=∫₀∞u^j thetaTail(u)du`. As igualdades existentes são

$$
\mu_0=\frac12-\frac14A_0,
\qquad
\mu_2=2A_0-\frac14A_2,
\qquad
\mu_0 h_0=\frac12\mu_2.
$$

O novo módulo prova, por majorantes exponenciais e soma geométrica,

$$
\operatorname{thetaTail}(u)\le\frac17e^{-5u}\quad(u\ge0),
\qquad A_0\le\frac1{35},\qquad A_2\ge0.
$$

A majorante usa `π>3`, `e^{2u}≥1+2u`, `(n+1)²≥1+3n` e `e^{−3}<1/16`; esta última desigualdade é reduzida a uma soma finita de Taylor. Integrando, obtém-se a cota racional. Substituição na recorrência real dos momentos prova `h₀<1/16` por aritmética exata.

Do lado geométrico, a primeira coordenada do gradiente é `1/√2−1`. Seu quadrado é maior que `1/16`; a estimativa de avaliação em `ℓ²` fornece `E≥|g₀|²>1/16`. Nenhuma sonda numérica entra na prova.

## Defeito e mudança de métrica necessária

O novo lema `canonicalCompletedC3ConcreteDressedCentralMomentDefect_eq_calibration` identifica exatamente

$$
\boxed{\Delta_0=E+L+E^2-h_0>0.}
$$

Não é uma conclusão obtida apenas da norma residual: o lado ordinário sozinho já excede `h₀`, e o logarítmico e o residual também foram mantidos.

Qualquer transporte isométrico do estado inteiro conserva `K₀(0,0)` e, portanto, conserva esse defeito. A identidade de retorno `E_M^*G_{E,M}E_M=I` das notas conserva a energia do espaço de origem; sozinha não muda a calibração de `h₀`. Para funcionar aqui, o espaço/observável de origem ou a métrica relevante precisam ser identificados de modo diferente.

Uma condição necessária para um operador métrico positivo `M` sobre esse carrier é

$$
\langle S(0),M S(0)\rangle=h_0.
$$

É uma redução de energia nessa direção. Ela pode ser atingida formalmente por uma correção de posto um, mas isso serve apenas como calibração central: com `N₀=‖S(0)‖²`, `P₀` a projeção na direção de `S(0)` e `h₀>0`,

$$
M_{\rm centro}=I-\left(1-\frac{h_0}{N_0}\right)P_0
$$

é positivo e invertível e satisfaz a igualdade central. **Essa escolha não foi formalizada nem proposta como origem geométrica da métrica nativa**: depende explicitamente do momento-alvo e não demonstra as demais entradas. O que ainda falta é a identidade de todos os produtos

$$
\langle S(x),M S(z)\rangle=\operatorname{dslope}a(x,z)
$$

ou uma transformação de estado/observável que a realize, com os cruzamentos e o bordo correto. A coluna A da recorrência e a simetria de deslocamento B continuam sendo testes exatos para esse próximo candidato.

## Declarações novas e validação

Arquivo remoto: `CarrySelfAdjointOperator/CompletedC3KernelMetricCalibration.lean` (227 linhas).

| Linha | Declaração |
|---:|---|
| 80 | `calibration_thetaTail_le_exp` |
| 101 | `completedNativeThetaTailMoment_zero_le_calibration` |
| 115 | `canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth` |
| 139 | `canonicalCentralCompletedGradient_firstCoordinate_sq_gt_sixteenth` |
| 156 | `infiniteReflectedGreenEnergy_half_gt_sixteenth` |
| 169 | `canonicalCompletedC3RealAxisPositiveKernel_zero_zero_re_gt_nativeMoment` |
| 181 | `canonicalCompletedC3ConcreteDressedCentralMomentDefect_pos` |
| 189 | `canonicalCompletedC3ConcreteDressedCentralMomentDefect_eq_calibration` |
| 202 | `not_canonicalCompletedC3ConcreteRealAxisPositiveSewing` |
| 219 | `not_hasCompletedNativeRealAxisNormalizedGreenKernel_concreteC3` |

`lake build --wfail CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration` passou: 9138 jobs, módulo novo compilado em 9,8s. A auditoria de seis teoremas principais reportou somente `propext`, `Classical.choice`, `Quot.sound`. Nenhum `sorry`, `admit` ou axioma novo.

Logs remotos: `/tmp/carry-kernel-calibration-build.log`, `/tmp/carry-kernel-calibration-lake-build.log`; script de axiomas `/tmp/carry-kernel-calibration-axioms.lean`.

SHA-256 do módulo: `b56f172daef156db2894ac6047fd028eb30b125f202a22ab2fc5e15518cba7b4`.

