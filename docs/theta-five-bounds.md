# Fechamento das cinco cotas theta e de Delta₂

Data: 2026-09-05. Base desta rodada: `9d009afb133fdc120effde352e2a3ae3d8e86dec`.

## Resultado formal

As cinco estimativas integrais antes abertas foram provadas no Lean, sem premissas matemáticas adicionais. O certificado algébrico existente agora fornece:

$$
\boxed{\Delta_2=h_0h_2-h_1^2>\frac{546}{10^{12}}=5.46\cdot10^{-10}>0.}
$$

Teoremas centrais em [`CompletedNativeSixthOrderThetaPositivity.lean`](../CarrySelfAdjointOperator/CompletedNativeSixthOrderThetaPositivity.lean):

- `canonicalCompletedNativeHankel_two_det_pos`;
- `canonicalCompletedNativeHankel_two_det_gt_546_div_trillion`;
- `canonicalCompletedNativeSecondSchurComplement_pos`;
- `canonicalCompletedNativeRadialThreePointDeterminant_eventually_re_pos`.

O último reutiliza o limite com resto já provado para $\varepsilon_k=1/(k+1)$ e conclui a positividade eventual da parte real do determinante da matriz nativa nos pontos $i\varepsilon_k,2i\varepsilon_k,3i\varepsilon_k$.

O complemento de Schur satisfaz, incondicionalmente,

$$h_2-\frac{h_1^2}{h_0}>0.$$

Esta rodada fecha essa não degenerescência inicial. A identificação Gamma/native Gram e os dois readouts BR2 em toda ordem continuam sendo obrigações distintas. Não foi construído outro operador, momento, Jacobi, Gamma ou certificado HP.

## Cadeia exata reutilizada

```text
thetaTail_ge_thetaFirstMode
thetaTail_le_geometric_first
  + convexidade do mesmo thetaFirstMode
  + células ponderadas certificadas + cauda explícita
    -> completedNativeThetaTailMoment_*_certified_bounds

completedNativeXiCosineMoment_zero_eq_thetaTailMoments
completedNativeXiCosineMoment_one_eq_thetaTailMoments
completedNativeXiCosineMoment_two_eq_thetaTailMoments
completedNativeXiCosineMoment_three_eq_thetaTailMoments
    -> cinco cotas cosseno sem hipóteses

canonicalCompletedNativeHankel_two_det_pos_of_xiMoment_bounds
    -> canonicalCompletedNativeHankel_two_det_pos

canonicalCompletedNativeHankel_two_det_pos_iff_schur
    -> canonicalCompletedNativeSecondSchurComplement_pos

canonicalCompletedNativeRadialThreePointDeterminant_eventually_re_pos_of_delta
    -> canonicalCompletedNativeRadialThreePointDeterminant_eventually_re_pos
```

O limite usado no último passo continua sendo o teorema existente `canonicalCompletedNativeRadialThreePointDeterminant_div_sixthStep_tendsto`. Não foi refeita a expansão do kernel.

## Cotas completas obtidas

Escreva $A_p=\texttt{completedNativeThetaTailMoment}\ p$ e $\mu_{2j}=\texttt{completedNativeXiCosineMoment}\ j$. O Lean prova:

| Momento theta | Limite inferior | Limite superior |
| --- | ---: | ---: |
| $A_0$ | $0.0115153$ | $0.011521$ |
| $A_2$ | $0.00024726$ | $0.00024748$ |
| $A_4$ | $0.0000199929$ | $0.000020029$ |
| $A_6$ | não necessário nesta prova | $0.000002891$ |

As identidades de integração por partes preservam todos os termos:

$$
\mu_0=\frac12-\frac{A_0}{4},\quad
\mu_2=2A_0-\frac{A_2}{4},\quad
\mu_4=12A_2-\frac{A_4}{4},\quad
\mu_6=30A_4-\frac{A_6}{4}.
$$

Elas implicam precisamente as cinco cotas solicitadas:

| Cota | Teorema novo |
| --- | --- |
| $\mu_0\ge497/1000$ | `completedNativeXiCosineMoment_zero_ge_497_div_1000` |
| $\mu_2\ge287/12500$ | `completedNativeXiCosineMoment_one_ge_287_div_12500` |
| $\mu_4\ge37/12500$ | `completedNativeXiCosineMoment_two_ge_37_div_12500` |
| $\mu_4\le593/200000$ | `completedNativeXiCosineMoment_two_le_593_div_200000` |
| $\mu_6\ge299/500000$ | `completedNativeXiCosineMoment_three_ge_299_div_500000` |

A sexta cota, $\mu_0<249/500$, já vinha de `completedNativeXiCosineMoment_zero_lt_249_div_500`. O numerador de $\Delta_2$ permanece o do certificado anterior, com margem racional $4861191/50000000000000$. Essa margem e o denominador positivo limitado por $1440(249/500)^3$ provam o limite quantitativo acima.

## Como as integrais foram certificadas

O objeto usado é o primeiro modo **já definido**:

$$f(u)=\texttt{thetaFirstMode}(u)=2e^{u/2}e^{-\pi e^{2u}}.$$

Sua derivada segunda é

$$f''(u)=\left(\frac14-6\pi e^{2u}+4(\pi e^{2u})^2\right)f(u)\ge0\quad(u\ge0).$$

A convexidade fornece dois limites numa célula $[a,b]$. Com

$$M_p=\int_a^b u^p\,du,\qquad m=\frac{M_{p+1}}{M_p},$$

a tangente em $m$ dá o limite inferior $M_p f(m)$: seu termo linear integra exatamente a zero. A secante entre $a,b$ dá o limite superior

$$\frac{(b f(a)-a f(b))M_p+(f(b)-f(a))M_{p+1}}{b-a}.$$

São usadas 128 células em $[0,1]$. Há 513 pontos distintos: extremos comuns e centros ponderados das ordens $0,2,4$. As ordens $0,2,4,6$ usam os mesmos extremos no limite superior. Os 896 limites de células são somados pela identidade existente de integrais em intervalos adjacentes.

Os valores pontuais são cercados por **aritmética racional**, a partir de `Real.sum_le_exp_of_nonneg`, `Real.exp_bound'` e dos limites de $\pi$ já provados no mathlib. O gerador Python usa apenas `fractions.Fraction` e operações inteiras; cada resultado gera uma desigualdade que `norm_num` demonstra no kernel. A impressão de aproximações decimais pelo gerador serve apenas à leitura humana.

As caudas são mantidas em duas camadas:

1. A estimativa existente $f(u)\le A(u)\le(8000/7999)f(u)$ controla todos os modos theta omitidos do primeiro modo.
2. Para $u\ge1$ e $p\le6$, o Lean prova

   $$u^p f(u)\le 2e^{-6}e^{-14u},\qquad
   \int_1^\infty u^p f(u)\,du\le10^{-8}.$$

Consequentemente,

$$
\int_0^1u^pf(u)\,du\le A_p\le
\frac{8000}{7999}\left(\int_0^1u^pf(u)\,du+10^{-8}\right).
$$

Não há quadratura Arb, lista de zeros, RH, hipótese de Herglotz ou positividade Hankel recebida como premissa dessa prova.

## Localização e reprodução

| Arquivo/diretório | Função |
| --- | --- |
| `CompletedNativeThetaExponentialBounds.lean` | Envelopes exponenciais e certificado racional genérico de valor pontual. |
| `CompletedNativeThetaFirstModeQuadrature.lean` | Convexidade, tangente/secante, integração ponderada, cauda e transporte para o theta completo. |
| `ThetaMomentCertificateData/ThetaNodes*.lean` | 513 certificados pontuais gerados. |
| `ThetaMomentCertificateData/ThetaCells*.lean` | 896 comparações integrais geradas. |
| `CompletedNativeThetaFiniteMomentCertificate.lean` | Soma exata das 128 células para cada momento usado. |
| `CompletedNativeSixthOrderThetaPositivity.lean` | Cinco cotas, $\Delta_2>0$, margem quantitativa e consequências existentes. |
| `CompletedNativeSixthOrderThetaPositivityAudit.lean` | `#print axioms` de todas as 1449 declarações públicas novas/expostas, incluindo os dados. |

Em `CompletedNativeXiThetaMomentBounds.lean`, somente a visibilidade de `thetaFirstMode`, `thetaTail_ge_thetaFirstMode` e `thetaTail_le_geometric_first` mudou, para reutilizá-los diretamente. Os corpos dessas declarações permanecem os mesmos.

O módulo final entra no aggregator; `Audit.lean` e `KernelConstructionAudit.lean` importam a auditoria específica.

Geradores e evidências: [`research/theta-five-bounds-2026-09-05/`](../research/theta-five-bounds-2026-09-05/).

```bash
python3 research/theta-five-bounds-2026-09-05/generate_theta_nodes.py --output-directory /tmp/theta-five-bounds-generated
python3 research/theta-five-bounds-2026-09-05/generate_theta_cells.py --output-directory /tmp/theta-five-bounds-generated
lake build --wfail CarrySelfAdjointOperator.CompletedNativeSixthOrderThetaPositivityAudit
bash scripts/audit.sh
git diff --check
```

Os 34 arquivos Lean gerados foram reproduzidos e comparados byte a byte com os fontes usados. Pins, revisão do mathlib e toolchain foram preservados em relação à base `9d009af`.

O audit dedicado aceita somente `propext`, `Classical.choice` e `Quot.sound`; o resultado de cada estágio do workflow está em `validation.txt`, acompanhado dos logs. A CI remota ficará por conta do usuário, conforme solicitado.
