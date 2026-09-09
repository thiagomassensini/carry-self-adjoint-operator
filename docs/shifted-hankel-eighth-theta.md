# Primeiro menor Hankel deslocado por cotas theta de oitava ordem

Data: 2026-09-08. Base da investigação: `e793e7c`.

## Resultado formal

Para os momentos logarítmicos nativos já definidos, o Lean agora prova

$$
\boxed{
\det\bigl(\operatorname{shiftedHankel}(h,2)\bigr)
= h_1h_3-h_2^2>0.
}
$$

O teorema final é
`canonicalCompletedNativeShiftedHankel_two_det_pos`, em
[`CompletedNativeShiftedHankelEighthGate.lean`](../CarrySelfAdjointOperator/CompletedNativeShiftedHankelEighthGate.lean).

Isto fecha somente o primeiro menor deslocado. Não identifica o Gram nativo
com o estado C3 cru, não acrescenta hipótese espectral e não fornece, por si
só, um certificado Hankel em todas as ordens.

## Redução exata

Escrevendo

$$
\mu_{2j}=\texttt{completedNativeXiCosineMoment}\ j,
$$

o Lean deriva, a partir da recorrência nativa existente e do novo coeficiente
de oitava ordem,

$$
h_1h_3-h_2^2=
\frac{P(\mu_0,\mu_2,\mu_4,\mu_6,\mu_8)}
{1209600\,\mu_0^4},
$$

onde

$$
\begin{aligned}
P={}&10\mu_0^2\mu_4\mu_8-21\mu_0^2\mu_6^2
-30\mu_0\mu_2^2\mu_8+350\mu_0\mu_2\mu_4\mu_6\\
&-350\mu_0\mu_4^3-420\mu_2^3\mu_6+525\mu_2^2\mu_4^2.
\end{aligned}
$$

As pontes reutilizadas são:

```text
canonicalCompletedNativeLogDerivativeMoment_real_recurrence
completedNativeRealEvenCharacteristicCoefficient_*_eq_xiCosineMoment
completedNativeXiCosineMoment_succ_eq_thetaTailMoments
```

Em particular, o novo teorema
`completedNativeRealEvenCharacteristicCoefficient_four_eq_xiCosineMoment`
identifica $c_4=\mu_8/8!$ na característica já existente.

## Certificado de sinal

As cotas theta refinadas fornecem o retângulo racional

| Momento | Intervalo usado |
| --- | --- |
| $\mu_0$ | $[0.497120448,\,0.497120925]$ |
| $\mu_2$ | $[0.022970760,\,0.022974587]$ |
| $\mu_4$ | $[0.002962661,\,0.002963444]$ |
| $\mu_6$ | $[0.000599238,\,0.000599474]$ |
| $\mu_8$ | $[0.000160944,\,0.000161051]$ |

O módulo `CompletedNativeEighthBernsteinCertificate.lean` prova

$$P\ge10^{-10}.$$

O certificado não faz quadratura externa nem importa valores de zeros. Ele
usa os limites integrais racionais do primeiro modo theta, a cauda refinada
$\theta_n\le\theta_0(1/12300)^n$ e cinco desigualdades algébricas de
monotonia. No retângulo, $P$ é decrescente em
$\mu_0,\mu_4,\mu_8$ e crescente em $\mu_2,\mu_6$; portanto o mínimo é
reduzido ao vértice racional

$$
(\mu_0^{\max},\mu_2^{\min},\mu_4^{\max},\mu_6^{\min},\mu_8^{\max}).
$$

Os cinco sinais e a avaliação do vértice são verificados por `norm_num`,
`ring`, desigualdades de produtos não negativos e `linarith` no kernel Lean.

## Auditoria

`CompletedNativeShiftedHankelEighthGateAudit.lean` imprime a base axiomática
do coeficiente de ordem oito, das cotas refinadas, do certificado do numerador
e do teorema final. Cada um depende apenas de:

```text
propext
Classical.choice
Quot.sound
```

O módulo entra em `CarrySelfAdjointOperator.lean`, `Audit.lean` e
`KernelConstructionAudit.lean`.
