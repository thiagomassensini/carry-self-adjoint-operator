# Teste da projeção branca de seis câmeras no estado ambiente normalizado

## Objeto histórico e entrada real

Depois do no-go do escape do porto de todas as câmeras, foi testada a projeção
histórica menor `sixCameraWhitenedNaimarkProjectionCLM`, derivada do Gram das
seis câmeras. A sua extensão para as duas quadraturas é literalmente
`realifiedContinuousLinearBlock P 0`; não há ajuste por momento, Gram alvo ou
fatoração abstrata.

Para o estado ambiente normalizado real `Ahat(z)`, foram definidos

\[
V_6(z)=P_6\widehat A(z),\qquad H_6(z)=(I-P_6)\widehat A(z).
\]

## Conservação polarizada já obtida

O teorema

```lean
inner_canonicalCompletedC3NormalizedAmbientResponseState_eq_sixCameraVisible_add_horizontal
```

prova, para todos os pares de parâmetros admissíveis,

\[
\langle\widehat A(z),\widehat A(w)\rangle=
\langle V_6(z),V_6(w)\rangle+\langle H_6(z),H_6(w)\rangle.
\]

Portanto esta é uma decomposição de Gram all-order do estado ambiente real,
não apenas uma identidade diagonal.

## O complementar é o halo histórico

O estado ambiente pertence ao porto de todas as câmeras. Assim, o
complementar de seis câmeras não contém um escape Naimark extra: ele é
exatamente o halo coerente global já existente,

\[
H_6(z)=(P_{\mathrm{global}}-P_6)\widehat A(z).
\]

Isto é certificado por

```lean
canonicalCompletedC3NormalizedAmbientSixCameraHorizontalState_eq_globalHalo
inner_canonicalCompletedC3NormalizedAmbientResponseState_eq_sixCameraVisible_add_globalHalo
```

Logo este candidato não soma canais por tentativa: é o setor de halo que
sobra da projeção histórica de seis câmeras dentro do porto global.

## Sanity-check central reduzido a uma identidade concreta

Com

\[
\delta_A=\|\widehat A(0)\|^2-h_0,
\qquad
\varepsilon_6=\|H_6(0)\|^2-\delta_A,
\]

o residual do candidato satisfaz exatamente

\[
\boxed{\varepsilon_6=h_0-\|V_6(0)\|^2.}
\]

Teorema:

```lean
canonicalCompletedC3SixCameraHorizontalCentralExcessResidual_eq_moment_sub_visible
```

Em particular,

\[
\boxed{\|H_6(0)\|^2=\delta_A
\quad\Longleftrightarrow\quad
\|V_6(0)\|^2=h_0.}
\]

Teorema:

```lean
canonicalCompletedC3SixCameraHorizontal_central_energy_eq_excess_iff
```

Os dois lados são agora energias de vetores e projeções concretas no carrier
ambiente. O repositório não contém ainda uma avaliação de
`||V_6(0)||^2 = h_0`; essa igualdade não foi assumida.

## Status contra o alvo quiral

| Pergunta | Estado formal |
|---|---|
| `P_6` é histórico e geométrico? | Sim. |
| Atua no estado ambiente normalizado real? | Sim. |
| Há segundo output concreto? | Sim: halo coerente global. |
| Há conservação polarizada/all-order? | Sim. |
| N=1 de energia ambiente | Reduzido a `||V_6(0)||² = h₀`. |
| N=2 e N=3 de Gram ambiente | Cobertos pela identidade polarizada all-order. |
| Identificação com `Q_i v_i` | Não encontrada. |
| `K_Pick = Gram(H_6)` | Não provado nem alegado. |
| Contractividade, Pick PSD, dslope PSD, Stieltjes | Não ativados. |

O halo de seis câmeras é, portanto, um candidato geométrico real para o
**excesso ambiente**, mas ainda não é uma dilatação da transformação
projetiva/quiral: ele existe sem `Q` e, sozinho, não satisfaz o guardrail de
proveniência quiral.

## Outro bloco lossless de seis câmeras auditado

`CameraReturnVarianceEnergyBalance.lean` também fornece um bloco histórico
de duas saídas, sobre coeficientes reais de seis câmeras:

\[
u\longmapsto (A_6u,S_6u),\qquad
\langle A_6u,A_6v\rangle+\langle S_6u,S_6v\rangle=\langle u,v\rangle.
\]

Os teoremas `sixCamera_return_variance_polarization` e
`sixCamera_return_variance_reconstruction` são uma conservação polarizada e
reconstrução exatas. Contudo, `CovariantCameraTraceTransport.lean` deixa
explícito que esse bloco é uma análise finita de coeficientes/traço e **não
define estado espectral**. Seus outputs são `A₆u` e `S₆u`, não `Qv`; o vetor
local chamado `Q₆` nesse arquivo é apenas um observador de seis coeficientes,
não o quociente quiral. Portanto esse bloco não fornece a ponte exigida para
o kernel Pick e não foi usado como defect channel.

## Auditoria lógica

`CompletedNativeSixCameraAmbientEnergyTestAudit.lean` imprime as axiomas da
ortogonalidade real, da polarização complexa, da identificação com o halo e do residual central. Não há `sorry`, axioma novo, Cholesky, RKHS, hipótese de Herglotz/Schur, Pick PSD, Stieltjes/Hankel/Jacobi, nem dado sobre zeros/RH.
