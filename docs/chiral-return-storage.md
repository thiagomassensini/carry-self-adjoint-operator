# Retorno quiral: balanço acumulado e fluxo local

Esta rodada calcula o balanço dos dois canais da realização Cauchy já
existente. O resultado é uma identidade em toda dimensão finita e um
fenômeno formal de duas leituras: **balanço acumulado não negativo pode
coexistir com fluxo negativo no bordo final**.

Não foi demonstrada positividade nativa em toda ordem. A palavra
"armazenamento" abaixo nomeia um balanço assinado; sua positividade geral
não faz parte da definição.

## Os mesmos dados e as mesmas coordenadas

Fixe a malha radial existente `canonicalCompletedC3RadialTiltPoint k i` e
escreva

$$
q_i=\frac{-F'(z_i)-iF(z_i)}{-F'(z_i)+iF(z_i)}.
$$

O código reutiliza `completedNativeHermiteBiehlerChiralQuotient` diretamente.
O par completado e suas correções permanecem incorporados nesse objeto.
Os nomes dos canais não postulam uma realização causal de transferência.

Os vetores Cauchy existentes são

$$
v_i(x)=\sqrt{k+1}\sqrt{x}\,x^i\quad\text{em }L^2([0,1]),
\qquad w_i=q_i v_i.
$$

Para coeficientes complexos arbitrários, lemos os dois polinômios

$$
p_c(r)=\sum_i c_i r^i,
\qquad \widetilde p_c(r)=\sum_i c_iq_i r^i.
$$

**`r` é a coordenada interna da realização Cauchy.** Não é a altura nativa,
o tempo material do carry, um novo cutoff C3 ou uma identificação adicional
com o parâmetro de resolvente.

## Identidade nova de balanço

O módulo `CompletedNativeChiralReturnStorage.lean`, no namespace
`CarrySelfAdjointOperator.ChiralReturn`, define apenas os readouts
`incident`, `returned` e `storage` sobre esses objetos existentes.

Se `D` é a matriz de defeito Gram já definida no projeto, então

$$
S_k(c,r)=\sum_{i,j}\overline{c_i}c_jD_{ij}r^{i+j+2}.
$$

`storage_eq_quadratic` e `storage_re_eq_norm_balance` provam

$$
\operatorname{Re}S_k(c,r)
=\left\|\sum_i c_i r^{i+1}v_i\right\|^2
-\left\|\sum_i c_i r^{i+1}w_i\right\|^2.
$$

O grau `i+j+2` cancela precisamente o denominador Cauchy da matriz. Daí,
`hasDerivAt_storage` e `integral_flux_eq_storage` demonstram

$$
\boxed{
S'_k(c,r)=(k+1)r
\left(|p_c(r)|^2-|\widetilde p_c(r)|^2\right)
}
$$

e a identidade integrada desde `0`, onde `S_k(c,0)=0`.
Todos os termos cruzados estão presentes nos quadrados das somas.
A derivada é a derivada real de uma função com valores complexos; a
expressão exibida tem valores reais.

## Ligação exata ao kernel nativo

Nenhuma amplitude foi ajustada. Com a amplitude projetiva já existente
`a_i = completedNativeNormalizedPositiveChiralAmplitude z_i`, o teorema
`storage_one_eq_native_quadratic` reutiliza a congruência canônica e prova

$$
S_k((c_i a_i)_i,1)=2\,c^*K_{\mathrm{nativo}}c.
$$

As únicas hipóteses desse enunciado são a regularidade das amostras exigida
pela identidade existente: pertença ao domínio e não anulação dos dois
denominadores indicados no tipo. Não se supõe sinal de `K`.

## Witness nativo: o fluxo local pode ser negativo

Escolha duas entradas `c=(1,-1)`. Então `p_c(1)=0`, e
`opposite_endpoint_flux` prova exatamente

$$
\operatorname{Re}S'_k(c,1)=-(k+1)|q_0-q_1|^2.
$$

`native_quotient_two_samples_ne_eventually` prova que `q_0≠q_1` para passos
suficientemente pequenos. Reutiliza a derivada central já formalizada
`q'(0)=-4ih_0` e a positividade incondicional de `h_0`.

Com a contração de duas leituras já obtida pelas estimativas theta,
o teorema principal é:

```lean
CarrySelfAdjointOperator.ChiralReturn.two_point_storage_nonnegative_but_endpoint_flux_negative
```

Seu enunciado, abreviado apenas pelo namespace aberto, é:

```lean
∀ᶠ k : ℕ in atTop,
  (∀ r : ℝ, 0 ≤ (storage k ![1, -1] r).re) ∧
    (deriv (storage k ![1, -1]) 1).re < 0
```

Os coeficientes `(1,-1)` são os dos readouts Cauchy. Na realização
projetiva, correspondem a `(1/a₀,-1/a₁)` nas seções regulares, pois a
identidade de transporte usa os produtos `cᵢaᵢ`. A amplitude original
continua presente.

Portanto, para a própria resposta completada, a intensidade de retorno no
bordo pode exceder a intensidade incidente naquele ponto enquanto o
balanço integrado permanece não negativo. Uma prova por atenuação
instantânea de todas as combinações não serve para essa família.

Isso é compatível com uma interpretação que contabilize armazenamento e
liberação. **Não prova que exista um sistema causal passivo realizando
esses readouts em toda ordem.**

## O que fica aberto e o que não deve ser reconstruído

A proposição all-order permanece a já existente
`CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive`.
Esta rodada fornece sua expressão como balanço integrado, sem assumir
que o integrando tenha sinal fixo. O controle de duas leituras foi
reutilizado; não foi estendido artificialmente para todo `N`.

Não há novo operador autoadjunto, Jacobi, Gamma, momento ou kernel
candidato. A norma C3 crua e o sewing refutado do Gamma fixado não são
usados como alvo.

## Cadeia reutilizada e auditoria

- `inner_completedNativeRadialChiralCauchyState` e
  `canonicalCompletedNativeRadialChiralMultiplierDefectMatrix_apply`:
  métrica e escala Cauchy exatas.
- `canonicalCompletedNativeRadialDslopeSampleMatrix_eq_pickCongruence`:
  identificação com o kernel nativo e amplitude preservada.
- `hasDerivAt_completedNativeHermiteBiehlerChiralQuotient_zero` e
  `canonicalCompletedNativeLogDerivativeMoment_zero_pos`:
  variação estrita da razão nativa.
- `canonicalCompletedNativeChiralTwoPoint_contractive_eventually`:
  sinal do balanço integrado para duas leituras.
- `Matrix.star_dotProduct_gram_mulVec` e o teorema fundamental do cálculo:
  síntese Hilbert e integração da identidade diferencial.

`CompletedNativeChiralReturnAudit.lean` imprime os axiomas dos teoremas
novos. O registro de execução fica em
`research/chiral-return-storage-2026-09-05/validation.txt`.
