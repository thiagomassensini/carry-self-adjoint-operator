# Espectro pontual positivo de Jacobi e zeros nativos

Para qualquer família `jet : (ℕ ⊕ ℕ) → E` em um espaço de Hilbert real e qualquer
`certificate : CompletedNativeRealHPCarrierCertificate jet`, o operador concreto

```lean
certificate.completedJacobiEnergySelfAdjointData.complexification
```

tem a correspondência exata, para todo `lambda : ℝ` com `0 < lambda`:

$$
\lambda\in\sigma_p(J_{\mathbb C})
\quad\Longleftrightarrow\quad
F\bigl((\sqrt{\lambda})^{-1}\bigr)=0,
\qquad F=\mathtt{completedNativeOperatorCharacteristic}.
$$

O predicado `LinearPMap.HasEigenvalue` exige um vetor não nulo no domínio do
operador parcial, com a equação de autovetor nesse domínio. O resultado também
é exportado para todo `t : ℝ`, `t ≠ 0`, na forma

$$
t^{-2}\in\sigma_p(J_{\mathbb C})\quad\Longleftrightarrow\quad F(t)=0.
$$

Os nomes completos ficam no namespace `CompletedNativeRealHPCarrierCertificate`:

- `completedNativeOperator_eq_zero_of_hasEigenvalue_inv_sq`;
- `completedJacobiEnergyComplexification_hasEigenvalue_inv_sq_iff_nativeZero`;
- `completedJacobiEnergyComplexification_hasEigenvalue_iff_nativeZero`.

A primeira declaração aceita `z₀ : ℂ`, pertencente a
`completedNativeHeightDomain`, com `z₀ ≠ 0` e `z₀.im = 0`. Nas duas equivalências,
a inclusão das alturas reais no domínio é descarregada pela prova existente.

## Hipóteses conservadas

O certificado continua a exigir exatamente:

```lean
IsGreenWronskianMomentKernelGramRepresentation
  canonicalCompletedNativeLogDerivativeMoment jet
LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))
LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))
```

O espaço ambiente inicial precisa de `NormedAddCommGroup E` e
`InnerProductSpace ℝ E`. A construção existente completa o jet e trabalha no
subespaço fechado par; completude do espaço inicial não é uma hipótese nova.
Não se assume existência incondicional desse certificado.

## Demonstração da recíproca

1. Uma órbita real de domínio com span denso detecta todo autovetor da
   complexificação. Se o autovetor fosse ortogonal ao vetor inicial, a identidade
   de adjunção propagaria a ortogonalidade por toda a órbita. As duas quadraturas
   reais seriam ortogonais a um subespaço denso e, portanto, nulas. O lema
   `CyclicPointSpectrum.eigenvector_visible_of_real_cyclicOrbit` explicita os
   domínios de cada passo.
2. Usa-se a aproximação já construída
   `lambda_n = lambda₀ + i/(n+1)`, com `lambda₀ = z₀⁻²`, e seu ramo de altura
   `z_n → z₀`, `z_n⁻² = lambda_n`. Seja
   `r_n = (J_C - lambda_n)⁻¹ e` e `u_n = (lambda_n - lambda₀) r_n`.
3. Se `F(z₀) ≠ 0`, a continuação de Weyl `W(z) = -F′(z)/(2zF(z))` é analítica
   perto de `z₀`. A identidade já provada transforma o readout escalado em
   `((z_n + z₀)/z₀²) (z_n - z₀) W(z_n)`, que tende a zero.
4. A identidade polarizada do resolvente, com os dois pesos positivos que somam
   um, implica `⟨u_k,u_n⟩ → 0`. Na diagonal, `‖u_n‖² → 0`; logo `u_n → 0` em norma.
5. Para um autovetor `x` de autovalor real `lambda₀`, a equação do resolvente e a
   adjunção dão exatamente `⟨x,u_n⟩ = -⟨x,e⟩`. O lado esquerdo tende a zero,
   contradizendo a detecção por ciclicidade.
6. A direção zero → autovalor é a extração atômica já existente em
   `CompletedNativeJacobiCyclicAtomicExtraction.lean`.

A convenção do readout permanece `m_J(lambda) = ⟨e,(J_C-lambda)⁻¹e⟩`.
A passagem ao limite vetorial dispensa uma estimativa quantitativa separada de
crescimento como `1/eta`; não acrescenta hipótese de medida espectral.

## Alcance

O resultado identifica o espectro **pontual positivo** de `J_C`. Não identifica
o espectro contínuo, não resolve o caso `lambda = 0` e não identifica a ordem
analítica dos zeros com a dimensão dos autoespaços. A recíproca para o operador
de altura assinado requer o transporte inverso dos autovetores e seus domínios.

A realização geométrica do certificado permanece uma obrigação própria. Sua
formulação com o kernel e os bordos efetivos está em
[Atualização do mapa de costuras](carry-seams-2026-09-04-update.md).

## Verificação

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeJacobiPointSpectrumConverseAudit
bash scripts/audit.sh
git diff --check
```

Executado no servidor em 2026-09-04, com Lean 4.32.0 e os pins preservados:
a auditoria dedicada concluiu 4.093 jobs e `scripts/audit.sh` terminou com
`kernel audit passed`.

A auditoria dedicada imprime os axiomas de todos os nove lemas novos; todos
dependem apenas de `propext`, `Classical.choice` e `Quot.sound`. Ela está
incluída no script completo, preservando a cobertura de `BoundaryTraceAudit` e
da universalidade multibase. Os resultados executados são registrados na PR.
