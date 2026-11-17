# Curvatura cruzada e equilíbrio dos resíduos Schur — auditoria 2026-11-17

**Estado:** resultados estruturais em Lean provados, cota universal da fonte **ABERTA**. Sem alturas de zeros como entradas. Esta worktree é isolada e não altera as demais branches.

## Objetos e proveniência

Os resíduos usados são os de `nativeSourceSchurRemainder s n` (CSA), com `s=0` par e `s=1` ímpar. Pela identidade já provada `nativeSourceSchurRemainder_eq`, equivalem a `c₀·sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment s n`; o `c₀` é o coeficiente inicial **da característica completada**, não uma renomeação do bracket original. Outra construção GoN tem `sourceSchur c b n = c₀²·sourceMomentSchur h s n` sob prefixo invertível. As escalas não devem ser misturadas.

Escrevendo `Eₙ=nativeSourceSchurRemainder 0 n`, `Oₙ=nativeSourceSchurRemainder 1 n`, a condição empírica forte é:

- `|EₙEₙ₊₁−Oₙ²| < (1/2)Oₙ²` (centro ímpar);
- `|OₙOₙ₊₁−Eₙ₊₁²| < (1/2)Eₙ₊₁²` (centro par).

Não há demonstração dessas duas desigualdades em todo `n` para a fonte nativa.

## Formalizado e compilado

Arquivo: `SchurCurvatureGate.lean`. Axiomas impressos: apenas `propext`, `Classical.choice`, `Quot.sound`. `-DwarningAsError=true` passou.

1. `evenR_zero_pos`, `oddR_zero_pos`: os **dois resíduos iniciais são positivos incondicionalmente** a partir dos certificados originais.
2. `cross_curvature_propagates_sign_of_bounded_budget`: qualquer orçamento relativo uniforme `ρ < 1` nos dois centros propaga positividade em todas as ordens. `native_boundary_pos_of_bounded_cross_curvature` conecta essa condição à **energia original de bordo** via equivalência preexistente; `native_radial_return_contractive_of_half_cross_curvature` fecha a contração radial eventualmente para cada `N`, sob a hipótese forte.
3. `abs_cross_curvature_iff_two_sided`: a cota absoluta possui **duas** obrigações: `(1−ρ)b² < ac` **e** `ac < (1+ρ)b²`. Para apenas o sinal, basta a primeira. `native_boundary_pos_of_one_sided_cross_curvature` prova essa versão mais fraca.
4. `evenR_eq_signedThetaMass`, `oddR_eq_signedThetaMass`: cada resíduo continua sendo a **diferença exata das massas positiva e negativa** da fonte teta original, não um integrando positivo ponto a ponto.
5. `actual_top_odd_product_ratio`, `actual_top_even_product_ratio`: identidades em **coeficientes líderes reais dos polinômios da fonte**, usando o teorema preexistente `nativeSchurThetaPolynomial_coeff_top` e as relações exatas entre fatoriais.
6. `oddLeadingRatio_gap`, `evenLeadingRatio_gap`, `oddLeadingRatio_tendsto_one`, `evenLeadingRatio_tendsto_one`: os dois quocientes de coeficientes líderes convergem **incondicionalmente** a 1 por baixo. Os defeitos são:

   ```text
   1 − Rodd(n)  = (8n+7)/(2(n+1)(4n+5)) <= 1/(n+1)
   1 − Reven(n) = (8n+3)/((2n+1)(4n+3)) <= 2/(n+1)
   ```

   Trata-se de **equilíbrio do símbolo líder**. Não equivale a `EₙEₙ₊₁/Oₙ²→1`, `OₙOₙ₊₁/Eₙ₊₁²→1` ou `Eₙ,Oₙ>0`.
7. `oddLead_negative`, `oddR_eq_leadingMass_add_lowerIntegral`, `oddR_positive_requires_lower_compensation`: o termo de maior grau da fonte ímpar tem **massa negativa**. Quando o resíduo ímpar é positivo, a integral do polinômio inferior precisa **superar em magnitude** essa massa negativa. Logo os termos inferiores não podem ser tratados como perturbativamente pequenos *sem nova estimativa comprovada*.
8. **Controles negativos:** `compact_uniform_control_breaks_half_gate` formaliza que a medida uniformemente positiva em `[0,1]`, momentos `mₖ=1/(k+1)`, viola a cota forte já no primeiro centro ímpar: `T₀=1,T₁=1/2,T₂=1/12`, razão `T₀T₂/T₁²=1/3`. `factorial_control_breaks_half_gate` fornece controle adicional `mₖ=k!` (medida exponencial positiva). **Nem Stieltjes positivo, nem compacidade do suporte, nem a recorrência formal bastam**, isoladamente, para impor `ρ=1/2`. São controles de outras fontes, não contraexemplos C2.

## Reconhecimento numérico (NÃO provado em Lean)

Dados: `stage_B/coefficients.json`, campo `canonical_h`, 256 momentos provenientes da auditoria, sem alturas de zeros como entrada. Eliminação de Schur multiprecisão (1800 dps), tamanho 128 em cada setor, cobriu 254 trincas de curvatura.

| Centros amostrados | Maior erro absoluto relativo |
|---|---:|
| Todos | 0,4576486343680939 (centro par n=1) |
| n ≥ 2 | 0,3244528939613302 |
| n ≥ 3 | 0,2140596118352575 |
| n ≥ 6 | 0,1667295525956180 |
| n ≥ 25 | 0,1138585327209717 |
| n ≥ 100 | 0,0670055485603045 |

Hipótese útil para segmentar obrigações: cabeça `n=0,1,2` com `ρ=1/2`; cauda `n≥3` com `ρ=1/4`. Ambas permanecem **sem certificação de fonte em ordem arbitrária**. A cota `ρ=1/4` se verificou numericamente apenas na faixa disponível.

## Lacuna matemática real

A curva de coeficientes líderes explica **um pré-equilíbrio algébrico**, mas a fonte original é uma integral assinada de polinômios de Schur. O lado ímpar tem cauda negativa em toda ordem (cf. `nativeSchurThetaPolynomial_odd_density_eventually_neg` e `nativeSchurThetaPolynomial_odd_negativeMass_pos`). Uma prova que tente inferir sinais apenas da parte líder falha na orientação.

**Obrigações úteis a seguir:**

1. Na cabeça `n≤2`, produzir caixas **correlacionadas e certificadas** para as duas desigualdades cruzadas a partir dos coeficientes originais (não apenas sinais individuais). Usar como insumo os certificados finitos C3/GoN existentes, preservando a comparação exata da fonte.
2. Na cauda `n≥3`, estimar **de forma conjunta** o produto dos três integrais assinados por meio de uma desigualdade de fonte com erro controlado: `|EₙEₙ₊₁−Oₙ²| ≤ εₙ Oₙ²` e `|OₙOₙ₊₁−Eₙ₊₁²| ≤ εₙEₙ₊₁²` com `εₙ<1`. Se apenas positividade for o objetivo imediato, atacar a cota unilateral inferior, estritamente mais fraca.
3. Só depois investigar `εₙ→0` e a taxa de aproximação do acoplamento Jacobi. Não presumir que o equilíbrio do símbolo líder passe à integral.
4. Guardar os casos de controle compacto/exponencial como testes para detectar provas genéricas indevidas.

## Validação

```bash
cd /home/thlinux/carry-self-adjoint-operator
lake env lean -DwarningAsError=true \
  /home/thlinux/worktrees/csa-source-schur-curvature-gate-20261117/research/source-schur-curvature-20261117/SchurCurvatureGate.lean

python3 /home/thlinux/worktrees/csa-source-schur-curvature-gate-20261117/research/source-schur-curvature-20261117/probe_curvature.py \
  /home/thlinux/momentos/native-jet-vm-20260930/native_jet_exploration/auditoria_corrected_vs_canonical/stage_B/coefficients.json
```

Não foi demonstrada positividade de Hankel em ordem arbitrária, nem qualquer consequência para a hipótese de Riemann. Nenhuma alteração em outras worktrees.
