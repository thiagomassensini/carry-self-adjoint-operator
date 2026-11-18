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

## Adendo — distribuição de ímpares por característica e rota C2/L² (2026-11-17)

**Correção de normalização:** a lei de contagem é uma massa `2⁻ᵏ` por ramo. Para ímpares agrupados pelo tipo efetivo `K_eff(n)=max(v₂(n−1),v₂(n+1))≥2`, existem **dois ramos**, logo a frequência entre ímpares é `P(K_eff=k)=2^(1−k)`. Assim, para `k=2,3,...`, aparecem `1/2,1/4,1/8,...`. Para o **centro de um par gêmeo** `c=p+1`, usamos uma variável diferente `v₂(c)≥1`; o modelo probabilístico é `2⁻ᵏ`, `k=1,2,...`. O fator `2^(-k/2)` é a escala de **amplitude/norma L²**, não a lei de contagem.

**Teste reproduzível:** `probe_odd_selection.py [N]`, por padrão `N=12000000`; usa crivo de primos e classes originais de profundidade inteira, **sem alturas dos zeros**. Foram 6 milhões de ímpares (efeitos de borda), 5.211.939 compostos, 650.038 primos isolados (definição operacional: `p±2` não primos), 69.010 pares gêmeos com ambos no intervalo da amostra.

| `K_eff` | Todos os ímpares | Compostos | Primos isolados | Primo inferior do par gêmeo |
|---|---:|---:|---:|---:|
| 2 | 50,0000% | 49,9993% | 50,0057% | 49,9464% |
| 3 | 25,0000% | 24,9998% | 24,9632% | 25,2992% |
| 4 | 12,5000% | 12,4993% | 12,5193% | 12,3475% |
| 5 | 6,2500% | 6,2494% | 6,2630% | 6,2324% |

A contagem dos gêmeos difere em uma unidade de outro protocolo da conversa (69.011 pares até `p+2 ≤ 12M`) porque o script de quatro subconjuntos seleciona só `p` em `odd<limit−1`; é **efeito de borda**, não divergência de algoritmo. Resultados para k fixo em recortes crescentes são observações finitas. Equidistribuição assintótica de gêmeos em classes diádicas não foi provada; não confundir com a teorema dos primos em progressões (primos *individuais*).

**Identidade exata da seleção:** para `A` a característica, `D_k` a classe e `a=P(A)>0`,
`P(D_k|A) = P(D_k)·P(A|D_k)/P(A)`. Portanto a distribuição condicional fica próxima da geométrica se e somente se a característica é aproximadamente não enviesada nas camadas, isto é `P(A|D_k)/P(A) ≈ 1`. Cauchy–Schwarz dá a cota universal
`|P(D_k|A)−P(D_k)| ≤ sqrt(((1−a)/a)P(D_k)(1−P(D_k)))`.
**Cuidado:** para propriedades raras, o coeficiente `sqrt((1−a)/a)` é grande; a cota não explica a precisão observada para gêmeos.

**Formalizado em `C2SelectionL2.lean`:**
- `finiteShellEnergy_le_card` e `finiteShellNormalizedEnergy_le_mass`: qualquer observável `f`, `|f|≤1` numa camada finita `D`, tem energia média ≤ massa da camada.
- `finiteShellNormalizedEnergy_le_dyadic`, `finiteShellAmplitude_le_sqrtDyadic`: **sob uma cota de massa da camada** ≤ `2^(-k)`, sua amplitude `sqrt(energia)` é ≤ `sqrt(2^(-k))`.
- `finiteShellCauchySchwarz`: ponte exata de produto interno via Cauchy–Schwarz, independente da primalidade.
- Este arquivo é **um enunciado genérico L²**. A contagem da fonte C2 está no outro repositório (`CPFormal/Carry/C2OddCorePushforward.lean`) e **não é importada automaticamente** no CSA. Nenhuma realização física de Schur pelo indicador de profundidade foi assumida.

**Obstrução formalizada em `SchurRelativeAmplification.lean`:** `nearSingularSchur_relative_change_one` mostra que matrizes `[[1,1],[1,1+eps]]` e `[[1,1],[1,1+2eps]]`, ambas positivas para `eps>0`, diferem apenas `eps` na diagonal, mas seu pivô de Schur dobra. `relative_schur_not_controlled_by_absolute_diagonal_margin` formaliza que isso ocorre com `eps` arbitrariamente pequeno. Consequência: uma cota absoluta de Parseval na fonte **não controla automaticamente** a curvatura **relativa** de Schur, principalmente quando o pivô é quase zero.

**Próxima obrigação específica:** construir uma aplicação fiel a partir das camadas **materiais C2**, por TFVD e Parseval existentes, para as **formas quadráticas canônicas completadas** e demonstrar uma cota relativa, da forma `erro_n ≤ eps_n × pivot_n`, ou um orçamento alternativo para os produtos de três resíduos. Sem isso, a correspondência entre o índice de bloco `j=floor(log₂ n)` e profundidade material `k` é apenas heurística.

Validação adicional:
```bash
lake env lean -DwarningAsError=true research/source-schur-curvature-20261117/C2SelectionL2.lean
lake env lean -DwarningAsError=true research/source-schur-curvature-20261117/SchurRelativeAmplification.lean
python3 research/source-schur-curvature-20261117/probe_odd_selection.py 12000000
```

## Adendo: controle relativo de fonte e fatoração exata da compensação assinada

**Teorema novo em Lean** `RelativeSchurSourceTransfer.lean`: suponha `g` uma fonte de comparação cuja **matriz do prefixo antigo** seja positiva definida, e `m` a fonte a ser certificada, com
`(1−δ) Q_g(x) ≤ Q_m(x)` para todos os vetores da matriz ampliada, onde `δ<1`. Então, sem hipótese de sinal de `sourceMomentSchur m s n`:
```
(1−δ) * sourceMomentSchur g s n ≤ sourceMomentSchur m s n.
```
A prova usa a direção crítica da fonte `m`, a identidade `sourceMomentSchur_critical_direction_total` e a complete-square de `g`. Se o pivô da fonte de comparação foi **independentemente** certificado positivo, a conclusão é positividade do pivô real. A versão `schur_lower_of_signed_relative_form_budget` aceita uma cota absoluta **relativa à energia da referência**, não uma cota absoluta de Parseval.

**Aviso:** a existência de referência positiva e a comparação relativa **não estão provadas** em todas as ordens para o C2 físico; o teorema é um transporte fiel de um certificado QUE AINDA FALTA. Uma referência arbitrariamente construída de momentos positivos não é o transporte do bracket material.

**Outra identidade exata** (adicionada em `SchurCurvatureGate.lean`): escrevendo
`Eₙ = nativeSourceSchurRemainder 0 n`, `Oₙ = nativeSourceSchurRemainder 1 n`, `L0ₙ>0`, `L1ₙ<0` seus coeficientes líderes,
```
C0ₙ = Eₙ/L0ₙ,    C1ₙ = Oₙ/(-L1ₙ)
Eₙ Eₙ₊₁ − Oₙ² =
  (L1ₙ)² * [Roddₙ C0ₙ C0ₙ₊₁ − C1ₙ²].
```
Existe a fórmula correspondente para o centro par. Ambas são teoremas em Lean:
`source_odd_curvature_eq_leading_mul_compensation`,
`source_even_curvature_eq_leading_mul_compensation`.
Os fatores `Roddₙ` e `Revenₙ` são EXATAMENTE os quocientes líderes já conhecidos, que tendem a 1 com defeito de ordem `1/n`.
O novo teorema `native_boundary_pos_of_compensation_budget` prova a positividade de bordo de todas as ordens **condicionada** às duas desigualdades de curvatura nas compensações `C0,C1`, agora sem mascarar os termos inferiores.

**Controle numérico:** `probe_compensation.py` recompõe os resíduos a partir de `canonical_h` e remove a lei conhecida `Rodd,Reven`. No bloco 64–126 o RMS original é `0.0359448`; o RMS do desequilíbrio restante `0.0356142`; o RMS do coeficiente líder sozinho é apenas `0.0110110`. O fenômeno de escala aproximadamente `2^(-j/2)` persiste na compensação assinada, não apenas nos fatoriais. Isto é observação finita, não um Parseval da fonte física.

**Pontos de origem já formalizados:** `C2GeometryNativeSourceBridge.lean` fornece `canonicalC2Geometry_nativeTaylorReadout_eq_seed_add_fibreBrackets` e a identificação da coluna corrigida C2 com momentos de câmera; `NativeBracketTfvdGreenSameGeometry.lean` dá a identidade de mesma geometria de bracket/TFVD/Green para câmera 3. A passagem da fonte à integral assinada é `nativeSchurThetaPolynomial_integral`. `research/native-moment-orthogonalization-audit/SchurLogic.lean` do GoN contém `native_boundary_real_sector` (energia de bordo original = 4 vezes a forma quadrática canônica), *não uma nova energia positiva*.

**Obstrução física que não pode ser descartada:** `research/native-cauchy-residual-return/ProjectionLoss.lean` do GoN prova `projection_loss_polarized` e `projection_loss_schur_tendsto`: projetar os canais de retorno pode perder um termo positivo de norma cujo limite normalizado NÃO se anula. Logo não se pode simplesmente substituir a energia original por uma soma de quadrados projetada.

**Restante aberto e específico:**
1. Construir a forma positiva de comparação a partir da fonte **material** (C2 → TFVD/Green e completamento, sem usar a positividade nativa por hipótese).
2. Demonstrar a desigualdade de forma **uniformemente para todas as direções** (incluindo os termos de retorno) ou estimar diretamente a curvatura das integrais `C0,C1`. Uma cota Parseval absoluta ou um controle só da primeira coluna não basta.
3. Certificar a cabeça difícil separadamente e então mostrar que o orçamento relativo da cauda é estritamente inferior ao pivô em escala correta.
4. Só assim transportar o decaimento diádico da energia física para a ordem matricial; nenhuma identificação `j=floor(log₂ n) = k` foi provada.
