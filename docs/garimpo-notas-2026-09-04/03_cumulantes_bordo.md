# Garimpo das notas: cumulantes, retorno Green, Möbius e métrica de bordo

Data da leitura: 2026-09-04. Escopo: seleção dos arquivos de Downloads indicada pelo agente principal; originais preservados. As fórmulas de papel foram confrontadas com os enunciados Lean disponíveis. Os rótulos históricos `[F]`, `CLOSED` e `NO_GO` não foram interpretados como verificação Lean nem como afirmações sobre qualquer realização futura.

## Resultado que ajuda a costura

As notas oferecem três mecanismos algébricos precisos, além do que já estava destacado no mapa: (i) decomposição da Green em traço visível mais compressão residual `Q D Q`; (ii) métrica positiva explícita das duas coordenadas do traço TFVD; (iii) Gram positivo de funções-cauda de Möbius, com independência por extremidade de suporte. Também há uma versão muito mais longa do registro Mellin, escondida na pasta `teoria_defeitos_pack`, que corrige as metas e os resultados negativos de versões curtas.

Não localizei nestes arquivos uma demonstração da identificação desses Grams com `dslope(-F′/(2F))` para a característica nativa completada. Isso é um resultado da leitura dos enunciados e seus objetos, não um no-go geral. A oportunidade concreta é usar as fórmulas para calcular o residual e a normalização do estado completo, mantendo os parâmetros e o bordo.

## 1. Versões: diferença material que não se deve perder

- Os sete arquivos `DEFEITO_GREEN_CUMULANTES_MELLIN*.md` na raiz de Downloads são cópias idênticas, de 353 linhas, terminando no §8.
- [Versão extensa](</home/thlinux/Downloads/teoria_de_defeitos/teoria_defeitos_pack/DEFEITO_GREEN_CUMULANTES_MELLIN.md:355>): 2142 linhas, 43 seções, com vários resultados posteriores. Esta deve ser consultada primeiro para a rota de retorno.
- [Consolidado mestre](</home/thlinux/Downloads/teoria_de_defeitos/teoria_defeitos_pack/CONSOLIDADO_MESTRE_C2_CP_GREEN_PSI.md:1286>) já registra que o modelo antigo tinha pequenos cortes com norma mínima acima de 1, enquanto um modelo reduzido local posterior volta a ter os cortes testados contrativos. São métricas/domínios diferentes.
- [Nota ponte de 31/08](</home/thlinux/Downloads/teoria_de_defeitos/teoria_defeitos_pack/NOTA_PONTE_ARQUIVOS_ANTIGOS_ROTA_POSITIVIDADE_TILT_DSLOPE_HANKEL_2026-08-31.md:339>) é um guia de hipóteses para a costura atual. Seus trechos “possível forma moderna”, “hipótese a testar” e H1–H7 continuam propostas de identificação; a própria nota não apresenta a igualdade nativa.

## 2. Traço complementar explícito e residual `Q D Q`

Fonte: [Relatório do canal oculto, §9, L499–589](</home/thlinux/Downloads/RELATORIO_CANAL_OCULTO_GREEN_NAIMARK_MOBIUS.md:499>), de 15/07/2026.

Para um atlas finito com análise de portas `Γ` sobrejetiva, defina

$$
G=\Gamma\Gamma^*,\qquad
P=\Gamma^*G^{-1}\Gamma,\qquad Q=I-P.
$$

Se `D* = −D` é o defeito Green do operador usado na nota, então

$$
\Psi_0=-G^{-1}\Gamma D\left(I-\frac12P\right)
$$

satisfaz a identidade exata

$$
\boxed{D=\Psi_0^*\Gamma-\Gamma^*\Psi_0+QDQ.}
$$

A prova é multiplicação de operadores: a diferença de traços é `PD+DP−PDP`; somando `(I−P)D(I−P)` recupera-se `D`. O artigo toma `D=L*−L`, mas o lema algébrico usa somente antiadjunção e a projeção ortogonal. Com `x,y` distintos, a fórmula preserva diretamente os termos bilineares; o residual é `⟨Qx,DQy⟩`.

O §10, L593–620, constrói ainda portas ocultas abstratas `Γ_H=HQ`, `Ψ_H=−(1/2)HQDQ`, com `H*H=Q`, fatorando exatamente o residual. Isso localiza a informação que a compressão visível perdeu. Não prova que essas portas abstratas sejam o Gamma/TFVD concretamente consumido pelo autoadjunto.

**Uso:** comparar `P`, `Q` e o estado da nota à projeção Bessel concreta e ao residual do mesmo estado completado, em vez de deduzir cancelamento do nome “residual”. O destino formal atual é `canonicalEnrichedScalarBoundary_eq_green_add_explicitDefects` / `..._iff_explicitDefects_cancel`, em `CanonicalEnrichedBoundaryResidualIdentity.lean:82,143`; o relatório oferece um modo candidato de organizar seus termos, mas não prova que a soma dos três defeitos seja `QDQ` nem que desapareça.

**Validação nesta leitura:** identidade matricial testada simbolicamente, com aritmética racional exata, para uma matriz `Γ` 2×4 de linhas não ortogonais e um `D` antissimétrico 4×4; igualdade exata confirmada. A derivação algébrica acima explica o caso geral. Nenhum novo lema Lean foi compilado.

## 3. Métrica de traço TFVD e polarização sem perder o cruzamento

Fonte: [Deep Dive V2, Derivações exatas, §6, L276–336](</home/thlinux/Downloads/PRIMOS_TFVD_HILBERT_COVARIANT_MASS_GAP_DEEP_DIVE_V2/DERIVACOES_EXATAS.md:276>); desenvolvimento de `A_q` em L7–130 e limite inferior em L132–173.

Em `ℓ²(ℕ₀;ℂ)`, `U` é o shift unilateral, `0<q<1` e

$$
A_q=q^{-1}(I-qU)^2.
$$

As primeiras coordenadas de `A_qx` são `(q⁻¹x₀,q⁻¹x₁−2x₀)`; a cauda é o bracket. No traço usado pela TFVD,

$$
t_q(x)=(x_0,q^{-1}x_1-x_0),\qquad
M_q=\begin{pmatrix}q^{-2}+1&-1\\-1&1\end{pmatrix},
$$

vale

$$
\|A_qx\|^2=\|B_qx\|^2+t_q(x)^*M_qt_q(x).
$$

**Dedução bilinear imediata nesta leitura**, pelas mesmas coordenadas ou polarização:

$$
\boxed{\langle A_qx,A_qy\rangle
=\langle B_qx,B_qy\rangle+t_q(x)^*M_qt_q(y).}
$$

Temos `M_q=J_q*J_q`, `J_q=[[q⁻¹,0],[−1,1]]`, e `det M_q=q⁻²>0`. A nota prova também `‖A_q⁻¹‖=q/(1−q)²` e `A_q*A_q≥(1−q)⁴/q² I`. Esses fatos fornecem uma métrica coerciva concreta no espaço de análise.

Essa métrica é distinta da norma de síntese `x=G_qB_qx+R_qt_q(x)`. [Relatório V2, L737–748](</home/thlinux/Downloads/PRIMOS_TFVD_HILBERT_COVARIANT_MASS_GAP_DEEP_DIVE_V2/RELATORIO_FINAL.md:737>) explicita por que Green e retorno podem ter grande termo cruzado após a síntese. A [extensão, §13, L715–753](</home/thlinux/Downloads/TFVD_PRIMOS_HILBERT_COVARIANT_MASS_GAP_EXTENDED/RELATORIO_FINAL.md:715>) mostra exatamente como as partes variam com a base enquanto sua soma é conservada.

**Confronto Lean:** a reconstrução ponderada e sua expansão em quatro canais já alimentam `canonicalCarryTfvd_inner_eq_fourChannel`, em `ProjectiveValveCarryEnergyFrontier.lean`, e `canonicalCompletedC3RawGammaGram_eq_causalFourChannel`, em `CompletedC3CausalGreenGramSewing.lean:98`. A nova peça de papel é a matriz 2×2 pública para o Gram da análise. Para descarregar A/B, falta provar qual mudança de métrica/observável produz o kernel nativo; o gap de `A_q*A_q` não identifica os momentos do Jacobi nativo.

## 4. Cumulantes: o que já virou Lean e o que ainda é extensão

Fontes: [teoria unificada, §3, L277–442](</home/thlinux/Downloads/teoria_defeitos_c2_unificada.md:277>), [teorema geral, L1–186](</home/thlinux/Downloads/teoria_de_defeitos/teoria_defeitos_pack/09_teorema_geral_cumulantes.md:1>), e Mellin extenso L1–82.

Para a massa com termo constante 1, a equação deconvolutiva é `B A=E A`, com `E=Σ log(p) x_p∂_p`. Na álgebra escalar comutativa,

$$
b_M(p^\alpha)=\log(p^\alpha)\,[x^\alpha]\log A_M.
$$

A recorrência triangular de `K_α=[x^α]log A` é

$$
K_\alpha=A_\alpha-\frac1{\alpha_k}
\sum_{0\ne u\le\alpha-e_k}A_u(\alpha_k-u_k)K_{\alpha-u}.
$$

A conexão vestida `Ψ=A B=E A` conserva o produto antes da divisão pela massa. No caso operador não comutativo, a equação triangular é a definição; `E log A` necessita de hipóteses adicionais. A coisometria local `A_m A_m*=I`, `A_mV_m=a_m`, `A_mD_m=E_mA_m` do script `c2_cumulant_naimark_intertwiner.py:1–22` é verdadeira nas fibras explicitadas, mas não demonstra por si só a identidade de deconvolução global.

**Peças já formalizadas conferidas no pin CPFormal `65d50f6db1208708e109982ba97e1d51d3039956`:**

| Módulo/declaração | Escopo verificado |
|---|---|
| `CpC2OddCorePushforwardTfvd.lean:239–291`, `c2OddCoreLogCoefficientArithmetic_mul_mass` | A massa concreta de cutoff, com semente normalizada, possui inverso de Dirichlet e satisfaz exatamente `b_T*a_T=a_T log`. Não é apenas uma hipótese formal. |
| Mesmo arquivo L334, `c2OddCoreLogCoefficient_distinct_primes` | Para primos ímpares distintos, o coeficiente em `pq` é `log(pq)` vezes o cumulante concreto. |
| Mesmo arquivo L456, `c2OddCoreLogCoefficient_mul_positiveDirichletValue`; L480, `positiveLogDirichletValue_eq_sum_range_gradient` | O cumulante vestido é o mesmo vértice log-Dirichlet e telescopa pelos gradientes do log-jet. |
| `CpC2DirichletJetTfvd.lean:95,169`, `c2OddCoreDirichletSpectralGap_eq_connectedCumulant_mul`, `c2OddCoreDirichletLogSpectralGap_eq_connectedCumulant_mul` | Células espectrais ordinary/log são cumulante concreto vezes o termo Dirichlet/log-Dirichlet na frequência `pq`. |
| `CpNativeCarryMobiusLogDerivativeGuardrail.lean:39–80` | `integerLog_mul_moebius_eq_primePowerSignal`, `primePowerSignal_mul_zeta_eq_integerLog`, round-trip, soma de divisores e identificação com log-derivada no semiplano `1<Re(s)` são teoremas; o título guardrail não amplia esse escopo. |

A recorrência multivariada geral é candidata de extensão da API, mas o autoadjunto já dispõe de uma recorrência escalar suficiente para identificar sua sequência: `completedNativeLogDerivativeMoment_fullConvolution`, `CompletedNativeWeylMoments.lean:63`, e `completedNativeLogDerivativeMoment_eq_canonical`, `CompletedNativeRealWeylMoments.lean:260`.

**Passo útil para A:** se os produtos internos candidatos produzirem uma sequência `g_n` que satisfaça a convolução concreta de `F`, a unicidade já prova `g=h`. Não é preciso adivinhar `h`. **Passo útil para B:** ainda é necessária a simetria de deslocamento das duas ordens, `c(p,q+1)=c(p+1,q)`; a deconvolução escalar isolada não a implica.

## 5. Mellin extenso: altura, canais de gráfico e metas que evoluíram

[§39, L1663–1735](</home/thlinux/Downloads/teoria_de_defeitos/teoria_defeitos_pack/DEFEITO_GREEN_CUMULANTES_MELLIN.md:1663>) conserva os pares `(m,n)` antes de reduzir sua razão. Com `D_t=diag(n⁻ⁱᵗ)`, a nota deriva

$$
K_{N,t}(R)=D_tK_{N,0}(R)D_t,\qquad
H_{N,t}=2^{it}D_tH_{N,0}D_t.
$$

Assim, uma igualdade **par a par** em altura zero é transportada por `R_t=2ⁱᵗR`, preservando a norma. O par usa um kernel bilinear refletido; por isso aparecem `D_t` nas duas pontas, sem adjunto. Ao reduzir `(ka,kb)` a `a/b`, perde-se a variável `k` onde mora a fase `k⁻²ⁱᵗ` (§38). Essa informação é relevante para não confundir parâmetro nativo e índice material.

[§40, L1740–1803](</home/thlinux/Downloads/teoria_de_defeitos/teoria_defeitos_pack/DEFEITO_GREEN_CUMULANTES_MELLIN.md:1740>) substitui certos canais crus por três canais covariantes `α∈{0,1/2,1}`:

$$
Y_{n,\alpha,d}(s)=\sqrt{h_n}\,V_{n+1}(d)
\Delta\bigl((\log n)^\alpha n^{-s}\bigr).
$$

Como `Σ_d|V_{n+1}(d)|²=1`, a energia de fibra é exatamente `h_n|Δ((log n)^α n⁻ˢ)|²`. A estimativa registrada é `≤C_s n⁻²σ⁻¹(1+log n)^(2α+2)` para `σ>0`, somável. Isso evita inferir ℓ² da amplitude nua `n⁻¹/²` em contagem usual; o ganho vem da diferença. Para a curva e os pesos efetivos escolhidos, a estimativa é uma candidata concreta de controle de cauda/domínio de gráfico.

No autoadjunto, `CompletedNativeTfvdCoefficientJets.lean:236–366` já apresenta as potências logarítmicas ímpares e sua independência. L449–495 prova a órbita `exp(−i t log m)` e limites de forward differences. A nota acrescenta o modelo de cauda covariante; é preciso alinhar exatamente os pesos `h_n` dessa nota e os coeficientes do estado completado.

**Evolução histórica dos resultados negativos:**

- §37, L1575–1631: a antiga conjectura `μ_N≤1` para todo corte falha nos números apresentados daquele modelo. O alvo é reformulado para `sup_N μ_N<∞`, mais passagem das equações e desaparecimento do halo.
- §41, L1805–1897: o trio covariante encontra retornos finitos de norma da ordem de 1 e propõe cota Hardy/Schur uniforme com tightness. São dados finitos, não prova da cota uniforme.
- §43, L1967–2015: a janela rígida `d<m≤2(n+1)` é numericamente incompatível com a igualdade par a par em certos cortes.
- **No mesmo texto, §43.2, L2017–2053:** após agregar os carries da mesma razão, essa janela é viável em todos os cortes testados e os ótimos espectrais são contrativos. Logo o insucesso par a par não pode ser utilizado para proibir a rota reduzida.
- §43.4, L2094–2131: ainda se propõem Schur uniforme e transferência diamagnética no problema reduzido. Não encontrei demonstração dessas estimativas em ordem arbitrária nesse registro.

## 6. Gram positivo de caudas de Möbius

Fonte: [Möbius log-clock, §§5–7, L259–473](</home/thlinux/Downloads/MOBIUS_LOG_CLOCK_CONNECTED_DRESSING_THEOREM.md:259>).

Para `r≥2`,

$$
f_r(u)=\sum_{a\mid r}\mu(r/a)\mathbf1_{[0,\log a)}(u),\qquad
Q(r,s)=\int_0^\infty f_r(u)f_s(u)\,du.
$$

Em um atlas ímpar finito, a correção conectada é

$$
(\mathcal C_{conn})_{ce}
=\sum_{d\mid\gcd(c,e),\ d\ge3}\varphi(d)Q(c/d,e/d).
$$

Isso dá uma fatoração positiva explícita. As funções `f_r` são independentes: na combinação finita, junto da extremidade `log(r_max)`, só a maior função ainda contribui, com valor 1. Por isso o núcleo da correção conectada é exatamente o setor das coordenadas primas ímpares; ela é definida positiva no setor composto finito.

O mesmo artigo prova a conjugação `Z⁻¹LZ`: diagonal `log d`, e entrada estritamente abaixo da diagonal `Λ(n/d)` quando `d|n`. A correção simétrica resulta da diferença entre esse transporte esparso e a metade causal conjugada.

**Validação nesta leitura:** o Gram e a conjugação foram recomputados simbolicamente com SymPy 1.14 no servidor para o atlas ímpar até 25, usando inteiros e logaritmos exatos; após simplificação, todas as entradas coincidem. O rank exato é 4, igual às quatro câmeras compostas. Isso valida a implementação finita e acompanha a prova de papel, sem substituir formalização Lean.

**Utilidade/limite:** é uma segunda realização positiva aritmética com independência estrutural, útil para uma extensão Lean do mecanismo de residual. Seus índices são câmeras/cofatores e suas funções são caudas de divisores; ainda não foi exibido um mapa dos jets nativos que transforme esse Gram em `h_(i+j)` e `h_(i+j+1)`. Não renomear esse Gram como Hankel nativo.

## 7. Sequência sugerida, com obrigações verificáveis

1. Escrever o lema bilinear da métrica `M_q` e a decomposição abstrata `D=traço+QDQ`, caso não exista equivalente no repositório específico. São provas pequenas a partir das fórmulas atuais, úteis para tornar a comparação auditável.
2. Instanciar `Γ,P,Q,D,x(s)` com os **mesmos** canais do estado C3 completado e calcular qual termo da identidade residual atual corresponde a `QDQ`. Essa é a parte de identificação que as notas ainda não entregam.
3. Em paralelo, usar a conexão cumulante vestida para calcular a coluna `c(p,0)`. Testar se a sequência resultante satisfaz a convolução **da característica nativa completada**; aplicar então a unicidade Lean, em vez de comparar apenas os primeiros números.
4. Demonstrar transporte de ordem por um operador simétrico/identidade bilinear sobre os jets assim identificados. Isso descarrega B. A covariância de fase par a par é apoio para a variável correta, mas não é por si mesma transporte da ordem de Taylor.
5. Para a passagem ao limite, acompanhar cauda, bordo próprio e a estimativa de gráfico que sobreviveram ao modelo escolhido. Uma falha de janela rígida não exclui uma cauda controlada nem outro retorno.

Perguntas precisas para uma próxima busca nas notas: existe uma fórmula de `Γ*G⁻¹Γ` **para a fonte completada**, uma identificação explícita de `QDQ` com os três defeitos, uma conexão `A B=E A` no estado com completion/bordo, ou uma construção do retorno reduzido cuja cota Schur vale simbolicamente para todo cutoff? Essas quatro peças teriam impacto direto maior que novos testes de positividade finita.

## 8. Hashes das notas centrais

Todos os caminhos abaixo são relativos a `/home/thlinux/Downloads`.

| Arquivo | Linhas | SHA-256 |
|---|---:|---|
| [teoria_defeitos_c2_unificada.md](</home/thlinux/Downloads/teoria_defeitos_c2_unificada.md>) | 2158 | `540cbf3648731ce11a975ba6b85c37ecebc6efc2f1a08b5bb5b162bf93ce7e7c` |
| [teoria_de_defeitos/teoria_defeitos_pack/NOTA_PONTE_ARQUIVOS_ANTIGOS_ROTA_POSITIVIDADE_TILT_DSLOPE_HANKEL_2026-08-31.md](</home/thlinux/Downloads/teoria_de_defeitos/teoria_defeitos_pack/NOTA_PONTE_ARQUIVOS_ANTIGOS_ROTA_POSITIVIDADE_TILT_DSLOPE_HANKEL_2026-08-31.md>) | 1591 | `62707484c7ed753600f19c3c842f2a9041c5b6accd3ae0688707974639fc0165` |
| [teoria_de_defeitos/teoria_defeitos_pack/DEFEITO_GREEN_CUMULANTES_MELLIN.md](</home/thlinux/Downloads/teoria_de_defeitos/teoria_defeitos_pack/DEFEITO_GREEN_CUMULANTES_MELLIN.md>) | 2142 | `96b46eca53aa1fd84534809dec342edb0599f0b9e9f68ee0e76f673e906dab55` |
| [DEFEITO_GREEN_CUMULANTES_MELLIN.md](</home/thlinux/Downloads/DEFEITO_GREEN_CUMULANTES_MELLIN.md>) | 353 | `b14260382ce44549036dac2d29f7ef3085e7eb93062d861dd1449a35143e9a4e` |
| [teoria_de_defeitos/teoria_defeitos_pack/CONSOLIDADO_MESTRE_C2_CP_GREEN_PSI.md](</home/thlinux/Downloads/teoria_de_defeitos/teoria_defeitos_pack/CONSOLIDADO_MESTRE_C2_CP_GREEN_PSI.md>) | 1996 | `e8058153690d936ff0fc17bf59ddd492529a1bae609a1fdca0584d0601558126` |
| [teoria_de_defeitos/teoria_defeitos_pack/TEORIA_GEOMETRICA_DO_CARRY_E_OPERADOR_ORTOGONAL_MULTIBASE.md](</home/thlinux/Downloads/teoria_de_defeitos/teoria_defeitos_pack/TEORIA_GEOMETRICA_DO_CARRY_E_OPERADOR_ORTOGONAL_MULTIBASE.md>) | 3007 | `a76b78fad008d138f08d8264b68bbf05c11d45d3c883c1ff455bf9ed5815d6a5` |
| [teoria_de_defeitos/teoria_defeitos_pack/09_teorema_geral_cumulantes.md](</home/thlinux/Downloads/teoria_de_defeitos/teoria_defeitos_pack/09_teorema_geral_cumulantes.md>) | 237 | `0836f3538c456b5bf55d7c2f62da496b5b8c9763fe702c6897d607463f7f7dde` |
| [MOBIUS_LOG_CLOCK_CONNECTED_DRESSING_THEOREM.md](</home/thlinux/Downloads/MOBIUS_LOG_CLOCK_CONNECTED_DRESSING_THEOREM.md>) | 581 | `13fa66e022dde4df7022ba45da37aa9a25c17ee098d8a6d4f2de5d0956288933` |
| [RELATORIO_CANAL_OCULTO_GREEN_NAIMARK_MOBIUS.md](</home/thlinux/Downloads/RELATORIO_CANAL_OCULTO_GREEN_NAIMARK_MOBIUS.md>) | 1319 | `de44acab16ab88161c175d011c61cf5eaf29ef5b78c16a3a28a180abbb9b2a98` |
| [TFVD_PRIMOS_HILBERT_COVARIANT_MASS_GAP_EXTENDED/RELATORIO_FINAL.md](</home/thlinux/Downloads/TFVD_PRIMOS_HILBERT_COVARIANT_MASS_GAP_EXTENDED/RELATORIO_FINAL.md>) | 1177 | `42e91b0492b3668641a77cb0f2be7fae2a848bc0437d1feefa66b63d5e3871ca` |
| [PRIMOS_TFVD_HILBERT_COVARIANT_MASS_GAP_DEEP_DIVE_V2/DERIVACOES_EXATAS.md](</home/thlinux/Downloads/PRIMOS_TFVD_HILBERT_COVARIANT_MASS_GAP_DEEP_DIVE_V2/DERIVACOES_EXATAS.md>) | 503 | `f7dcedd03731eda99300efa80689910ff8484b1a95115497d713e83b12d31fd2` |
| [PRIMOS_TFVD_HILBERT_COVARIANT_MASS_GAP_DEEP_DIVE_V2/RELATORIO_FINAL.md](</home/thlinux/Downloads/PRIMOS_TFVD_HILBERT_COVARIANT_MASS_GAP_DEEP_DIVE_V2/RELATORIO_FINAL.md>) | 1605 | `1f3ec0a8ebe962ab8be18fb5e13c5f79cdf38f1c0f9fe251c854afea5e6fc538` |
| [MEMORIAL_DO_PMFO_AO_OPERADOR_NATIVO_2026-08-05_v1.1_CORRIGIDO.md](</home/thlinux/Downloads/MEMORIAL_DO_PMFO_AO_OPERADOR_NATIVO_2026-08-05_v1.1_CORRIGIDO.md>) | 1650 | `45b4e336b82af19cf947186872e8eed6956daa8f74a87e9d78f9bed895d994e6` |
| [Nota informal — Möbius, von Mangoldt, log-derivada e o carry.md](</home/thlinux/Downloads/Nota informal — Möbius, von Mangoldt, log-derivada e o carry.md>) | 805 | `604c58660ed287b38e29568c418a8fd96656cfa7197fa8cf8d65f64b68e8d5bf` |

O memorial foi usado para a genealogia e a origem do peso, não como prova nova do Gram. A nota informal Möbius remete ao round-trip já formalizado; não acrescenta a identificação métrica com a característica completada.

## Referência de execução

- Fonte Lean autoadjunto lida em `/tmp/carry-garimpo-local/self-adjoint`, snapshot associado ao mapa anterior `7b29b5938b58ffd45d34a3697536836c646291c1`.
- CPFormal lido diretamente no servidor, pin `65d50f6db1208708e109982ba97e1d51d3039956`.
- Nenhum original alterado, nenhuma dependência atualizada, nenhum teorema apresentado como recém-verificado pelo kernel.

[Voltar ao mapa principal](../mapa-notas-costura-energia-momentos-carry.md).
