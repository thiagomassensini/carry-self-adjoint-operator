# Dinâmica nativa, trace completado e forma de Green calculada

Data: 2026-09-05.

## Resultado desta rodada

A relação dinâmica da PR #51 foi estendida a **todos os blocos completos**. O log-jet continua sendo calculado pelos mesmos dados ordinários, com a semente de entrada de cada bloco. Esse cálculo foi ligado ao trace de `9e106f8` e às suas caudas exatas.

A forma local e os três resíduos existentes foram avaliados nessa realização. O resultado mostra exatamente os cancelamentos entre os canais; não produz um Gram positivo identificado com os momentos nativos.

O teste de sinal foi feito no Lean: a forma local orientada tem valores de sinais opostos em estados finitos com log-jet consistente. Separadamente, a soma dos três resíduos é comprovadamente não nula na família canônica de um bloco fora da linha crítica, incluindo o witness $s=1/4$. Esse segundo resultado não usa um pulso independente de log-jet.

O alcance é a comparação com o **Green refletido finito existente**. Nenhum desses testes exclui toda possível realização da geometria; eles não confundem essa forma com a métrica nativa ainda por identificar.

## Bases e arquivos

- Base do trace: `9e106f8ac2a70382cfcf67cb38005232e2a765d2`.
- Dinâmica da [PR #51](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/51): `fe3312b063509ad2e52a4efa2f8657a967f29b05`.
- Integração local dessas histórias: `92059e4`, na branch de investigação `agent/dynamic-completed-green-form`. A PR e a main não foram mergeadas no GitHub.
- Módulo novo: [C3DynamicCompletedGreenForm.lean](../CarrySelfAdjointOperator/C3DynamicCompletedGreenForm.lean).
- Integração: aggregator principal, `Audit.lean` e `KernelConstructionAudit.lean`.
- Pins e toolchain preservados. A ancestralidade da base exigida `225a85d9e8e3e0a3b659c5b6ad821458770b3195` foi mantida.

## 1. Estado ordinário, relógio e semente

No bloco $m$, usamos os valores nativos e seus gradientes:

$$
f=f_{3m},\qquad
g=(g_{3m},g_{3m+1},g_{3m+2}),\qquad
g_n=f_{n+1}-f_n,\quad f_n=(n+1)^{-s}.
$$

Escreva

$$
d=\log(3m+1),\quad a=\log(3m+2),\quad
b=\log(3m+3),\quad c=\log(3m+4).
$$

A mesma `gradientClock` da #51 dá

$$
\boxed{
\ell=\operatorname{gradientClock}(a,b,c)g
       +f\,(a-d,b-a,c-b).
}
$$

`nativeC3BlockDynamicLogJet_eq` identifica essa expressão com os três `positiveLogDirichletGradient` originais. Não é uma hipótese de compatibilidade adicionada ao estado.

A semente de cada bloco também foi identificada com a reconstrução causal do prefixo:

$$
f_{3m}=f_0+\sum_{n<3m}g_n.
$$

Teorema: `nativeC3Block_seed_eq_prefix`, reutilizando `sum_range_forwardDifference`.

O primeiro bloco coincide com os objetos da #51 por `nativeC3BlockGradient_zero` e `nativeC3BlockDynamicLogJet_zero`.

### A direção invisível ao valor permanece na próxima leitura

A expressão calculada é

$$
\boxed{
\ell_2-\ell_1=(a-2b+c)(g_0+f)+(c-2b)g_1+c g_2.
}
$$

Teorema: `c3AffineClock_trace`.

Em todo bloco,

$$
a-2b+c<0,
$$

porque $(3m+2)(3m+4)<(3m+3)^2$. Isso foi provado em `nativeC3Block_logTraceGap_neg`. A coordenada $g_0$ ausente do valor $g_2-g_1$ continua necessária para a evolução desse valor.

## 2. Encaixe no trace e no dressing existentes

`nativeC3DynamicLogHead` soma a leitura acima, usando exatamente $M$ blocos completos. Temos

~~~lean
nativeC3DynamicLogHead M s = finiteCanonicalLogBracketChart M s
~~~

e

~~~lean
nativeC3DynamicLogHead M s =
  c3ReturnVarianceHeadReadout M s
    (canonicalCompletedC3HilbertPrefixState s (3*M)).2
~~~

Teoremas: `nativeC3DynamicLogHead_eq` e `nativeC3DynamicLogHead_eq_returnVariance`.

Consequentemente, `nativeC3Dynamic_completedTrace` recupera, com as duas caudas originais,

$$
\bigl(i(J_M+J_{\rm tail}),\;V_M+V_{\rm tail}\bigr)
=(\text{rawHeightCompanion},\text{rawHeightValue}).
$$

Aqui $V_M$ inclui a semente $1$; $J_M$ tem a semente logarítmica original $0$.

A cadeia de dressing permanece a anterior:

`nativeC3DynamicLogHead_eq_returnVariance`
→ `c3ReturnVariance_dressedTrace_eq_F_negFprime`
→ `canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime`.

Essa cadeia conserva o fator da carta, sua derivada e os fatores de completion. Não constrói outro $F$, outro momento ou outro Gamma. O parâmetro material $s$, a altura e um eventual parâmetro de resolvente não foram identificados.

## 3. A forma local calculada

Substituir a relação dinâmica nas duas células existentes dá

$$
P_m=g_1\ell_0-g_0\ell_1+g_2\ell_1-g_1\ell_2
$$

com a expressão explícita

$$
\begin{aligned}
P_m={}&(a-b)g_0^2+(a-c)g_0g_1+(b-a)g_0g_2\\
&+(b-c)g_1^2+(b-c)g_1g_2\\
&+f\bigl[(a-b)g_0+(a+b-c-d)g_1+(b-a)g_2\bigr].
\end{aligned}
$$

`c3AffineClock_boundary` prova a expansão. `canonicalC3BoundaryCells_eq_dynamic` e `canonicalC3PairBoundary_eq_dynamic` identificam-na com as células e a soma de bordo originais, para qualquer normalização TFVD não nula permitida pelas fontes existentes.

Essa forma é orientada e bilinear. Para coordenadas complexas, os quadrados acima são quadrados algébricos, não módulos quadrados.

### Teste exato de sinal

Na seção real com semente zero e log-jet forçado pelo relógio:

$$
P_m(1,0,0)=a-b<0,
\qquad
P_m(1,0,2)=b-a>0.
$$

Teorema: `c3DynamicBoundaryPolynomial_sign_witnesses`.

São estados de teste na realização finita consistente, não dois parâmetros da família aritmética canônica. O resultado impede interpretar diretamente esse polinômio como uma norma quadrática não negativa. Não constitui uma obstrução nova aos Grams nativos.

## 4. O que vira bordo e o que permanece nos resíduos C3

Somando **todos os três resíduos de cada bloco**, a dinâmica telescopa:

$$
E=\sum_{m<M}(g_0+g_1+g_2)=f_{3M}-f_0,
$$

$$
L=\sum_{m<M}(\ell_0+\ell_1+\ell_2)
=\log(3M+1)f_{3M}.
$$

Teorema: `nativeC3Dynamic_threeResidue_totals`, com reuso de `sum_range_threeBlocks_eq_range` e `sum_range_forwardDifference`.

As quatro somas de pernas do ledger, porém, omitem coordenadas distintas. Com $S_L,S_R,S_{JL},S_{JR}$ na ordem dos índices Lean $0,1,2,3$:

$$
\begin{aligned}
S_L+\sum g_2&=E,& S_R+\sum g_0&=E,\\
S_{JL}+\sum\ell_2&=L,& S_{JR}+\sum\ell_0&=L.
\end{aligned}
$$

Teorema: `nativeC3Dynamic_sums_add_omittedResidues`.

Portanto há endpoints literais e há somas de resíduos C3 que precisam continuar presentes. Não se substituiu cada soma de duas pernas pelo endpoint da soma das três.

## 5. Os três canais existentes, agora avaliados

Defina, apenas para ler as fórmulas,

$$
P=\sum_{m<M}P_m,\qquad B=S_R S_{JL}-S_L S_{JR},
$$

$$
W=\overline{V_M}J_M-\overline{J_M}V_M,
$$

e seja $G$ a forma Green do porto finito existente em $s$ e `reflectedParameter s`.

Os nomes dos resíduos não mudaram. As avaliações provadas são:

| Canal original | Expressão calculada | Teorema novo |
|---|---|---|
| `finiteCanonicalTfvdSameSGreenProvenanceDefect` | $P-G$ | `canonicalC3GreenProvenance_eq_dynamic` |
| `canonicalBoundaryCrossProvenance` | $B-P$ | `canonicalC3CrossProvenance_eq_dynamic` |
| `canonicalBoundaryReadoutResidualCorrection` | $W-B$ | `canonicalC3ReadoutCorrection_eq_dynamic` |

`canonicalC3ResidualLegs_eq_dynamic` e `canonicalC3ResidualSums_eq_dynamic` fazem a identificação tipada com as pernas decodificadas; não foi presumida uma síntese escalar.

Assim,

$$
\boxed{D_{\rm prov}+D_{\rm cross}+D_{\rm readout}=W-G.}
$$

O conteúdo da avaliação é que $P$ e $B$ acima já estão calculados nos gradientes e sementes, e cada parcela original foi identificada separadamente. `canonicalC3ThreeResiduals_eq_dynamic` combina os resultados.

### Witness na própria família canônica

`scalarBoundaryWedge_real_part_zero` dá $\Re W=0$. O Green canônico de um bloco tem parte real não nula fora da linha crítica dentro do strip, pelo resultado existente `canonicalEnrichedC3ReflectedGreenBulk_re_eq_zero_iff_re_eq_half`.

Logo a soma dos três resíduos não se anula ali. Teoremas:

- `canonicalC3Dynamic_threeResiduals_ne_zero`;
- `canonicalC3Dynamic_threeResiduals_quarter_ne_zero`.

O witness fechado pelo Lean é:

~~~lean
finiteCanonicalTfvdSameSGreenProvenanceDefect 3 1 (1/4) +
  canonicalBoundaryCrossProvenance 1 1 (fun _ => 1) (1/4) +
  canonicalBoundaryReadoutResidualCorrection 1 1 (fun _ => 1) (1/4) ≠ 0
~~~

Este é um resultado sobre a soma finita original, antes de confundi-la com o trace vestido. Não se concluiu que as caudas e o dressing fossem descartáveis.

## 6. Caudas, rotação e dois parâmetros

`nativeC3Dynamic_completedScalarBoundary_ledger` reinseriu as duas caudas no ledger escalar original. Sua contribuição exata é

$$
\overline Vj+\overline vJ-\overline Jv-\overline jV
+\overline vj-\overline jv,
$$

com $v$ a cauda do valor e $j$ a cauda log-jet. Os termos cabeça–cauda e cauda–cauda permanecem.

A forma do trace rodado é outra expressão, cuja orientação também foi provada. Para $\tau_x=(iJ_x,V_x)$ e $\tau_y=(iJ_y,V_y)$:

$$
\operatorname{Green}(\tau_x,\tau_y)
=i\bigl(\overline{V_x}J_y+\overline{J_x}V_y\bigr).
$$

O sinal é **mais** nessa soma. Não se usou o wedge escalar $\overline VJ-\overline JV$ em seu lugar. Na convenção do repositório, o Wronskiano com ordem $(x,y)$ corresponde à forma Green com os argumentos desses pares trocados.

`c3RotatedTrace_greenForm_with_tails` expande os oito produtos de cabeça/cauda em dois parâmetros. `nativeC3Dynamic_completedTrace_greenForm` aplica essa fórmula à família canônica, com cutoffs independentes $M,N$ e as hipóteses de domínio já existentes.

## 7. Até onde a rodada chega

Chegamos a uma forma de fluxo calculada, com sua relação dinâmica e todas as parcelas de bordo. A realização finita permite recuperar o trace existente; sua forma local orientada não é automaticamente positiva.

Não surgiu nesta rodada um novo Gram positivo identificado com o nativo. Por isso não se fabricaram vetores $u_k$ para um teste Hankel nem se ajustou uma normalização central. O teste $\langle u_0,u_2\rangle=\langle u_1,u_1\rangle$ continua sendo uma exigência de uma futura identificação concreta, não um resultado desta rodada.

A questão matemática que permanece é como a forma completa, após a leitura e o dressing originais, se relaciona a uma métrica positiva. O resultado atual explicita os termos dessa comparação e uma falha concreta de sua versão finita sem os canais de correção.

## 8. Validação e confiança

Foram acrescentados 28 teoremas e seis expressões de coordenadas, readouts e polinômios. Nenhum novo espaço Hilbert, operador espectral, Gamma, momento ou Jacobi.

As hipóteses novas são somente as de argumentos dos lemas algébricos e de seus testes: não se acrescentou premissa matemática à família canônica. Não há prova incompleta no módulo.

**Validação final:** build do módulo com `--wfail` aprovado; **15/15 estágios** do workflow passaram (os 14 anteriores mais `ObservableJetAudit` da #51), junto da auditoria estática. Os 28 resultados passaram em `#check` e `#print axioms`, usando somente `propext`, `Classical.choice` e `Quot.sound`, sem `sorryAx`.

Evidências: ver [proveniência](../research/dynamic-green-form-2026-09-05/provenance.json), [assinaturas e axiomas](../research/dynamic-green-form-2026-09-05/new-theorems-axioms.log) e [log integral](../research/dynamic-green-form-2026-09-05/full-audit.log.gz).

Não foi realizado merge em main, nem monitoramento do CI remoto.
