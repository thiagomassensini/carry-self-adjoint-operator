# Teste da rota covariante: readouts completos e limite do Gamma atual

Data: 2026-09-05.

Base desta rodada: `f31b38744491fd0f77620f498d2b69beca8f7224`, no ramo descendente da base exigida `225a85d9e8e3e0a3b659c5b6ad821458770b3195`.
Módulo: [CovariantCameraTraceTransport.lean](../CarrySelfAdjointOperator/CovariantCameraTraceTransport.lean).

## Resultado

O transporte conjunto de estado e observador encaixa na análise **retorno + variância** já construída. Ele recupera exatamente o valor e, quando aplicado também à coordenada log-jet existente, recupera a companheira. Com as caudas e o dressing já formalizados, chega ao mesmo par $(F,-F')$ em todo cutoff.

Isso é uma nova identificação do readout dessa análise com o endpoint existente. A construção de $(F,-F')$, os momentos e a equivalência espectral não foram refeitos.

Duas fronteiras foram provadas:

1. A fonte ordinária avaliada num ponto não determina o log-jet independente do estado enriquecido geral. Um pulso de log-jet deixa a fonte inteira e seu Gamma iguais, mas muda a companheira em $i$.
2. Transportar isometricamente o **Gamma atual** não muda sua diagonal. Portanto a discrepância canônica com o Gram nativo, já provada anteriormente, permanece inclusive para uma isometria escolhida em cada parâmetro.

O primeiro resultado não bloqueia a curva canônica: nela o log-jet é a derivada do valor. A nova análise foi ligada a essa identidade existente, inclusive com a cauda diferenciada.

## 1. O encaixe geométrico exato

Mantiveram-se $G,H,V$ e

$$
A=G^{-1/2}(H-GT)G^{-1/2},
\qquad S=\sqrt V,
\qquad A^*A+S^*S=I.
$$

O observador de valor já tinha a normalização determinada por $G$:

$$
q=\left(\frac9{139},\frac9{278},-\frac3{139},0,-\frac9{278},\frac1{42}\right),
\qquad Gq=e_7-e_6.
$$

Para os coeficientes $c$ do porto, escreva $u_c=\sqrt G\,c$ e $u_q=\sqrt G\,q$. O novo teorema prova

$$
\boxed{
\langle Au_q,Au_c\rangle+\langle Su_q,Su_c\rangle
=c_7-c_6.
}
$$

Os subscritos $6,7$ aqui são os rótulos das câmeras; os índices Lean correspondentes são `4,5 : Fin 6`.

**Teorema:** `sixCamera_return_variance_valueTrace`.

**Reuso exato:**
`sixCamera_return_variance_source_gram`
→ `sixCamera_valueTrace_dual_readout`.

Não foi ajustado coeficiente para bater um momento. A positividade dos dois canais de análise não transforma automaticamente a leitura escalar ou seu Wronskiano em um Gram positivo.

A função `sixCameraReturnVarianceTrace` faz a mesma leitura nas duas quadraturas complexas. Seu teorema de avaliação dá exatamente $c_7-c_6$, sem descartar os produtos cruzados de $G$.

`sixCameraReturnVarianceTrace_greenPort` fixa a correspondência tipada com o porto original:

~~~lean
let p := greenPort 3 s state
sixCameraReturnVarianceTrace
  ![p.1 0, p.1 1, p.1 2, p.2 0, p.2 1, p.2 2]
  = state.1 2 - state.1 1
~~~

Não se substituiu esse porto pelo vetor de resultantes das câmeras.

## 2. Até onde a reconstrução chega

A segunda função nova, `c3ReturnVarianceHeadReadout`, aplica a mesma análise a cada bloco completo de três coordenadas. Ela recebe uma coordenada do `CarryVerticalL2` já existente.

O carrier original é

~~~lean
CanonicalCompletedC3HilbertState = CarryVerticalL2 × CarryVerticalL2
~~~

e mantém separadas a coordenada ordinária e a log-jet. Temos

$$
1+R_{M,s}(g)=\operatorname{valueHead}_M(g,j),
\qquad
R_{M,s}(j)=\operatorname{logJetHead}_M(g,j).
$$

Depois de reinserir as caudas originais,

$$
\left(
i\,[R_{M,s}(j)+J_{\rm tail}],
\,1+R_{M,s}(g)+V_{\rm tail}
\right)
=
(\text{rawCompanion},\text{rawValue})
$$

sobre a família canônica, em todo cutoff $M$.

**Teoremas:**

- `c3ReturnVariance_valueHead`;
- `c3ReturnVariance_logJetHead`;
- `c3CanonicalPrefix_returnVarianceCompletedTrace`;
- `c3ReturnVariance_completedReadouts_eq_bracketTfvd`.

A igualdade com os readouts da estrutura TFVD permite aplicar seu dressing existente. O endpoint novo mais alto desta cadeia é:

**`c3ReturnVariance_dressedTrace_eq_F_negFprime`**.

Ele conserva o fator da carta, sua derivada, o fator Xi e sua companheira de produto. A prova termina reutilizando

`canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime`.

Não exige divisão por $F$, hipótese sobre zeros, positividade do Hankel ou dados espectrais. A hipótese de domínio é a já existente:

~~~lean
hz : operatorHeightParameter z ∈ genuineCriticalStrip
~~~

O Wronskiano escalar desse mesmo par já é tratado por `canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime`. A resposta $-F'/2F$ e os momentos continuam a cargo dos teoremas existentes em `CompletedNativeTfvdWronskianMoments.lean`. Não se inferiu a positividade dessa resposta a partir da reconstrução.

## 3. O log-jet canônico é recuperável pela curva

O porto Green avaliado num ponto e a curva desse porto são dados distintos.

Para a família canônica, os novos teoremas ligam a análise à identidade derivativa já provada:

$$
\frac d{ds}\bigl[1+R_{M,s}(g_s)\bigr]=-R_{M,s}(j_s),
$$

e, no domínio da cauda,

$$
\frac d{ds}\bigl[1+R_{M,s}(g_s)+V_{{\rm tail},M}(s)\bigr]
=-\bigl[R_{M,s}(j_s)+J_{{\rm tail},M}(s)\bigr].
$$

**Teoremas:**

- `hasDerivAt_c3ReturnVariance_valueHead_eq_neg_logJet`;
- `hasDerivAt_c3ReturnVariance_completedValue_eq_neg_logJet`.

**Peças reutilizadas:**

- `hasDerivAt_finiteBracketedDirichletChart_three_eq_neg_logJet`;
- `hasDerivAt_realCpBracketCutoffTail_eq_neg_logJetTail`;
- as identidades dos heads canônicos com as somas de bracket.

Estas derivadas usam o parâmetro complexo nativo $s$. A rotação para altura e o dressing da companheira permanecem no caminho já formalizado. Não se identificou $s$ nem a altura com um parâmetro de resolvente.

## 4. O primeiro termo que o source ordinário não carrega

A definição atual do porto, em `CompletedC3EnrichedSymplecticNoLeakBridge.lean`, é

~~~lean
greenPort N s state =
  (WithLp.toLp 2 (fun n : Fin N =>
      (((3 : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ) * state.1 n),
   WithLp.toLp 2 (fun n : Fin N => state.1 n))
~~~

Ambas as pernas dependem de `state.1`. O empacotamento posterior nas seis câmeras é fiel a **esse porto**; ele não injeta automaticamente a coordenada `state.2`.

A nova identidade

~~~lean
greenPort N s (state + (0, jet)) = greenPort N s state
~~~

é `c3GreenPort_add_logJet`.

Para $M>0$ e $\delta j=a\,\delta_2$,

$$
\delta V=0,\qquad \delta C=i\,a.
$$

Isso foi provado com caudas arbitrárias ainda presentes:

**`c3CompletedTrace_add_lastLogJet`**.

O witness unitário está em

**`c3LogJetPulse_sameSource_differentCompanion`**,

e sua aplicação ao campo Gamma existente está em

**`c3LogJetPulse_sameGamma_differentCompanion`**.

Neste último, $s$ e $\lambda$ são argumentos independentes. Para todo $\Im\lambda\ne0$, o mesmo Gamma recebe fontes iguais, enquanto a companheira difere exatamente em $i$.

O teorema geral `not_c3CompletedCompanion_factors_through_processed_source` prova que nenhum pós-processamento do source pontual resolve isso no carrier enriquecido inteiro. Seu quantificador sobre o processamento inclui whitening, centramento e avaliação fixa de Gamma. Não é um argumento de dimensão nem de rank numérico.

**Limite lógico:** o witness varia o log-jet independentemente do valor. Ele não representa dois pontos da curva canônica. Por isso não elimina a recuperação por derivada da seção anterior.

### Resíduo polarizado completo

Se dois estados recebem pulsos $a,b$ em seus log-jets, mantendo seus valores completados $V_x,V_y$, o Wronskiano muda por

$$
\boxed{
\Delta W=i\,a\,\overline{V_y}+i\,V_x\,\overline b.
}
$$

**Teorema:** `c3CompletedTrace_lastLogJet_boundaryDifference`.

Os dois produtos cruzados e as caudas estão presentes na assinatura. O termo pulso–pulso é zero porque ambos os incrementos de valor são zero. Esse é o resíduo explícito, não apenas um nome novo para uma diferença desconhecida.

## 5. Limite da solução por transporte isométrico

O novo teorema

**`canonicalC3Gamma_isometricTransport_ne_native_diagonal`**

reutiliza o no-go canônico anterior e prova: para pontos não reais suficientemente próximos do centro pelo eixo imaginário, toda isometria complexa linear aplicada ao Gamma normalizado atual mantém uma diagonal diferente da nativa.

O quantificador sobre a isometria fica **depois** do parâmetro. Logo a conclusão também abrange uma escolha de isometria que varia com o parâmetro.

Cadeia exata:

`canonicalCompletedC3NormalizedPolarizedGammaKernel_eq_inner`
+ `LinearIsometry.inner_map_map`
+ `canonicalC3NormalizedGamma_ne_native_near_imaginary_center`.

Isso delimita a seta que foi testada. Uma troca isométrica de representação desse Gamma não corrige sua energia diagonal. Não se conclui que toda geometria de carry seja incapaz de fornecer a métrica nativa.

O endpoint cru anterior continua sendo a equação
`canonicalCompletedC3RawGammaWronskianDefect z w hz hw = 0`.
Para o Gamma fixo atual, a prova existente `canonicalC3RawGammaWronskianDefect_ne_zero_near_imaginary_center` já exclui essa equação nos pontos indicados. Portanto não foi apresentada como um goal aberto que a nova isometria supostamente resolveria.

## 6. O que usar na próxima etapa

O encaixe positivo desta rodada é

$$
\text{estado ordinário + log-jet}
\;\longrightarrow\;
\text{análise retorno + variância, com os observadores transportados}
\;\longrightarrow\;
\text{valor + fluxo, head + tail}
\;\longrightarrow\;
(F,-F').
$$

A geometria conservada exige acompanhar ambos os canais e ambos os observadores. A curva canônica fornece a relação derivativa entre os canais.

A comparação seguinte deve partir desse estado enriquecido já existente e da sua forma Green completa. A passagem de uma forma de bordo para um Gram positivo identificado continua sendo uma obrigação própria. Esta rodada não integrou o levantamento primo por valuações das notas com o CameraHilbert, nem postulou tal integração.

## 7. Entrega e validação

- Novo módulo: `CarrySelfAdjointOperator/CovariantCameraTraceTransport.lean`.
- Alterados: `CarrySelfAdjointOperator.lean`, `CarrySelfAdjointOperator/Audit.lean`, `CarrySelfAdjointOperator/KernelConstructionAudit.lean`.
- 20 teoremas novos; duas funções novas de **readout**. Nenhum operador espectral, Gamma, momento, Jacobi ou espaço Hilbert novo.
- Hipóteses matemáticas novas para a família canônica: nenhuma. Foram mantidas as hipóteses de domínio dos teoremas reutilizados.
- Todas as provas estão fechadas; nenhum goal Lean incompleto foi incorporado.
- **14/14 estágios passaram**, com audit estático aprovado. Os 20 teoremas foram consultados individualmente com #check e #print axioms: somente propext, Classical.choice e Quot.sound, sem sorryAx.
- O teste adicional de invariância da diagonal foi seguido por nova execução integral do workflow sobre a versão final.
- Dependency pins e toolchain preservados. Não foi feito merge.

Artefatos: [axiomas e assinaturas](../research/covariant-completed-trace-2026-09-05/new-theorems-axioms.log), [comandos Lean](../research/covariant-completed-trace-2026-09-05/NewTheorems.lean.txt), [auditoria integral](../research/covariant-completed-trace-2026-09-05/full-audit.log.gz), [proveniência](../research/covariant-completed-trace-2026-09-05/provenance.json).

Mapa de origem: [covariantes e câmeras](covariantes-camera-geometry-map.md).
