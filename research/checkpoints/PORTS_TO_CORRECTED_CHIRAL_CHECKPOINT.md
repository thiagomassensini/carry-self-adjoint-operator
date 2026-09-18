=== CHECKPOINT ===
Objetivo atual:
Fechar `PORTS → corrected causal/chiral first column`, isto é, obter um readout
geométrico dos dados TFVD que produza o coeficiente corrigido antes do
crosswalk para os momentos.

ATUALIZAÇÃO ESTRATÉGICA (17-09-2026):
- Este objetivo de interface está agora fechado no domínio honesto de seis
  análises TFVD enriquecidas; o bloco `GARGALO EXATO` abaixo registra o tipo
  mínimo. Portanto não se deve abrir uma nova realização material positiva
  antes de haver uma razão estrutural independente para ela.
- A próxima obrigação matemática recomendada é o primeiro certificado novo da
  escada Stieltjes, `det (hankelGram canonicalCompletedNativeLogDerivativeMoment 3) > 0`.
  A identidade algébrica e o bridge theta já existem; o defeito localizado é
  uma caixa racional certificada de ordem dez, em particular uma cota superior
  refinada para `completedNativeThetaTailMoment 10`.
- Este redirecionamento é uma inferência de estratégia, não um novo teorema:
  ele preserva o carrier/material correto já fechado e corrige somente a
  variável analítica que ainda impede o certificado de sinal.

CONFIRMADO:
- No TFVD vertical, `B_q : CarryVerticalL2 →L[ℂ] CarryVerticalL2` e
  `Tr_q : CarryVerticalL2 →L[ℂ] (ℂ × ℂ)`, com
  `Tr_q x = (x 0, q⁻¹*x 1 - x 0)` conforme a definição Lean.
- `G_q (B_q x) + R_q (Tr_q x) = x`; `Tr_q ∘ R_q = I`; `B_q ∘ R_q = 0`.
- A análise enriquecida guarda `((B_q x, Tr_q x), provenance)` e a
  reconstrução composta com a análise é a identidade. Portanto bracket + ports
  são dados lossless; não é necessário um novo Dirichlet-to-Neumann/Weyl.
- O estado causal TFVD concreto é o par
  `(G_q (B_q x_M), R_q (Tr_q x_M))` em
  `WithLp 2 (CarryVerticalL2 × CarryVerticalL2)`, e a soma dos dois canais é
  `x_M` exatamente. A expansão da Gram existente tem os quatro termos
  causal–causal, causal–retorno, retorno–causal e retorno–retorno.
- O carrier corrected causal/chiral é
  `WithLp 2 (FullWronskianOperatorCarrier × CoisometricCameraChiralEnergyCarrier)`.
  O readout é real-linear e nasce do mesmo source enriquecido; ele não é o
  carrier vertical TFVD.
- `CompletedC3SameStructuredBoundaryState.lean` confirma uma única fonte
  estruturada `CanonicalC3BracketTfvdCompletionState 1`: sua projeção escalar
  é o par orientado `(-F',F)` e sua projeção `greenPort` é a fonte de seis
  câmeras Gamma. A compatibilidade entre as duas formas Green é equivalente
  ao defeito raw Gamma--Wronskian ser zero; essa compatibilidade de locus de
  fonte ainda não está provada.
- O corrected scalar coefficient, antes de qualquer identificação com `h_n`, é
  o coeficiente Taylor do readout assinado de dois canais:
  `I * (⟪positiveState M 0, positiveState M z⟫ -
       ⟪negativeState M 0, negativeState M z⟫)`.
  Portanto a geometria correta é diferença de dois Gram chiral positivos,
  seguida da meia-volta complexa; não é uma norma positiva nem `A* A`.
- Existe uma realização TFVD estruturada mais rica
  `CanonicalC3BracketTfvdCompletionState M`, com campos separados
  `transport`, `valueTail` e `logJetTail`. As projeções de valor/log-jet e
  `greenPort` vêm do mesmo estado.
- O `greenPort` desse estado é exatamente o Genuine bracket port. O readout
  `canonicalC3BracketTfvdMixedCorrectedBoundary` subtrai a proveniência Green
  independente e satisfaz exatamente
  `correctedBoundary = GreenReadout(greenPort_w, greenPort_reflected_z)`.
- A rota TFVD estruturada também fornece um par escalar completo
  `(F, -F')` após unir head + tails; o `mixedScalarBoundaryWedge` desse par nos
  dois pontos é o Wronskiano completed. Isso é mais rico que `Tr_q x` cru.
- A compressão Hatano–Nelson `Green(Bᵀ Δ B) = Bᵀ Green(Δ) B` confirma o
  mecanismo de compressão de defeitos suportados no bordo, mas é uma identidade
  finita matricial com transpose; ainda não é, por si só, um mapa Lean entre o
  `Tr_q` infinito e o carrier chiral.

NOVO NESTA RODADA:
- Foi criado e compilado
  `CarrySelfAdjointOperator/CompletedNativeTfvdSixChannelJet.lean`. Ele não
  inventa um novo carrier: usa o já existente
  `canonicalCompletedC3AllCutoffKernelLedgerState (M+1) z 0`, cujo
  `mixedChannels` é literalmente o ledger de seis termos. A definição
  `canonicalC3BracketTfvdSixChannelNormalizedResponse` toma o `finalReadout`
  desse estado e a normalização central correta.
- Formalmente provado nesse novo módulo: o response do ledger de seis canais
  é eventualmente igual ao response bracket--TFVD pré-existente, e portanto,
  para todo `M p`,
  `canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p =
   iteratedDeriv (p+1) sixChannelResponse_M 0/(p+1)!`.
  A prova usa o sewing do ledger e não usa momentos.
- Os testes estruturais de baixa ordem foram promovidos a teoremas Lean:
  índice `p=0` é o jet `1`; índice `p=1` é o jet `2` e zera pela paridade do
  response completed; índice `p=2` é o jet `3`. Somente em dois teoremas
  posteriores esses jets `1` e `3` são reconhecidos como `h_0` e `h_1`.
- Foi definido o domínio honesto da análise de fonte,
  `CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S`: são **seis**
  `NativeGpreFiniteTfvdAnalysisCarrier S`, correspondendo aos canais
  ordinary/log-jet nos três pontos `z`, `w`, `reflected z`. A função de
  reconstrução correspondente satisfaz no Lean
  `reconstruct (analyze source) = source` para qualquer
  `CanonicalC3AllCutoffMixedSourceHilbert`.
- Em consequência, o triple estrutural é agora um funcional explícito desses
  seis dados TFVD analisados. Para a fonte canônica foram provados, coordenada
  a coordenada, os três resultados:
  `greenProvenance`, `offDiagonal` e `readoutResidual` recuperados das seis
  análises são exatamente os três canais do ledger finito. Em particular o
  cross term `offDiagonal` não é parâmetro externo nem termo descartado.
- Pesquisa externa (17-09-2026), classificada explicitamente como **inferência
  arquitetural, não teorema do projeto**: o manuscrito OpenAI de Navier--Stokes
  constrói um campo de fundo, calcula um defeito/estresse explícito no anel de
  transição e o cancela por pulsos oscilatórios e correções sucessivas, mantendo
  as restrições de divergência e de momentos. A lição transportável para este
  seam é não tentar anular isoladamente `greenProvenance`, `offDiagonal`,
  `readoutResidual`, `tailCompletion` e `archimedeanChart`.
- Em particular, o resultado externo reforça a alternativa já isolada pelo
  probe: o objeto alvo deve ser um `TfvdPortJet` enriquecido cujo ledger contém
  `corrected port + cinco resíduos`, e não um `Λ_p` do `Tr_q` cru. A nova rota
  preferencial é construir o mapa de proveniência
  `((B_q x_M, Tr_q x_M), provenance) → TfvdSixChannelJet M`; só depois se
  pergunta se esse ledger admite uma compressão canônica. Isto não prova que
  o mapa exista nem que os resíduos cancelem.
- O melhor readout já existente é um readout bilinear de dois estados/ports,
  não um funcional linear pontual de um único port. Ele é a composição:
  reconstruir cada dado por `G_q·bracket + R_q·port`, manter os quatro termos,
  aplicar a correção de proveniência, e só então tomar o Green/Naimark ou o
  wedge escalar e o coeficiente Taylor.
- Foi compilada em `/tmp/ports_to_chiral_probe.lean` a identidade exata,
  para todo `M p`,
  `canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p =
   canonicalC3BracketTfvdResponseTaylorCoefficient M (p + 1)`.
  A prova usa somente a igualdade corrected-response, a igualdade
  `canonicalC3BracketTfvdResponseTaylorCoefficient_eq_completed` e a
  identificação do response completed; não usa `h_n` para definir o readout.
- Portanto, se
  `R_M(z) := canonicalC3BracketTfvdNormalizedResponse M z`, o crosswalk
  geométrico exato já fechado é
  `C_M(p) = (∂_z^(p+1) R_M)(0)/(p+1)!`.
  Aqui `R_M` é calculado pelo `mixedScalarBoundaryWedge` do par de trace
  escalar completado `(F,-F')` produzido pelo estado estruturado
  `CanonicalC3BracketTfvdCompletionState`; ele inclui transport, value tail e
  log-jet tail. Isso é um readout TFVD enriquecido, não o trace vertical cru.
- A mesma compilação fecha os três primeiros índices antes do crosswalk de
  momentos: `C_M(0)` é o response de ordem `1`, `C_M(1)` é o response de
  ordem `2` e zera pela paridade, e `C_M(2)` é o response de ordem `3`.
  Só depois, pelo teorema já existente da primeira coluna ímpar, eles são
  reconhecidos como `h_0`, `0`, `h_1`.
- Um segundo probe Lean, `/tmp/ports_to_chiral_residual_probe.lean`, também
  compila a decomposição pontual correta. Para `z` no strip e
  `F(z) ≠ 0`, o response `canonicalC3BracketTfvdNormalizedResponse M z`
  é o quociente por
  `mixedHermitianWeight canonicalC3ChartFactorHeight z 0 *
   (2 * F(z) * star(F(0)))` da soma de:
  `mixedHermitianWeight nativeXiCompletionFactor z 0 *
   canonicalC3BracketTfvdMixedCorrectedBoundary (M+1) s_z s_0`, mais os
  cinco canais explícitos `greenProvenance`, `offDiagonal`,
  `readoutResidual`, `tailCompletion` e `archimedeanChart`. Assim o
  readout de ports correto já aparece como um termo exato, mas acompanhado
  de residual; nenhum termo cruzado foi apagado.
- Um terceiro probe Lean, `/tmp/ports_to_chiral_six_channel_probe.lean`,
  empacota essa soma como uma família
  `probeTfvdSixChannelNormalizedResponse` e prova, para todo `M p`,
  `C_M(p) = iteratedDeriv (p+1) probeTfvdSixChannelNormalizedResponse M 0 /
   (p+1)!`. Portanto o gate all-order está fechado no carrier TFVD
  enriquecido de seis canais: `corrected port + cinco resíduos`, com o
  índice `p` realizado honestamente como jet. O probe não usa `h_n` para
  definir a função; a identificação com momentos só entra através dos
  teoremas já existentes.
- Um quarto probe, `/tmp/ports_to_chiral_portjet_interface_probe.lean`,
  compila a interface mínima restante: qualquer família `portJet : ℂ → ℂ`
  que seja eventualmente igual ao response TFVD já fornece imediatamente
  `C_M(p) = iteratedDeriv (p+1) portJet 0/(p+1)!`. Assim o único conteúdo
  matemático ainda novo é construir `portJet` a partir de `Tr_q`/bracket,
  não a identificação com a primeira coluna.
- O teorema
  `canonicalC3BracketTfvdGlobalGreenReadout_tendsto_wronskian_iff` mostra
  que a versão global de Green converge ao Wronskiano completed se e somente
  se o `canonicalC3FiniteMixedHeightStructuralDefect` tende a zero. Logo a
  eliminação do residual não é uma consequência formal da reconstrução TFVD.
- A fórmula exata que deve servir de candidato estrutural é, em notação
  abreviada,
  `K_M(z,w) := correctedTfvdBoundary M z w`
  `= GreenForm(greenPort(τ_M w), greenPort(τ_M(reflected z)))`,
  com `τ_M` o `CanonicalC3BracketTfvdCompletionState`; a fórmula chiral
  univariada é o jet no centro do correspondente readout signed chiral.
- A igualdade existente entre `canonicalCompletedNativeCorrectedChiralBoundaryCoefficient`
  e o response Taylor coefficient é provada, mas ela ainda não fatoriza o
  coeficiente por `Tr_q` de um estado vertical. O índice `p` é um índice de jet;
  um `Λ_p` pontual precisa portanto receber um jet/proveniência, ou incluir
  explicitamente uma operação de derivada sobre uma família de ports.
- Baixa ordem, sem usar `h_n` até a última linha:
  `C_M(0) = signedChiralResponseTaylorCoefficient M 1`;
  `C_M(1) = signedChiralResponseTaylorCoefficient M 2 = 0` pela paridade even;
  `C_M(2) = signedChiralResponseTaylorCoefficient M 3`.
  Só no crosswalk final, o teorema odd da resposta reconhece esses como
  `h_0`, `0`, `h_1`, respectivamente.
- O mecanismo de quatro canais não é opcional: a igualdade Lean
  `canonicalCompletedC3RawGammaGram_eq_causalFourChannel` expande exatamente
  os quatro inner products. Não há teorema que permita apagar os cross terms.
- **Novo fechamento formal desta continuação.** O canal radial foi promovido
  de fato ao domínio das mesmas seis análises TFVD: os ports `w` e
  `reflected z` são reconstruídos das análises, enviados aos seus `greenPort`s,
  e sua `greenForm` é provadamente
  `canonicalC3BracketTfvdMixedCorrectedBoundary`. Os teoremas novos são
  `canonicalC3AllCutoffMixedSourceTfvdDirectGreenPort_canonicalPrefix`,
  `...ReflectedGreenPort_canonicalPrefix` e
  `...CorrectedBoundary_canonicalPrefix`.
- A estratificação de parâmetros foi checada no Lean: a fonte vertical vive em
  `(operatorHeightParameter z, operatorHeightParameter w)`, enquanto
  `tailCompletion`, o peso `xi` e o chart arquimediano vivem no par global
  `(z,w)`. O primeiro teste que tentou identificar um ledger em `(s_z,s_w)`
  com o ledger global em `(z,w)` falhou por essa dupla aplicação do mapa de
  altura; a versão correta, agora provada, é
  `canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary_canonicalPrefix_eq_ledgerRadial`.
  Isto é uma distinção de tipos/proveniência, não um residual novo.
- Foi definida a montagem escalar completa
  `canonicalC3AllCutoffMixedSourceTfvdFinalReadout`: ela mantém explicitamente
  `xi * (correctedGreenPort + greenProvenance + offDiagonal +
  readoutResidual + tailCompletion) + archimedeanChart`. O teorema
  `...FinalReadout_canonicalPrefix` prova que essa montagem de seis análises é
  exatamente o `finalReadout` de
  `canonicalCompletedC3AllCutoffKernelLedgerState`. Nenhum dos cinco canais
  não-radiais foi anulado ou absorvido.
- Consequentemente, o readout final não é mais apenas o nome de um estado do
  ledger. A função
  `canonicalC3BracketTfvdSixAnalysisNormalizedResponse M q hq0 hq1 S` é
  definida por analisar as seis fontes canônicas, reconstruir o carrier
  completo acima, e normalizar no centro. Para qualquer `0 < q < 1` e qualquer
  `S`, ela é **pontualmente** igual ao response de seis canais já existente.
- O funcional all-order pedido foi definido como
  `canonicalC3BracketTfvdSixAnalysisJetCoefficient M p q hq0 hq1 S`, o
  jet central de ordem `p+1` desse response. Foi formalmente provado:
  `canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p =
  canonicalC3BracketTfvdSixAnalysisJetCoefficient M p q hq0 hq1 S`.
  Esta é a identidade `PORTS (enriquecidos) → corrected chiral first column`
  antes dos momentos.
- Os três primeiros índices agora têm teoremas no domínio das seis análises:
  `Λ_0 = C_M(0)`, `Λ_1 = 0`, `Λ_2 = C_M(2)`. Só depois há os crosswalks
  `Λ_0 = h_0` e `Λ_2 = h_1`. A anulação de `Λ_1` vem da paridade do response
  completed transferida pela igualdade pontual, não de uma definição por
  momentos.
- A interface com o clock material foi reduzida e formalizada sem hipótese
  escondida: se a primeira coluna de um `seededClockAtlasCoefficient block`
  coincide com o novo jet TFVD, então
  `seededClockAtlas_hasCorrectedNativeChiralBoundaryTransport_of_sixAnalysisJet`
  produz o transporte chiral corrigido e
  `seededClockAtlas_sameEdgeTransport_of_sixAnalysisJet` produz diretamente
  `HasSameEdgeGreenToClockBoundaryTransport M block`. Portanto não resta uma
  segunda costura abstrata depois da igualdade material da primeira coluna.
- **Novo fechamento formal do micro-gate material.** Foi criado e compilado
  `CarrySelfAdjointOperator/CompletedNativeSeededClockTfvdSixSource.lean`.
  O bloco `nativeC3SeededClockMaterialBlock m s` empacota apenas dados já
  existentes: `nativeBlockSeededData m s` e as quatro frequências
  `log(3m+1),...,log(3m+4)`. A observação enriquecida
  `seededClockTfvdBoundaryObservation` retém `(incoming, ordinary, logJet)`
  como seed, as três pernas antes do clock e as três pernas após um passo.
- Formalmente provado no Lean, para todo `m : Fin M` e `r : Fin 3`, que a
  coordenada `3*m+r` de `c2DirichletGradientPrefixCore s (3*M)` é exatamente
  a perna `ordinary r` do bloco material `m`, e a coordenada correspondente de
  `c2LogJetPrefixCore s (3*M)` é sua perna `logJet r`. Assim, os `M` blocos
  materiais fornecem exatamente os `3M` pares ordinary/log-jet usados pela
  fonte TFVD canônica; não há no-go de tipo ou de dimensão nessa ponte local.
- **Fechamento formal all-order da observação material enriquecida.** As
  definições `nativeC3SeededClockOrdinaryTfvdAnalysis`,
  `nativeC3SeededClockLogJetTfvdAnalysis` e
  `nativeC3SeededClockTfvdSixSourceAnalysis` montam as seis análises nos
  pontos `z,w,reflected z`. O teorema
  `nativeC3SeededClockTfvdSixSourceAnalysis_eq_canonical` identifica esse
  dado com a análise da fonte prefixada canônica, e
  `canonicalC3AllCutoffMixedSourceTfvdReconstruction_seededClockAnalysis`
  prova que a reconstrução das seis análises retorna exatamente essa fonte.
- A porta radial material foi nomeada por
  `nativeC3SeededClockTfvdSixSourceCorrectedBoundary`. Ela é a `greenForm`
  dos ports direto/refletido após reconstrução das seis análises e satisfaz,
  no Lean,
  `...CorrectedBoundary_eq_ledgerRadial`: é exatamente a coordenada radial do
  ledger completed. Os cross terms continuam no triple estrutural do mesmo
  dado reconstruído; não foram incorporados ao Gram positivo material.
- A montagem completa
  `nativeC3SeededClockTfvdSixSourceFinalReadout` é pontualmente o
  `finalReadout` do ledger. Logo, para todo `M,p,0<q<1,S`, o teorema Lean
  `canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_seededClockTfvdSixSourceJet`
  prova
  `C_M(p) = ∂^(p+1) R_material_enriquecido,M(0)/(p+1)!`.
- Cálculo formal de baixa ordem para a observação material enriquecida:
  `Λ_material,0=C_M(0)`, `Λ_material,1=0` e
  `Λ_material,2=C_M(2)`. Somente nos teoremas subsequentes
  `...Jet_zero_eq_canonicalMoment` e `...Jet_two_eq_canonicalMoment` os
  extremos são reconhecidos como `h_0` e `h_1`; a definição geométrica não
  usa momentos.
- **Novo FAIL útil, formalizado no Lean.** Foi criado e compilado
  `CarrySelfAdjointOperator/CompletedNativeSeededClockTfvdRawAtlasNoGo.lean`.
  O atlas material nativo literal
  `nativeC3SeededClockMaterialAtlas M s : Fin (M+1) → SeededClockBlock`
  contém os blocos completos `0,...,M` sem centering, sinal ou correção.
  Seu coeficiente cru `(0,0)` é exatamente
  `∑ m, ↑‖seededRecover (nativeBlockSeededData m s)‖²`.
- O teorema Lean `one_le_nativeC3SeededClockMaterialAtlas_energySum` prova
  que essa soma é pelo menos `1`, pois contém o bloco zero com seed unitário.
  O teorema
  `nativeC3SeededClockMaterialAtlas_zero_zero_ne_tfvdSixSourceJet_zero`
  compara diretamente o raw coeficiente com o jet material enriquecido e
  prova que são diferentes para todo `M,s,0<q<1,S`. O único uso de momento é
  na última linha da contradição: `Λ_material,0=h_0<1/16`.
- Em particular,
  `nativeC3SeededClockMaterialAtlas_not_sameEdgeTransport` prova
  `¬ HasSameEdgeGreenToClockBoundaryTransport M
    (nativeC3SeededClockMaterialAtlas M s)` para todo `M,s`. Assim o atlas
  positivo nativo inteiro — não só o átomo `m=0` já auditado — não pode ser a
  realização final da primeira coluna.
- **Novo avanço no gate analítico `Theta10 → det G3`.** Foi criado e compilado
  `CarrySelfAdjointOperator/CompletedNativeThetaTenthSupport.lean`. O suporte
  Lean agora contém `thetaFirstMode_node_bounds_d20`, a caixa exponencial
  `thetaExp128_bounds` necessária ao segundo modo, a identidade exata
  `thetaSecondMode_eq_two_thetaTailMode_one` e a decomposição estrutural
  `thetaFirstMode + thetaSecondMode ≤ thetaTail`.
- Ainda no mesmo módulo, foi provada a cota do resto iniciado em `n=2`,
  `thetaTail_le_first_add_secondMode_plus_remainder`, preservando o primeiro
  e o segundo modo separadamente. A extensão de integrabilidade foi fechada
  até ordem dez por `thetaFirstMode_weighted_tail_pointwise_ten` e
  `completedNativeThetaTailMoment_finite_upper_refined_ten`.
- **Refinamento exterior formal.** A tangente exponencial em `u=1`, usando
  `π * exp 2 ≥ 23`, produz `thetaFirstMode_weighted_tail_pointwise_ten_sharp`
  e `integral_thetaFirstMode_weighted_tail_le_ten_sharp`; o último certifica
  `∫_[1,∞) u^p thetaFirstMode u ≤ 1/10^11` para `p≤10`. O módulo passa em
  `lake build CarrySelfAdjointOperator.CompletedNativeThetaTenthSupport`.
- **Integração combinada formalizada nesta retomada.** O mesmo módulo agora
  contém `thetaSecondMode_le_thetaTail`,
  `integrableOn_pow_mul_thetaSecondMode` e
  `completedNativeThetaTailMoment_finite_upper_refined_two_mode`. A última
  desigualdade mantém `thetaFirstMode` e `thetaSecondMode` explicitamente em
  `[0,1]`, acrescenta o resto `1/(12300*12299)` do modo geométrico e usa no
  exterior o fator `12300/12299` vezes a cota `10^-11`. A prova inclui os
  produtos de continuidade e os quatro termos de integração sem esconder
  nenhum termo; `lake build` foi executado com sucesso.
- **Replay racional completo concluído.**
  `CompletedNativeThetaSecondModeQuadrature.lean` prova a convexidade do
  segundo modo e as cotas de célula por tangente/corda. O artefato gerado em
  `ThetaTenthMomentCertificateData/` contém 3.585 nós compartilhados, 512
  células e as seis potências `0,2,4,6,8,10`. O comando
  `lake build CarrySelfAdjointOperator.ThetaTenthMomentCertificateData.CompletedNativeThetaTenthMomentCertificate`
  terminou com `4146/4146` tarefas e sucesso. Assim, os limites racionais
  das integrais compactas de ambos os modos são teoremas Lean, não apenas
  saída do screen.
- As caixas finais usam conservadoramente `A_p ≥ ∫_[0,1]u^p
  thetaFirstMode` e a nova cota superior de dois modos. Sobre `10^15`, os
  limites inferiores de `A_p` para `p=0,2,4,6,8,10` são
  `11516544931740`, `247316428382`, `20000021893`, `2876933922`,
  `589716911`, `155192558`; as cotas superiores combinadas são
  `11517046272860`, `247328041335`, `20001454250`, `2877230214`,
  `589803742`, `155227863`.
- Essas caixas implicam os limites outward dos seis momentos `mu_0,...,mu_5`,
  todos sobre `10^15`:
  `mu0=[497120738431785,497120863767065]`,
  `mu1=[22971257853146,22972263438625]`,
  `mu2=[2962796777021,2962936490547]`,
  `mu3=[599281349236,599324394020]`,
  `mu4=[160960848696,160977462757]`,
  `mu5=[53035715024,53043538641]`.
- A tela centrada com essas caixas conservadoras dá `N10 ≥ 1.2177e-14`.
  A prova planejada pode usar a margem simples `center ≥ 23/10^14` e
  `error ≤ 223/10^15`, deixando `N10 ≥ 7/10^15`. Esses dois números ainda
  são screen até o replay da expansão; não são teoremas Lean nesta linha.
- **Screen corrigido, ainda não-prova.** O script
  `research/theta-tenth-screen-2026-09-17.py` soma corretamente a cauda
  `u>1` com o fator global. Para `512` células, `pi=d20`, segundo modo
  explícito e erro exterior `10^-11`, obteve as caixas indicativas
  `mu0≈[0.497120738431785317,0.497120798057960128]`,
  `mu1≈[0.022971783525985492,0.022972263284121831]`,
  `mu2≈[0.002962804193027923,0.002962936488771107]`,
  `mu3≈[0.000599281560733995,0.000599324393938663]`,
  `mu4≈[0.000160960858146124,0.000160977462725664]` e
  `mu5≈[0.000053035715692610,0.000053043538574142]`.
- A avaliação ingênua, termo a termo, ainda dá um intervalo grande em torno
  de zero (`aprox. [-1.4517e-10,1.4565e-10]`). Depois da expansão centrada de
  `N10` em desvios dos centros — que preserva o cancelamento algébrico entre
  ocorrências repetidas — o screen dá
  `N10≈[2.9247e-14,4.5254e-13]`, com centro `2.4089e-13` e erro absoluto
  `2.1165e-13`. Isso é evidência racional externa, não teorema Lean; a
  expansão centrada ainda trata as caixas dos `mu_j` como independentes e
  precisa ser replayada formalmente.
- A primeira versão do screen, que omitia a cauda `u>1`, foi descartada e não
  deve ser reutilizada. O intervalo positivo dessa versão não é evidência
  válida.

NO-GO / NÃO REPETIR:
- O raw Gamma/Cauchy não pode ser costurado globalmente ao Wronskiano
  completed; o no-go diagonal já está registrado no repositório.
- O raw bracket Hilbert C3 falha: `c(0,2)=0` mas `c(1,1)=6`.
- O carrier Taylor TFVD positivo atual falha já em `(0,0)`; existe o teorema
  `enrichedTfvdTaylor_zero_zero_ne_moment` e o defeito exato correspondente.
- O frame Green/projetivo literal também tem Gram `(0,0)` estritamente acima
  do momento nativo; portanto não pode ser o kernel de momentos.
- Não existe fatorização linear global de apenas o positive Wronskian readout
  para o readout coisométrico/chiral ampliado. Isso não prova impossibilidade
  no subespaço coerente TFVD, mas exige preservar a proveniência.
- O Green-port global sem os cinco canais residuais não pode ser identificado
  globalmente com o Wronskian completed sem o no-leak estrutural; em zero
  Genuine fora da linha crítica, o teorema existente impede precisamente
  esse cancelamento no limite.
- **No-go novo e específico para a última interface.** O atlas canônico
  uncentered `nativeC3SeededClockMaterialAtlas M s` de todos os blocos
  nativos até `M` falha já em `(p,q)=(0,0)`: sua massa é uma soma positiva
  `≥1`, enquanto o jet chiral corrigido de ordem zero é `h_0<1/16` somente no
  crosswalk final. Logo ele não satisfaz
  `HasSameEdgeGreenToClockBoundaryTransport`. Isto não exclui uma extensão
  centrada, assinada, Green-corrigida ou defect-complemented do atlas.
- Um `Λ_p` pontual com domínio somente `(ℂ × ℂ)` não carrega, por si só, a
  informação do índice Taylor `p`; o domínio mínimo honesto é um jet de ports
  ou uma família de estados, salvo incluir a derivação na própria operação.
  Isso é uma obstrução de interface, não um no-go contra uma família
  arbitrária de funcionais `Λ_p` que fosse ajustada externamente.
- Não usar `diag(r/c)`, `P_dark D P_dark`, `A_6* A_6`, nem o bracket C3 cru como
  operador de alturas; nenhum deles resolve este seam.

IDENTIDADES IMPORTANTES:
- `nativeGpreFiniteTfvdReconstruction_comp_analysis`.
- `canonicalCompletedC3DirichletGradient_causalGreen_add_boundary`.
- `canonicalCompletedC3DirichletGradientCausalGreenBoundaryState_sum`.
- `canonicalCompletedC3RawGammaGram_eq_causalAdjointSquare` e
  `canonicalCompletedC3RawGammaGram_eq_causalFourChannel`.
- `canonicalC3BracketTfvdMixedCorrectedBoundary_eq_greenReadout`.
- `completedWronskian_factors_through_correctedTfvdBoundary_then_green`;
  ele é a fonte da decomposição `port + cinco resíduos` verificada no probe.
- `canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime` e
  `canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime`.
- `canonicalC3BracketTfvdResponseTaylorCoefficient_eq_completed` junto com
  `canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_response`;
  sua composição é a identidade all-order corrected-response/TFVD compilada.
- `canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_response`.
- `completedNativeGreenResponseTaylorCoefficient_even_eq_zero` e
  `canonicalCompletedC3FullWronskianChiralResponse_odd_eq_canonicalMoment`.
- `HasSameEdgeGreenToClockBoundaryTransport` continua sendo exatamente a
  calibração material não provada; a equivalência com o transporte corrigido
  já existe, mas não fornece sua instância.

ARQUIVOS/TEOREMAS USADOS:
- `primos/CPFormal/Analytic/CpCarryWeightedVerticalBracketTrace.lean`;
  `CpCarryWeightedVerticalReturn.lean`;
  `CpCarryWeightedVerticalTfvdIdentity.lean`;
  `CpNativeGpreTfvdAnalysis.lean`.
- `CarrySelfAdjointOperator/CompletedC3DirichletGradientBracketSource.lean`.
- `CompletedC3CausalGreenGramSewing.lean`;
  `CompletedNativeCausalGreenProvenance.lean`.
- `CarrySelfAdjointOperator/CompletedNativeSeededClockTfvdSixSource.lean`
  (novo; bridge material coordenada a coordenada para os cores TFVD
  ordinary/log-jet, reconstrução lossless, porta radial e jet chiral
  enriquecido all-order).
- `CarrySelfAdjointOperator/CompletedNativeSeededClockTfvdRawAtlasNoGo.lean`
  (novo; expansão da massa do atlas material literal e no-go all-`M` contra o
  jet enriquecido / transporte same-edge).
- `CompletedC3BracketTfvdGreenFactorization.lean`;
  `CompletedC3SameStructuredBoundaryState.lean`;
  `CompletedNativeCorrectedCausalChiralGate.lean`;
  `CompletedNativeChiralBlockMomentProbe.lean`;
  `CompletedC3FullWronskianPolarization.lean`.
- Hatano repo: `HatanoNelsonBoundaryAtlas/Green.lean` e
  `HatanoNelsonBoundaryAtlas/BoundaryCompression.lean`.
- Probes Lean compilados sem modificar a teoria: `/tmp/ports_to_chiral_probe.lean`,
  `/tmp/ports_to_chiral_residual_probe.lean` e
  `/tmp/ports_to_chiral_six_channel_probe.lean`,
  `/tmp/ports_to_chiral_portjet_interface_probe.lean`.
- `CarrySelfAdjointOperator/CompletedNativeThetaTenthSupport.lean` (novo;
  suporte `pi=d20`, segundo modo, resto geométrico separado e cauda exterior
  sharp até `p≤10`).
- `CarrySelfAdjointOperator/CompletedNativeThetaSecondModeQuadrature.lean`
  (novo; derivadas, convexidade e cotas de célula do segundo modo).
- `CarrySelfAdjointOperator/ThetaTenthMomentCertificateData/` (artefato
  gerado; replay Lean completo `4146/4146`).
- `research/theta-tenth-bounds-2026-09-17-generate.py` (novo; gerador dos
  nós/células compartilhados e do agregado racional).
- `research/theta-tenth-screen-2026-09-17.py` (novo; screen racional externo
  com primeiro/segundo modo, cauda exterior e expansão centrada de `N10`).

GARGALO EXATO:
O gate `PORTS (enriquecidos) → corrected causal/chiral first column` está
formalmente fechado. O domínio mínimo não é `Tr_q x : ℂ×ℂ`, mas o **jet
orientado de seis análises TFVD** (ordinary/log-jet em `z`, `w` e `reflected z`),
cada uma contendo `((B_q x, Tr_q x), provenance)`, junto aos parâmetros globais
para tail/xi/chart. Uma compressão ulterior para um port pontual só pode ser
pedida depois de provar que preserva essa proveniência e os cross terms.

O Gram positivo cru foi agora decidido negativamente para o atlas material
canônico uncentered completo `nativeC3SeededClockMaterialAtlas M s`: ele não
pode atravessar a interface já em `p=0`. O gargalo restante não é calibrar
esse Gram, mas identificar a realização material **enriquecida/corrigida** que
substitui sua soma positiva por um readout assinado de ports Green, cross terms
e proveniência. Uma nova candidata só pode ser considerada se não contiver a
mesma massa central positiva não compensada.

PRÓXIMO MICRO-PASSO:
O micro-gate de interface material acima já foi superado pela realização
`nativeC3SeededClockTfvdSixSourceFinalReadout`; não construir um novo Gram.

O próximo gate recomendado é `THETA10 → det G3`:

1. ~~Formalizar a cota de cauda exterior sharp junto com a decomposição de dois
   modos na cota superior de `completedNativeThetaTailMoment`.~~ **Concluído**:
   `completedNativeThetaTailMoment_finite_upper_refined_two_mode` integra
   formalmente `[0,1] + Ioi 1` para todo `p≤10`.
2. ~~Reusar o gerador preservado, agora com `512` células, `pi=d20`, potência
   `10` e o segundo modo explícito, para emitir limites Lean para
   `∫_0^1 x^p*thetaFirstMode x` e
   `∫_0^1 x^p*thetaSecondMode x`. Gerar fora da árvore primeiro e validar
   antes de acrescentar os artefatos grandes.~~ **Concluído:** o replay
   `4146/4146` passou.
3. Formalizar a expansão centrada de `N10`: um lema de erro absoluto para os
   desvios dos seis `mu_j`, seguido de uma instância racional com as caixas do
   screen. Esse é o certificado que preserva a aritmética do cancelamento;
   avaliar os treze monômios originais separadamente continua insuficiente.
4. Transportar a caixa formal por
   `completedNativeXiCosineMoment_five_eq_thetaTailMoments`, provar o sinal
   estrito de `N10`, e combinar com
   `canonicalCompletedNativeHankel_three_det_eq_xiTenthMomentRatio` e
   `completedNativeXiCosineMoment_pos 0` para concluir `det G3 > 0`.

Critério de PASS: todos os limites e a expansão centrada são Lean, o último
passo usa apenas o crosswalk downstream theta/xi, e o teorema final é o
determinante do momento native. Se a margem desaparecer depois de incluir a
cauda exterior e replayar a aritmética, o resultado correto é FAIL/ajuste de
caixa, não invocar positividade genérica de uma medida cosseno nem retornar à
rota Hausdorff/dilation, que já tem no-go de quarto jet.

LIÇÃO EXTERNA, SOMENTE METODOLÓGICA:
O manuscrito OpenAI de Navier--Stokes consultado nesta rodada organiza a prova
em campo-base, defeito/estresse explícito, correções no suporte do defeito e
verificação formal das restrições preservadas. Isso não é insumo matemático
para este repositório nem torna o resultado externo definitivo; a aplicação
honesta aqui é isolar `A10` como defeito residual e não reabrir o carrier
TFVD/material que já satisfaz a interface corrigida.

STATUS:
PARTIAL + FAIL ÚTIL. A rota enriquecida
`SeededClockBlock → ordinary/log-jet → seis análises TFVD → ports +
proveniência → first-column chiral corrigida` foi formalizada all-order. A
última interface para o atlas positivo nativo literal foi decidida por no-go
em `p=0`, inclusive para todos os blocos `0,...,M`. Portanto
`HasSameEdgeGreenToClockBoundaryTransport` é impossível nessa realização crua;
o próximo objeto precisa ser assinado/Green-corrigido por construção. No gate
  novo, a extensão theta até `p=10` e a cota exterior sharp estão formalizadas,
  e o screen corrigido tem margem positiva apenas no certificado centrado ainda
  não replayado no Lean; `det G3 > 0` permanece OPEN. O subgate da cota de
  momento theta de ordem dez e o replay Lean das caixas de quadratura estão
  PASS (`4146/4146`); falta a expansão centrada de `N10` e o transporte final
  ao determinante.
=== END CHECKPOINT ===

=== CHECKPOINT: AUDITORIA DE INTEGRAÇÃO DO REPOSITÓRIO — 2026-09-17 ===
Objetivo atual:
Auditar PRs, commits e artefatos produzidos, verificar compilação Lean local e
integrar somente o conteúdo validado no repositório remoto, preservando o
trabalho local ainda não classificado.

CONFIRMADO:
- O PR #59 (`Integrate native geometry/operator audit checkpoints`) foi
  mergeado por squash. `origin/main` e o checkout atual estão em
  `1a5f60bb9c642b679be064cf2c8dad458fd04cca`.
- A auditoria remota encontrou 59 PRs no total: 45 `MERGED`, 14 `CLOSED` e
  nenhum `OPEN`. Os PRs fechados são rascunhos/rotas exploratórias; não foram
  reabertos nem misturados ao histórico principal.
- O PR #59 foi compilado antes do merge em worktree isolado após unir
  `origin/main` e passou com 9.522 jobs. A colisão de ambiente entre os dois
  predicados `HasCorrectedNativeChiralBoundaryTransport` foi corrigida por
  renomeação semântica do predicado do atlas finito para
  `HasCorrectedNativeSeededClockBoundaryTransport`; o build da união passou.
- O `lake build` final no checkout pós-merge passou: `Build completed
  successfully (9522 jobs)`, exit 0.
- `git diff --check` não encontrou erro. No diff Lean introduzido pelo PR #59
  não há linhas novas com `sorry`, `admit` ou declaração `axiom`; os
  `#print axioms` auditados permanecem nos axiomas padrão observados
  (`propext`, `Classical.choice`, `Quot.sound`, conforme o teorema).
- As duas modificações rastreadas que estavam no worktree local,
  `CompletedNativeCameraTfvdGreenFrameDefectCrosswalk.lean` e
  `CompletedNativeChiralReturnStorage.lean`, compilaram diretamente com
  `lake env lean` (exit 0) e foram incorporadas pelo PR #60.
- A bateria local anterior dos módulos Lean diretos passou para os 26 arquivos
  auditados (25 arquivos de produção e um probe); os 113 nós e 16 células do
  certificado theta, além do agregado, também passaram. Esses resultados são
  testes locais de arquivos ainda não integrados, não teoremas publicados em
  `main`.

NOVO NESTA RODADA:
- A integração remota foi efetivamente concluída no commit
  `1a5f60bb9c642b679be064cf2c8dad458fd04cca`; o comando de merge só falhou na
  limpeza de uma branch local porque ela está referenciada por um worktree
  antigo em `/tmp/carry-corrected-native-20260913`. Esse worktree não foi
  alterado.
- O worktree temporário criado para a auditoria em `/tmp/csa-next-audit` foi
  removido depois de confirmado que estava limpo.

NO-GO / NÃO REPETIR:
- `CompletedNativeTenthOrderHankelPositivity.lean` não é PASS: a compilação
  ficou mais de 25 minutos em alto uso de CPU/memória, sem erro Lean e sem
  produzir `.olean`, e foi interrompida de forma controlada. Classificação:
  `TIMEOUT/OPEN`, não falha matemática.
- Os artefatos pós-PR localizados no checkout — dados theta gerados, probes,
  scripts, backups, `tmp/` e `__pycache__/` — não foram apagados nem incluídos
  no merge. O worktree continua deliberadamente sujo.
- O sucesso de compilação do PR #59 não fecha o gate matemático
  `positividade nativa → dslope`; o checkpoint anterior continua válido:
  storage/contractivity e o transporte explícito TFVD→return permanecem
  condicionais/abertos.

IDENTIDADES IMPORTANTES:
- `origin/main = 1a5f60bb9c642b679be064cf2c8dad458fd04cca`.
- PR #59: https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/59
- Build final: `lake build` → `Build completed successfully (9522 jobs)`.
- O conteúdo publicado do PR são os 18 arquivos listados no merge; o material
  local posterior permanece fora da história remota.

ARQUIVOS/TEOREMAS USADOS:
- `/home/thlinux/carry-self-adjoint-operator/CarrySelfAdjointOperator.lean`.
- `/home/thlinux/carry-self-adjoint-operator/CHECKPOINT_NATIVE_GEOMETRY_OPERATOR_2026-09-14.md`.
- `/home/thlinux/carry-self-adjoint-operator/docs/CHECKPOINT_AUTO_ADJUNTO.md`.
- `/home/thlinux/carry-self-adjoint-operator/CarrySelfAdjointOperator/CompletedNativeCameraTfvdGreenFrameDefectCrosswalk.lean`.
- `/home/thlinux/carry-self-adjoint-operator/CarrySelfAdjointOperator/CompletedNativeChiralReturnStorage.lean`.

GARGALO EXATO:
A integração do conjunto do PR #59 está PASS e `main` compila. O que ainda
não pode ser chamado de “tudo produzido integrado” é o lote local posterior:
há 25 módulos de produção/provenance compilados isoladamente, um consumidor
de décima ordem em timeout e artefatos gerados que precisam de separação antes
de qualquer novo PR. Independentemente disso, o gargalo matemático upstream
da positividade native/Green para `dslope` segue PARTIAL/OPEN.

PRÓXIMO MICRO-PASSO:
Em uma retomada explícita, separar o lote local em um PR limpo: excluir
backups/tmp/dados gerados, decidir o destino dos dois arquivos modificados,
reproduzir o timeout da décima ordem com uma estratégia incremental e só então
integrar qualquer parte adicional. Não fazer isso durante a pausa.

STATUS:
PARTIAL — integração remota validada e mergeada; lote local adicional e gate
matemático native-positivity→dslope permanecem fora de `main`.
=== END CHECKPOINT ===

=== CHECKPOINT: FECHAMENTO DA AUDITORIA — 2026-09-18 ===
Objetivo atual:
Deixar o repositório pausado em um estado reproduzível, com os PRs validados
mergeados e o restante local explicitamente separado.

CONFIRMADO:
- PR #60 foi mergeado como
  `fba7b5e3d058ea7d573f004d284966a668747492`; `HEAD`, `main`, `origin/main` e
  `origin/HEAD` apontam para esse SHA.
- O build final pós-PR #60 passou com `lake build` e 9.522 jobs. O agregador
  `CarrySelfAdjointOperator/Audit.lean` também passou localmente.
- O `#print axioms` pontual dos oito teoremas novos do PR #60 reportou apenas
  `propext`, `Classical.choice` e `Quot.sound`.
- Estado remoto final: 60 PRs conhecidos, 46 `MERGED`, 14 `CLOSED` e nenhum
  `OPEN`. Isso não significa que todas as branches exploratórias remotas sejam
  ancestrais de `main`; significa que não há PR aberto pendente.

NOVO NESTA RODADA:
- `main...origin/main` está sincronizado (`0 0`) e não há modificações
  rastreadas pendentes; somente os artefatos locais untracked permanecem.
- A branch local antiga do PR #59 não foi apagada porque um worktree antigo a
  referencia; nenhum worktree antigo foi alterado.

NO-GO / NÃO REPETIR:
- O consumidor `CompletedNativeTenthOrderHankelPositivity.lean` segue
  `TIMEOUT/OPEN`: execução acima de 25 minutos, sem erro Lean e sem `.olean`.
- Os 25 módulos de produção/provenance locais que compilaram isoladamente, o
  probe separado, os 130 arquivos do certificado theta e os arquivos em
  `tmp/` não devem ser tratados como integrados até existir um PR limpo e um
  build conjunto; backups, scripts e caches continuam preservados.
- O build verde do repositório não promove o gate matemático
  native-positivity→dslope a teorema: o checkpoint de storage/contractivity
  continua `PARTIAL / OPEN`.

IDENTIDADES IMPORTANTES:
- `chiralMultiplierContractiveAt_iff_storage_one_nonnegative`.
- `chiralMultiplierEventuallyContractive_iff_storage_one_eventually_nonnegative`.
- `fullWronskianRegularizedChiralSampleMatrix_eq_dslope`.
- `storage_one_eventually_nonnegative_iff_dslope`.
- `br2CameraBracketProjectiveHilbertParityJet_zeroGram_gt_nativeMoment`.
- `br2CameraBracketGreenFrameParityJet_zeroGram_gt_nativeMoment`.

ARQUIVOS/TEOREMAS USADOS:
- `/home/thlinux/carry-self-adjoint-operator/CarrySelfAdjointOperator/CompletedNativeChiralReturnStorage.lean`.
- `/home/thlinux/carry-self-adjoint-operator/CarrySelfAdjointOperator/CompletedNativeCameraTfvdGreenFrameDefectCrosswalk.lean`.
- `/home/thlinux/carry-self-adjoint-operator/CarrySelfAdjointOperator/Audit.lean`.
- `/home/thlinux/carry-self-adjoint-operator/research/checkpoints/PORTS_TO_CORRECTED_CHIRAL_CHECKPOINT.md`.

GARGALO EXATO:
Do ponto de vista de integração, não há gate remoto pendente: `main` compila.
Do ponto de vista matemático, ainda falta a desigualdade geométrica all-order
que identifica a energia Green/return upstream com a positividade de
`dslope`; o PR #60 apenas tornou explícita a equivalência condicional e os
no-gos locais.

PRÓXIMO MICRO-PASSO:
Ao retomar, revisar o lote untracked em um worktree limpo, começando pelo
timeout da décima ordem e pelo transporte TFVD→storage. Não fazer staging
global nem incluir dados/probes automaticamente.

STATUS:
PASS — auditoria e integração dos PRs validados concluídas.
PARTIAL / OPEN — trabalho local adicional e gate matemático permanecem
deliberadamente fora de `main`.
=== END CHECKPOINT ===

=== CHECKPOINT ===
Objetivo atual:
Retomar a missão de positividade nativa e fechar a interface
`carry/incidência → energia Green/Tilt → TFVD/completed/return → dslope`,
sem usar momentos ou theta como definição.

CONFIRMADO:
- O lado escalar `completed ledger → dslope` continua formalmente fechado;
  a proveniência material six-source/TFVD e a reconstrução
  `G_q B_q + R_q Tr_q = I` também continuam fechadas.
- `ChiralReturn.storage k c r` é uma energia acumulada de retorno já definida
  no carrier Cauchy nativo. Sua identidade exata
  `storage_re_eq_norm_balance` preserva todos os termos de interferência e
  diz que sua parte real é `‖incidente‖² - ‖retornado‖²`.
- `integral_flux_eq_storage` identifica essa energia acumulada com o fluxo
  Green/retorno integrado no eixo real interno `r`; `hasDerivAt_storage`
  mantém explícita a lei local, que pode ter sinal oposto.
- `CanonicalCompletedNativeRadialChiralMultiplierContractiveAt` é a
  desigualdade de norma para toda combinação finita das câmeras Cauchy e do
  multiplicador chiral nativo.
- A identificação geométrica nova a ser formalizada é:
  `storage ≥ 0 para todo coeficiente e todo r`
  `↔` `CanonicalCompletedNativeRadialChiralMultiplierContractiveAt`.
  A ida para a esquerda usa apenas a seção `r=1` e
  `storage_re_eq_norm_balance`; a volta usa a mesma identidade para os
  coeficientes escalados por `r^(i+1)`. Nenhum `h_n`, Hankel PSD ou theta é
  premissa.
- Portanto, após essa equivalência, os teoremas existentes já dão como
  consequência condicional a equivalência entre positividade eventual do
  storage, positividade eventual do carrier projectivo e positividade
  eventual das matrizes radiais de `dslope`.

NOVO NESTA RODADA:
- O micro-gate escolhido é um bridge Lean pequeno:
  `return storage nonnegative ↔ finite chiral return contractive`.
  Ele fornece uma formulação upstream do mesmo defeito positivo que o
  carrier projectivo assinado lê como `dslope`, sem renomear o alvo pelo
  resultado.
- A distinção crucial foi preservada: a não-negatividade integrada do
  `storage` não implica positividade do fluxo local. Já existe o exemplo
  formal `two_point_storage_nonnegative_but_endpoint_flux_negative`.

NO-GO / NÃO REPETIR:
- O carrier ReturnMetric de gradiente ordinário é grande demais no centro:
  seu kernel central excede o momento nativo. Isso é no-go local dessa
  realização/metric, não da geometria inteira.
- O atlas positivo seeded-clock uncentered falha em `(0,0)` por massa
  central `≥ 1` contra `h_0 < 1/16`; não reabrir esse atlas.
- O raw Gamma/Cauchy, o bracket C3 cru e o Taylor TFVD cru continuam
  descartados pelos no-gos já registrados.
- Não promover a equivalência storage/contractivity a uma prova de
  contractividade all-order: a propriedade storage não-negativa ainda é o
  gate geométrico aberto.

IDENTIDADES IMPORTANTES:
- `ChiralReturn.storage_re_eq_norm_balance`.
- `ChiralReturn.integral_flux_eq_storage`.
- `ChiralReturn.hasDerivAt_storage`.
- `canonicalCompletedNativeRadialChiralMultiplierContractiveAt_iff_pickPosSemidef`.
- `canonicalCompletedNativeRadialChiralMultiplierEventuallyContractive_iff_dslope`.
- `canonicalCompletedNativeRadialProjectiveChiralEventuallyPosSemidefinite_iff_contractive`.
- `canonicalCompletedNativeRadialProjectiveChiralSampleMatrix_eventually_eq_dslope`.

ARQUIVOS/TEOREMAS USADOS:
- `/home/thlinux/carry-self-adjoint-operator/CarrySelfAdjointOperator/CompletedNativeChiralReturnStorage.lean`.
- `/home/thlinux/carry-self-adjoint-operator/CarrySelfAdjointOperator/CompletedNativeRadialChiralMultiplier.lean`.
- `/home/thlinux/carry-self-adjoint-operator/CarrySelfAdjointOperator/CompletedNativeProjectiveChiralCarrier.lean`.
- `/home/thlinux/primos/CPFormal/Analytic/CpNativeGpreTfvdAnalysis.lean` e
  os módulos `CpCarryWeightedVertical*` para a reconstrução upstream.

GARGALO EXATO:
Ainda falta demonstrar a propriedade geométrica
`∀ N, ∀ᶠ k, ∀ c r, 0 ≤ Re(storage k c r)` a partir de carry/incidência,
Green refletido, TFVD enriquecido e/ou uma contração derivada desses canais.
O bridge atual só mostra que essa é exatamente a mesma desigualdade finita
do multiplicador chiral; ele não fornece a desigualdade.

PRÓXIMO MICRO-PASSO:
Criar `CompletedNativeChiralReturnGreenGate.lean` com:
1. a definição da não-negatividade do storage em `(k,N)`;
2. a equivalência finita com `ContractiveAt`;
3. a equivalência eventual all-order com o gate de contração;
4. a consequência condicional para a matriz radial `dslope`, via os bridges
   projectivo/chiral já provados;
5. `#print axioms` dos novos teoremas.
Depois disso, comparar esse `storage` com os seis canais TFVD; se não houver
intertwiner exato, registrar o defeito canal por canal em vez de afirmar
identificação de Gram.

STATUS:
PARTIAL / OPEN. O defeito positivo foi isolado em uma propriedade de energia
de retorno upstream e a rota exata até `dslope` está disponível
condicionalmente. A prova da propriedade geométrica all-order e o transporte
explícito dos ports TFVD para esse storage ainda não estão fechados.
=== END CHECKPOINT ===
