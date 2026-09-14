# CHECKPOINT AUTO-ADJUNTO

Branch: `agent/next-natural-native-gate`
HEAD: `e0d3d09` (`Record native carrier seam checkpoint`)
Data: 2026-09-14

## Meta global

Remover a hipótese geométrica restante e instanciar nativamente
`CompletedNativeRealHPCarrierCertificate` pela cadeia carry → bracket/TFVD →
Green → carrier Hilbertiano correto → momentos canônicos → Jacobi/altura,
sem zeros, fitting, RH ou certificado assumido.

## Estado confirmado

- `CompletedNativeGeometryHeightProvenance.lean`: a cadeia
  `nativeGeometry_to_finiteHeight_chain_of_greenMomentKernel_and_incidenceTransport`
  já consome `IsGreenWronskianMomentKernelGramRepresentation` e o transporte
  incidencial; a independência par/ímpar já existe.
- `NaturalNativeOperatorShiftCapstone.lean`: a equação de coeficientes do
  response Green e o shift estão fechados antes de Gram.
- `CompletedNativeReturnMetricReadoutCrosswalk.lean`: a métrica
  `I + poisson† ∘L poisson` é positiva, auto-adjunta e possui identidade
  polarizada de retorno; ainda recebe a escolha do readout/canal.
- `CompletedNativeTfvdGreenMomentGramBridge.lean`: o defeito exato entre o
  Gram do jet Green e o kernel de momentos está nomeado como
  `canonicalCompletedNativeGreenMomentGramDefect`; a equivalência com o
  transporte Green está formalizada, mas o defeito não é zero em geral.
- `CompletedNativeCorrectedClockBoundaryGate.lean`: o transporte corrigido
  de primeira coluna, `HasCorrectedNativeChiralBoundaryTransport`, implica a
  equação de coeficientes, o kernel de momentos e o certificado HP.
- PR #57 (`agent/corrected-native-chiral-clock-tower`) está confirmado como
  **OPEN**, não mergeado em `main`; deve ser auditado antes de depender dele.

## Hipóteses ainda abertas

- Realizar geometricamente, no mesmo carrier, o Gram
  `polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment`.
- Provar o readout corrigido/valvulado ou a costura de bordo que fornece a
  primeira coluna sem assumir o transporte chiral.
- Se a rota radial for usada, provar simultaneamente a boundary intertwining e
  a strictness uniforme; elas não estão fechadas incondicionalmente.

## No-goes já provados

- O carrier C3 concreto padrão `ordinary ⊕ logJet ⊕ real residual` falha no
  defeito central `(0,0)`; não deve ser ressuscitado nem reescalado.
- A métrica de retorno genérica é positiva, mas seu kernel central é energia
  Green estritamente maior que `h₀`; portanto não é o carrier de momentos.
- O kernel projectivo bruto tem massa diagonal ≥ 1 e não coincide com `h₀`.
- A resposta BR2 causal literal tem massa mínima incompatível com `h₀`.
- Coeficientes corretos da torre quiral não são, sozinhos, uma realização
  Hilbertiana positiva.

## O que NÃO precisa ser refeito

- Não reconstruir Hankel, Jacobi, resolvente, equivalência zero↔autovalor ou
  independência par/ímpar já formalizada.
- Não usar tabela de zeros, scan em `t`, fitting, RH ou positividade assumida.
- Não confundir energia positiva pré-Hankel com igualdade de momentos.

## Alterações feitas nesta sessão

- arquivo: `docs/CHECKPOINT_AUTO_ADJUNTO.md`
- theorem: interface de retomada; nenhum theorem Lean novo ainda.
- motivo: registrar o estado obrigatório antes da arqueologia do PR #57 e
  preservar o gargalo como uma única folha verificável.

## Builds/audits executados

- comando: `ssh llm 'cd /tmp/carry-corrected-native-20260913 && git status ...'`
- resultado: branch limpa além do `.lake` não rastreado; HEAD `e0d3d09`.
- comando: `gh pr view 57 --json number,state,mergedAt,headRefName,baseRefName,title`
- resultado: PR #57 OPEN, base `main`, head
  `agent/corrected-native-chiral-clock-tower`, `mergedAt = null`.

## Gargalo atual EXATO

Provar, para um jet `jet` construído diretamente do carrier Green/TFVD/valva
corrigido,

```lean
IsGreenWronskianMomentKernelGramRepresentation
  canonicalCompletedNativeLogDerivativeMoment jet
```

sem usar `CompletedNativeRealHPCarrierCertificate`, `K`, `J` ou uma métrica
positiva escolhida retroativamente.

## Próxima ação mínima

Auditar o HEAD do PR #57 e comparar seus teoremas de torre corrigida com
`CompletedNativeCorrectedClockBoundaryGate.lean`, identificando se já existe
uma seta não usada para o carrier Hilbertiano; se não existir, registrar o
menor residual de primeira coluna que ainda impede essa seta.

## Retomada

"AO RETOMAR, LEIA ESTE CHECKPOINT PRIMEIRO E CONTINUE DAQUI.
NÃO REPITA INVESTIGAÇÕES MARCADAS COMO FECHADAS OU NO-GO."
