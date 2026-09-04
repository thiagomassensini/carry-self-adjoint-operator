# Atualização do mapa de costuras — 4 de setembro de 2026

Esta atualização complementa o `Mapa_costuras_carry_2026-09-04.md` fornecido no
notebook. Preserva a distinção entre resultados do kernel, identidades
condicionais e os argumentos dos anexos de limites.

## Integração e dependências matemáticas

| Etapa | Resultado e referência |
| --- | --- |
| Reconstrução discreta–projetiva | Integrada pela #46; merge `fd2797dd922d7f3510d07df2eb6060270f41e02f`. |
| Boundary trace | Correção e cobertura da auditoria integradas pela #47; merge `08fe08cb7e491531dcd9411c86459d1ffb7185e0`. |
| Universalidade multibase | #48 corrigida e integrada; commit validado `8884d673e2871f52b2ba65b112014839b1442b05`, merge `b5421bfc853c8008f4dd6b9c8f084662e6674c6d`. Auditoria dedicada: 4.039 jobs; auditoria completa: `kernel audit passed`. |
| Recíproca do espectro pontual | `CompletedNativeJacobiPointSpectrumConverse.lean`: sob o certificado real, `lambda > 0` implica `HasEigenvalue J_C lambda ↔ F((sqrt lambda)⁻¹) = 0`. Auditoria dedicada: 4.093 jobs; auditoria completa: `kernel audit passed`. |
| Realização geométrica global | Continua exigindo a identificação Hilbert do kernel logarítmico nativo e a independência de todas as ordens. As equivalências de positividade existentes não fornecem uma prova incondicional dessa entrada. |

```text
câmeras com cabeça + cauda exata
  → característica normalizada comum F
  → coeficientes pares e momentos logarítmicos únicos
  → matrizes G_N e K_N comuns em toda ordem

realização Gram nativa + independência par e ímpar
  → CompletedNativeRealHPCarrierCertificate
  → Jacobi positivo, fechado, maximalmente autoadjunto e cíclico
  → resolvente e leitura escalar nativa
  → F(t)=0 ⇒ t⁻² autovalor (extração atômica existente)
  → t⁻² autovalor ⇒ F(t)=0 (nova recíproca, t real não nulo)
```

A correspondência pontual agora é bidirecional. A existência geométrica do
certificado está na entrada dessa cadeia, antes da construção do operador.

## Kernel exato a realizar

Escreva `F = completedNativeOperatorCharacteristic` e
`Psi = completedNativeOperatorBoundaryCompanion = -F′`. A normalização é fixa:

$$
\widehat\Psi_{\rm state}(z)
  = (\sqrt{2}\,F(z))^{-1}\,\mathrm{state}(z),
\qquad a(z)=\frac{-F'(z)}{2F(z)}.
$$

A hipótese real mínima utilizada pela construção de diferenças finitas é a
definição existente em `CompletedGreenForwardDifferenceGramBridge.lean`:

```lean
HasCompletedNativeRealAxisNormalizedGreenKernel state
```

Sua expressão exata, para todos `x z : ℝ` com `F(x) ≠ 0` e `F(z) ≠ 0`, é

```lean
inner ℂ
  (normalizedCompletedGreenState
    completedNativeOperatorCharacteristic state (x : ℂ))
  (normalizedCompletedGreenState
    completedNativeOperatorCharacteristic state (z : ℂ)) =
  dslope
    (completedGreenNormalizedResponse
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion) (x : ℂ) (z : ℂ)
```

O valor diagonal de `dslope` é a derivada da resposta. Fora da diagonal, a
ordem é `(a(z)-a(x))/(z-x)`; a identidade complexa usa a conjugação no primeiro
argumento. Os coeficientes de paridade são exatamente

$$
K_{\rm mom}(\mathrm{inl}\,i,\mathrm{inl}\,j)=h_{i+j},\quad
K_{\rm mom}(\mathrm{inr}\,i,\mathrm{inr}\,j)=h_{i+j+1},\quad
K_{\rm mom}(\mathrm{inl}\,i,\mathrm{inr}\,j)=0.
$$

`hasCompletedNativeGreenKernelTwoStepLimit` já prova o limite escalar conjunto.
`canonicalCompletedNativeGreenForwardDifferenceLimitParityJet_momentKernel`
constrói e identifica o Gram dos vetores limite **quando** recebe o kernel
Hilbert acima, em um carrier completo. Não é preciso acrescentar uma hipótese
de existência do limite escalar.

## Obrigação concreta para a rota Green-frame/BR2

Para uma base e raio com `IsSupported base` e `radius ∈ radiusSet base`, a
seguinte proposição é uma entrada suficiente já aceita pelas APIs existentes
(no namespace `CarrySelfAdjointOperator`, com `open Filter Topology
CPFormal.Analytic.Cp`). Seu tipo foi conferido pelo Lean nesta etapa:

```lean
∃ state : ℂ → CarryVerticalL2,
  HasCompletedNativeRealAxisNormalizedGreenKernel state ∧
  ∀ i : ℕ ⊕ ℕ,
    Tendsto
      (fun k ↦ canonicalCompletedGreenFrameAnalysisCLM
        (completedGreenForwardDifferenceParityJet
          (normalizedCompletedGreenState
            completedNativeOperatorCharacteristic state) k i) -
        br2CameraBracketGreenFrameParityJet base radius i)
      atTop (nhds 0)
```

`completedNativeRealHPCarrierCertificate_of_greenFrameDefect`, em
`BR2GreenFrameDslopeLimitBridge.lean`, transforma esses dados no certificado do
jet limite efetivo. A nova equivalência espectral aplica-se então diretamente.
Essa proposição registra o alvo restante; não foi provada nesta etapa.

A igualdade vetorial com as coordenadas BR2 fixa também uma escolha de fase e
identificação. O mesmo arquivo demonstra
`not_forall_greenFrameDslopeBR2DefectLimit_of_kernel`: o kernel escalar sozinho
não força a mesma identificação BR2 para `state` e `-state`. Uma realização
geométrica precisa demonstrar a compatibilidade dessa escolha. Uma alternativa
é fornecer um transporte real-linear injetivo
`BR2BracketIncidenceJetTransport base radius jet`, preservando o Gram nativo;
as famílias de incidência já têm independência global provada.

## O que a investigação das fontes fornece

| Fonte efetivamente consumida | Conteúdo disponível | Passo que não fica automático |
| --- | --- | --- |
| `CompletedC3CausalGreenGramSewing.lean` | Gram C3 cru como adjunto-quadrado da resposta causal mais bordo, incluindo cruzamentos. A igualdade com o readout global é equivalente à igualdade explícita de energias. | Igualdade com o kernel logarítmico nativo normalizado. |
| `CompletedC3FinalReadoutKernelBridge.lean` | O ledger completo, após divisão pelos fatores de chart, característica e separação espectral, dá exatamente `dslope a`; inclui a diagonal real e os coeficientes. | Esse readout escalar ser um produto interno positivo do estado concreto. |
| `CanonicalEnrichedBoundaryResidualIdentity.lean` | Identidade incondicional com três defeitos explícitos: proveniência Green, cruzamentos de arestas e correção dos resíduos dos readouts. | O cancelamento da soma dos três canais para o estado efetivo. |
| `CompletedNativeProjectiveChiralCarrier.lean` | Realização assinada como diferença do Gram Cauchy e do Gram do multiplicador, com amplitude projetiva. | Contratilidade quiral eventual em toda ordem e não degenerescência. |
| `CompletedNativeSignedGeneratorHerglotzGram.lean` | Positividade estrita Stieltjes é equivalente a Herglotz radial eventualmente PSD mais não degenerescência de ambas as torres. | Provar essas duas condições a partir da geometria, sem usar o certificado que elas devem construir. |
| `CPFormal/Analytic/CpMinimalProvenanceQuotient.lean` | Presente no pin: quociente por `ker Q ⊓ ker A`, ambos os mapas descendem, com equivalência linear ao range conjunto. | Continuidade, fechamento e compatibilidade da forma Hilbert na realização analítica. |

Não foi alterado nenhum pin para usar essas fontes.

## Relação com os anexos do notebook

Foram lidos os anexos de limite resolvente forte, Weyl comprimido, frame de
probes e a nota `RELACAO_DE_BORDO_UNITARIA_CARRY_WEYL.md`. Eles propõem o operador
`H_log = V L V*`, `L e_n = log(n)e_n`, com extensão zero no complemento. Sua
compressão usa `(zeta-H_log)⁻¹`, enquanto o readout de Jacobi usa
`(J_C-lambda)⁻¹`. Os sinais, operadores e parâmetros são distintos.

A nota de bordo conserva a fonte externa e fornece, no chart de impedância,
`Gamma_0 = J_E* f`, `Gamma_1 = u`, com domínio dinâmico
`{(f,H_log f + J_E u) : f ∈ Dom H_log}` e família
`(J_E*(zeta-H_log)⁻¹J_E)⁻¹`. Esses argumentos ajudam a conservar a resposta e o
bordo no limite. Não identificam por si o kernel `dslope a`. As alegações de
limite e maximalidade desses anexos não foram promovidas aqui a novos teoremas
Lean; os resultados numéricos citados neles também não foram usados como prova.

Com seis câmeras e `zeta` fixo, um estado que fatoriza somente por esse espaço
de saída tem dimensão efetiva no máximo seis sobre os complexos, ou doze sobre
os reais. Assim, essa escolha finita não fornece sozinha independência estrita
em toda ordem. A próxima construção deve conservar um carrier mais rico e
provar o acoplamento polarizado, com a normalização acima e todos os bordos.

A universalidade das câmeras da #48 permite trabalhar com uma câmera
normalizada para os momentos. Ela não elimina o problema da realização positiva.
