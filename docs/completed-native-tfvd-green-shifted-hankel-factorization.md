# Fatoração Green/TFVD do Hankel deslocado

Esta branch parte de `d24418fe03cd0af306b9c0e15ca095ae0dfda570` e investiga a derivação camera-free do operador HP. As notas em `/home/thlinux/Documentos/maximo/` foram usadas somente como registro arqueológico; nenhuma afirmação das notas foi importada como hipótese Lean.

## Escopo e resultado

A definição geométrica nova é

```lean
greenJetOddPrefixSynthesis jet N
```

que envia `c : Fin N → ℝ` para a soma dos primeiros jatos ímpares de Green:

$$
B_Nc=\sum_{i<N}c_i\,o_i,
\qquad o_i=\texttt{greenJetOddSectorJet jet i}.
$$

Ela não menciona `moments`, `shiftedHankel`, `K_N`, Cholesky, `Y_N`, alturas ou autovalores. O objeto geométrico associado ao seu adjunto quadrático é

```lean
greenJetOddPrefixGram jet N
```

ou seja, a matriz `Matrix.gram` dos vetores `o_i`. Os teoremas

```lean
greenJetOddPrefixSynthesis_basis
 greenJetOddPrefixSynthesis_basisGram
 greenJetOddPrefixSynthesis_inner_eq_gram
```

provam, respectivamente, a ação nos vetores coordenados, a matriz Gram na base e a forma polarizada. Assim a fatoração geométrica `B_N* B_N` é incondicional na forma de Gram.

A identificação desse Gram com o Hankel deslocado continua sendo exatamente o seam já exposto pelo repositório:

```lean
IsGreenWronskianMomentKernelGramRepresentation moments jet
```

Sob essa hipótese, `greenJetOddPrefixGram_eq_shiftedHankel_of_greenRepresentation` e `greenJetShiftedHankelFactorization_of_greenRepresentation` dão

$$
\operatorname{Gram}(o_0,\ldots,o_{N-1})
=(h_{i+j+1})_{i,j<N}.
$$

Portanto a rota fecha a positividade geométrica e a fatoração condicional, mas não fabrica o certificado nativo ausente.

## Mapa do gap

| Passo | Status | Evidência |
|---|---|---|
| TFVD/Wronskian → sequência canônica `h_n` | CLOSED EXISTING | `cameraFreeTfvdWronskianMoment_eq_canonical`, baseado em `canonicalC3BracketTfvdMoment_eq_canonical` |
| quociente dividido de `q` → `h_{i+j+1}` | CLOSED EXISTING no nível do kernel de coeficientes | `greenWronskianMomentKernel`, `greenWronskianMomentKernel_odd_shiftedMomentGram` |
| definição finita de `K_N` | CLOSED EXISTING | `shiftedHankel moments N` |
| TFVD vetorial → porta Green | CLOSED EXISTING | `cameraFreeTfvdGreenPort_vector_intertwiner` e `CompletedTfvdGreenAllOrderIntertwining` |
| energia positiva de proveniência nativa em todos os coeficientes | OPEN | os estados CPFormal são finitos/representacionais; não dão o `jet` nativo completo |
| polarização em duas variáveis dessa energia | CONDITIONAL | a polarização geométrica existe para `greenJetOddPrefixSynthesis`; a comparação nativa requer a hipótese Gram |
| energia positiva → Wronskiano deslocado | CONDITIONAL | `IsGreenWronskianMomentKernelGramRepresentation` |
| `K_N = B_N* B_N` | CONDITIONAL para o `K_N` nativo; CLOSED GEOMETRICAMENTE para `greenJetOddPrefixGram` | `greenJetOddPrefixSynthesis_inner_eq_gram`, e comparação sob `hrep` |
| `K_N` PSD | CONDITIONAL para o `shiftedHankel`; CLOSED para o Gram geométrico | `greenJetOddPrefixGram_posSemidef`, `shiftedHankel_posSemidef_of_greenJetFactorization` |
| `Y_N` PSD | CONDITIONAL | segue da transferência já existente quando o Hankel deslocado é PSD |
| consequência Jacobi/altura | CONDITIONAL | depende do Gram nativo; a álgebra downstream já está formalizada |

## Objetos e dependências

O kernel de coeficientes já existente é

```lean
greenWronskianMomentKernel moments :
  Matrix (ℕ ⊕ ℕ) (ℕ ⊕ ℕ) ℝ
```

com bloco ímpar/ímpar `moments (i + j + 1)` e blocos mistos nulos. A representação requerida é

```lean
IsGreenWronskianMomentKernelGramRepresentation moments jet
```

com `jet : (ℕ ⊕ ℕ) → E`, `[InnerProductSpace ℝ E]`, e igualdade entrywise entre esse kernel e `Matrix.gram ℝ jet`.

O fator finito novo tem tipo

```lean
(Fin N → ℝ) →ₗ[ℝ] greenJetOddHilbertSubspace jet
```

O contradomínio é o subespaço fechado ímpar do carrier Green já existente. Não foi criada outra completion. A função `greenJetOddSectorJet` é a família geométrica usada pelo fator.

O teorema

```lean
greenJetOddPrefixSynthesis_norm_sq_eq_shiftedHankel_quadratic
```

afirma, sob `hrep`,

$$
\|B_Nc\|^2
=\sum_{i,j<N}c_i h_{i+j+1}c_j.
$$

O defeito entrywise explícito é

```lean
greenJetShiftedHankelFactorizationDefect moments jet N i j
  = moments (i+j+1) - greenJetOddPrefixGram jet N i j.
```

`greenJetOddPrefixGram_eq_shiftedHankel_iff_defect_zero` prova que o Gram nativo coincide com o Hankel deslocado se e somente se esse defeito é zero em cada entrada. Esse é o único residual da comparação nesta branch.

## Relação com a energia Green/Jacobi

`greenJetOddPrefixSynthesis_generator_eq_greenJetEnergyFactorCore` identifica cada vetor coordenado com a aplicação do fator algébrico existente

```lean
greenJetEnergyFactorCore heven
```

em `greenJetEvenCoreJet`. Não foi usada a sequência `h_n` para construir o fator. Quando `hrep` está disponível, `GreenJetJacobiFiniteCompression` já fornece a compressão Jacobi e a igualdade da Gram ímpar com o `shiftedHankel`.

A versão canônica de completion

```lean
canonicalCompletedNativeForwardDifferenceOddPrefixFactorization
```

é deliberadamente condicional: recebe `hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel ...` e aplica o teorema existente `canonicalCompletedNativeGreenForwardDifferenceLimitParityJet_momentKernel`. Ela mostra que, se um kernel Green nativo concreto for fornecido, o prefixo ímpar resultante tem exatamente o Hankel deslocado. Não há neste commit uma prova incondicional de `hkernel`; os no-go da métrica C3 estática e dos carriers Taylor anteriores permanecem respeitados.

Os objetos CPFormal

```lean
finiteSeededTfvdBesselEnergy
canonicalEnrichedPrimeCarryDefectProvenanceState
nativeGpreHilbertGluedGreenDefect
```

foram auditados como fontes históricas/representacionais, mas não foram promovidos a `B_N` universal: dependem de cartas, sementes ou dados finitos específicos e não fornecem a família de coeficientes Green completa exigida aqui.

## Três distinções preservadas

1. `greenJetOddPrefixGram` é o Gram do fator geométrico ímpar.
2. `shiftedHankel moments N` é o kernel escalar determinado por `h_{i+j+1}`.
3. `Y_N`, a torre Jacobi e a altura são construções posteriores que só podem consumir a identificação dos dois primeiros.

A igualdade entre esses objetos não foi assumida por positividade. A única ponte é `IsGreenWronskianMomentKernelGramRepresentation`.

Não foram usados `sixCamera`, limites de atlas, `allBasesWeylInverse`, Gamma/Cauchy escalar refutado, carriers C3 positivos refutados, `Gpre` como atalho, primalidade, theta, zeta, zeros, RH ou fitting numérico.

## Outcome

**Outcome C — residual exato isolado.** A energia Green ímpar e a forma `B_N*B_N` geométrica estão fechadas sem circularidade. A passagem para o `K_N` nativo é equivalente ao anulamento do defeito `greenJetShiftedHankelFactorizationDefect`, isto é, à construção camera-free de uma representação Gram Green/Wronskiana para o estado nativo. A branch não afirma esse anulamento.

O próximo theorem mínimo é uma identidade concreta, anterior a qualquer Cholesky ou positividade matricial:

```lean
IsGreenWronskianMomentKernelGramRepresentation
  canonicalCompletedNativeLogDerivativeMoment
  canonicalNativeTfvdGreenJet
```

ou, na forma mais operacional, a igualdade de cada pairing ímpar

$$
\langle b_j,b_i\rangle
=h_{i+j+1}
$$

para a família vetorial construída diretamente da energia TFVD/Green completa, incluindo os canais de fronteira e proveniência que ainda não foram empacotados num `jet` nativo único.

## Relatório técnico

1. A cadeia histórica recuperada é `carry → TFVD → Wronskian/Green → energia positiva → Hankel deslocado → Jacobi → altura`; as notas são apenas arqueologia.
2. O objeto analítico atual que representa `q` é `completedNativeLogDerivative`; sua sequência de coeficientes é `canonicalCompletedNativeLogDerivativeMoment`.
3. `cameraFreeTfvdWronskianMoment_eq_canonical` (por `canonicalC3BracketTfvdMoment_eq_canonical`) identifica os coeficientes com `h_n`.
4. O kernel deslocado é `greenWronskianMomentKernel`; o bloco ímpar é `shiftedHankel`.
5. A igualdade dos coeficientes `h_{i+j+1}` é provada sob `IsGreenWronskianMomentKernelGramRepresentation`, via `greenWronskianMomentKernel_odd_shiftedMomentGram`.
6. O fator positivo antes da comparação escalar é `greenJetOddPrefixSynthesis`, ligado a `greenJetEnergyFactorCore`.
7. Sim: sua definição não menciona `h_n`, `K_N` ou Cholesky.
8. A fonte é a família `greenJetOddSectorJet jet` no subespaço ímpar fechado do carrier Green.
9. A identidade de duas variáveis é a igualdade entrywise de `greenWronskianMomentKernel` com `Matrix.gram`; o residual explícito mede sua falha para o jet concreto.
10. O formalismo preserva diagonal, off-diagonal e separação par/ímpar; a presença de canais de proveniência, fronteira, log-jet e completion está encapsulada na hipótese `hrep`, não demonstrada por esta branch.
11. O numerador Wronskiano é o kernel de coeficientes cuja expansão ímpar dá `h_{i+j+1}`; o nome Lean é `greenWronskianMomentKernel` no nível já normalizado.
12. O numerador positivo é o Gram `Matrix.gram ℝ (greenJetOddSectorJet jet)`.
13. Eles coincidem somente sob `hrep`; para um jet concreto nativo isso permanece o residual acima.
14. O residual exato é `greenJetShiftedHankelFactorizationDefect`.
15. Ele pertence ao canal de identificação Green/Wronskiana do jet; a origem concreta (fronteira, proveniência ou completion) ainda não é separada internamente.
16. A igualdade `⟨b_j,b_i⟩ = h_{i+j+1}` é obtida condicionalmente pelo teorema de representação Gram e `gram_greenJetOddSectorJet_prefix`.
17. Sim: `B_N` é `greenJetOddPrefixSynthesis`, construído diretamente dos jatos.
18. Sim, em forma de Gram e forma quadrática; para o `K_N` escalar nativo a igualdade é condicional a `hrep`.
19. O Gram geométrico fica PSD incondicionalmente; o `K_N` nativo fica PSD quando o defeito é zero.
20. PosDef não é concluído automaticamente; exige independência linear dos jatos ímpares, via `shiftedHankel_posDef_of_greenJetFactorization`.
21. `Y_N` permanece condicional à positividade transferida do Hankel deslocado.
22. Não. A construção do fator usa apenas o jet e a estrutura de Hilbert; momentos entram somente na comparação.
23. Não há câmera em nenhum theorem novo de fatoração.
24. Não foi usada primalidade.
25. Não foram usados theta, zeta ou zeros.
26. Nenhum carrier refutado foi reutilizado como fundamento.
27. Outcome C.
28. Próximo theorem mínimo: construir a representação Gram Green/Wronskiana camera-free do `jet` TFVD/Green nativo completo, ou provar o anulamento do defeito entrywise.
29. Os teoremas novos não introduzem axiomas; a auditoria deve mostrar no máximo `propext`, `Classical.choice` e `Quot.sound` herdados das APIs.
30. `lake build`, os dois módulos de auditoria, `scripts/audit.sh`, `git diff --check` e `python3 -m json.tool` são os checks a executar antes do commit.
31. Branch `agent/native-tfvd-green-shifted-hankel-factorization`, base `d24418fe03cd0af306b9c0e15ca095ae0dfda570`; commit/push serão registrados após esses checks.

## Próximo gate

A derivação positiva não deve começar em `K_N`. O próximo passo é empacotar a energia TFVD/Green completa (incluindo off-diagonal, boundary e proveniência) numa família `jet` e provar a igualdade `greenWronskianMomentKernel = Matrix.gram`. Uma vez anulando o defeito, toda a positividade e a torre Jacobi já disponíveis podem ser reutilizadas sem nova fatoração artificial.
