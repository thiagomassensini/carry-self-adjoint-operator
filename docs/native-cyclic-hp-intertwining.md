# Realização cíclica nativa: auditoria da derivação e seam tipado

Base confirmada em `origin/main`: `535ddcf9eb3cd5f48e062f3918dfe9c11b0962ff`.
Branch: `agent/native-cyclic-realization-hp-intertwining`. Sem merge.

**Outcome C.** A derivação do operador a partir da resposta do carry existe literalmente. Não foi identificada, nas fontes auditadas, uma realização positiva cíclica **anterior aos momentos** que descarregue o certificado HP. Esta conclusão não refuta a derivação existente nem afirma inexistência de outra realização nativa.

## Conferência dos scripts originais solicitada durante a rodada

Foram lidos os scripts em `/home/thlinux/Downloads/Wayl/`, sem executá-los como prova:

- `native_autoadjunto.py:113`: `native_state_series` é a rotação de amplitude `1/sqrt(n)` e frequência `-log(n)`.
- Linhas 159–201: stencil de carry e cauda integral, com pesos e canais preservados na construção escalar.
- Linhas 289–295: `closed_native_series` soma head e tail, divide pelo fator da câmera e aplica a completion.
- Linhas 298–321: divisão logarítmica e matrizes `G_ij=h_(i+j)`, `K_ij=h_(i+j+1)`.
- Linhas 325–343: `build_operator` aplica Cholesky a `G`, forma `J=L⁻¹KL⁻ᵀ` e calcula `J⁻¹/²`. Portanto a origem nativa do operador é explícita; não há ajuste de uma lista espectral nesta função.
- `native_carry_height_moment_jacobi_operator_lab.py:219–282`: o operador generalizado, a closure de última coluna, `x₀=sqrt(h₀)e₀` e os jets Krylov são construídos **depois** dos momentos. Nas linhas 278–284 o próprio script distingue a fatoração positiva via Cholesky de `K` da identificação com um readout TFVD nativo, que permanece um crosswalk separado.
- `native_carry_hilbert_polya_operator_lab.py:108–135` chama a construção nativa unificada antes do doubling assinado.
- O módulo unificado não está solto nesse diretório. Foi localizado dentro de `_VENDORED` em `native_carry_signed_height_operator_standalone.py`, decodificando literais com AST/base85/zlib, sem executar o script. Em `native_carry_unified_exact_height_operator_lab.py:212–224`, a sequência é coeficientes → momentos → `jacobi_from_moments` → height.

SHA-256 dos scripts consultados:

```text
native_autoadjunto.py
38100a3c6731cb79d85cd8903c02b2f61c667026303683ae5f99073c91e4d8d3
native_carry_height_moment_jacobi_operator_lab.py
e82e9ff9efe98991f38f5dd50ace0a12a124253f8d6ec61355c1654541eaf929
native_carry_signed_height_operator_standalone.py
e6e8a664aa83a81861ff44eb1fc7d11070c514449470a879b317504fc8625ea4
```

As notas de `/home/thlinux/Documentos/maximo/` confirmam essa ordem. Em `MEMORIA_DERIVACAO_OPERADOR_AUTOADJUNTO_GENUINE.md:388–477`, `X_N=L_N*`, `Y_N=L_N⁻¹K_NL_N⁻*` e depois `x₀=sqrt(h₀)e₀`. `IDENTIDADE_PROJETIVA_EXATA_LIMITE_OPERADOR_ALTURAS.md:368–431` separa expressamente a identificação do Wronskiano da positividade TFVD ainda necessária. Foram também consultadas as seções pertinentes de `NATIVE_CARRY_PRIMITIVE_TO_SPECTRAL_BRIDGE_AUDIT.md` e `OPERADOR_ESPECTRAL_CAMERAS_DEFECT_WEYL.md`. Nenhuma dessas notas foi usada como hipótese Lean.

**Duas afirmações distintas:** o HP é derivado da resposta nativa por uma cadeia determinística; identificar esse HP por uma isometria com uma dinâmica positiva upstream exige, adicionalmente, uma igualdade de readout/Gram. O primeiro fato não foi negado pelo segundo gate.

## Inventário do main

| Passo | Status | Evidência / limite |
|---|---|---|
| `nativeLogGenerator` | CLOSED EXISTING | `NativeLogEvolution`, maximal autoadjunto em ℓ² |
| órbita espectral nativa | CLOSED EXISTING | identidade coordenada e em cada corte finito |
| source crítica como vetor do mesmo ℓ² | OBSTRUCTED | massa harmônica; consequência tipada nesta branch |
| câmera/bracket readout | CLOSED EXISTING | characteristic head+tail e TFVD/Wronskian |
| completed `F` independente de câmera | CLOSED EXISTING | `CompletedOperatorCharacteristic` |
| `F → h_n` | CLOSED EXISTING | recorrência real e transporte triangular |
| definições `G_N,K_N` | CLOSED EXISTING | `hankelGram`, `shiftedHankel`; definição não implica positividade |
| whitening canônico | CONDITIONAL | `canonicalHankelWhitening`, exige `G_N.PosDef` |
| `J_N` canônica | CONDITIONAL | `canonicalFiniteJacobiSection`, mesma hipótese |
| `T_N=J_N⁻¹/²` | CONDITIONAL | `CanonicalFiniteHeight`, exige positividade apropriada |
| realização cíclica positiva nativa `Y,x₀` upstream | OPEN | não fornecida pelos operadores/fontes auditados |
| momentos nativos `⟨x₀,Y^n x₀⟩` | OPEN | para tal realização upstream |
| Gram Krylov nativo `=G_N` | OPEN | igualdade de momentos não descarregada |
| forma deslocada nativa `=K_N` | OPEN | mesmo seam |
| isometria cíclica nativa → Jacobi | OPEN | além do Gram, distinguir compressão e invariância |
| intertwining funcional → height | OPEN | requer hipótese de subespaço redutor |
| diagnóstico triangular exato | CLOSED THIS BRANCH | transporte invertível do erro de momentos |
| HP → readout nativo | CONDITIONAL | já fechado a partir do certificado HP |

## Tipos e candidatos realmente encontrados

`nativeLogGenerator : NativeLogHilbert →ₗ.[ℂ] NativeLogHilbert`, onde
`NativeLogHilbert = ℓ²(ℕ,ℂ)`. Seu domínio maximal exige que
`log(n+1) * x(n)` também pertença a ℓ². `nativeLogGenerator_isSelfAdjoint` e
`nativeLogGenerator_basisVector_log` já fixam essa dinâmica.

A órbita crítica `realSpectralState t : ℕ → ℂ` é coordenada, não um vetor bundled desse espaço. O pin prova

```lean
norm_realSpectralState_sq_eq_inv
not_summable_norm_sq_realSpectralState
```

A nova consequência `nativeLogHilbert_no_undampedCyclicSource` afirma precisamente:

```lean
¬ ∃ x : NativeLogHilbert, ∀ n : ℕ, x n = realSpectralState t n
```

Não se deduz daí que os momentos HP são incompatíveis com toda geometria nativa. Deduz-se que esta source não pode ser passada, sem transformação adicional, a um resolvente Hilbertiano desse gerador.

Há uma source Hilbertiana upstream `nativeCarryWeightedRealSpectralState q hq0 hq1 t : CarryVerticalL2`, com coordenadas `q^n * realSpectralState t n`. Seu amortecimento radial é real e não pode ser apagado. Os teoremas de trace/bracket não a identificam com um readout cíclico da resposta completada. Nenhum peso foi escolhido nesta branch.

O outro objeto upstream auditado é

```lean
nativeGpreCanonicalTfvdBoundaryPencil (q : ℝ) :
  LinearBoundaryPencil NativeGpreComplexEdgeCore NativeGpreTfvdProductBoundary
```

Seus traços são `(x 0, nativeGpreBoundaryValueLift x)` e
`((q:ℂ)⁻¹*x 1-x 0, nativeGpreBoundaryNumberFluxLift x)`.
`nativeGpreCanonicalVerticalRealization` preserva as coordenadas.
`nativeGpreHilbertGluedGreenDefect_eq_verticalWronskian` identifica a forma de bordo e cancela proveniência dentro dela. Isso não fornece sozinho uma relação de defeito espectral com um operador positivo nem a identificação com o Wronskiano completed-native.

Os resolventes `logarithmicResolventRealOperator`/`logarithmicResolventImaginaryOperator` de Spectral-Weyl atuam em `NaimarkSpace` com multiplicador `1+log(x)`. Não há, nos teoremas auditados, a identificação de seu readout com `completedNativeLogDerivative`. Não foram adotados como o `Y_native` procurado.

A realização `MomentPreHilbertSpace` em `CanonicalCompletedNativeStieltjesOperator` usa os próprios `h_n`. É downstream e não serve como construção independente nesta missão.

## Seam escalar existente e diagnóstico novo

A identidade escalar já exata utilizada como fonte de comparação é
`canonicalC3BracketTfvdMoment_eq_canonical M n`. O transporte vetorial existente é
`canonicalCompletedTfvdGreenPortState_eq_bracketGreenPort`; ele identifica funções vetoriais antes dos jets, mas não afirma que um readout resolvente cíclico reproduz os momentos.

A API `PositiveObservableParityKernel` aceita, independentemente dos momentos,

```lean
S : H →L[ℝ] H
x : H
```

Com `S.toLinearMap.IsSymmetric`, a coordenada positiva é `Y=S*S` e
`positiveObservableMoment S x n = ⟨x,S^(2*n)x⟩`.
Seu resolvente local é `Ring.inverse (1-t² • (S*S)) x`, válido sob
`|t|*‖S‖<1`, e sua resposta é `t*⟨x,resolventVector⟩`.
A coordenada reduzida é `u=t²`; não se identifica diretamente tempo logarítmico, altura e variável reduzida.

Nenhum `S,x` concreto nativo foi inserido nessa API nesta branch.

Definimos somente o teste para um candidato fornecido independentemente:

```text
c_N(i) = positiveObservableMoment S x i
D_N = T_N c_N - a_N
```

Aqui `T_N=completedNativeLogDerivativeTriangularMatrix N` (não o operador de altura) e `a_N=completedNativeLogDerivativeSourceVector N`. A definição de `c_N` não menciona momentos canônicos. `D_N` compara com coeficientes da característica; não define uma métrica.

Resultados kernel-checked novos:

1. `nativeCyclicTriangularReadoutDefect_eq_transport`:
   `D_N = T_N (c_N - h_N)`.
2. `nativeCyclicTriangularReadoutDefect_zero_iff`:
   `D_N=0 ↔ ∀ i:Fin N, positiveObservableMoment S x i = h_i`.
3. `nativeCyclicTriangularReadoutDefect_all_zero_iff_convolution`:
   todos os testes finitos zeram se e somente se o defeito de convolução **já existente** zera em toda ordem.

Não há afirmação de que esses defeitos zeram. A fórmula residual exata é

```text
phi_0 <x,S^(2n)x>
+ sum_{k<n} <x,S^(2k)x> phi_(n-k)
+ (n+1) phi_(n+1).
```

O centro requer `phi_0 ‖x‖² + phi_1 = 0`; não é uma licença para ajustar a norma da source.

Hipóteses remanescentes literais da API downstream existente:

```lean
(hS : S.toLinearMap.IsSymmetric)
(hcyclic : LinearIndependent ℝ (positiveObservableOrbit S x))
(hdefect : ∀ n, positiveObservableNativeConvolutionDefect S x n = 0)
```

Antes delas é necessário identificar geometricamente `H,S,x`. `hcyclic` aqui significa independência de todos os vetores da órbita, não apenas densidade do span. A API de resolvente local exige também `[CompleteSpace H]` e `|t|*‖S‖<1`.

## Compressão não é intertwining

Mesmo depois de obter os momentos, `J_N=Q_N*YQ_N` é compressão. Para uma isometria `Q_N`,

```text
Y Q_N - Q_N J_N = (I-Q_N Q_N*) Y Q_N.
```

A igualdade forte só segue se esse leakage zera. Um prefixo Krylov geralmente perde a próxima potência pela última coluna; não é automaticamente invariante. Da mesma forma, `f(Q_N*YQ_N)=Q_N*f(Y)Q_N` não vale em geral. Para `f(y)=y⁻¹/²`, requer-se uma realização redutora e hipóteses de domínio/invertibilidade adequadas. Estas observações são condições matemáticas para a etapa futura, não novos theorems Lean desta branch.

O whitening atual permanece `canonicalLDLInverseFactor`, com `BGBᵀ=I`.
A orientação futura é `Q=XBᵀ`, `J=BKBᵀ`. Não foi construída outra implementação Cholesky.

## Respostas obrigatórias

1. Operador upstream auditado: `nativeLogGenerator`, e o pencil TFVD canônico como candidato a uma futura relação; nenhum identificado como a coordenada compacta HP.
2. Source literal auditada: `realSpectralState 0`; não pertence ao ℓ². A versão radial existe mas não tem a identificação de readout exigida.
3. Esses objetos upstream não usam momentos/Jacobi. A source cíclica do laboratório, por outro lado, usa `sqrt(h₀)e₀`.
4. `Y_native` independente ainda não foi identificado. `S*S` é a coordenada da API genérica, sem instanciação nativa.
5. Autoadjunção de `nativeLogGenerator` já existe; não foi provada identificação desse gerador com a coordenada positiva compacta.
6. O readout genérico é o resolvente de `I-t²S²`, com a resposta ponderada por `t` acima.
7. Sua igualdade com o `q` completed-native não foi provada para um par nativo concreto.
8. Residual: a convolução explícita acima; seu diagnóstico finito é exatamente `T_N(c_N-h_N)`.
9. Não foi provada a igualdade de todos os momentos de uma órbita nativa independente.
10. Não foi provado um novo `G_N=X_N*X_N` nativo.
11. Não foi provado um novo `K_N=X_N*Y X_N` nativo.
12. PSD/PosDef canônicos continuam condicionais. A positividade dos Grams do candidato genérico já existe e não identifica os Grams nativos.
13. LDL canônico existente; não modificado.
14. `Q_N` nativo não construído.
15. Compressão/intertwining nativo não provado; invariância é condição adicional.
16. Intertwining funcional não provado e não foi inferido da compressão.
17. Signed HP já existe downstream, sem nova identificação upstream nesta branch.
18. Não construído certificado HP incondicional.
19. A igualdade signed-generator/readout nativo continua disponível sob o certificado existente.
20. Nenhum operador ou source foi definido dos momentos para simular independência.
21. Nenhuma prova nova usa theta/zeta/lista de zeros. A completion já definida permanece como dado do projeto; scripts históricos foram inspecionados, não usados como prova numérica.
22. Outcome C. O no-go tipado da source sem amortecimento é local; não é Outcome D contra a derivação.
23. Próximo theorem mínimo: construir no carrier nativo uma relação positiva e source justificadas, e provar seu readout completed = resolvente cíclico. Na rota limitada `Y=S²`, isso deve fornecer `hdefect` acima para o par concreto; a independência permanece separada.
24. Os quatro theorems novos usam apenas `propext`, `Classical.choice`, `Quot.sound`.
25. Validação registrada abaixo.
26. Branch e base no início; commit/push no relatório de entrega. Não há merge.

## Alteração de manutenção e validação

O build direto revelou no próprio commit-base uma falha em
`completedNativeLogDerivativeTriangularMatrix_mulVec_moments`: o `change` tentava identificar `(if p then a else 0)*b` com `if p then a*b else 0` por igualdade definicional. Foi acrescentado somente `simp only` para abrir `mulVec`, distribuir `ite_mul` e simplificar `zero_mul`. Enunciado, definições e pins preservados.

O módulo novo e sua auditoria compilam. As verificações completas são registradas após a execução.
