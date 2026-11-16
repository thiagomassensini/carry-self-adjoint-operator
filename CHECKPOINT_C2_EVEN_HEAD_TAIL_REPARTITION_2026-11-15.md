# Checkpoint — repartição par da fonte C2

## Base e arquivos

- Base matemática indicada: `c999ce41ccdec0ff194e7969bf1f7f329d374d3a`.
- A branch isolada parte do head do PR #117 `87e448a6c2fdd35b61cc3f6ff824bef9dc1b4b88` e inclui o commit de transporte de erro `0af49efe5951e2c2542f2729d0ee97b99d9434c4` por cherry-pick (`f71bf69`).
- Fontes conferidas: `C2LegCompletionPolarization.lean`, `CompletedNativeC2ExactTailTransport.lean`, `CompletedNativeTfvdWronskianMoments.lean`, a declaração de paridade em `CompletedGreenDiagonalClosure.lean` e `C2SourceFormErrorTransport.lean`.
- Novos artefatos: `CarrySelfAdjointOperator/C2EvenHeadTailRepartition.lean` e `CarrySelfAdjointOperator/C2EvenHeadTailRepartitionAudit.lean`; o módulo e a auditoria foram registrados em `CarrySelfAdjointOperator.lean`.

## Resultados Lean

- `c2EvenProjection` é um mapa linear complexo, idempotente e com imagem par.
- A igualdade eventual `F = H + T` mais a paridade local de `F` implica `F =ᶠ P(H) + P(T)`. A fórmula da derivada projetada e o companheiro negativo também foram provados.
- Para germes analíticos, o logaritmo derivado é analítico sob a hipótese explícita de valor central não nulo e ímpar quando o germe é par. O mesmo foi instanciado na variável complexificada radial `f(y)=P(H)(iy)`.
- A identidade polinomial finita para `(y^(2j+1)+t^(2j+1))/(y+t)` foi provada por fatoração, sem divisão; fora da diagonal, o quociente segue por cancelamento.
- A repartição foi instanciada usando a cabeça original já vestida `c2FiniteChartHeightCharacteristic M` e a cauda original vestida `L*T_M`. A identidade de cauda existente fornece `F-H_M=Tfull_M` no domínio do germe; a paridade usada é `completedNativeOperatorCharacteristic_eventually_even`. Nenhuma paridade ou positividade individual da cabeça foi assumida.
- A convergência da cauda exata para zero prova `P(H_M)(0)≠0` eventualmente, a partir de `F(0)≠0`.
- `c2ProjectedMomentForm_error_transport` reaproveita diretamente `complexSourceMomentForm_error_lower`; a soma dupla não foi refeita.
- Os módulos novo e Audit passaram por `lean -DwarningAsError=true`. O `#print axioms` transitivo retorna apenas `propext`, `Classical.choice` e `Quot.sound`; não há `sorryAx` nem axioma novo.

## Extensão analítica e transporte de erro: argumento escrito e obrigação de formalização

Se `u(w)=Σⱼ aⱼw^(2j+1)` é ímpar e analítica num disco de raio `r₀>0`, escolha `0<ρ<r<r₀`. Para `|y|,|t|≤ρ`, cada polinômio `Qⱼ(y,t)=Σ_{ℓ=0}^{2j}(-1)^ℓy^(2j-ℓ)t^ℓ` satisfaz `|Qⱼ(y,t)|≤(2j+1)ρ^(2j)`. Além disso,
`(2j+1)|aⱼ|ρ^(2j) = (|aⱼ|r^(2j+1)/r)·(2j+1)(ρ/r)^(2j)`;
como `(2j+1)(ρ/r)^(2j)` é limitada e `Σⱼ|aⱼ|r^(2j+1)` converge, a série dos polinômios converge absoluta e uniformemente no bidisco fechado de raio `ρ`. Seus somatórios parciais são polinômios, logo o limite localmente uniforme é analítico em `(y,t)`. Fora de `y+t=0`, a fatoração finita já provada identifica o limite com `(u(y)+u(t))/(y+t)`. Esta prova analítica é escrita, mas a construção do PowerSeries bivariado/teorema Lean de limite analítico permanece pendente.

Para os momentos, a ponte ainda não formalizada é: em um disco aberto que contém `|z|≤R`, provar `H=P(H_M)` sem zeros no disco e `q=Tfull_M/H` analítica com `|q|≤η<1`; definir o ramo por `g=Σₙ₌₁∞(-1)^(n+1)qⁿ/n`, que converge uniformemente, é par e satisfaz `|g|≤B=-log(1-η)`. Então `-F'/(2F) - (-H'/2H)=-g'/2`; Cauchy no círculo de raio `R` dá `|hⱼ-htildeⱼ|≤(j+1)B/R^(2j+2)`. Para `R=1/4`, o limite é `(j+1)16^(j+1)B`, exatamente a entrada do adaptador para `C2SourceFormErrorTransport`. Ainda é preciso formalizar a realidade dos coeficientes do corte projetado e provar, para a fonte concreta, as condições de domínio, não anulação e razão pequena; elas não são postuladas aqui.

## Controle negativo e verificações

- O pacote externo `certificar_cabeca_simetrica.py`/`certificado_cabeca_M8.json` é cálculo intervalar, não Lean. Para `M=8`, ele certifica `htilde₁∈[-0.0101330523,-0.0101330501]⊂(-0.01014,-0.01013)`. Isso impede concluir PSD para toda cabeça projetada; não diz impossibilidade para a fonte completa ou para cortes adaptativos.
- Comandos Lean concluídos: compilação de `CarrySelfAdjointOperator/C2EvenHeadTailRepartition.lean`, `CarrySelfAdjointOperator/C2EvenHeadTailRepartitionAudit.lean` e do agregador `CarrySelfAdjointOperator.lean`, todos com `-DwarningAsError=true`, usando as interfaces compiladas das revisões citadas.
- `lake build +CarrySelfAdjointOperator.C2EvenHeadTailRepartition` foi tentado no worktree limpo. A reconstrução da cadeia importada chegou a `[9081/9840]` e foi interrompida (código 130) devido ao tempo/custo da recompilação em paralelo; não houve erro de prova no módulo novo. A compilação direta Lean acima e a auditoria transitiva terminaram com código 0.

## Hipóteses restantes

Não há hipótese de positividade nem de zeros da característica completa adicionada. A hipótese `P(H)(0)≠0` aparece explicitamente no teorema abstrato de analiticidade e, para as cabeças finitas concretas, sua validade eventual é deduzida da convergência. Permanecem abertas apenas as pontes de convergência analítica e o controle concreto de Cauchy descritos acima.
