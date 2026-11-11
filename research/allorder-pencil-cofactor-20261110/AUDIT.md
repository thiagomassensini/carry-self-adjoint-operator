# Auditoria — all-order pencil/cofactor

## Proveniência e limites

- Os momentos são os `canonicalCompletedNativeLogDerivativeMoment` já definidos na cadeia da fonte. Não foram redefinidos por zeros, alturas ou modos espectrais.
- O `nativeSourceCofactorThetaPolynomial_integral_bordered` existente é uma identidade sem hipótese de invertibilidade ou positividade. Usa adjugata/determinante, e identifica a integral com um escalar bordeado.
- `nativeSourceCofactorSign_iff_stieltjes` identifica um gate de sinal all-order com a positividade de Stieltjes. É uma equivalência, não uma derivação da desigualdade de fonte.
- `nativeSchurEuler_even_balance` e `nativeSchurEuler_odd_balance` requerem que o prefixo anterior seja `IsUnit`. O balanço ímpar retém um quadrado não negativo, mas também retém uma integral assinada.
- `nativeSchurEuler_odd_pos_iff_mass_balance` é condicional à mesma invertibilidade e reduz o sinal do pivô a uma desigualdade estrita entre massas. A dominância das massas não está provada.
- `NativeSourceSchurThetaMasses.lean` define massas positiva e negativa como integrais de partes positiva/negativa e prova que a massa negativa é estritamente positiva em toda ordem ímpar. Logo não se pode substituir a integral assinada por uma alegação de não negatividade pontual.
- `NativeSourceThetaGreenTransport.lean` mantém explicitamente os termos de fronteira na integração de Green; depois mostra que os traços centrais dos polinômios Schur específicos se anulam. A transferência não estabelece densidade não negativa.
- `GreenWronskianHankelBridge.lean` prova positividade das Hankel sob uma representação de Gram de um único kernel de Green e independência linear dos jets (para positividade estrita). Esse módulo não constrói tal representação para os momentos nativos completados; usá-la como se já estivesse construída seria hipótese analítica adicional.

## Categorias de resultado

| Categoria | Estado atual |
|---|---|
| Identidade algébrica provada no código existente | Cofatores, escalar bordeado e integral cofactor theta (`nativeSourceCofactorThetaPolynomial_integral_bordered`). |
| Identidade algébrica provada nesta branch | `nativeSourceHankelPencilPolynomial_eq_cofactor`: `det(XG-K)` igual ao polinômio da direção de cofatores para todo `s,n`, sem hipótese de inversibilidade ou sinal. A transformação triangular tem determinante 1; a prova é division-free. |
| Identidade algébrica provada nesta branch | `nativeSourceHankelCriticalVector_mul` e `nativeSourceHankelCriticalVector_energy`: a janela seguinte aplicada ao vetor crítico dá `(0,…,0,τ_{s,n+1})`, com energia `τ_{s,n}τ_{s,n+1}` para todo `s,n`. |
| Identidade algébrica provada nesta branch | `nativeSourceCofactorThetaPolynomial_integral_eq_prefixDet_mul_succ`: a integral original é `c₀τ_{s,n}τ_{s,n+1}`, sem hipótese de sinal. |
| Teorema condicional novo | `nativeSourceCofactorThetaPolynomial_integral_pos_iff_nextPrefixDet_pos` requer explicitamente `0<c₀` e `0<τ_{s,n}`; não prova `0<I_{s,n}`. |
| Identidade algébrica parcial desta branch | `arbitraryHankelToda_one` verifica a identidade de Toda apenas em `n=1`, para sequência arbitrária. Não implica a fórmula para todo `n`. |
| Teorema condicional novo | `nativeSource_even_odd_towers_posDef_of_euler_mass_gates` dá as duas torres sob `c₀>0` e dominâncias explícitas; `nativeSource_all_shift_windows_posDef_of_euler_mass_gates` estende por submatrizes principais a todo shift. As dominâncias continuam como hipóteses. |
| Teorema condicional novo | `nativeSchurEuler_even_pos_iff_mass_balance` caracteriza o gate par sob `IsUnit` do prefixo. No setor ímpar, `nativeSchurEuler_odd_pos_iff_mass_balance` existente foi reutilizado. |
| Teorema Lean existente com hipótese explícita | Critério Schur de extensão positiva e balanços Euler para prefixos invertíveis. |
| Teorema condicional | Equivalência entre o sinal do pivô ímpar e a dominância das massas, sob `IsUnit`. |
| Hipótese analítica da fonte | Uma desigualdade que domine a massa theta negativa pela massa positiva (e pelo quadrado ímpar sobrevivente). |
| Teste numérico/simbólico | Não usado como fundamento de resultado universal nesta branch. As notas de pesquisa mencionam testes finitos, que não substituem prova para todo `n`. |
| Conjectura/obrigação aberta | As duas dominâncias Euler/theta para todo grau, suficientes para as duas torres Hankel. |

## Riscos de circularidade a evitar

1. Não provar positividade de `nativeXiPolynomialIntegral (nativeSourceCofactorThetaPolynomial s n)` assumindo `CanonicalCompletedNativeStieltjesPositivity`; a equivalência existente já mostra que isso contém o gate desejado.
2. Não obter `sourceMomentMatrix` positiva a partir de um Gram positivo cuja representação para a fonte completada ainda não foi construída.
3. Não descartar a parcela negativa da integral Green/Euler. Os arquivos de massas e transporte documentam contribuições negativas reais.
4. Não usar as identidades do pencil, energia ou Toda para inferir sinal sem hipóteses explícitas; essas identidades são division-free e algébricas.
5. Não interpretar `IsUnit`/`PosDef` dos balanços condicionais como resultado all-order já estabelecido.

## Estado do ambiente

- Repositório correto e branch nova confirmados; alterações já existentes no checkout principal ficaram fora da worktree.
- Lean fixado em `leanprover/lean4:v4.32.0`; Lake e todas as revisões do manifest foram lidos.
- Uma primeira resolução foi interrompida durante a obtenção de pacotes. Os clones resultantes foram preservados; `.lake/packages` da worktree foi apontado para a cache existente do checkout principal, com as revisões do manifest mantidas. `lake env lean --version` passou depois disso.
- O build da dependência `NativeThetaCofactorMargin` no checkout isolado começou a recompilar um grafo amplo com certificados theta (interrompido em 9300/9844 tarefas, sem erro relatado). Para compilar o módulo novo, foi usado `lake env lean` do checkout principal com o arquivo de fonte na worktree; o `.olean` da margem corresponde ao último commit sem alteração do respetivo fonte. Resultado: exit code 0, sem warnings.
- `nativeSourceHankelPencilPolynomial_eq_cofactor` foi compilado no módulo focado para todos os `s,n`; seu enunciado não assume `IsUnit`, `PosDef` ou qualquer sinal. O caso `n=0` está incluído no teorema geral.
- `nativeSourcePrefixDet_succ_eq_borderedScalar`, `nativeSourceHankelCriticalVector_mul` e `nativeSourceHankelCriticalVector_energy` também compilam para todo `s,n`, sem inversa, positividade ou condição de posto.
- `NativeHankelPencilThetaBridge.lean` compila contra o módulo do checkpoint 2; a identidade integral usa o teorema bordeado original e a equivalência de sinal permanece condicional. O teorema `nativeThetaCofactorSign_iff_stieltjes` não foi reescrito.
- A identidade division-free de Toda para `n≥1` permanece aberta. A busca local de `Desnanot`, `Dodgson`, `Jacobi`, `condensation`, `minor` e `det_submatrix` não encontrou uma identidade geral apropriada. O lema de bloco `Matrix.det_fromBlocks₁₁` usa `[Invertible A]`, logo não foi usado como substituto.
- A composição condicional das massas com `nativeSchurEuler_even_balance`, `nativeSchurEuler_odd_pos_iff_mass_balance`, `sourceMomentMatrix_succ_posDef_iff` e indução foi compilada. Ela não usa Stieltjes como hipótese e não estabelece os gates das massas.
- `nativeSchurThetaPolynomial_odd_negativeMass_pos` prova que a massa negativa está presente em toda ordem ímpar; `nativeThetaMasses_first_odd` prova dominância apenas no primeiro caso ímpar. Não há passagem nesses resultados para a dominância geral dos polinômios Euler.
- `nativeThetaOddPrincipal_not_pointwise_nonneg` refuta a não negatividade pontual da densidade principal ímpar considerada, mas seu próprio módulo diz que isso não determina o sinal da integral.
- `nativeXiPolynomialIntegral_eq_thetaGreen_integral` mantém os dois termos centrais; `nativeSchurThetaPolynomial_center_traces` os zera apenas para os Schur polinômios. A densidade Green ainda tem termos de sinal negativo (`nativeSchurThetaGreenPolynomial_even_coeff_top_neg` e `nativeSchurThetaGreenPolynomial_first_even_negative`). Isso impede inferir as desigualdades a partir do sinal ponto a ponto.
- Estado de pesquisa: nenhuma prova de `M⁺_{0,n}>M⁻_{0,n}` ou `M⁺_{1,n}+2c₀T_n²>M⁻_{1,n}` para todo `n`; nenhuma hipótese equivalente foi adicionada ao contexto como axioma.
- A hipótese externa `c₀>0` foi retirada dos dois corolários de positividade condicional. O sinal decorre do teorema CSA `completedNativeRealEvenCharacteristicCoefficient_zero_ge_third`, que prova `1/3 ≤ c₀`. `#print axioms` para os corolários atualizados e para esse teorema retorna somente `[propext, Classical.choice, Quot.sound]`; isso não fecha os gates de massa.
- O argumento permanece condicional apenas às desigualdades explícitas das massas: os teoremas não assumem `PosDef` da janela de dimensão seguinte. Em cada passo de Schur, `IsUnit` vem da matriz já positiva definida da dimensão anterior.
- Em `n=2`, `nativeSourceFiveEvenDiscriminant = 8 det(G_{0,3})` e `nativeSourceSixOddDiscriminant = 8 det(G_{1,3})`; as identidades usam apenas a correspondência já provada entre o coeficiente de fronteira fonte-first e `2 H_j`. A positividade dos escalares fonte-first está provada por certificados theta/source de ordem 10 e 12, respetivamente. Os discriminantes de ordem 2 dão apenas `IsUnit` aos prefixos antigos. Com o determinante do passo Schur e os balanços Euler, isso prova as duas dominâncias de massa em `n=2`, mantendo ambas as massas e o quadrado ímpar no enunciado.
- Esta composição não assume positividade definida 3×3: usa as desigualdades fonte-first para demonstrar positividade dos determinantes 3×3. À época, não havia gates além de `n=2`; a continuação abaixo acrescenta somente o gate par `n=3`, sem obter uma recorrência entre as massas.
- Para investigar `n→n+1`, foram reutilizados `nativeSchurCriticalCoefficients_orthogonal`, `sourceMomentConvolution_critical_even` (cancelamento integral completo) e `sourceMomentConvolution_critical_odd` (resíduo exato `T_n²`) por meio dos balanços Euler existentes. As massas são `M⁺=∫max(f,0)` e `M⁻=∫max(-f,0)`; as identidades determinam apenas `M⁺−M⁻`, não controlam separadamente os incrementos de `M⁺` e `M⁻`.
- Definindo `D^even_n := M⁻_{0,n}−M⁺_{0,n}` e `D^odd_n := M⁻_{1,n}−M⁺_{1,n}−2c₀T_n²`, os balanços dão exatamente `D^even_n=−(4n+2)R_{0,n}` e `D^odd_n=−(4n+4)R_{1,n}` quando o prefixo anterior é `IsUnit`. No passo `2→3`, `D^even_3−D^even_2=10R_{0,2}−14R_{0,3}` e `D^odd_3−D^odd_2=12R_{1,2}−16R_{1,3}`. Na auditoria daquele checkpoint, as comparações reduziam aos sinais dos restos. A continuação abaixo fecha `R_{0,3}>0` pela face fonte de ordem 14; o sinal ímpar continua aberto.
- O transporte Green para o polinômio Euler foi formalizado com termos centrais explícitos: `E_{s,n}(0)/2 + E'_{s,n}(0) thetaTail(0)=0`, pois os dois traços são nulos. Isso transporta apenas a integral assinada para `∫G(E) thetaTail`; não dá controle das integrais de `max(f,0)` e `max(-f,0)`.
- Foram inspecionados `nativeSourceSevenEvenDiscriminant_pos` e `nativeSourceEightOddDiscriminant_pos_iff_characteristic_ceiling` como entradas fonte-first para ordem 3/4. Nesta continuação foi concluída a ponte formal 4×4: o primeiro transfere positividade a `det(G_{0,4})`; o segundo deixa `det(G_{1,4})` equivalente ao ceiling estrito de `c₈`. O teorema de ceiling especifica um alvo adicional, mas não prova a dominância de massa.
- A compilação focada terminou com exit code 0. Lean imprimiu apenas uma sugestão de reescrita por `ring_nf`; isso não foi erro nem lacuna. Não foi alegada compilação do grafo completo de Lake, cujo build anterior foi interrompido por custo.
- Os dois documentos de pesquisa pedidos foram lidos da branch remota `research/sigma-pade-dimension-depth-20261104` do repositório `momentos`. Ambos dizem explicitamente que a síntese é algébrica/em papel e não anuncia novo build Lean nem prova de dominância all-order.

## Continuação source-first: characteristic ceiling e faces 4×4

- `NativeAllOrderCharacteristicCeiling.lean` reutiliza a recorrência original `canonicalCompletedNativeLogDerivativeMoment_real_recurrence` e a definição existente `nativeSourceSchurRemainder`. O teto `nativeSourceCharacteristicCeiling s n` depende somente dos momentos/coefs anteriores e da correção de acoplamento definida pelo Schur original.
- `nativeSourceSchurRemainder_eq_characteristic_gap` prova, para todo `s,n`, `R_{s,n}=(2n+s+1)(ceiling_{s,n}-c_{2n+s+1})`; `nativeSource_schur_eq_characteristic_recurrence` dá a equação isolada de C1; `nativeSource_schur_pos_iff_characteristic_ceiling` dá o iff, usando `c₀≥1/3` da fonte. Não há `PosDef`. A definição `sourceMomentSchur` usa a inversa total do Lean; quando o prefixo é `IsUnit`, ela coincide com o complemento de Schur usual. O resultado de sinal continua uma equivalência, não prova que o teto é satisfeito.
- As especializações confirmam a indexação central `c_(2n+1)` e deslocada `c_(2n+2)`. `nativeSourceEightOddDiscriminant_pos_iff_characteristic_ceiling` continua reutilizado como caso finito de ordem 4; não foi reprovado nem duplicado.
- `NativeAllOrderFiniteDiscriminantBridge.lean` prova, por expansão determinantária e pela identidade fonte `nativeSourceOddBoundaryCoefficient = 2*m`, as pontes `nativeSourceSevenEvenDiscriminant_eq_sixteen_hankelDet` e `nativeSourceEightOddDiscriminant_eq_sixteen_shifted_hankelDet`. O teorema source-first `nativeSourceSevenEvenDiscriminant_pos` então prova `nativeSourceCentral_hankelDet_four_pos`. No setor deslocado, `nativeSourceShifted_hankelDet_four_pos_iff_characteristic_ceiling` é apenas uma equivalência com a cota explícita de `c₈`; a cota/sinal ainda está aberta.
- Os dois módulos novos foram compilados individualmente com `lake env lean --root=... <arquivo>`, exit code 0 e sem warnings após remover os argumentos `simp` não utilizados. Seus módulos `...Audit.lean` também compilaram; `#print axioms` dos nove teoremas centrais mostrou somente `[propext, Classical.choice, Quot.sound]`.
- O `lake build --wfail CarrySelfAdjointOperator.NativeAllOrderCharacteristicCeiling` foi interrompido com `SIGINT` após cerca de 13 minutos, enquanto reconstruía vários certificados theta de ordem 12/14 e não tinha alcançado o módulo-alvo. Isso não é build verde nem erro matemático. A compilação focada via `lake env lean` dos dois módulos novos e das auditorias terminou com código 0. Não foi concluído build integral.
- Teste exato executado da branch Momentos `eeac8c13581e026df409886751a9368ff05d488d`: `verify_all_n_pencil_cofactor_toda.py` (parte racional) passou em 63 casos `n=0..6`, shifts `0..2`, incluindo prefixos singulares e momentos negativos. `verify_signed_tail_no_go.py` passou 18 casos exatos para `r=1..6`, shifts `0,1,3`. `exact_fourier_positive_hankel_countermodel.py` confirmou exatamente `D₃=-1274953/268240896000<0` para uma fonte Fourier positiva. Esses controles testam contraexemplos/instâncias finitas e não substituem as provas Lean gerais.
- As identidades division-free do pencil/cofator/energia theta já compiladas continuam válidas para prefixos singulares. A identidade Toda geral segue aberta (só o caso `n=1` está em Lean). Não foi provada dominância de massas Euler em `n≥3`, positividade do determinante deslocado 4×4, nem positividade universal das torres.
- Auditoria de lacunas nos módulos novos: nenhuma ocorrência de `sorry`, `admit` ou declaração `axiom`; nenhum momento novo foi definido e nenhum zero foi usado como entrada.
- Regressão exata local `test_allorder_exact_regressions.py`: 126 casos `Fraction`, seis sequências com pivôs positivos, negativos, singulares e indefinidos, dimensões `n=0..6`, shifts `s=0..2`; pencil/cofator em pontos racionais, vetor crítico, energia, ortogonalidade e Toda passaram. É `TESTADO_EXATO`, distinto das provas gerais Lean.
- Reprodução Lean: dentro do worktree isolado a compilação direta falha por falta dos `.olean` legados nesse worktree. A execução focada, a partir do checkout principal usando `--root` para o worktree, recompilou os dois módulos e os dois arquivos `#print axioms`: todos exit code 0. Nenhum arquivo versionado do checkout principal foi alterado. O build completo continua não verificado.

## Gate source-first de ordem 3 — continuação

- `NativeHankelPencilEulerOrderThree.lean` prova `nativeSourceEuler_even_remainder_three_pos` e `nativeSchurEuler_even_orderThree_mass_gate`. A prova usa `nativeSourceCentral_hankelDet_four_pos` (certificado fonte-first de ordem 14), `nativeSourceEuler_even_three_prefixDet_pos`, `nativeSourcePrefixDet_succ_eq_borderedScalar`, `nativeSourceBorderedScalar_eq` sob invertibilidade do prefixo 3×3 e o balanço Euler. Ela não supõe `PosDef` da matriz 4×4.
- O mesmo módulo prova `nativeSchurEuler_odd_orderThree_mass_gate_iff_characteristic_ceiling`: o gate ímpar em `n=3` é equivalente ao teto genérico `c₈ < nativeSourceCharacteristicCeiling 1 3`. A ponte finita anterior também relaciona `det(G_{1,4})` ao teto específico `nativeSourceEightCharacteristicCeiling`; nenhum desses tetos foi provado verdadeiro aqui.
- `NativeHankelPencilEulerOrderThreeAudit.lean` imprime para os três teoremas apenas `[propext, Classical.choice, Quot.sound]`. Os dois módulos foram compilados focadamente com exit code 0.
- Assim, a comparação de incrementos do setor par em `2→3` pode ser fechada a partir do novo resto positivo; a comparação ímpar continua exatamente reduzida a `R_{1,3}>0`. Isso não dá uma recorrência para ordens posteriores.
- Diagnóstico numérico exploratório, classificado exclusivamente como `TESTADO_NUMERICO`: o script reproduzível `probe_shifted_c8_ceiling_numeric.py` faz extração Cauchy/DFT da característica real-height `Xi(1/2+it)` com `mpmath`, usando `(N,r)=(128,1.5)` e `(256,2)`. Dá `c₈≈2.09976980814952875×10⁻¹⁹`, teto `≈2.09978821567271976×10⁻¹⁹` e margem `≈1.840752319100597×10⁻²⁴` em ambos os refinamentos. Não usa zeros; não é certificado intervalar nem prova Lean. O majorante absoluto já provado para `c₈`, `|c₈|≤1/(35·25⁷)≈4.681142857×10⁻¹²`, é cerca de 22 milhões de vezes maior que o próprio teto numérico, então esse majorante grosseiro não entrega a comparação.

## Regressões fonte reutilizadas — 2026-11-10

Compilação focada (`lake env lean --root=<worktree> <arquivo>`, executada a partir do checkout principal com a cache CSA) terminou com exit code 0 para:

- H6/K6 e limites theta: `CompletedNativeSixthOrderThetaPositivityAudit.lean`, `CompletedNativeShiftedHankelEighthGateAudit.lean`;
- fonte/calibração: `NativeSourceKernelCalibrationAudit.lean`;
- massas/resíduo Schur: `NativeSourceSchurThetaAudit.lean`;
- Green: `CompletedNativeTfvdGreenShiftedHankelFactorizationAudit.lean` e `GreenWronskianHankelBridge.lean`;
- Hankel e momentos característicos: `CompletedNativeTenthOrderHankelGateAudit.lean`, `CompletedNativeTenthOrderHankelMomentFormAudit.lean`;
- câmera/TFVD: `C2LiteralCameraAllOrderJetCrosswalkAudit.lean`, `CompletedNativeCameraTfvdGreenFrameDefectCrosswalkAudit.lean`.

Os arquivos `...Audit.lean` acima executam guardas/`#print axioms`; as declarações listadas dependem somente de `[propext, Classical.choice, Quot.sound]`. Essa execução confere os regressions focados solicitados; não equivale ao build integral de Lake, que continua interrompido antes do alvo por custo de reconstrução.

## Piso theta de ordem 16 e obstrução da caixa deslocada

### Categorias da evidência

- `PROVADO_LEAN`: `thetaBoxEighthCandidate_ge_theta16_floor_target` e `thetaBoxEighthCandidate_order16_floor_countermodel` provam aritmeticamente que a candidata racional já formalizada satisfaz o limite inferior proposto `7675700000/10^18`, todos os dados antigos do box, a recorrência logarítmica finita, positividade dos momentos e Gram brutas correspondentes, e ainda possui direção negativa para a forma de resposta ímpar.
- `TESTADO_EXATO`: a diferença candidata menos o limiar é exatamente `114697358544125403/5000000000000000000000000000 > 0` (≈`2.29394717088×10⁻¹¹`).
- `ABERTO`: provar e compilar `theta16_floor_sum_lower_target` a partir das 576 células e provar sua conexão com `completedNativeThetaTailMoment 16`. O arquivo fonte `ThetaSixteenthFloorCertificateData/Aggregator.lean` declara a soma local, mas a tentativa focada de compilá-lo nesta sessão foi interrompida por custo depois de cinco minutos (`SIGINT`, código 130); esse resultado não foi contado como verificação.
- `ABERTO`: o contraexemplo é uma sequência racional abstrata, não a fonte theta real. Ele demonstra somente que o limiar escalar de ordem 16, somado ao box antigo e às condições listadas, não basta para deduzir a positividade do response Hankel deslocado.

### Auditoria Lean

Os dois teoremas novos estão em `NativeThetaSixteenthFloorCountermodel.lean`; `NativeThetaSixteenthFloorCountermodelAudit.lean` executa `#print axioms`, que retorna somente `[propext, Classical.choice, Quot.sound]` para ambos. A compilação focada de cada arquivo terminou com exit code 0 usando Lean `v4.32.0` e as dependências pinadas existentes. Os novos arquivos não contêm `sorry`, `admit` ou declarações `axiom`.

### Escopo que não foi provado

O teorema `theta16_floor_sum_lower_target` não foi usado por esses resultados. Assim, não se afirma nesta atualização que o momento theta real de ordem 16 é pelo menos `7675700000/10^18`, nem que essa cota decorre do agregado no estado compilado da branch. Mesmo quando estabelecida, a cota candidata isolada não exclui a sequência racional com testemunha negativa. Ela também não prova nem refuta o sinal da fonte completada.
