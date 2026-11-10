# CHECKPOINT — ALL-ORDER PENCIL/COFACTOR

## Estado
Checkpoint atual: prioridade 3 — gates Euler de ordem 3 após as pontes fonte/Hankel 4×4
Status: PARTIAL (o gate par `n=3` foi provado; o ímpar reduz ao teto de `c₈`, ainda aberto; Toda geral e gates all-order permanecem abertos)

Os checkpoints 0–3 estão GREEN. O checkpoint 4 permanece PARTIAL: compila o caso base de Toda `n=1`, mas o passo division-free geral está aberto. O checkpoint 5 está GREEN como teorema **CONDICIONAL**: as duas famílias de dominância Euler/theta implicam positividade das torres nativas `s=0,1` em toda dimensão; `c₀>0` é obtido do teorema CSA `completedNativeRealEvenCharacteristicCoefficient_zero_ge_third`. Um lema por paridade estende o resultado a todo shift por submatrizes principais. As Missões A e B estão GREEN; os dois gates de massa em `n=2` vieram de certificados fonte-first. A auditoria inicial da Missão C reduziu os incrementos `2→3` a `R_{0,3}>0` e `R_{1,3}>0`; desde então, `R_{0,3}>0` e o gate par de massa em `n=3` foram provados pela face fonte de ordem 14. `R_{1,3}>0`, equivalente ao teto de `c₈`, continua aberto. Isso não estabelece positividade all-order.

## Atualização auditada — 2026-11-10

### Teoremas desta etapa (`PROVADO_LEAN`)

- `CarrySelfAdjointOperator.nativeSourceSchurRemainder_eq_characteristic_gap`, `nativeSource_schur_eq_characteristic_recurrence`, `nativeSource_schur_pos_iff_characteristic_ceiling`, `nativeSourceCentralSchur_pos_iff_characteristic_ceiling`, `nativeSourceShiftedSchur_pos_iff_characteristic_ceiling` em [NativeAllOrderCharacteristicCeiling.lean](../../CarrySelfAdjointOperator/NativeAllOrderCharacteristicCeiling.lean). Valem para todo `s,n`, sem `PosDef` ou `IsUnit`; a expressão `sourceMomentSchur` usa a inversa total de Lean, e sob `IsUnit` é o complemento de Schur usual. O teto é explícito e a equivalência usa o resultado fonte-first `c₀≥1/3`; não prova que a cota é satisfeita.
- `CarrySelfAdjointOperator.nativeSourceSevenEvenDiscriminant_eq_sixteen_hankelDet`, `nativeSourceEightOddDiscriminant_eq_sixteen_shifted_hankelDet`, `nativeSourceCentral_hankelDet_four_pos`, `nativeSourceShifted_hankelDet_four_pos_iff_characteristic_ceiling` em [NativeAllOrderFiniteDiscriminantBridge.lean](../../CarrySelfAdjointOperator/NativeAllOrderFiniteDiscriminantBridge.lean). A central 4×4 é positiva pelo certificado source-first de ordem 14. A deslocada 4×4 tem sinal equivalente à cota ainda aberta de `c₈`.
- `CarrySelfAdjointOperator.nativeSourceEuler_even_remainder_three_pos`, `nativeSchurEuler_even_orderThree_mass_gate` e `nativeSchurEuler_odd_orderThree_mass_gate_iff_characteristic_ceiling` em [NativeHankelPencilEulerOrderThree.lean](../../CarrySelfAdjointOperator/NativeHankelPencilEulerOrderThree.lean). O gate par de massa em `n=3` decorre do determinante central fonte-first de ordem 14, do prefixo 3×3 invertível e do balanço Euler. Não se assume `PosDef(G₀,₄)`. O gate ímpar de `n=3` é equivalente a `c₈ < nativeSourceCharacteristicCeiling 1 3`; não foi provado.

### Compilação e auditoria

- Compilação direta do módulo characteristic ceiling: `lake env lean --root=/home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110 /home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110/CarrySelfAdjointOperator/NativeAllOrderCharacteristicCeiling.lean` — exit code 0.
- Compilação direta da ponte 4×4: comando análogo para `NativeAllOrderFiniteDiscriminantBridge.lean` — exit code 0, sem warnings.
- `NativeAllOrderCharacteristicCeilingAudit.lean` e `NativeAllOrderFiniteDiscriminantBridgeAudit.lean` compilaram. `#print axioms` em todos os nove teoremas listados imprimiu somente `[propext, Classical.choice, Quot.sound]`.
- `NativeHankelPencilEulerOrderThree.lean` e `NativeHankelPencilEulerOrderThreeAudit.lean` compilaram; os três teoremas novos imprimem somente `[propext, Classical.choice, Quot.sound]`.
- `lake build --wfail CarrySelfAdjointOperator.NativeAllOrderCharacteristicCeiling` foi interrompido por `SIGINT` após cerca de 13 minutos, enquanto reconstruía certificados theta transitivos de ordens 12 e 14 e antes de alcançar o módulo-alvo. Não conta como build verde; a compilação Lean focada acima terminou. O build completo não foi executado.
- Testes exatos de pesquisa da branch Momentos SHA `eeac8c13581e026df409886751a9368ff05d488d`: 63 casos racionais do pencil/cofator/energia/Toda para dimensões 0–6, shifts 0–2 passaram; o no-go da cabeça finita passou em 18 casos `Fraction`; o controle Fourier positivo confirmou o menor negativo exato `-1274953/268240896000`. São `TESTADO_EXATO`, não provas all-order.
- Regressão exata local `test_allorder_exact_regressions.py`: 126 casos `Fraction` (seis sequências, dimensões 0–6, shifts 0–2) passaram para pencil/cofator, vetor crítico, energia, ortogonalidade e Toda, incluindo pivôs negativos e singulares. São `TESTADO_EXATO`, não substituem os teoremas Lean.
- `probe_shifted_c8_ceiling_numeric.py` repetiu a extração Cauchy/DFT em duas resoluções sem zeros: o teto shifted ficou `1.8407523191×10⁻²⁴` acima de `c₈`. É somente `TESTADO_NUMERICO`, sem aritmética intervalar; o majorante theta atual de `|c₈|` não certifica essa margem.
- Reexecução focada: compilação dentro do worktree falha por ausência dos `.olean` legados naquele cache isolado; a compilação repetida a partir do checkout principal, com `--root` no worktree, terminou com exit code 0 para os três módulos novos desta continuação e seus três arquivos de `#print axioms`. O checkout principal não teve alterações versionadas.

### Obrigação ainda aberta

- A identidade Toda para sequência arbitrária segue compilada apenas para `n=1`; sua versão division-free para todo `n≥1` não foi concluída.
- O gate par de massa em `n=3` agora está provado por `nativeSchurEuler_even_orderThree_mass_gate`. O menor gate de sinal ainda aberto é o ímpar em `n=3`, equivalente a `c₈ < nativeSourceCharacteristicCeiling 1 3`; não há certificado para ele nem para as ordens seguintes.
- Não há positividade universal, representação Gram completada, ou uso de zeros como entrada.

## Git
Repositório: `/home/thlinux/carry-self-adjoint-operator`
Worktree de trabalho: `/home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110`
Branch: `agent/allorder-pencil-cofactor-euler-20261110`
Commit SHA do último checkpoint matemático: `80e1f6208065237f1fcaa9c83bd0db71981d8cd4`.
Commits desta continuação: Missão A `48365a0e3cb509d20ca7353a07cb9ec49e694878`; Missão B `2c6892866e586cd703fe37d328d46907ed282782`; auditoria de incrementos `c2adb35d10082f70f280d661590c4ac96a5662fc`; teto/ponte 4×4 `0974fe6dde468da822a35b6489b3d8135cd6618d`; gate par de ordem 3 `939aa3aacb8154a740c81d3e3648fe3b3473db9f`; sondagem numérica reprodutível `80e1f6208065237f1fcaa9c83bd0db71981d8cd4`.
Último commit matemático/auditado: `research: record order-three gate and numeric c8 probe` (`80e1f6208065237f1fcaa9c83bd0db71981d8cd4`).

## Ambiente
Lean: `leanprover/lean4:v4.32.0`; `lean --version` confirma commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
Lake: `5.0.0-src+8c9756b`.
Dependências: manifest preservado; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, `geometry-of-numbers` `d7cc54f5c485320f1fada33118e9e6101488819a`, `NativeCarryC3Crosswalk` `150cfc7fb08da96bf8117f15869cc2b819d593c2`; nenhuma dependência foi atualizada.
Ambiente de build: `lake env lean --version` funciona. Para evitar recompilar dependências pinadas, `.lake/packages` nesta worktree usa a cache de pacotes já existente no checkout principal; os clones inicialmente obtidos foram preservados em `.lake/packages.initial-local` (fora do Git). Um `lake build CarrySelfAdjointOperator.NativeThetaCofactorMargin` foi interrompido em 9300/9844 tarefas por incluir dezenas de certificados de quadratura de alto grau; não houve erro reportado nesse build. A compilação isolada do módulo novo usou o `.olean` já existente da margem, cujo fonte não mudou desde o commit `28d57ad` de 15/10.

## Teoremas concluídos

- Nome completo: `CarrySelfAdjointOperator.nativeSource_even_odd_towers_posDef_of_euler_mass_gates`, `CarrySelfAdjointOperator.nativeSource_all_shift_windows_posDef_of_euler_mass_gates`.
- Arquivo: [NativeHankelPencilConditionalPositivity.lean](../../CarrySelfAdjointOperator/NativeHankelPencilConditionalPositivity.lean).
- Hipóteses: continuam **CONDICIONAIS** às duas famílias de dominância das massas. A hipótese externa `0 < c₀` foi retirada; os teoremas agora obtêm esse sinal de `completedNativeRealEvenCharacteristicCoefficient_zero_ge_third`.
- Comando de compilação: `lake env lean --root=/home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110 /home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110/CarrySelfAdjointOperator/NativeHankelPencilConditionalPositivity.lean`, executado a partir de `/home/thlinux/carry-self-adjoint-operator`.
- Resultado: exit code 0. `#print axioms` para ambos os teoremas e o lema do coeficiente constante imprime somente `[propext, Classical.choice, Quot.sound]`; ver [NativeHankelPencilConditionalPositivityAudit.lean](../../CarrySelfAdjointOperator/NativeHankelPencilConditionalPositivityAudit.lean).

- Nome completo: `CarrySelfAdjointOperator.nativeSourceFiveEvenDiscriminant_eq_eight_hankelDet`, `nativeSourceSixOddDiscriminant_eq_eight_shifted_hankelDet`, `nativeSchurEuler_even_orderTwo_mass_balance`, `nativeSchurEuler_odd_orderTwo_mass_balance`, `nativeSchurEuler_even_orderTwo_mass_gate`, `nativeSchurEuler_odd_orderTwo_mass_gate`.
- Arquivo: [NativeHankelPencilEulerOrderTwo.lean](../../CarrySelfAdjointOperator/NativeHankelPencilEulerOrderTwo.lean).
- Hipóteses: nenhuma nos teoremas finais. Os dois prefixos de dimensão 2 tornam-se `IsUnit` pelos discriminantes fonte-first existentes; os determinantes 3×3 positivos vêm dos certificados de fronteira fonte-first de ordem 10 e 12. Não há hipótese `PosDef` de matriz 3×3.
- Comando de compilação: `lake env lean --root=/home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110 /home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110/CarrySelfAdjointOperator/NativeHankelPencilEulerOrderTwo.lean`, executado a partir de `/home/thlinux/carry-self-adjoint-operator`.
- Resultado: exit code 0. `#print axioms` nas identidades, nos gates, nos balanços e nos dois certificados fonte-first imprimiu somente `[propext, Classical.choice, Quot.sound]`; ver [NativeHankelPencilEulerOrderTwoAudit.lean](../../CarrySelfAdjointOperator/NativeHankelPencilEulerOrderTwoAudit.lean).

- Nome completo: `CarrySelfAdjointOperator.nativeSchurEulerPolynomial_integral_eq_green`, `nativeSchurEuler_even_massDeficit_eq_neg_remainder`, `nativeSchurEuler_odd_massDeficit_eq_neg_remainder`, `nativeSchurEuler_even_massDeficit_increment_two_to_three`, `nativeSchurEuler_odd_massDeficit_increment_two_to_three`, `nativeSchurEuler_even_increment_gate_iff_orderThree_remainder_pos`, `nativeSchurEuler_odd_increment_gate_iff_orderThree_remainder_pos`.
- Arquivo: [NativeHankelPencilEulerMassRecurrenceAudit.lean](../../CarrySelfAdjointOperator/NativeHankelPencilEulerMassRecurrenceAudit.lean).
- Hipóteses: as identidades de déficit valem com a hipótese `IsUnit` exigida pelos balanços Euler; no passo `2 → 3`, a invertibilidade dos prefixos de dimensão 3 é obtida dos determinantes positivos provados no checkpoint anterior. Não se assume PosDef 4×4 nem a positividade do novo resto.
- Comando de compilação: `lake env lean --root=/home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110 /home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110/CarrySelfAdjointOperator/NativeHankelPencilEulerMassRecurrenceAudit.lean`, executado a partir de `/home/thlinux/carry-self-adjoint-operator`.
- Resultado: exit code 0. `#print axioms` em todas as identidades novas imprime apenas `[propext, Classical.choice, Quot.sound]`.

- Nome completo: `CarrySelfAdjointOperator.sourceMomentMatrix`, `sourceMomentCoupling`, `sourceMomentSchur`.
- Arquivo: [NativeSourceAllOrderSchur.lean](../../CarrySelfAdjointOperator/NativeSourceAllOrderSchur.lean), linhas 13–22.
- Hipóteses: as duas primeiras definições aceitam sequência real arbitrária `m` e índices `s n`; `sourceMomentSchur` também não tem hipótese, mas usa a inversa da matriz na própria definição.
- Comando de compilação: não executado neste checkpoint; as declarações foram inspecionadas no fonte original.
- Resultado: inventário confirmado.

- Nome completo: `CarrySelfAdjointOperator.nativeSourcePrefixDet`, `nativeSourceCofactorVector`, `nativeSourceCofactorThetaPolynomial`, `nativeSourceBorderedScalar`.
- Arquivo: [NativeThetaCofactorMargin.lean](../../CarrySelfAdjointOperator/NativeThetaCofactorMargin.lean), linhas 18–28.
- Hipóteses: definições para todo `s n`; o vetor usa adjugata e determinante, sem inversa.
- Comando de compilação: não executado neste checkpoint.
- Resultado: inventário confirmado.

- Nome completo: `CarrySelfAdjointOperator.nativeSourceCofactorThetaPolynomial_integral_bordered`.
- Arquivo: [NativeThetaCofactorMargin.lean](../../CarrySelfAdjointOperator/NativeThetaCofactorMargin.lean), linha 99.
- Hipóteses: nenhuma; válido para todo `s n`, inclusive prefixos singulares.
- Comando de compilação: não executado neste checkpoint.
- Resultado: fornece a integral como `c₀ * nativeSourcePrefixDet * nativeSourceBorderedScalar`.

- Nome completo: `CarrySelfAdjointOperator.sourceMomentMatrix_succ_posDef_iff`.
- Arquivo: [NativeSourceAllOrderSchur.lean](../../CarrySelfAdjointOperator/NativeSourceAllOrderSchur.lean), linha 96.
- Hipóteses: sequência `m`, shift `s`, dimensão `n`, e `(sourceMomentMatrix m s n).PosDef`; conclui equivalência entre positividade definida da matriz seguinte e positividade do pivô Schur.
- Comando de compilação: não executado neste checkpoint.
- Resultado: passo de Schur condicional existente.

- Nome completo: `CarrySelfAdjointOperator.sourceMomentMatrix_all_posDef_iff_schur`.
- Arquivo: [NativeSourceAllOrderSchur.lean](../../CarrySelfAdjointOperator/NativeSourceAllOrderSchur.lean), linha 128.
- Hipóteses: sequência `m` e shift `s` arbitrários, sem hipótese adicional; caracteriza `∀ n, PosDef` por `∀ n, 0 < sourceMomentSchur`.
- Comando de compilação: não executado neste checkpoint.
- Resultado: critério all-order, não prova os sinais do lado direito para a fonte nativa.

- Nome completo: `CarrySelfAdjointOperator.nativeThetaCofactorSign_iff_stieltjes`.
- Arquivo: [NativeThetaCofactorSignGate.lean](../../CarrySelfAdjointOperator/NativeThetaCofactorSignGate.lean), linha 31.
- Hipóteses: nenhuma; equivalência entre o sinal estrito de todas as integrais cofactor theta nas torres `s = 0, 1` e `CanonicalCompletedNativeStieltjesPositivity`.
- Comando de compilação: não executado neste checkpoint.
- Resultado: equivalência lógica existente; não fornece por si só o sinal.

- Nome completo: `CarrySelfAdjointOperator.nativeSchurEuler_even_balance`.
- Arquivo: [NativeSchurEulerBalance.lean](../../CarrySelfAdjointOperator/NativeSchurEulerBalance.lean), linha 162.
- Hipóteses: `n` e `IsUnit (sourceMomentMatrix m 0 n)` para os momentos canônicos `m`; identidade entre o resto Schur escalado e a integral Euler assinada.
- Comando de compilação: não executado neste checkpoint.
- Resultado: balanço condicional existente; não assume o sinal da integral.

- Nome completo: `CarrySelfAdjointOperator.nativeSchurEuler_odd_balance`.
- Arquivo: [NativeSchurEulerBalance.lean](../../CarrySelfAdjointOperator/NativeSchurEulerBalance.lean), linha 141.
- Hipóteses: `n` e `IsUnit (sourceMomentMatrix m 1 n)`; além da integral Euler assinada, o lado direito contém `2*c₀*(nativeSchurCriticalReadout 1 n)^2`.
- Comando de compilação: não executado neste checkpoint.
- Resultado: balanço condicional existente com quadrado não negativo explícito.

- Nome completo: `CarrySelfAdjointOperator.nativeSchurEuler_odd_pos_iff_mass_balance`.
- Arquivo: [NativeSchurEulerBalance.lean](../../CarrySelfAdjointOperator/NativeSchurEulerBalance.lean), linha 210.
- Hipóteses: `n` e invertibilidade do prefixo `sourceMomentMatrix m 1 n`; caracteriza positividade do resto Schur pela dominância da massa theta positiva mais o quadrado sobre a massa theta negativa.
- Comando de compilação: não executado neste checkpoint.
- Resultado: equivalência condicional; a dominância não é provada.

- Nome completo: `CarrySelfAdjointOperator.nativeSourceHankelPencil`, `nativeSourceHankelPencilPolynomial`, `nativeSourceCofactorPolynomial`, `lastRowZeroExtension_adjugate_lastColumn`, `lastRowZeroExtension_adjugate_last`, `nativeSourceAugmentedZeroMatrix_adjugate_lastColumn`, `nativeSourceAugmentedZeroPolynomialMatrix_adjugate_lastColumn`, `nativeSourceBorderedPolynomialMatrix_det`, `sourceHankelColumnDifferenceMatrix_det`, `nativeSourceBordered_mul_columnDifference_minor`, `nativeSourceHankelPencilPolynomial_eq_cofactor`, `nativeSourceHankelPencilPolynomial_zero`.
- Arquivo: [NativeHankelPencilCofactor.lean](../../CarrySelfAdjointOperator/NativeHankelPencilCofactor.lean), linhas 18–31.
- Hipóteses: definições e teoremas para quaisquer `s n`; o teorema principal vale também para `n = 0` e prefixos singulares. Não assume positividade nem usa inversa.
- Comando de compilação: `lake env lean /home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110/CarrySelfAdjointOperator/NativeHankelPencilCofactor.lean`, executado a partir de `/home/thlinux/carry-self-adjoint-operator`.
- Resultado: exit code 0. Lean imprimiu uma sugestão de normalização `ring_nf`; não houve erro de elaboração e nenhuma declaração ficou sem prova.

- Nome completo: `CarrySelfAdjointOperator.nativeSourceHankelBorderedMatrix`, `nativeSourceHankelBorderedMatrix_eq`, `nativeSourceHankelBorderedMatrix_lastRow`, `nativeSourceHankelBorderedMatrix_det_eq_adjugateDot`, `nativeSourcePrefixDet_succ_eq_borderedScalar`, `nativeSourceHankelCriticalVector_mul`, `nativeSourceHankelCriticalVector_energy`.
- Arquivo: [NativeHankelPencilCofactor.lean](../../CarrySelfAdjointOperator/NativeHankelPencilCofactor.lean), após a identidade do pencil.
- Hipóteses: quaisquer `s n`; sem `IsUnit`, `PosDef`, hipótese de sinal ou inversa. `nativeSourcePrefixDet_succ_eq_borderedScalar` identifica o escalar bordeado existente com o próximo determinante; o vetor produto tem as coordenadas `Fin.snoc (fun _ => 0) τ_{s,n+1}`.
- Comando de compilação: `lake env lean /home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110/CarrySelfAdjointOperator/NativeHankelPencilCofactor.lean`, executado a partir de `/home/thlinux/carry-self-adjoint-operator`.
- Resultado: exit code 0; nenhuma lacuna no módulo. Lean imprimiu uma sugestão informativa `ring_nf` originada por um passo `ring`.

- Nome completo: `CarrySelfAdjointOperator.nativeSourceCofactorThetaPolynomial_integral_eq_prefixDet_mul_succ`, `nativeSourceCofactorThetaPolynomial_integral_pos_iff_nextPrefixDet_pos`.
- Arquivo: [NativeHankelPencilThetaBridge.lean](../../CarrySelfAdjointOperator/NativeHankelPencilThetaBridge.lean).
- Hipóteses: a identidade integrada vale para todo `s n` sem hipótese de sinal; a equivalência é **CONDICIONAL** a `0<c₀` e `0<τ_{s,n}`.
- Comando de compilação: `lake env lean --root=/home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110 /home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110/CarrySelfAdjointOperator/NativeHankelPencilThetaBridge.lean`, executado a partir de `/home/thlinux/carry-self-adjoint-operator`.
- Resultado: exit code 0, sem warnings ou lacunas.

- Nome completo: `CarrySelfAdjointOperator.nativeSchurEuler_even_pos_iff_mass_balance`.
- Arquivo: [NativeHankelPencilConditionalPositivity.lean](../../CarrySelfAdjointOperator/NativeHankelPencilConditionalPositivity.lean).
- Hipóteses: **CONDICIONAL** a `IsUnit (sourceMomentMatrix m 0 n)`, necessária pelo balanço Euler par existente. Caracteriza a positividade do resto par pela dominância da massa positiva sobre a negativa para o polinômio Euler par.
- Comando de compilação: o mesmo comando focado de `NativeHankelPencilConditionalPositivity.lean` acima.
- Resultado: exit code 0, sem lacunas.

- Nome completo: `CarrySelfAdjointOperator.nativeSource_all_shift_windows_posDef_of_twoTowers`, `nativeSource_all_shift_windows_posDef_of_euler_mass_gates`.
- Arquivo: [NativeHankelPencilConditionalPositivity.lean](../../CarrySelfAdjointOperator/NativeHankelPencilConditionalPositivity.lean).
- Hipóteses: o primeiro teorema assume PosDef das torres `s=0,1` em toda dimensão; o segundo assume **CONDICIONALMENTE** `c₀>0` e os dois gates de massa explícitos, e conclui PosDef para todo shift `s` e dimensão `n`.
- Comando de compilação: o mesmo comando focado de `NativeHankelPencilConditionalPositivity.lean` acima.
- Resultado: exit code 0, sem warnings ou lacunas.

- Nome completo: `CarrySelfAdjointOperator.arbitraryHankelWindowDet`, `arbitraryHankelToda_one`.
- Arquivo: [NativeHankelPencilToda.lean](../../CarrySelfAdjointOperator/NativeHankelPencilToda.lean).
- Hipóteses: `arbitraryHankelToda_one` vale para toda sequência `m : ℕ → ℝ` e todo shift `s`; é apenas o caso `n=1`, não o passo all-order.
- Comando de compilação: `lake env lean --root=/home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110 /home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110/CarrySelfAdjointOperator/NativeHankelPencilToda.lean`, executado a partir de `/home/thlinux/carry-self-adjoint-operator`.
- Resultado: exit code 0; Lean imprimiu uma sugestão informativa `ring_nf`. Nenhuma lacuna foi usada.

- Nome completo: `CarrySelfAdjointOperator.nativeSource_even_odd_towers_posDef_of_euler_mass_gates`.
- Arquivo: [NativeHankelPencilConditionalPositivity.lean](../../CarrySelfAdjointOperator/NativeHankelPencilConditionalPositivity.lean).
- Hipóteses: **CONDICIONAL** a `0<c₀`, `M⁻_{0,n}<M⁺_{0,n}` e `M⁻_{1,n}<2c₀T_n²+M⁺_{1,n}` para todo `n`. Conclui PosDef das duas torres de origem para todo `n`; não conclui as hipóteses de massa.
- Comando de compilação: `lake env lean --root=/home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110 /home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110/CarrySelfAdjointOperator/NativeHankelPencilConditionalPositivity.lean`, executado a partir de `/home/thlinux/carry-self-adjoint-operator`.
- Resultado: exit code 0, sem warnings ou lacunas.

## Teoremas ainda abertos

- Nome: próximo passo Euler `n=3`, depois dos gates `n=2`.
- Enunciado: provar `M⁻_{0,3}<M⁺_{0,3}` e `M⁻_{1,3}<2c₀T₃²+M⁺_{1,3}`.
- Primeira comparação de incrementos sem prova, em termos exatos: no setor par, `(M⁻_{0,3}-M⁻_{0,2})-(M⁺_{0,3}-M⁺_{0,2}) < 10 R_{0,2}`; no ímpar, `(M⁻_{1,3}-M⁻_{1,2})-(M⁺_{1,3}-M⁺_{1,2})-2c₀(T₃²-T₂²) < 12 R_{1,2}`. Lean prova que cada comparação é equivalente, respetivamente, a `0<R_{0,3}` ou `0<R_{1,3}`. Logo a identidade de incremento não fecha o próximo sinal.
- Próxima tentativa: procurar um novo controle de fonte que prove o resto de ordem 3; não inferir o sinal apenas dos gates de ordem 2 nem dos incrementos assinados.

- Nome: gates Euler/theta para `n≥3`.
- Enunciado: provar as duas dominâncias de massas em todas as dimensões.
- Obstáculo: os certificados fonte-first identificados nesta etapa fecham somente os determinantes de dimensão 3 (passo Euler `n=2`); não há comparação all-order das partes positiva e negativa.
- Próxima tentativa: procurar uma desigualdade de transporte entre ordens consecutivas sem descartar a massa negativa.

- Nome: identidade de Toda/Desnanot–Jacobi geral.
- Enunciado: `τ_{s,n}τ_{s+2,n}−τ_{s+1,n}²=τ_{s,n+1}τ_{s+2,n−1}`, para todo `m : ℕ → ℝ`, `s` e `n≥1`.
- Obstáculo: Mathlib não contém um lema geral correspondente nos módulos pesquisados; `Matrix.det_fromBlocks₁₁` e `det_fromBlocks₂₂` em `Mathlib/LinearAlgebra/Matrix/SchurComplement.lean` requerem `[Invertible A]`/`[Invertible D]`. Usá-los exigiria hipótese adicional e não satisfaria a identidade division-free.
- Próxima tentativa: provar o lema genérico de Desnanot–Jacobi diretamente a partir da multilinearidade/expansão de determinantes, sem assumir que o bloco central é invertível; então especializar os menores à sequência Hankel.

- Nome: desigualdades de dominância das massas Euler/theta.
- Enunciado: provar para todo `n` `M⁺_{0,n}>M⁻_{0,n}` e `M⁺_{1,n}+2c₀T_n²>M⁻_{1,n}` diretamente da fonte completada.
- Obstáculo: `nativeSchurThetaPolynomial_odd_negativeMass_pos` prova massa negativa estritamente positiva em toda ordem ímpar. `nativeThetaOddPrincipal_not_pointwise_nonneg` exclui uma rota de positividade pontual para aquela densidade. A transferência Green mantém os traços centrais explicitamente e, mesmo após seu cancelamento para os polinômios Schur, `nativeSchurThetaGreenPolynomial_even_coeff_top_neg`/`nativeSchurThetaGreenPolynomial_first_even_negative` exibem sinal negativo na densidade transportada. Nenhum desses fatos controla a diferença das integrais.
- Próxima tentativa: buscar cancelamento ou dominância integrada quantitativa na fonte original, incluindo termos arquimedianos/de fronteira; não descartar a massa negativa nem assumir Stieltjes/Gram positivo.

## Auditoria lógica
Há sorry/admit?: nenhum introduzido nos arquivos novos.
Há axiomas novos?: não.
Foi assumida positividade?: não para as identidades algébricas inventariadas; os teoremas de Schur/Euler acima declaram suas hipóteses explicitamente.
Foram usados zeros como entrada?: não.
Há risco de circularidade?: sim, se `nativeThetaCofactorSign_iff_stieltjes` for usado para alegar prova do sinal cofactorial, ou se o balanço Euler for usado sem demonstrar a dominância das massas assinadas.

## Próxima ação exata
1. Provar ou refutar por estimativa fonte-first `c₈ < nativeSourceCharacteristicCeiling 1 3`, equivalente ao gate ímpar de massa em `n=3`.
2. Após `n=3`, procurar um controle quantitativo independente para os gates positivos/negativos nas ordens subsequentes; não extrapolar pelo balanço assinado.
3. Manter a positividade all-order condicional aos gates restantes.
4. Tratar a identidade Toda geral em frente separada.
