# CHECKPOINT — ALL-ORDER PENCIL/COFACTOR

## Estado
Checkpoint atual: 3 — ponte pencil/energia/integral theta
Status: GREEN

Os checkpoints 0–3 estão concluídos. Para quaisquer `s n`, a integral theta cofactorial é exatamente `c₀ τ_{s,n} τ_{s,n+1}`. Também está compilada a equivalência **CONDICIONAL** de sinais sob `c₀>0` e `τ_{s,n}>0`; ela não fornece a positividade da integral. O teorema antigo `nativeThetaCofactorSign_iff_stieltjes` foi mantido como resultado existente e não duplicado.

## Git
Repositório: `/home/thlinux/carry-self-adjoint-operator`
Worktree de trabalho: `/home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110`
Branch: `agent/allorder-pencil-cofactor-euler-20261110`
Commit SHA: será registrado após o commit validado do checkpoint 3; checkpoint 2: `221c6f9d2144baa2f5fdcd4f1e5f4d89d4a072bc`.
Último commit: `research: record green critical-vector energy checkpoint`.

## Ambiente
Lean: `leanprover/lean4:v4.32.0`; `lean --version` confirma commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
Lake: `5.0.0-src+8c9756b`.
Dependências: manifest preservado; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, `geometry-of-numbers` `d7cc54f5c485320f1fada33118e9e6101488819a`, `NativeCarryC3Crosswalk` `150cfc7fb08da96bf8117f15869cc2b819d593c2`; nenhuma dependência foi atualizada.
Ambiente de build: `lake env lean --version` funciona. Para evitar recompilar dependências pinadas, `.lake/packages` nesta worktree usa a cache de pacotes já existente no checkout principal; os clones inicialmente obtidos foram preservados em `.lake/packages.initial-local` (fora do Git). Um `lake build CarrySelfAdjointOperator.NativeThetaCofactorMargin` foi interrompido em 9300/9844 tarefas por incluir dezenas de certificados de quadratura de alto grau; não houve erro reportado nesse build. A compilação isolada do módulo novo usou o `.olean` já existente da margem, cujo fonte não mudou desde o commit `28d57ad` de 15/10.

## Teoremas concluídos

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

## Teoremas ainda abertos

- Nome: identidade de Toda/Desnanot–Jacobi para uma sequência arbitrária.
- Enunciado: `τ_{s,n}τ_{s+2,n}−τ_{s+1,n}²=τ_{s,n+1}τ_{s+2,n−1}`, para `n≥1`.
- Obstáculo: a identidade de menores ainda não foi localizada/composta para as janelas de Hankel.
- Próxima tentativa: localizar o lema division-free de Desnanot–Jacobi em Mathlib e provar a identidade para sequência arbitrária, sem sinais.

## Auditoria lógica
Há sorry/admit?: nenhum introduzido nos arquivos novos.
Há axiomas novos?: não.
Foi assumida positividade?: não para as identidades algébricas inventariadas; os teoremas de Schur/Euler acima declaram suas hipóteses explicitamente.
Foram usados zeros como entrada?: não.
Há risco de circularidade?: sim, se `nativeThetaCofactorSign_iff_stieltjes` for usado para alegar prova do sinal cofactorial, ou se o balanço Euler for usado sem demonstrar a dominância das massas assinadas.

## Próxima ação exata
1. Formalizar Toda/Desnanot–Jacobi para uma sequência arbitrária e shifts `s,n` com `n≥1`.
2. Compor Toda com a ponte theta mantendo explícitas todas as condições de sinal.
3. Preservar como aberta a dominância de massas theta/Euler; nenhuma equivalência condicional prova essas desigualdades.
