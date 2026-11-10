# CHECKPOINT — ALL-ORDER PENCIL/COFACTOR

## Estado
Checkpoint atual: 1 — polinômio do pencil para todo `n`
Status: PARTIAL

O inventário foi concluído e commitado. No checkpoint 1, os polinômios do pencil e da direção de cofatores foram definidos; o caso `n = 0` compila. A identidade para dimensões positivas segue aberta.

## Git
Repositório: `/home/thlinux/carry-self-adjoint-operator`
Worktree de trabalho: `/home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110`
Branch: `agent/allorder-pencil-cofactor-euler-20261110`
Commit SHA: `6954b71` (base da branch; o commit parcial do checkpoint 1 será registrado logo após a auditoria)
Último commit: `research: initialize all-order pencil/cofactor formalization checkpoint`

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

- Nome completo: `CarrySelfAdjointOperator.nativeSourceHankelPencil`, `nativeSourceHankelPencilPolynomial`, `nativeSourceCofactorPolynomial`, `nativeSourceHankelPencilPolynomial_zero`.
- Arquivo: [NativeHankelPencilCofactor.lean](../../CarrySelfAdjointOperator/NativeHankelPencilCofactor.lean), linhas 18–31.
- Hipóteses: definições para quaisquer `s n`; o lema provado cobre `n = 0` e não assume positividade.
- Comando de compilação: `lake env lean /home/thlinux/worktrees/agent-allorder-pencil-cofactor-20261110/CarrySelfAdjointOperator/NativeHankelPencilCofactor.lean`, executado a partir de `/home/thlinux/carry-self-adjoint-operator`.
- Resultado: exit code 0, sem warnings após remover um argumento `simp` não usado.

## Teoremas ainda abertos

- Nome: identidade do pencil por coefatores `P_{s,n}=C_{s,n}`.
- Enunciado: formalizar em `ℝ[X]`, para quaisquer `s n`, o determinante do pencil dos momentos canônicos igual ao polinômio da direção de cofatores, inclusive com prefixo singular.
- Obstáculo: falta ligar os menores da matriz bordeada aos componentes `-adj(G)b` sem pressupor invertibilidade; o determinante do pencil e a expansão de Laplace requerem essa identidade de cofatores.
- Próxima tentativa: formalizar primeiro o determinante da matriz bordeada por expansão da última linha e a fórmula de Cramer `Matrix.cramer_eq_adjugate_mulVec`; em paralelo usar transformação triangular das colunas para obter `det(XG-K)`.

## Auditoria lógica
Há sorry/admit?: nenhum introduzido nos arquivos novos.
Há axiomas novos?: não.
Foi assumida positividade?: não para as identidades algébricas inventariadas; os teoremas de Schur/Euler acima declaram suas hipóteses explicitamente.
Foram usados zeros como entrada?: não.
Há risco de circularidade?: sim, se `nativeThetaCofactorSign_iff_stieltjes` for usado para alegar prova do sinal cofactorial, ou se o balanço Euler for usado sem demonstrar a dominância das massas assinadas.

## Próxima ação exata
1. Provar a fórmula de determinante bordeado em termos de `nativeSourceCofactorVector`, inclusive para prefixos singulares.
2. Provar a transformação triangular do bordered matrix para o pencil `XG-K`.
3. Compilar o módulo isoladamente, auditar lacunas e registrar o resultado antes de seguir.
