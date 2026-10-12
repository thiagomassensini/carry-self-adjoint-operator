# Avanço, defeito de relógio e compressão — lote 2

Base: lote A–C, PR #70, commit `db1ac4805b76b59495f74927092c9fc2e7055872`.
Host/pins/dicionário de tipos: os mesmos do relatório do lote 1; nenhum repin.

## PASS_LEAN

`NativeLaguerreAdvanceMatrix.lean`:

* `advanceEntry`: matriz binomial exata `choose(r+s,r)/2^(r+s+1)`.
* `advanceEntry_symmetric`, `advanceEntry_nonneg`.
* `hasSum_advance_feature`, `tsum_advance_feature`: para quaisquer r,j naturais,
  a soma da linha contra a feature converge e é exatamente a feature em j+1.
  A prova reutiliza `hasSum_choose_mul_geometric_of_norm_lt_one` de Mathlib.
  Não é uma rearrumação informal de séries.

`NativeLaguerreClockDefect.lean`:

* `fullJacobiRow_eq_derivativeFormula`: recorrência algébrica universal da linha.
* `finite_clock_defect_entry`: ação da linha Jacobi truncada menos o relógio
  material; retém exatamente `1_(r=R)(R+1)f_(R+1)(j)`.
* `finite_clock_defect_seed`: caso R=0,j=0 igual a -2/3.
* `material_clock_commutator_entry`, `material_clock_does_not_commute`: matriz
  Cauchy e relógio material não comutam já em M=2.

`featureDerivativeFormula` é uma fórmula algébrica. Este lote não apresenta
um teorema `HasDerivAt` para a extensão real de j. `cutoffJacobiRow` é a ação
explícita da linha tridiagonal; não é uma declaração sobre um operador não limitado.

`NativeLaguerreFiniteCompression.lean`:

* `compression_square`, `compression_polynomial`, `compression_scaled_polynomial`:
  álgebra de compressão para uma matriz e uma projeção idempotente arbitrárias.
* `compressionLeakage_eq_gram`, `compressionLeakage_posSemidef`: além da
  idempotência, exigem explicitamente P e A hermitianas. Estas são condições
  estruturais da proposição geral; não se pressupõe que uma matriz física
  desconhecida as satisfaz.
* `inner_intervalMonomialLp`: realização integral dos monômios no MESMO
  `Lp ℂ 2 (volume : Measure unitInterval)` usado pela fonte física.
* `compression_R0_radial_moments`, `compression_R0_leakage`,
  `compression_R0_valve`, `compression_R0_naive_and_gap`: canário físico R=0
  certificado no Lp: A00=1/2, (A²)00=1/3, fuga=1/12, válvula q=1/2 igual a
  7/6, aproximação 9/8 e diferença racional 1/24.

## OPEN

`OPEN_LAGUERRE_LP_REALIZATION`: falta construir todos os polinômios Laguerre
como vetores Lp, provar os overlaps integrais e ligar a matriz binomial acima
ao multiplicador físico. O caso constante R=0 foi construído independentemente.

`OPEN_LAGUERRE_COMPLETENESS`: falta ortonormalidade integral e densidade da
família; nenhuma equivalência unitária ou sobrejetividade é declarada.

`OPEN_GEOMETRIC_LOG_DOMAIN`: falta transportar o domínio maximal de
multiplicação por log u. Nenhum relógio geométrico limitado foi criado.
`OPEN_FUNCTIONAL_A_EXP_J`: falta cálculo funcional/conjugação no domínio correto.

`OPEN_FULL_LAGUERRE_COMPRESSION`: a álgebra universal de compressão e o canário
R=0 estão certificados. A aplicação à torre Laguerre infinita e a fórmula
integral universal de (A²)_rs continuam abertas. Definir essa fórmula racional
não seria provar sua igualdade com o operador físico.

`OPEN_FIXED_M_OPERATOR_TAIL_BOUND`: convergência entrada a entrada foi provada
no lote 1. Ainda falta uma prova Lean da cota π(k+1)θ² na norma de coeficientes.
Os limites cofinal/jet permanecem condicionais a amplitude, quociente e ordem.

## Validação

Cada módulo foi executado por `lake env lean`; cada Audit imprime os axiomas
de todas as declarações públicas e foi construído com `lake build --wfail`.
Apenas `propext`, `Classical.choice`, `Quot.sound` ou subconjuntos.
O build completo passou com exit 0 (10112 jobs). Commits e estado do CI constam no PR e no relatório all-order.

Os 1613 canários do ap-29 foram reexecutados no llm, exit 0. As verificações
universais integrais da matriz que ainda não receberam prova Lean mantêm status
`PASS_NUMERIC_ONLY`. Amplitudes/quocientes são sintéticos. A fonte assinada,
seus cruzamentos e a costura material–radial não são consequências de PSD da fuga.

PR incremental baseado no PR #70; sem merge automático.
