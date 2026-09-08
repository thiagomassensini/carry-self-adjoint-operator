# Newton jets, coordenada projetiva e Green vertical

## Resultado desta rodada

Para a profundidade vertical `k` e a ordem de jet `r`, a família

$$
E_r^{(q)}(k)=\binom{k}{r}q^k
$$

tem série geradora formal exatamente

$$
\operatorname{mk}(E_r^{(q)})=Y_q^r(1+Y_q),
\qquad Y_q=\frac{qX}{1-qX}.
$$

`Y_q` é `PowerSeries.rescale q ProjectiveDepth.coordinate`. Não é uma
coordenada alternativa ao módulo `ProjectiveDepthEquivalence`: usa a mesma
coordenada depois da dilatação `X ↦ qX`. A identidade sem divisão
`(1 - C q * X) * weightedCoordinate q = C q * X` vale sobre qualquer anel
comutativo, inclusive para `q = 0`. As séries aqui são formais.

O primeiro resultado principal é
`ProjectiveDepth.mk_newtonJet_eq_weightedProjective`, em
[NewtonProjectiveDepthJets.lean](../CarrySelfAdjointOperator/NewtonProjectiveDepthJets.lean).

## A diferença já existia

O operador usado é **exatamente**
`CPFormal.Analytic.Cp.carryWeightedScalarFirstDifference`, da dependência fixada
`CpCarryWeightedVerticalTfvdFinite.lean`:

$$
\nabla_q f(k)=q^{-1}f(k+1)-f(k).
$$

Para `q ≠ 0`, o Lean prova

$$
\nabla_q E_0=0,
\qquad \nabla_q E_{r+1}=E_r,
\qquad \nabla_q^mE_{r+m}=E_r,
\qquad \nabla_q^{r+1}E_r=0.
$$

A forma com `r+1` evita o erro de interpretar `r-1` como subtração truncada
dos naturais em `r=0`.

## Realização e retorno no Hilbert existente

Para `0 ≤ q < 1`, cada ordem tem norma somável e define um vetor no **mesmo**
`CarryVerticalL2`. Os teoremas estão em
[NewtonCarryGreenBridge.lean](../CarrySelfAdjointOperator/NewtonCarryGreenBridge.lean).

| Identidade | Teorema no namespace `ProjectiveDepth` |
|---|---|
| `E₀` é o vetor geométrico existente | `newtonCarryVector_zero_eq_geometric` |
| `E₁` é o vetor afim existente | `newtonCarryVector_one_eq_affineSlope` |
| `E₁(k) = carryWeightedVerticalGreenKernel q k` | `newtonJet_one_eq_carryGreenKernel` |
| `R_q(a,b)=aE₀+bE₁` | `carryReturn_eq_newtonModes` |
| `Tr_q x=(x(0),∇_q x(0))` | `carryTrace_eq_depthTrace` |
| `B_q x(k+1)=q∇_q²x(k)` para `q ≠ 0` | `carryBracket_succ_eq_depthDifference_sq` |
| `B_q E_{r+2}(k+1)=qE_r(k)` para `0<q<1` | `carryBracket_newtonCarryVector_succ` |
| `Tr_q E_{r+2}=0` | `carryTrace_newtonCarryVector_succ_succ` |
| `G_q B_q E_{r+2}=E_{r+2}` para `0<q<1` | `carryGreen_bracket_newtonCarryVector_succ_succ` |

A última identidade é uma aplicação direta de
`CPFormal.Analytic.Cp.carryWeightedVerticalTfvd_apply`: o retorno é zero
porque os dois dados de bordo do jet são exatamente zero. A coordenada zero
reservada pelo bracket continua presente; a fórmula da segunda diferença
está explicitamente restrita à coordenada `k+1`.

## Origem nativa e normalização

Reutilizando `primeCarryAmplitudeRatio_eq_criticalAmplitude_one`, obtém-se
para toda base natural `p` e toda profundidade `k`:

$$
E_0^{(q_p)}(k)=\operatorname{criticalAmplitude}(p,k),
\qquad
\log(p^k)\operatorname{criticalAmplitude}(p,k)
=\log(p)E_1^{(q_p)}(k).
$$

São `newtonJet_zero_eq_criticalAmplitude` e
`tower_log_criticalAmplitude_eq_newtonJet_one`. A segunda equação preserva o
fator `log p` e não divide por ele. Para usar toda a realização Hilbert e a
lei de descida com `q_p`, as estimativas existentes fornecem `0<q_p<1`
quando `p≥2`, sem necessidade de primalidade.

Também ficou formalizado

$$
X\frac{dY_q}{dX}
=\operatorname{rescale}_q(\operatorname{greenVelocity}),
\qquad
\operatorname{mk}(K_q)=Y_q(1+Y_q).
$$

## Fronteira preservada

O resultado vale para **todas as ordens de Newton na profundidade de uma
fibra**. A mudança triangular por Stirling para as potências logarítmicas
de ordem arbitrária ainda não é um teorema deste módulo. Também permanecem
distintos: profundidade `k`, ordem `r`, índice horizontal e altura espectral.

Nenhuma identidade Gram dos momentos nativos, isometria entre as torres,
conexão de Cartan ou igualdade com o shift espectral é concluída aqui.
Em particular, pertencer ao Hilbert existente não identifica sua métrica
com o Hankel nativo. O retorno afim de dimensão dois também não é declarado
igual ao defeito de truncagem da relação de Heisenberg.

## Auditoria

[NewtonProjectiveDepthAudit.lean](../CarrySelfAdjointOperator/NewtonProjectiveDepthAudit.lean)
imprime a dependência axiomática dos resultados centrais. O audit está
integrado em `Audit.lean` e `KernelConstructionAudit.lean`; a implementação
está no agregador principal. Nenhum pin de dependência é alterado.

Validação executada: `lake build --wfail CarrySelfAdjointOperator.NewtonProjectiveDepthAudit` passou;
os 24 resultados auditados dependem somente de `propext`, `Classical.choice` e `Quot.sound`.
`scripts/audit.sh` completou seus 15 builds com `kernel audit passed` e saída zero.
`git diff --check` e a auditoria estática passaram. A conferência dos arquivos de
configuração confirmou que toolchain e dependências foram preservados. Este fechamento
não afirma a costura Gamma–Gram nativo.
