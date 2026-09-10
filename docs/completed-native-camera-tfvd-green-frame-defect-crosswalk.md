# Completed native camera / TFVD / Green-frame defect crosswalk

Base deste estudo: `fa73796f594dc08a0f059355f99c26354ea9c7d6`.

Esta rodada testa o gate vetorial exposto por
`BR2GreenFrameDslopeLimitBridge`. O alvo não é um kernel escalar: é a
igualdade, no carrier Green-frame completo, entre o jet `dslope` nativo e o
jet BR2. A ordem zero é testada antes de qualquer comparação all-order.

## Auditoria do par canônico

O candidato semântico para o bloco literal C2 é `base = 2`, `radius = 1`.
O pin atual prova os fatos usados no módulo:

```lean
c2CanonicalBase_isSupported : IsSupported 2
c2CanonicalRadius_one_mem : (1 : ℕ) ∈ radiusSet 2
```

O centro da incidência é o `alignedCenter` da câmera BR2. Para qualquer par
suportado, `br2CameraBracketVerticalState` tem o pivô exclusivo `-2` em
`alignedCenter base 0`; isto é exatamente
`br2CameraBracketVerticalState_apply_alignedCenter`.

## Resultado do anchor de ordem zero

O primeiro teorema novo é:

```lean
canonicalCompletedNativeGreenFrame_evenZero_anchor_impossible
```

Para qualquer `state : ℂ → CarryVerticalL2` que satisfaça
`HasCompletedNativeRealAxisNormalizedGreenKernel state`, ele prova

```lean
¬ normalizedCompletedGreenState
    completedNativeOperatorCharacteristic state 0
    = br2CameraBracketVerticalState base radius 0
```

sob `IsSupported base` e `radius ∈ radiusSet base`.

A prova conserva os dois lados da comparação. A identidade diagonal de
`hkernel` e `dslope_same`, seguida de
`completedNativeGreenNormalizedResponse_hasDerivAt_h0.deriv`, dá

```text
‖normalizedState 0‖² = h₀.
```

Se o anchor valesse, a norma do estado seria a norma do vetor BR2. O pivô
`-2`, lido por `lp.norm_apply_le_norm`, dá `2 ≤ ‖BR2₀‖`, enquanto o resultado
existente
`canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth` dá
`h₀ < 1/16`. Essas desigualdades contradizem a igualdade diagonal.

Logo, o bloqueio já ocorre no primeiro vetor, antes de fase, residual ou
ordens superiores.

## Defeito explícito

O teorema

```lean
canonicalCompletedNativeGreenFrame_evenZero_defect_tendsto_explicit
```

não apaga nenhum canal. Ele identifica o limite do defeito finito como

```lean
canonicalCompletedGreenFrameAnalysisCLM
    (normalizedCompletedGreenState ... state 0)
  - br2CameraBracketGreenFrameParityJet base radius (Sum.inl 0)
```

O teorema
`canonicalCompletedNativeGreenFrame_evenZero_defect_limit_ne_zero` prova que
esse limite é não nulo para todo par suportado. Portanto
`canonicalCompletedNativeGreenFrame_evenZero_defect_not_tendsto_zero` mostra
formalmente que o defeito não tende a zero.

Como a análise Green é injetiva, o limite só poderia ser zero se o anchor
impossível fosse verdadeiro. A redução é vetorial; nenhuma igualdade de
kernel escalar é usada.

Também foi provado o corolário all-order:

```lean
canonicalCompletedNativeGreenFrameDslopeJet_ne_br2_of_kernel
```

Assim, nenhum estado que realize o kernel normalizado nativo pode coincidir
com o jet BR2 completo, porque sua componente `Sum.inl 0` já falha. As versões
`c2Canonical...` instanciam o par `(2,1)`.

## O que isso não afirma

O estado `canonicalCompletedC3ConcreteRealAxisGreenState` vive no carrier
positivo que mantém `ordinary`, `logJet` e `residual` separados; o argumento do
bridge abstrato usa `state : ℂ → CarryVerticalL2`. Não foi feita uma
identificação artificial entre esses carriers. Independentemente disso, o
pin já contém `not_hasCompletedNativeRealAxisNormalizedGreenKernel_concreteC3`
para o estado positivo padrão, derivado da calibração da diagonal. O resultado
desta rodada é mais forte no ponto relevante: mesmo um estado abstrato em
`CarryVerticalL2` que satisfizesse o kernel não poderia passar o anchor BR2.

O bloqueio é, portanto, de magnitude/normalização do anchor (categoria H do
mapa de obstruções), com uma distinção de carrier (categoria I) quando se tenta
usar diretamente o estado positivo C3. Não é uma falha de comparação de
ordem, nem uma licença para escolher uma fase ou renormalizar o pivô.

## Status das etapas

| Etapa | Status |
|---|---|
| `(base,radius) = (2,1)` suportado | fechado |
| pivô e norma do estado BR2 | fechado, `norm_ge_two` |
| anchor de ordem zero | **impossível** sob o kernel nativo |
| limite explícito do defeito | fechado |
| defeito de ordem zero tende a zero | **falso; limite não nulo** |
| igualdade vetorial all-order | **não pode seguir**, já falha em ordem zero |
| ordinary/logJet/residual all-order crosswalk | não iniciado por causa do anchor |
| HP certificate via `greenFrameDefect` | não aplicável nesta rota |
| Hankel, shifted Hankel e Jacobi | permanecem nas APIs existentes, sem novo handoff |

## Axiomas e validação

O audit correspondente imprime os axiomas de todos os teoremas novos. A prova
usa apenas os resultados já presentes do pin e os axiomas padrão aceitos pelo
projeto (`propext`, `Classical.choice`, `Quot.sound` transitivamente); não há
`sorry`, `admit` ou axioma novo.

## Next HP Gate

O próximo gate não é comparar ordens superiores do mesmo estado. É fornecer
uma realização cuja componente de ordem zero tenha simultaneamente:

1. a diagonal nativa `h₀` exigida pelo kernel; e
2. um readout/incidência BR2 com a escala correta, sem o pivô `-2` medido na
   métrica `CarryVerticalL2` crua.

Esse theorem mínimo é um **crosswalk de métrica/readout no anchor**, não um
theorem de Hankel ou de Jacobi. Enquanto ele não existir, os teoremas
`canonicalCompletedNativeGreenFrameDslopeJet_eq_br2_iff*` continuam sendo
critérios exatos, e o defeito de ordem zero acima é a obstrução concreta.

Para a construção positiva C3, ainda seria necessário primeiro resolver a
diferença de carrier e a calibração da métrica; o no-go já existente da
calibração deve permanecer explícito.
