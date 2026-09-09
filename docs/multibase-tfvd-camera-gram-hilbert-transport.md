# Multibase TFVD camera Gram Hilbert transport

This note records the finite, typed transport added on top of commit
`e014c684724bfb016cff9e0ac127338da3f4dc0e`.  The construction keeps the
outer camera index separate from the coordinates inside a Hilbert-valued
state.  It therefore applies to the existing camera-resolved TFVD channels
without identifying a camera label with a vertical/sample index.

## Carrier and matrix orientation

For finite types `input`, `output`, and a complex Hilbert space `H`, the new
abbreviation

```lean
FiniteHilbertFamily input H := PiLp 2 (fun _ : input => H)
```

is a finite family of `H`-valued vectors.  For
`A : Matrix output input ℝ`,
`finiteHilbertMatrixSynthesis A` maps an input family to the output family by

```text
(T_A X)_j = ∑ i, (A j i : ℂ) • X_i.
```

Rows are output indices and columns are input indices.  Consequently the raw
camera synthesis by the transposed literal matrix is

```lean
finiteCameraHilbertRawSynthesis C
  = finiteHilbertMatrixSynthesis Cᵀ
```

and maps camera-indexed states to state-indexed states.  The `H`-valued entry
is untouched by the external matrix operation.

## Generic lift and composition

The module proves:

```text
finiteHilbertMatrixSynthesis_apply
finiteHilbertMatrixSynthesis_comp
finiteHilbertMatrixSynthesis_one
```

The composition theorem has the matrix orientation

```text
T_B (T_A X) = T_(B * A) X.
```

It is proved by finite sum rearrangement, so no tensor-product or infinite
completion is introduced.

## Raw camera Gram metric

For an arbitrary complex inner-product space `H`, the central identity is

```text
finiteCameraHilbertRawSynthesis_inner
```

which states

```text
⟪S_C X, S_C Y⟫
  = ∑ i, ∑ j, ((finiteCameraRowGram C i j : ℝ) : ℂ)
      * ⟪X_i, Y_j⟫.
```

Thus the external metric is induced by the literal synthesis and is exactly
the existing row Gram `C * Cᵀ`; it is not postulated as a new metric.  On
single-channel coordinate vectors the specialization

```text
finiteCameraHilbertRawSynthesis_single_channel
```

gives

```text
⟪S_C (e_i ⊗ x), S_C (e_j ⊗ y)⟫
  = ((finiteCameraRowGram C i j : ℝ) : ℂ) * ⟪x,y⟫.
```

Off-diagonal row-Gram entries therefore measure raw camera overlap.  The
module does not assert that raw camera axes are orthogonal.

For a literal finite camera family, the theorem

```text
finiteLiteralCameraHilbertRawSynthesis_inner
```

rewrites those entries to the existing
`literalFiniteCameraGram` through
`finiteLiteralCameraMatrix_rowGram_apply_eq_literalFiniteCameraGram`.

## Canonical whitening and Parseval

The existing positive-inverse-square-root readout and synthesis are lifted as

```lean
finiteCanonicalCameraHilbertReadout
finiteCanonicalCameraHilbertSynthesis
```

under the same row-Gram positive-definiteness hypothesis.  The main results
are:

```text
finiteCanonicalCameraHilbertSynthesis_isometry
finiteCanonicalCameraHilbertReadout_synthesis
finiteCanonicalEnrichedCameraHilbert_parseval
```

The first is the Hilbert-valued form of `Vᵀ V = I`; the second is the
coisometric reconstruction `R V = I`.  The Parseval theorem transports the
existing visible/blind identity to `H`-valued finite families:

```text
⟪R_H X, R_H Y⟫ + ⟪B_H X, B_H Y⟫ = ⟪X,Y⟫,
```

where `B_H` is the lift of the existing blind projection.  This is a
finite-family identity and does not identify this provenance blind sector
with the separate scalar `logEvalBlindVector` direction.

The concrete specialization

```text
finiteLiteralWhitenedCameraResolvedLogSlopePrefixState
```

restricts the existing global algebraic carrier
`CameraResolvedCarryVertical := ℕ →₀ CarryVerticalL2` to a finite family of
camera labels and applies the canonical whitened synthesis.  Its two cutoff
parameters remain separate: `cameraCutoff` controls the literal matrix and
`tfvdCutoff` controls the TFVD prefix.  The theorem
`finiteLiteralWhitenedCameraResolvedLogSlopePrefixState_isometry` is the
corresponding `CarryVerticalL2` specialization.

## Commutation with the inner TFVD map

The generic theorem

```text
finiteHilbertMatrixSynthesis_map_linearMap_commutes
```

proves that an arbitrary linear map `T : H →ₗ[ℂ] K` commutes with the external
finite matrix lift.  It applies in particular to any existing TFVD analysis
or reconstruction map whose domain is `CarryVerticalL2`, without introducing
a new TFVD carrier or a tensor-product API.

## What is deliberately not identified

The prime-depth channel carrier from the preceding module remains

```text
ℕ →₀ CarryVerticalL2
```

with an outer camera label and an inner vertical coordinate.  The present
module can restrict it to a finite family `camera : index → ℕ`, but it does
not assert that this prime ledger is the same family as a chosen literal
all-base camera matrix.  In particular, a six-camera literal package may
contain composite cameras and cannot be silently identified with the prime
factorization ledger.

Likewise, the algebraic decomposition
`cameraVerticalLine p ⊕ cameraHorizontalSpace p` is not promoted to an
orthogonal decomposition before whitening.  No `InnerProductSpace` is added
to the global `Finsupp` carrier, and no infinite cutoff limit of the
Hilbert-valued operators is claimed.

## Next Gram/Hankel Gate

1. **Camera Gram realization:** yes, for every finite real matrix `C`, as the
   pairing identity `finiteCameraHilbertRawSynthesis_inner` on
   `PiLp 2 (fun _ => H)`.
2. **Carrier:** finite `H`-valued families, with the `CarryVerticalL2`
   specialization obtained by restriction from `CameraResolvedCarryVertical`.
3. **Raw orthogonality:** not assumed.  The single-channel theorem exhibits
   the overlap coefficient `finiteCameraRowGram C i j`.
4. **Whitened modes:** images of finite camera families under
   `finiteCanonicalCameraHilbertSynthesis`; they are isometric under row-Gram
   positive definiteness.
5. **Canonical synthesis:** its lift is isometric by
   `finiteCanonicalCameraHilbertSynthesis_isometry`.
6. **Canonical readout:** its lift satisfies the coisometric reconstruction
   identity `finiteCanonicalCameraHilbertReadout_synthesis`.
7. **Visible/blind Parseval:** transported to finite Hilbert-valued families
   by `finiteCanonicalEnrichedCameraHilbert_parseval`.
8. **External/internal commutation:** proved for every internal linear map by
   `finiteHilbertMatrixSynthesis_map_linearMap_commutes`; this is the generic
   result needed for TFVD analysis or reconstruction.
9. **Prime versus literal semantics:** still separate.  The finite restriction
   is a typed operation, not a semantic identification of the two camera
   families.
10. **All-order Taylor jets:** no pairing theorem with this camera Gram is
    proved here.  The next theorem must identify the all-order TFVD jet family
    with a chosen finite literal camera family and its induced Gram.
11. **Moment Gram representation:** not yet formulable honestly from this
    module alone; no Hankel dependence on `i + j` is established.
12. **Distance to Hankel:** after the semantic family match, prove that the
    Taylor/Green jet pairings equal a moment sequence (and, separately, the
    shifted sequence for the odd sector).  Only then can an
    `IsMomentGramRepresentation` or shifted counterpart be introduced.
