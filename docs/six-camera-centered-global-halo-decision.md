# Six-camera centered-log global halo decision

## Scope and base

This module starts from commit `ddf0b5d4dcd832b089a9d793bece124f3c541653` and works entirely in the intrinsic real `NaimarkSpace`. It introduces no cutoff, limit, realification, new completion, or spectral hypothesis.

The selected six-camera labels are `2, 3, 4, 5, 6, 7`. The exceptional C2 slope is `4), and every selected slope is at most `7`. A camera with label at least `8) has slope at least `8).

## Exact external orthogonality

The existing mixed Gram identity

```
inner (naimarkCameraVector b) (centeredNaimarkCameraVector c)
  = gramKernel b c *
      (Real.log (min (cameraSlope (cameraLabel b))
        (cameraSlope (cameraLabel (atlasSixCameraIndex i)))) -
       Real.log (cameraSlope (cameraLabel (atlasSixCameraIndex i))))
```

vanishes for an external camera `b) with `8 <= cameraLabel b`, because the minimum is the selected slope. The module proves this first for the raw centered-log synthesis and then after six-camera whitening:

- `externalCamera_inner_sixCameraCenteredLogNaimarkSynthesis_eq_zero`
- `externalCamera_inner_sixCameraWhitenedCenteredLogNaimarkSynthesis_eq_zero`

The halo projector is `H6 = P_infinity - P6`. Symmetry of the global projector and the preceding orthogonality give:

- `externalCamera_inner_centeredHalo_eq_neg_sixProjection`
- `externalCameraWhitenedReadout_centeredHalo_eq_neg_returnReadout`

Thus an external readout of the halo is the negative selected-camera readout.

## Selected projection and return compression

The selected projection is identified with the return-compression synthesis:

- `sixCameraProjection_centeredLog_eq_returnSynthesis`
- `sixCameraProjection_centeredLog_eq_cameraReturnCompression_synthesis`

The second theorem exposes the matrix

```
cameraReturnCompression sixCameraGram sixCameraFirstMoment
  (cameraLogSlopeDiagonal sixCamera).
```

No scalar readout is used as a substitute for vector equality.

## Camera 8 witness calculation

The existing halo witness camera is label `8`. Its exact Gram row against the selected six cameras is

```
[8, 0, 16, 0, 8, 0].
```

The corresponding inverse-Gram row is represented by

```
q8 = [91/278, -12/139, 155/278, 0, 12/139, 0].
```

The module proves

- `sixCameraExternalEightGramRow`
- `sixCameraExternalEightDual_mul_gram`

with exact rational arithmetic.

Let

```
K = sixCameraFirstMoment
    - sixCameraGram * cameraLogSlopeDiagonal sixCamera.
```

For the fourth basis vector `e4`, the exact external readout is

```
q8 dot (K e4)
  = (8/139) * (91 * Real.log 2 - 82 * Real.log 3).
```

The logarithmic factor is nonzero. If it vanished, `Real.log_pow` would give

```
Real.log (2^91) = Real.log (3^82),
```

and injectivity of `Real.log` on positive reals would imply the impossible natural-number equality `2^91 = 3^82`.

The witness is

```
sixCameraCenteredGlobalHaloWitness
  = CFC.sqrt sixCameraGram *ᵥ (Pi.single (4 : Fin 6) 1).
```

The exact nonzero chain is:

- `sixCamera_centeredSlopeDefect_e4`
- `sixCameraExternalEightDual_dot_centeredSlopeDefect`
- `sixCameraExternalEightDual_log_combination_ne_zero`
- `externalCamera8WhitenedReadout_centeredWitness`
- `externalCamera8WhitenedReadout_centeredHalo_witness_ne_zero`
- `sixCameraCenteredGlobalHaloProjection_centeredWitness_ne_zero`

## Decision

The explicit camera-8 readout is nonzero, so the centered six-camera halo vector is nonzero for the displayed witness. The existential theorem is:

```
sixCameraGlobalCoherentHaloProjection_centeredLog_exists_ne_zero :
  exists c : Fin 6 -> Real,
    sixCameraGlobalCoherentHaloProjection
      (sixCameraWhitenedCenteredLogNaimarkSynthesis c) != 0
```

Therefore the desired universal vanishing is false:

```
not (forall c,
  sixCameraGlobalCoherentHaloProjection
    (sixCameraWhitenedCenteredLogNaimarkSynthesis c) = 0)
```

This is a restriction result for the centered-log six-camera family. It is distinct from the earlier theorem that the halo operator is nonzero on the whole `NaimarkSpace`.

Combining this decision with the existing decomposition yields a genuinely nontrivial centered-state identity:

```
sixCameraVariance
  = six-camera coherent halo Gram
  + global Naimark escape Gram.
```

The stronger equality with only the global escape term is unavailable for this family.

## Required audit answers

1. For every external `b` with `8 <= cameraLabel b`, the centered-log readout is exactly zero: **CLOSED**.
2. `P6 D6 c = U6 (sixCameraWhitenedCrossGram *ᵥ c)`: **CLOSED**, through `sixCameraProjection_centeredLog_eq_returnSynthesis`.
3. The external halo readout reduces exactly to the negative selected readout: **CLOSED**.
4. The camera-8 functional is the exact row `[8,0,16,0,8,0]), represented after inverse Gram by `q8`: **CLOSED**.
5. `r8 A6 = 0): **FALSE**. On `e4` it equals `(8/139) * (91 log 2 - 82 log 3)`.
6. `sixCameraMixedReturnRay` is not needed for the decision. The primary witness is the square-root lift of `Pi.single 4 1`.
7. An exact witness is `sixCameraCenteredGlobalHaloWitness`.
8. `H6 D6 = 0): **FALSE**.
9. `H6 D6 != 0): **CLOSED** by the explicit camera-8 readout.
10. `sixCameraVariance = globalNaimarkEscapeGram` alone: **not available**; the halo term is nonzero on the displayed centered state.
11. The geometric meaning is a nonzero component coherent with the all-camera ordinary range but invisible to the selected six-camera ordinary range. No scalar-blind, Gpre, or provenance identification is claimed.
12. No density or totality theorem is needed for the negative decision: one nonzero functional suffices.
13. No cutoff or limit is used.
14. No Genuine or zero hypothesis is used.
15. Comparison with `projectorBlindEnergy` remains a separate carrier-level theorem.
16. The next minimal theorem is a typed comparison between this external readout and the relevant Weyl camera-return coefficient; this module does not assert that identification.

## Semantic residuals

The following remain distinct:

- selected six-camera projector `P6`;
- global ordinary projector `P_infinity`;
- coherent halo `H6 = P_infinity - P6`;
- global escape `B_infinity`;
- scalar synthesis blindness and any Gpre/provenance sector.

No statement here identifies these sectors with one another.

## Validation and trust

The source audit prints axioms for the principal theorems. The intended checks are:

```bash
lake build
bash scripts/audit.sh
git diff --check
python3 -m json.tool audit/theorem-registry.json
```

No `sorry`, `admit`, or project-specific axiom is used.
