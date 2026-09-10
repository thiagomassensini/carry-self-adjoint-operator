# Six-camera centered-log Naimark variance crosswalk

This module is a finite, intrinsic calculation in the real Naimark space.  It
keeps the ordinary camera vectors and their centered-log translates as two
separate syntheses, applies the existing positive inverse square root of the
six-camera Gram, and identifies the orthogonal escape energy of the centered
synthesis with `sixCameraVariance`.

The result is deliberately below the completed C3 port.  No new completion,
realification, moment source, Genuine hypothesis, zero hypothesis, or spectral
claim is introduced.

## Types and metrics

| object | type | meaning |
|---|---|---|
| `CameraIndex` | `{camera : ℕ // 2 ≤ camera}` | all supported camera labels |
| `NaimarkSpace` | `Lp KolmogorovSpace 2 positiveLebesgueMeasure` | real intrinsic Naimark ambient |
| `Fin 6 → ℝ` | finite coefficient vectors | the fixed labels `2,3,4,5,6,7` |
| `sixCameraGram` | `Matrix (Fin 6) (Fin 6) ℝ` | limiting six-camera Gram |
| `sixCameraFirstMoment` | `Matrix (Fin 6) (Fin 6) ℝ` | first logarithmic moment matrix |
| `sixCameraVariance` | `Matrix (Fin 6) (Fin 6) ℝ` | positive centered/return variance |
| `positiveInverseSqrt sixCameraGram` | real `6 × 6` matrix | canonical whitening matrix |
| `RealifiedNaimarkComplexification` | `WithLp 2 (NaimarkSpace × NaimarkSpace)` | completed realified ambient |
| `canonicalCompletedC3AmbientPortEscape` | continuous linear endomorphism of the realified ambient | complement of the all-camera completed port |

The finite construction uses the first two rows of this table: its projector is
the projection onto the span of the six selected ordinary vectors.  The
completed escape uses the all-camera `realifiedNaimarkPort`; these projectors
are therefore not identified here.

## Mixed Gram and finite syntheses

For `e_b = naimarkCameraVector b` and
`d_b = centeredNaimarkCameraVector b`, the module proves, for every supported
pair `b,c`,

```text
⟪e_b, d_c⟫ = gramKernel b c *
  (log (min (slope b) (slope c)) - log (slope c)).
```

The reverse pairing is recorded by real symmetry.  For the selected six
cameras, this is exactly the entrywise matrix identity

```text
⟪e_i, d_j⟫ =
  (sixCameraFirstMoment - sixCameraGram *
    cameraLogSlopeDiagonal sixCamera) i j.
```

The two finite syntheses are

```text
E c = ∑ i, c i • e_i
D c = ∑ i, c i • d_i.
```

Their pairings are kernel-checked:

```text
⟪E c, E d⟫ = c ⬝ᵥ (sixCameraGram *ᵥ d)
⟪D c, D d⟫ = c ⬝ᵥ (sixCameraGram *ᵥ d)
⟪E c, D d⟫ = c ⬝ᵥ
  ((sixCameraFirstMoment - sixCameraGram *
    cameraLogSlopeDiagonal sixCamera) *ᵥ d).
```

The equality for `D` is the existing centered-Naimark Gram theorem; it is not
a new normalization.

## Whitening and return compression

Set `W = positiveInverseSqrt sixCameraGram` and define

```text
U c  = E (W *ᵥ c)
D₀ c = D (W *ᵥ c).
```

The existing positive-definite six-camera Gram theorem and the existing
whitening identity give

```text
⟪U c, U d⟫   = c ⬝ᵥ d
⟪D₀ c, D₀ d⟫ = c ⬝ᵥ d.
```

The mixed pairing is

```text
⟪U c, D₀ d⟫ = c ⬝ᵥ (A₆ *ᵥ d),
```

where the module proves definitionally

```text
A₆ = cameraReturnCompression sixCameraGram sixCameraFirstMoment
       (cameraLogSlopeDiagonal sixCamera).
```

Thus the two whitened maps are isometric on the finite coefficient space, but
their cross Gram is the return compression rather than the identity.

## Finite Naimark projection and escape

The finite ordinary range is represented by the Riesz coordinates

```text
analysis x i = ⟪U (Pi.single i 1), x⟫.
P x = U (analysis x)
B x = x - P x.
```

The module proves that `analysis (U c) = c`, that `P` is idempotent on the
Naimark space, and that `B (U c) = 0`.  On a centered-log state it proves the
explicit formula

```text
B (D₀ c) = D₀ c - U (A₆ *ᵥ c).
```

The main result is the polarized escape identity

```text
⟪B (D₀ u), B (D₀ v)⟫ =
  u ⬝ᵥ (sixCameraVariance *ᵥ v).
```

Its diagonal specialization is

```text
‖B (D₀ u)‖ ^ 2 =
  u ⬝ᵥ (sixCameraVariance *ᵥ u).
```

Finally, the existing square-root Gram identity gives the equivalent amplitude
form

```text
(CFC.sqrt sixCameraVariance *ᵥ u) ⬝ᵥ
  (CFC.sqrt sixCameraVariance *ᵥ u) =
  u ⬝ᵥ (sixCameraVariance *ᵥ u).
```

This is the finite Naimark realization of the pullback statement
`D₀* (I - P) D₀ = sixCameraVariance`, expressed by pairings rather than by an
untyped operator equality.

## Completed escape seam

`canonicalCompletedC3AmbientPortEscape` acts on
`RealifiedNaimarkComplexification`, while the finite escape above acts on the
real `NaimarkSpace` and projects only onto the six selected ordinary camera
vectors.  The completed projection is the projection onto the range of the
all-camera `realifiedNaimarkPort`.  No current theorem identifies the six-camera
finite range with that completed range, and the centered synthesis is not an
ordinary `realifiedNaimarkPort` image by definition.

Consequently the finite variance pullback is closed, but the stronger statement
with `canonicalCompletedC3AmbientPortEscape` is left as an explicit
embedding/subspace seam.  No artificial realification or cast is used to hide
it.  The previously proved raw-BR2 order-zero obstruction is unchanged.

## Audit status

The audit file checks the principal declarations with `#print axioms`.  They use
only the accepted standard axioms
`propext`, `Classical.choice`, and `Quot.sound`.

No cutoff convergence, moment source, Genuine/zero hypothesis, `projectorBlindEnergy`,
connected C2/Gpre object, or completed port identification is used in this
module.

## Next Blind/Provenance Gate

1. `centeredNaimarkCameraVector` was already in the pinned Spectral-Weyl API; the mixed formula is new here.
2. The mixed Gram and both centered/ordinary six-camera synthesis pairings are proved exactly.
3. Centered centered Gram recovers `sixCameraGram` by the existing theorem.
4. Ordinary synthesis has Gram `sixCameraGram`.
5. Centered-log synthesis has the same Gram.
6. Both whitened maps are finite isometries in the pairing sense.
7. The cross Gram is exactly `cameraReturnCompression`.
8. The finite escape Gram is exactly `sixCameraVariance`.
9. Its diagonal is the variance quadratic form and equals the square-root amplitude pairing.
10. The completed `canonicalCompletedC3AmbientPortEscape` identification is not closed.
11. The remaining seam is the typed embedding of the six-camera centered state together with a comparison of the six-camera projector and the all-camera completed projector.
12. No continuity in a cutoff is needed for the finite result.
13. No moment source is used.
14. No Genuine or zero hypothesis is used.
15. `projectorBlindEnergy` is not compared with this finite Naimark variance.
16. The next minimum theorem is a typed finite-six restriction/embedding theorem relating the six-camera projector to a completed port restriction.
17. Connected C2/Gpre remains separate and bilinear/quadratic.
18. Provenance enters exactly at the unresolved comparison between the finite six-camera complement and the completed all-camera escape (and, separately, any Gpre carrier).
