# Finite camera logarithmic moment crosswalk

This module is a typed crosswalk between the explicit finite sums of Naimark camera vectors and the period-indexed finite moment matrices already supplied by `NativeCarrySpectralWeyl`.

## Scope and source APIs

The finite family is an arbitrary type `ι` with `[Fintype ι]` and a map
`camera : ι → CameraIndex`, where `CameraIndex` is the supported camera subtype
(`2 ≤ cameraLabel`).  The global realization remains the pinned
`NaimarkSpace = Lp KolmogorovSpace 2 positiveLebesgueMeasure`.

| object | domain | codomain / type | index meaning |
| --- | --- | --- | --- |
| `finiteCameraNaimarkSynthesis camera u` | `u : ι → ℝ` | `NaimarkSpace` | finite camera labels in `camera` |
| `finiteCameraLogarithmicSynthesis camera u` | `u : ι → ℝ` | `NaimarkSpace` | finite sum of `Y e_i`, with `Y(x)=1+log x` |
| `finiteCameraNaimarkGramMatrix camera` | — | `Matrix ι ι ℝ` | Naimark column Gram |
| `finiteCameraNaimarkFirstMomentMatrix camera` | — | `Matrix ι ι ℝ` | `⟨e_i,Y e_j⟩` form |
| `finiteCameraNaimarkSecondMomentMatrix camera` | — | `Matrix ι ι ℝ` | `⟨Y e_i,Y e_j⟩` form |
| `periodicGramMatrix period labels` | finite labels and `period : ℕ` | `Matrix ι ι ℝ` | pinned finite periodic profile |
| `firstMomentMatrix period labels` | same | `Matrix ι ι ℝ` | upstream `log(min slope)` moment |
| `secondCenteredMomentMatrix period labels` | same | `Matrix ι ι ℝ` | upstream raw `Y²` form, `1 + log(min slope)^2` |
| `positiveInverseSqrt G` | `G : Matrix ι ι ℝ` | `Matrix ι ι ℝ` | pinned `G⁻¹/²` |
| `logarithmicMultiplication` | `logarithmicMultiplication.domain` | `NaimarkSpace` | unbounded partial multiplier by `Y` |
| `sixCamera...` aliases | `Fin 6 → ℝ` | corresponding finite objects | labels `2,3,4,5,6,7`, period `420` |

The finite moment matrices and the Naimark family use related but distinct
indexing functions.  The only generic comparison hypothesis is the explicit
pairwise equality
`periodicGramMatrix period (fun i => cameraLabel (camera i)) i j =
gramKernel (camera i) (camera j)`.

## Domain and column identities

`finiteCameraNaimarkDomainSynthesis` packages the finite raw sum with a proof
that it belongs to `logarithmicMultiplication.domain`.  The theorem
`finiteCameraNaimarkDomainSynthesis_apply` proves that applying the partial
multiplier is exactly the finite sum
`finiteCameraLogarithmicSynthesis`.

For supported cameras, the existing centered vector gives the exact algebraic
identity

```text
Y e_c = centeredNaimarkCameraVector c
       + log(cameraSlope (cameraLabel c)) • e_c.
```

The mixed column theorem
`inner_naimarkCameraVector_logarithmicMultiplication` is

```text
⟪e_b, Y e_c⟫ = gramKernel b c * log(min(slope_b, slope_c)).
```

The apparent absence of an extra `1` is intentional: the pinned integral
identity is `∫(1 + log x) = b * log b` on `(0,b]`.  The second form theorem is

```text
⟪Y e_b, Y e_c⟫
  = gramKernel b c * (1 + log(min(slope_b, slope_c))^2).
```

These are form identities on explicit domain vectors.  The current pin has no
closure theorem placing every finite `Y`-image in `Dom(Y)` a second time, so the
module does not assert an operator-valued `Y²` domain statement.

## Raw and whitened finite synthesis

`finiteCameraNaimarkSynthesis_inner` proves

```text
⟪E u, E v⟫ = uᵀ (finiteCameraNaimarkGramMatrix camera) v.
```

The corresponding first and second form identities are
`finiteCameraNaimarkSynthesis_log_inner` and
`finiteCameraLogarithmicSynthesis_inner`.

The whitened synthesis is

```text
finiteCameraWhitenedNaimarkSynthesis camera G u
  := E (positiveInverseSqrt G *ᵥ u).
```

Its exact pairing before any Gram assumption is

```text
⟪J u, J v⟫
 = uᵀ ((G⁻¹/²)ᵀ * rawGram * G⁻¹/²) v.
```

`finiteCameraWhitenedNaimarkSynthesis_inner` adds the necessary hypothesis
`rawGram = G` and `G.PosDef`; then the pinned whitening theorem gives
`⟪J u,J v⟫ = uᵀv`.

The analogous first and second form pairings are

```text
⟪J u, Y J v⟫
 = uᵀ ((G⁻¹/²)ᵀ * rawFirst * G⁻¹/²) v,

⟪Y J u, Y J v⟫
 = uᵀ ((G⁻¹/²)ᵀ * rawSecond * G⁻¹/²) v.
```

The entrywise compression theorems expose these pairings as finite matrices.
They do not silently identify a raw arbitrary `G` with the camera Gram.

## Periodic source and six-camera recovery

The following theorems transport the finite Naimark matrices to the pinned
period-indexed source whenever the pairwise Gram hypothesis is supplied:

- `finiteCameraNaimarkGramMatrix_eq_periodicGramMatrix`;
- `finiteCameraNaimarkFirstMomentMatrix_eq_firstMomentMatrix`;
- `finiteCameraNaimarkSecondMomentMatrix_eq_secondCenteredMomentMatrix`.

For `atlasSixCameraIndex`, the period is `420`.  The exact specialization is
proved by:

- `finiteCameraNaimarkGramMatrix_six_eq`;
- `finiteCameraNaimarkFirstMomentMatrix_six_eq`;
- `finiteCameraNaimarkSecondMomentMatrix_six_eq`.

Thus `sixCameraGram`, `sixCameraFirstMoment`, and
`sixCameraSecondCenteredMoment` are recovered literally.  In particular, the
upstream name `secondCenteredMomentMatrix` denotes the raw second moment of the
coordinate `Y=1+log x`; it is not already the variance defect.

The six-camera form crosswalks are:

```text
sixCameraWhitenedNaimarkSynthesis_log_inner
sixCameraWhitenedLogarithmicSynthesis_inner
sixCameraWhitenedNaimarkSynthesis_inner_eq_identity
```

They identify the first form with `sixCameraLogOperator`, the second with
`sixCameraWhitenedSecondMoment`, and the zero-th form with the Euclidean identity.

## Variance and centered-log presentation

The existing finite definition is recorded by
`sixCameraVariance_eq_logarithmic_compression_defect`:

```text
sixCameraVariance
  = sixCameraWhitenedSecondMoment
    - sixCameraLogOperator * sixCameraLogOperator.
```

The theorem `sixCameraVariance_eq_centered_logarithmic_form` then puts this
same matrix form beside the already-proved finite centered-log Naimark escape.
The fully oriented crosswalk is
`sixCameraLogarithmicCompressionDefect_eq_centeredNaimarkEscape`.
It uses the existing theorem for
`sixCameraWhitenedNaimarkEscape (sixCameraWhitenedCenteredLogNaimarkSynthesis u)`
and introduces no new carrier or normalization.

## Explicit residual / next gate

The zero-th and first form identities are closed, and the second moment is
closed as the Gram/form of the explicit vectors `Y e_i`.  The remaining domain
seam for a literal expression `J* Y^2 J` is a theorem that the finite `Y`-image
lies in the maximal domain of `Y` once more (or an equivalent integrability
statement).  No inverse of a Cauchy compression, Weyl expansion, cutoff limit,
`Big-O`, TFVD, Gpre, Hankel, Jacobi, or spectral hypothesis is used here.

The next mathematically precise gate is therefore to supply that `Dom(Y²)`
closure theorem if an operator-level square is required.  Until then, the
form-level second moment and the variance/centered-escape identity are the
strong statements supported by the current pin.
