# Camera vertical/horizontal energy crosswalk

This audit tests a narrow hypothesis only:

```text
ambient central excess = energy of the historical camera-horizontal sector.
```

It does **not** revisit the literal normalized ambient Gram.  That carrier is
already closed by the no-go
`not_canonicalCompletedC3NormalizedAmbientRadialTiltBoundaryIntertwining`.

## Carrier map

The concrete objects currently have the following typed route.

```text
cameraLogContributionVector n : CameraLogSpace = ℕ →₀ ℝ
        │
        ├─ vertical/horizontal algebraic split at prime p
        │    V_p(n), H_p(n) : CameraLogSpace
        │    IsCompl(cameraVerticalLine p, cameraHorizontalSpace p)
        │    (no inner product is supplied here)
        │
        ├─ coefficientwise log-gradient construction
        ▼
CameraResolvedCarryVertical = ℕ →₀ CarryVerticalL2
        │
        ├─ restriction to a chosen finite camera family
        ▼
FiniteHilbertFamily state CarryVerticalL2
        │
        ├─ finiteCanonicalCameraProjection C = V_C R_C
        ├─ finiteCanonicalCameraBlindProjection C = I - V_C R_C
        ▼
finite historical visible/blind state families
        │
        ╳  missing semantic/isometric transport E and camera transport J
        ▼
realified Naimark port/escape
        │
        ╳  no supplied identification with the normalized ambient response
        ▼
canonicalCompletedC3NormalizedAmbientResponseState 0
  : CarryGammaComplexNaimark
```

The first missing typed intertwiner is not a scalar identity: it is the pair
of squares packaged by `NaimarkProjectorIntertwiningSeam`:

```text
J ∘ R_C = U* ∘ E
E ∘ V_C = U ∘ J.
```

Here `R_C,V_C` act on the finite matrix state/camera spaces, while `U,U*` act
between the completed camera and realified Naimark carriers.  The current API
does not construct either `E` or the cutoff-compatible whitened `J`.  The
normalized ambient response is furthermore a complexified Naimark state;
there is no supplied map that identifies it with an embedded finite
state-valued TFVD family.

Thus visible/blind and vertical/horizontal are **not** identified.  Matching
dimensions, a shared camera vocabulary, or algebraic `IsCompl` cannot bridge
this gap.

The resulting typed residual is now formalized rather than merely described:

```text
R_HB = (ℛ_read, ℛ_synth)
ℛ_read  = J ∘ R_C - U* ∘ E,
ℛ_synth = E ∘ V_C - U ∘ J.
```

`naimarkProjectorIntertwiningSeam_iff_residuals_eq_zero` proves that
`R_HB = 0` exactly when both required squares hold.  This is intentionally an
operator-valued residual: without `E` and `J`, a scalar norm difference would
not even compare terms in a common carrier.

## What is closed at the algebraic and finite levels

For every nonzero `n` and prime `p`, the new all-other-cameras theorem is

```text
cameraLogContributionSynthesis (cameraLogHorizontalContribution n p)
  = ∑ q ∈ (n.factorization.support).erase p,
      n.factorization q * log q.
```

Equivalently it is `log (cameraHorizontal n p)`.  This is an exact finite
factor-support formula.  It establishes the intended provenance of the
*algebraic* horizontal log channel, but it does not give that channel a
Hilbert norm or identify it with a finite blind state.

For a finite camera matrix `C` with positive-definite row Gram, the historical
finite splitting is genuinely orthogonal in the finite `PiLp` Hilbert metric.
Writing

```text
P_C X = finiteCanonicalCameraHilbertVisibleState C X,
B_C X = finiteCanonicalCameraHilbertBlindState C X,
```

the proved polarized identity is

```text
⟪P_C X, P_C Y⟫ + ⟪B_C X, B_C Y⟫ = ⟪X,Y⟫.
```

In particular, `‖P_C X‖² + ‖B_C X‖² = ‖X‖²`.  This uses the actual
`finiteCanonicalCameraProjection` / `finiteCanonicalCameraBlindProjection`,
not the `CameraLogSpace` complement theorem.

## Exact central residual frontier

The source code introduces a deliberately uninstantiated test interface
`CanonicalCompletedNativeCameraAmbientEnergyEmbedding X0`.  Its data are an
isometry

```text
E : FiniteHilbertFamily state CarryVerticalL2 →ₗᵢ[ℂ] CarryGammaComplexNaimark
```

and the source match

```text
E X0 = canonicalCompletedC3NormalizedAmbientResponseState 0.
```

No canonical value of this structure is declared or assumed.

If a future construction provides it and also proves the required projection
intertwining, define

```text
ε_V = ‖E(P_C X0)‖² - h₀,
ε_H = ‖E(B_C X0)‖² - δ_A,
δ_A = ‖Â(0)‖² - h₀.
```

The new formal theorem proves, conditional only on the displayed isometry and
the existing finite row-Gram definiteness,

```text
ε_H = -ε_V.
```

Therefore `ε_V = 0` if and only if `ε_H = 0`: the two proposed central norm
equalities are one test rather than two independently adjustable constants.
The transported Pythagoras identity is also proved conditionally:

```text
‖E(P_C X0)‖² + ‖E(B_C X0)‖² = ‖Â(0)‖².
```

This is the smallest concrete residual currently supported by the types.  It
cannot be numerically or symbolically evaluated in the present pin because
there is no actual `(C, X0, E)` whose image is the normalized ambient state.

## Consequences for the proposed ambient-excess identification

* The desired equality `δ_A = ‖H(0)‖²` is **not yet formulated for the
  actual ambient state**, since `H(0)` cannot be constructed from the current
  finite blind output in the ambient carrier.
* The finite historical projection is self-adjoint and idempotent on its
  finite real state metric; its Hilbert-valued lift has exact Parseval.
* The atlas vertical/horizontal split is an algebraic finite-support split,
  with no outer Hilbert metric.  It must not be called the historical
  visible/blind split.
* The existing Naimark port/escape Parseval applies in a different completed,
  realified carrier.  It has no instantiated finite moving-whitened
  intertwiner.
* Consequently there is no N=1, N=2, N=3, or all-order Pick/dslope/Green
  comparison to report from this route.  Such statements would require the
  missing bridge first.

The next admissible theorem is a construction (or a scoped no-go) for a
specific finite camera family: a semantic finite-state embedding `E`, a
whitened coordinate transport `J`, the two seam squares, and a proof that the
embedded finite central state is the same normalized ambient/Green state.
Only then can `ε_V` be evaluated and then polarized.
