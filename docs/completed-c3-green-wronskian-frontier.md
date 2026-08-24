# Completed C3 Green-Wronskian frontier

This note records the exact formal status of the completed C3 transport.  It
distinguishes identities proved by finite algebra and completion from the
remaining global Green-Wronskian identification.

## Module map

| Module | Formal role |
| --- | --- |
| `CompletedC3AllCutoffHilbertState` | Constructs the ordinary and log-jet `l2` states and proves norm convergence of their finite prefixes. |
| `CompletedC3RawGreenGamma` | Identifies the finite raw gamma kernel with a prefix-state inner product and passes it to the completed Gram kernel. |
| `CompletedC3GenuineBracketGreenTransport` | Transports causal bracket data and the finite Genuine C3 Green pair to the same completed ordinary state. |
| `CompletedC3RawSpectralTraceTransport` | Performs the radial phase/cofactor normalization and identifies the completed trace pair with `(F,-F')`. |
| `CompletedC3GreenWronskianSameState` | Expresses the completed trace Wronskian as the Green form of its separated boundary pair and isolates the diagonal frontier. |
| `GlobalKernelProbe` | Rules out raw coefficient renaming and proves that a genuine off-zero kernel sewing would extend continuously to zeros. |
| `CompletedC3MixedGreenWronskianDefect` | Polarizes the finite ledger at independent `z,w`, retains provenance and residual channels, and proves only the actual tail correction tends to zero. |
| `CompletedC3FNegFPrimeMixedKernel` | Applies the height rotation and xi/chart product rule, gives the exact six-channel final readout, and computes the structural limit. |
| `CanonicalC3SymplecticNaimarkBridge` | Realifies each complete C3 leg without loss, applies the symplectic sign before scalar readout, and transports `re(greenForm)` exactly through the global camera completion and Naimark isometry. |

All nine modules are imported by `CarrySelfAdjointOperator.lean` and their
public theorem surface is checked by `CarrySelfAdjointOperator/Audit.lean`.

## Completed finite ledger

Let `S_M(z,w)` denote the retained structural triple

```text
Green provenance + ordered off-diagonal provenance + readout residual.
```

Let `T_M(z,w)` be the independent head-tail completion correction.  The
finite height-coordinate sewing theorem has the literal form

```text
W_raw(z,w) = G_M(z,w) + S_M(z,w) + T_M(z,w).
```

The completion proofs establish

```text
G_M(z,w) -> G_radial(z,w),
T_M(z,w) -> 0.
```

Consequently, uniqueness of limits gives the forced structural limit

```text
S_M(z,w) -> W_raw(z,w) - G_radial(z,w).
```

This is formalized by
`canonicalC3FiniteMixedHeightStructuralDefect_tendsto` and
`canonicalC3FiniteMixedHeightStructuralDefect_tendsto_zero_iff`.

Separately, the six retained channels

```text
radial Green
Green provenance
off-diagonal provenance
height readout residual
tail completion
archimedean/chart product
```

have an exact final readout at every cutoff.  After the nonzero C3 chart
weight is divided only at the end, this readout is the completed Wronskian of
`(F,-F')`.  The relevant theorems are
`finalScalarReadout_eq_completedFNegFPrimeWronskian` and
`finalScalarReadout_div_chartWeight_eq_completedFNegFPrimeWronskian`.

## Diagonal Genuine zero

For `s` in the open Genuine strip with `genuineContinuation s = 0`, use the
centered height `z = centeredHeightParameter s`.  The completed raw value and
therefore its diagonal raw Wronskian vanish.  The structural limit becomes

```text
S_M(s,s) -> -G_radial(s,s).
```

The completed reflected Gram factor is nonzero in the open strip.  Its radial
coefficient is `cpRadialDifference 3 (criticalDisplacement s.re)`, which
vanishes exactly when `s.re = 1/2`.  Lean therefore proves

```text
S_M(s,s) -> 0  <->  s.re = 1/2.
```

The exact theorem is
`canonicalC3FiniteMixedHeightStructuralDefect_tendsto_zero_at_genuineZero_iff`.
The stronger negative statement off the critical line is
`canonicalC3FiniteMixedHeightStructuralDefect_not_tendsto_zero_of_offCritical_genuineZero`.

Thus the structural triple is not a completion tail that can be discarded.
Proving that it vanishes at every Genuine zero has the same strength as the
critical-line conclusion itself.

## Symplectic global transport

The faithful six-camera real/imaginary storage map is injective, but it does
not preserve the intrinsic C3 Green form.  The corrected map keeps each
complex boundary leg intact, realifies it isometrically, and sends

```text
(x1, x2) -> (-R x1, R x2).
```

Only after this rotation is the ambient real skew evaluated.  Lean proves

```text
realifiedGreenSkew (pack x) (pack y) = re (greenForm x y),
```

and the same equality after coordinatewise Naimark promotion.  Both maps are
injective.  On the canonical direct/reflected pair this gives the exact radial
factorization in the global Hilbert space and vanishing exactly at
`re s = 1/2` in the open strip.  These statements are unconditional finite/core
transport identities; they do not equate the ambient Green skew with the
completed `(F,-F')` Wronskian.

## Remaining gate

The corrected Green kernel now has an exact, injective global
camera/Naimark realization.  The outstanding step is the noncircular equality
between that concrete ambient skew and the completed Wronskian.  It must
either control the retained structural channels by an independent positive
Hilbert identity or reconstruct them inside a larger completed direct-sum
state.  Applying `re` before the channel-local rotation, renaming the raw
camera coefficient, or assuming the structural limit is zero would bypass the
exact obstruction proved above.

No unconditional global confinement theorem is claimed by these modules.

## Verification

The local commands matching the main GitHub Actions workflow are

```bash
bash scripts/static_audit.sh
bash scripts/audit.sh
```

The audit rejects local trust escapes and compiles the full root import and
the theorem registries with `--wfail`.
