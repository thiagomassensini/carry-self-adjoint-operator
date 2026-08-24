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
| `CompletedC3SymplecticNaimarkLimitBridge` | Uses one permanent orthonormal camera family for every cutoff, retains two real skew quadratures through Naimark promotion, reconstructs the full complex Green form, and passes its Genuine radial readout to the completed kernel. |
| `CompletedC3BracketTfvdGreenFactorization` | Bundles TFVD heads, value/log-jet tails, and the bracket port in one state; identifies its completed trace with `(F,-F')`; and factors the full ledger through bracket, enriched TFVD, and Green in that order. |

All eleven modules are imported by `CarrySelfAdjointOperator.lean` and their
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

and the same equality after coordinatewise Naimark promotion.  The all-cutoff
extension assigns the real and imaginary parts of cell `n` permanently to
coordinates `2n` and `2n+1` in one infinite orthonormal camera family.  Thus
all finite ports live in the same global camera and Naimark spaces.

A second skew is evaluated after rotating the right port by `i`, before any
real projection.  Keeping the two readings separate gives

```text
q0 = re G,
q1 = re (i G) = -im G,
G = q0 - i q1.
```

Lean proves this reconstruction equals the full finite complex `greenForm`,
not merely its real part.  On the mixed Genuine ports at cutoff `3M`, this
readout is literally the radial field of the existing six-channel ledger.  It
converges to the completed radial Gram kernel; after adding the separately
retained chart channel, it converges to
`canonicalCompletedC3FNegFPrimeMixedGreenKernel`.

## Bracket--TFVD factorization

`CanonicalC3BracketTfvdCompletionState M` retains three fields before any
boundary pairing:

```text
finite enriched TFVD transport
unresolved value tail
unresolved log-jet tail
```

The transport itself retains the value head, log-jet head, all boundary
cells, and the complete Green port.  For every cutoff, Lean proves
simultaneously that its heads are the finite bracket charts and that its
Green port is the Genuine bracket boundary pair.  Head plus tail is
cutoff-independent.  After chart normalization and xi completion, the trace
projection of this same carrier is exactly `(F,-F')`.

The other projection is taken in the opposite order.  The independently
defined enriched TFVD boundary is first corrected by its block Green
provenance.  It is then proved equal to the Green form of the retained ports;
only afterwards are those ports identified with the Genuine brackets and
read through the two Naimark quadratures.  The central finite theorem is

```text
completedWronskian_factors_through_correctedTfvdBoundary_then_green
```

It has the literal channel structure

```text
chartWeight * completed Wronskian
  = xiWeight * corrected TFVD Green boundary
  + Green provenance
  + off-diagonal provenance
  + readout residual
  + tail completion
  + archimedean/chart channel.
```

Thus the Wronskian and Green constructions now demonstrably originate in the
same bracket-derived enriched TFVD ledger.  This theorem does not discard the
remaining channels or assert that they vanish.

## Remaining gate

The corrected complex Green kernel now has an exact all-cutoff global
camera/Naimark realization and a proved completed limit.  The theorem
`canonicalCompletedC3FiniteFNegFPrimeSymplecticGlobalGreenReadout_tendsto_wronskian_iff`
states the remaining frontier without an abstract readout: this concrete
global sequence converges to the completed `(F,-F')` Wronskian if and only if
the retained structural triple tends to zero.

The same statement is now proved after forcing the construction through the
bracket--TFVD carrier, as
`canonicalC3BracketTfvdGlobalGreenReadout_tendsto_wronskian_iff`.  Hence the
earlier obstruction was not caused by skipping a definitional transport:
the full state-level transport is closed, and the remaining issue is the
independent no-leak behavior of its structural channels.

The outstanding step must therefore control those structural channels by an
independent positive Hilbert identity or reconstruct them inside a larger
completed direct-sum state.  Applying `re` before the quarter-turn, renaming
the raw camera coefficient, or assuming the structural limit is zero would
bypass the exact obstruction proved above.

No unconditional global confinement theorem is claimed by these modules.

## Verification

The local commands matching the main GitHub Actions workflow are

```bash
bash scripts/static_audit.sh
bash scripts/audit.sh
```

The audit rejects local trust escapes and compiles the full root import and
the theorem registries with `--wfail`.
