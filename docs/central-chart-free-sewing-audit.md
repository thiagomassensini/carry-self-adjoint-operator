# Central chart-free sewing audit

## Scope and result

This audit is center-only.  It does not use theta, zeros, confinement, a new
carrier, a Naimark return, all-order promotion, or the `h1` gate.

The chart cancellation suggested after commit `b5db035` is exact.  Lean now
proves

```text
raw response coefficient 1 = C3-chart coefficient 1 + native coefficient 1,
h0 = xi coefficient 1 + native coefficient 1.
```

Consequently the central sewing is equivalent, without a hypothesis, to

```text
Re <rawTFVD0,rawTFVD0> - Re(native coefficient 1)
  = Re(xi coefficient 1) - ||residual0||^2,
```

and this is equivalent to

```text
Re <rawTFVD0,rawTFVD0> + ||residual0||^2 = h0.
```

The formal statements are in
`CompletedC3CentralChartFreeSewingAudit.lean`.

## What the existing geometry realizes

Write

```text
E = infiniteReflectedGreenEnergy(1/2),
L = ||canonicalCompletedC3LogJetState(1/2)||^2.
```

The existing theorems give the following exact, unconditional identities:

```text
Re <rawTFVD0,rawTFVD0> = E + L,
||residual0||^2         = E^2.
```

The first line combines the ordinary/logarithmic TFVD Gram split with the
self-dual reflected-Green identity.  The second is the concrete retained
precompression-residual normalization.  The distinction between `E` and
`E^2` is essential: the residual state has amplitude `E`, hence quadratic
Gram contribution `E^2`.

The two response coefficients are also opened individually, without using
their sum:

```text
native coefficient 1
  = -1/2 * ((G'' G - (G')^2) / G^2),

xi coefficient 1
  = -1/2 * ((A'' A - (A')^2) / A^2),
```

at the centered height, where `G = nativeHeightScalar` and
`A = nativeXiCompletionFactor`.  Thus the chart-free gate is literally the
comparison of the Green/log-TFVD expression with the two factor
log-curvatures and the squared residual energy.

## Directed search for a common intermediate

The relevant existing realizations were checked as follows.

- The canonical Green-frame/compatible-Poisson-graph theorems realize `E`
  losslessly, including seed, external residual, depth-one, bulk, and causal
  response/boundary cross terms.  They do not add the independent log-jet
  norm `L` or the quadratic scalar `E^2`.
- The retained precompression residual realizes exactly `E^2`; it has no
  theorem identifying it with an xi/native factor curvature.
- The head--tail and endpoint boundary theorems reconstruct the raw
  Wronskian and show that the completed outer endpoint tends to zero.  They
  do not turn `E + L` into the native response curvature or `E^2` into a
  completion curvature.
- The mixed completed-C3 ledger realizes the raw response coefficient,
  including structural, off-diagonal, readout, and tail terms.  Its total
  Taylor identity fixes the sum but supplies no Gram theorem equating that
  raw coefficient with the raw TFVD norm.
- The product-response theorem realizes `h0` as the sum of the xi and native
  logarithmic curvatures.  Reusing that total identity to assign either
  curvature to a Green carrier would be exactly the sewing assertion being
  tested.
- The central clock Schur energy and the central Green-bulk first variation
  are different existing scalars: respectively a projective subtraction and
  `2 log(3) E`.  Neither equals the required `E + L + E^2` by an existing
  theorem.

No theorem in the current repository or the archived covariant tree supplies
a common intermediate for the two chart-free sides.  The existing named
`canonicalCompletedC3ConcreteDressedCentralMomentDefect` merely names their
difference after scalarization; it is not an independent geometric
realization and cannot close the gate.

## First genuinely new scalar identity

After every available exact identification is applied, the central sewing is
equivalent to one scalar equality:

```text
E + L + E^2 = h0.
```

Opening the analytic side as far as the existing factor theory allows gives

```text
E + L + E^2
  = Re[-1/2 * (
      (A'' A - (A')^2) / A^2
      + (G'' G - (G')^2) / G^2)].
```

Lean proves that the sewing holds if and only if this displayed equality
holds; it does not assume or rename the equality.  This is therefore the
first genuinely new center identity.  The four raw finite channels need not
be decomposed further unless a future proof of this precise equality uses
their provenance.

## Numerical route diagnostic

A high-precision evaluation of the literal definitions gives approximately

```text
E       = 0.1163742489678478,
L       = 0.2664774379590911,
E^2     = 0.0135429658228306,
E+L+E^2 = 0.3963946527497696,
h0      = 0.0231049931154190.
```

This calculation is not used by Lean and is not a formal refutation.
However, it is a strong route diagnostic: with the current concrete
normalizations, the missing equality appears numerically false by about
`0.3732896596343506`.  The likely issue is therefore not a hidden endpoint
identity waiting to be imported, but a mismatch in the proposed concrete
dressed Gram/readout normalization or in which residual/cross coordinate
should enter the one-point state.
