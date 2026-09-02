# Central completion/product dressing audit

## Verdict

The current concrete carrier `P` is scalarized and orthogonalized before the
canonical product dressing.  Its state is, by definition, the orthogonal sum

```text
ordinary Parseval TFVD ⊕ log-jet Parseval TFVD ⊕ retained residual.
```

That construction has the exact Gram `E + L + E^2` at the center.  The
product rule does not provide a triangular matrix on these three coordinates
which could be inserted afterward to repair that value.

There is nevertheless an older canonical dressed state already in the
repository.  It is the product ledger

```text
completedNativeC3ProductLedgerState xiState z
  = G(z) • xiState(z) ⊕ A(z) • canonicalCompletedOperatorC3HilbertState(z),
```

where

```text
A = nativeXiCompletionFactor,
G = nativeHeightScalar.
```

This is the lossless state-level realization of the exact Green-Wronskian
product rule.  It occurs before normalization, Taylor extraction, and Gram
scalarization.  Thus the upstream concern was correct, but the existing
dressing is not a mixing of the three coordinates of `P`: it is a two-factor
Green direct sum on a different carrier.

The formal center calculation and closure interface are in
`CompletedNativeCentralProductDressingAudit.lean`.

## Exact central state

The canonical normalized completed state was already defined as

```text
canonicalCompletedNativeNormalizedGreenState xiState
  = normalizedCompletedGreenState (A * G)
      (G • xiState ⊕ A • canonicalCompletedOperatorC3HilbertState).
```

Lean now proves its exact center coordinate identity

```text
Psi_dressed(0)
  = xiState(0) / (sqrt(2) A(0))
      ⊕ canonicalCompletedOperatorC3HilbertState(0) / (sqrt(2) G(0)).
```

Consequently

```text
<Psi_dressed(0), Psi_dressed(0)>
  = <xi_normalized(0), xi_normalized(0)>
      + <native_C3_normalized(0), native_C3_normalized(0)>.
```

There are no cross inner products between these two coordinates.  This is
not an omission: the exact identity

```text
W_(A G) = |G|^2 W_A + |A|^2 W_G
```

cancels the mixed Wronskian terms before the state is formed and is realized
losslessly by the weighted direct sum.

## Where the triangular/binomial transport lives

The triangular rule is already formalized on the scalar product jets.  At
the center the repository proves

```text
(A G)'  = A' G + A G' = 0,
(A G)'' = A'' G + 2 A' G' + A G''.
```

The zeroth moment is therefore

```text
h0 = -(A'' G + 2 A' G' + A G'') / (2 A G).
```

After using the exact first-jet cancellation, the same scalar becomes

```text
h0 = -1/2 * (
        (A'' A - (A')^2) / A^2
      + (G'' G - (G')^2) / G^2).
```

The mixed `2 A' G'` term is therefore real and indispensable, but it does
not become an adjustable cross Gram between ordinary and log-jet TFVD
coordinates.  It is absorbed canonically into the two logarithmic curvature
corrections when the normalized product response is split into factor
responses.

`CompletedGreenJetCoefficientRecurrence.lean` is downstream of this step.
Its recurrence propagates coefficients of a normalized two-variable Green
kernel to the boundary; it does not implement the Leibniz/binomial transport
between completion and native jets.

## Reused center closure

No new scalar sewing hypothesis is needed once genuine Green states for the
two factors are available.  The old theorem

```text
completedNativeC3ProductLedger_inner_self_zero_eq_responseDerivative
```

already removes the diagonal collision.  Combining it with the proved
analytic Taylor coefficient of the completed response gives

```text
<Psi_dressed(0), Psi_dressed(0)> = h0.
```

The new audit module packages this consequence and also opens its right-hand
side both as the full second product jet and as the sum of factor logarithmic
curvatures.  Thus the center calculation itself is complete conditional only
on the intended vector Green representations, not on `E + L + E^2 = h0`.

## First missing vector statements

The product ledger file explicitly leaves `xiState` arbitrary.  The first
missing objects/theorems are exactly:

```text
HasDivisionFreeGreenRepresentation
  nativeXiCompletionFactor
  nativeXiCompletionBoundaryCompanion
  xiState
```

for some continuous Hilbert-valued `xiState`, and

```text
HasDivisionFreeGreenRepresentation
  nativeHeightScalar
  nativeHeightScalarBoundaryCompanion
  canonicalCompletedOperatorC3HilbertState.
```

Neither statement is proved by an existing theorem.  The latter is stronger
than the old diagonal C3 intertwiner obligation: it is the full polarized,
two-variable factor identity

```text
W_G(z,w)
  = (z - conjugate(w)) *
      <canonicalCompletedOperatorC3HilbertState(w),
       canonicalCompletedOperatorC3HilbertState(z)>.
```

At center-only strength, these statements would force the two separately
normalized factor norms to realize their respective first response
coefficients.  Proving only their sum by naming it as a hypothesis would hide
the same sewing problem, so the audit stops at the vector representations.

## Relation to the concrete carrier `P`

The carriers do not currently match:

```text
P
  = ordinary Green-frame
      ⊕ log-jet Green-frame
      ⊕ complexified residual,

product carrier
  = Hxi ⊕ CanonicalCompletedC3HilbertCarrier.
```

No theorem constructs `Hxi`, maps `P` into the product carrier, or identifies
the ordinary/log/residual combination with either factor Green state.  In
particular, `P` contains no xi-completion state coordinate.  Its channels may
still provide source data for a future construction of the native factor
state, but the repository does not presently justify treating their direct
orthogonal sum as the completed defect state.

Therefore the discrepancy

```text
E + L (+ E^2)  versus  h0
```

is not explained by a missing residual or by omitted cross terms inside the
existing `P` Gram.  It reflects comparison of two different states:

1. a prematurely orthogonalized TFVD/readout carrier; and
2. the canonical but not-yet-instantiated completion/native product Green
   carrier.

The shortest honest next attack is to construct or refute the two factor
Green representations above, starting with the center/polarized germ needed
for `h0`.  No all-order recurrence is required for that test.
