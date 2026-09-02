# Symplectic crossing normal audit

## Scope and conclusion

This audit identifies the geometry of the linear crossing functional isolated
in commit `41c7c73`.  It uses only the existing full Wronskian carrier,
operator, central state, and real source tangent.

The answer is:

- `J_full` is skew-adjoint and unitary;
- the Riesz normal is canonically `n = -J_full X_full(0)`;
- the crossing kernel is the hyperplane `span(n)^perp`;
- state, tangent, functional, and normal are independent of the cutoff;
- projecting the tangent onto the normal gives a canonical nonnegative
  number, but it equals `h0` only under one additional scale identity which
  is not presently supplied by the repository.

No Hessian, clock quotient, provenance quotient, theta representation, zero
hypothesis, confinement statement, `h1`, Hankel matrix, or Jacobi operator is
used.  The Lean implementation is
`CarrySelfAdjointOperator/CompletedC3SymplecticCrossingNormalAudit.lean`.

## 1. Geometry of the full operator

The polarization module had already proved the inner-product identity

```text
<J_full x,y> = -<x,J_full y>.
```

The new audit promotes it to the literal operator-adjoint theorem

```text
J_full.adjoint = -J_full.
```

Together with `J_full^2 = -I`, this gives

```text
J_full.adjoint * J_full = I,
||J_full x|| = ||x||,
Isometry J_full,
||J_full|| = 1.
```

Thus the full Wronskian operator is a unitary quarter turn, not merely an
operator whose diagonal readout happens to be purely imaginary.

## 2. The Riesz normal

For the old cutoff-indexed functional

```text
L_M(v) = <X_full,M(0), J_full v>,
```

define its Riesz vector without first using skew-adjointness:

```text
n_M = J_full.adjoint X_full,M(0).
```

The adjoint identity then proves exactly

```text
n_M = -J_full X_full,M(0),
L_M(v) = <n_M,v>.
```

With Lean's convention, the inner product is conjugate-linear in the first
slot and linear in the second.  This orientation is why the Riesz vector is
`J_full.adjoint X_full,M(0)`.

The kernel is therefore the canonical normal hyperplane:

```text
ker L_M = (C span n_M)^perp.
```

No positivity or second variation is needed for this statement.

## 3. The cutoff disappears

The prior analytic-state theorem identifies, throughout the real collision
line,

```text
X_full,M(t) = X_full,analytic(t).
```

Consequently Lean proves that all of the following are independent of `M`:

```text
X_full,M(0),
d/dt X_full,M(t) at t=0,
L_M,
n_M.
```

The cutoff-free objects are named

```text
canonicalCompletedC3FullWronskianCentralState,
canonicalCompletedC3FullWronskianRealSourceTangent,
canonicalCompletedC3FullOperatorCrossingFunctional,
canonicalCompletedC3FullOperatorCrossingNormal.
```

Write the tangent as `T`.  The central theorem is now exactly

```text
h0 = <n,T> / D(0),
```

or, before division,

```text
<n,T> = D(0) * h0.
```

## 4. Projection onto the normal

The normal is nonzero.  Indeed, its norm is preserved by the unitary quarter
turn:

```text
||n|| = ||X_full(0)||,
```

and the raw value coordinate of `X_full(0)` is a product of three already
proved nonzero factors.

Let `P_n` be the orthogonal projection onto `C span n`, with no fitted scale,
and define

```text
E_normal = ||P_n T||^2.
```

The rank-one projection formula gives

```text
E_normal = ||<n,T>||^2 / ||n||^2.
```

Using the crossing identity, the requested closed formula is

```text
E_normal
  = ||D(0) * h0||^2 / ||n||^2
  = ||D(0)||^2 * h0^2 / ||n||^2.
```

This calculation introduces no weight or normalization beyond the existing
ledger denominator `D(0)`.

## 5. Exact mismatch with `h0`

Normal projection alone does not formally turn the crossing into the energy
`h0`.  Lean reduces that assertion to the exact scalar condition

```text
E_normal = h0
  <->
h0 * (||D(0)||^2 * h0 - ||n||^2) = 0.
```

On the nonzero-`h0` branch this is

```text
E_normal = h0
  <->
||n||^2 = ||D(0)||^2 * h0.
```

The repository has identities for the symplectic crossing and for the total
Hilbert norm/polarization of the full carrier, but no theorem equating the
central full-state norm with `||D(0)||^2 * h0`.  Therefore this last scale
identity is the first genuinely missing equality.  It is not hidden under a
new hypothesis in the Lean file.

## Conclusion

The crossing functional has a completely canonical geometric normal, and
the cutoff can be removed.  What remains linear is exactly linear: the
projection energy squares the crossing amplitude and divides by the normal
norm.  Recovering `h0` from that energy requires the additional scale
identity above.  Hence a Riesz projection by itself does not promote the
first symplectic variation to an energy identity.
