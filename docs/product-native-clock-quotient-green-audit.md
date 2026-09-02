# Product native clock quotient versus the Green defect

## Scope and conclusion

This audit tests whether the finite clock quotient found after commit
`76b5756` is forced by the native Green/product geometry, rather than merely
being a canonical positive projection which lowers the center energy.

The conclusion has two parts.

1. The clock quotient is completely canonical as a **real-axis central
   quotient**.  It exists both on the one-leg finite-prefix carrier and on
   the original two-leg C3 Hilbert carrier.  No weight is fitted.
2. It does **not** by itself close, or become forced by, the division-free
   two-point native Green identity.  The first failure is already the
   collision value of the native Wronskian.  Thus the raw native Green excess
   is not exhausted by a fixed pure-clock rank-one kernel correction.

No xi carrier, theta representation, zeros, confinement, `h1`, or all-order
construction is used.

## The finite quotient is an actual orthogonal projection

Let

```text
O3 = canonicalCompletedNativeC3CenterFiniteOrdinaryState,
L3 = canonicalCompletedNativeC3CenterFiniteLogJetState,
R3 = O3 - <L3,O3>/||L3||^2 * L3.
```

The new module defines

```text
Q3 = projection onto span(L3)^perp
   = I - P_span(L3).
```

Lean proves explicitly

```text
Q3 * Q3 = Q3,
adjoint Q3 = Q3,
ker Q3 = span{L3},
Q3 O3 = R3,
||Q3 x|| <= ||x||.
```

Thus the Schur removal in `76b5756` is not merely an energy formula.  It is
the literal canonical orthogonal quotient on the finite-prefix carrier.

For the varying finite ordinary prefix `O3(z)`, the projected kernel is

```text
Kquot(w,z) = <Q3 O3(w), Q3 O3(z)>.
```

With Lean's convention, conjugate-linear in the first slot and linear in the
second, the exact expansion is

```text
Kquot(w,z)
  = Kraw(w,z)
    - <L3,O3(z)> * <O3(w),L3> / ||L3||^2.
```

This fixes the orientation of the requested rank-one Schur term without a
new hypothesis.

## Lift to the original two-leg carrier

Write `l3` for the finite three-coordinate logarithmic leg.  The lifted
direction in `CanonicalCompletedC3HilbertCarrier` is

```text
T3 = (l3,l3).
```

The true physical real-height tangent is `-i T3`.  Reusing the existing
derivative theorem for `positiveDirichletGradient`, Lean proves for every
`n : Fin 3` and for both original port legs that

```text
d/dt canonicalCompletedOperatorC3HilbertState(t)[leg,n] | t=0
  = (-i T3)[leg,n].
```

Hence the lifted line is forced by differentiating the existing port along
the native real-height axis.  It is not chosen from the numerical value of
`h0`.

The corresponding rank-one quotient `Qport` satisfies

```text
Qport^2 = Qport,
adjoint Qport = Qport,
ker Qport = span{T3}.
```

Duplication cancels between the projection numerator and denominator, so the
two-leg projection coefficient is exactly the same `c3` as on the one-leg
prefix.  The center-collapse identities are

```text
collapse(Qport(rawState(0))) = sqrt(2) * R3,
collapse(Qport(g0))          = G(0)^(-1) * R3.
```

This is the smallest exact bridge requested between quotient-before-collapse
and the residual already computed in `76b5756`.

## Comparison with the actual native Green defect

The local audit `da09c10` uses the full two-leg raw kernel

```text
Kport_raw(w,z)
  = <canonicalCompletedOperatorC3HilbertState(w),
      canonicalCompletedOperatorC3HilbertState(z)>.
```

The new module projects this exact carrier and proves

```text
Kport_quot(w,z)
  = Kport_raw(w,z)
    - <T3,state(z)> * <state(w),T3> / ||T3||^2.
```

Define the raw native Green defect with the same orientation as the previous
audit:

```text
Delta_port(z,w)
  = W_G(z,w) - (z - conj(w)) Kport_raw(w,z).
```

Then the projected state is a division-free native Green state if and only
if the following concrete identity holds:

```text
Delta_port(z,w)
  = -(z - conj(w))
      * <T3,state(z)> * <state(w),T3> / ||T3||^2.
```

This is the precise candidate equality saying that the Green excess is pure
clock.

It fails the decisive collision test.  At `z = w = 0`, every fixed kernel
correction on the right is annihilated by `z - conj(w)`, while

```text
Delta_port(0,0) = W_G(0,0).
```

Lean therefore proves

```text
projected two-leg Green representation
  -> W_G(0,0) = 0
  -> deriv nativeHeightScalar 0 = 0.
```

This is exactly the same scalar obstruction isolated in `da09c10`; clock
projection does not remove it.  The prior numerical audit gives

```text
W_G(0,0) ~= -11.4569079517 i,
```

so the concrete normalization decisively rejects the pure-clock Green
identity.  The formal Lean result deliberately stops at the exact implication
to `G'(0)=0`, rather than importing a numerical nonvanishing claim as an
axiom.

## Why the center lift is not an off-diagonal complex clock jet

The real-axis tangent exists on both legs, but the original raw two-leg state
is not complex differentiable at the center.  Its first retained coordinate
contains

```text
exp(log(3) * im(z)) * holomorphicFactor(z),
```

with nonzero holomorphic factor at zero.  Reusing the radial-phase no-go,
Lean proves

```text
not DifferentiableAt C canonicalCompletedOperatorC3HilbertState 0.
```

Therefore the center collapse cannot be promoted silently to a holomorphic
off-diagonal clock tangent field.  This is the exact carrier/domain mismatch
which was hidden if one looked only at `collapse(g0)`.

## Status of the `h0` remainder

The center quotient still leaves the previously computed positive numerical
remainder

```text
h0 - ||R3||^2 / |G(0)|^2
  ~= 0.0215154513252357.
```

This audit does **not** interpret that remainder as xi energy.  The quotient
is structurally justified as the physical real-axis clock removal, but it is
not justified as the missing two-point Green/product compensation.  Returning
to an xi product carrier at this point would therefore overstate what has
been proved.

The first missing object is not another scalar weight.  It is a coupled
completion/collision contribution capable of cancelling the nonzero native
center Wronskian before the factor `z - conj(w)` annihilates ordinary kernel
corrections.  The already formalized weighted cancellation
`nativeXi_native_centerWronskians_weighted_cancel` remains the relevant exact
product-level clue.
