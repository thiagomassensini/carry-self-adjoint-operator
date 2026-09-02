# Geometric low-order closure audit

## Outcome

The low-order Herglotz/Pick gate now has a complete geometric **spelling**,
but not yet a second, theta-free geometric proof.

The exact proved chain is

```text
theta-tail moment inequality
        |
        v
      h0 > 0 and h1 > 0
        |
        +--> positive first and third chiral-signature variations
        |
        +--> positive-definite 1x1 even and shifted Loewner defects
        |
        `--> eventual 2-point Herglotz/Pick positivity
```

The geometric identifications in the lower three lines predate the theta
estimate.  `CompletedNativeGeometricLowOrderClosure.lean` now packages their
unconditional consequences without hiding the theta dependency.

## What the defect geometry already proves

The formal development contains four genuinely geometric positive objects.

1. Every nonempty finite bracket-coupled Green bulk has strictly positive
   centered first variation, and these variations converge to a strictly
   positive infinite reflected Green energy.
2. The two-channel full-Wronskian kernel is an honest Hilbert Gram and hence
   positive semidefinite.
3. The coisometric Naimark ambient response kernel is positive definite on
   every finite family of distinct positive real exponents.
4. The completed logarithmic moments are exactly the odd Taylor readouts of
   the signed chiral block.  In particular, its first and third variations
   are `h0` and `h1`.

The obstruction is the word **signed**.  The scalar readout is the positive
chiral diagonal minus the negative chiral diagonal.  Positivity of the
uncollapsed block Gram therefore does not imply positivity of the readout.

## Why the raw coisometric flatness route does not close

The unregularized ambient sewing defect vanishes on the collapsing radial
grid because it contains the Hermitian separation as a factor.  After
division by that separation, its central limit is the nontrivial mismatch

```text
||normalized ambient response at 0||^2 - h0.
```

Thus first-order flatness is equivalent to identifying the naked ambient
gradient energy with `h0`; it is not a consequence of coisometry alone.

A high-precision diagnostic of the concrete quantities gives

```text
h0                                             ~= 0.0231049931154
||normalized naked ambient response at 0||^2  ~= 0.470904737591
```

These numbers are included only as a route diagnostic, not as a formal
inequality theorem.  They show that the old naked-gradient identification is
not the identity to pursue.  The same issue is visible in the exact product
ledger: completion curvature and the mixed completion/native jet cannot be
discarded.

## The honest independent geometric gate

The note on the old defect route points to the correct repair: scalarization
must occur only after completion dressing and triangular transport.  The
target should be an identity on an honest two-variable Hilbert carrier of the
form

```text
K_plus(w,z) - K_minus(w,z)
  = <D Psi(w), D Psi(z)>,
```

or equivalently a contraction identity

```text
I - C* C = D* D.
```

Here `Psi` must be the dressed product/completion state, not the naked
Dirichlet-gradient state.  The triangular cumulant recurrence must be applied
before taking scalar Taylor coefficients; at coefficient level the two
centered chiral contributions are already additive inverses, so a defect-Gram
argument there is circular.

For the current two-point gate, the minimal independent construction only
needs the first two nonzero defect jets.  Their squared norms must realize
`h0` and `h1`, with the second jet nonzero.  Differentiating the defect-Gram
identity would then give the first and third chiral variations, the two
one-dimensional Loewner defects, and hence the two-point Herglotz/Pick gate
without using the theta moment inequality.

## Recommended next attack

1. Build the completed/product-dressed two-variable chiral state before any
   diagonal or Taylor readout.
2. Define the candidate contraction between its negative and positive
   channels using the coisometric Naimark block.
3. Compute `I - C* C` through order three at the center, retaining the
   carrier/cross completion remainder.
4. Match the two defect jets to the existing first and third chiral signature
   coefficients.
5. Prove the second defect jet is nonzero.  This is the strict `h1 > 0` input.

This is now the precise remaining geometric problem.  Reusing the naked
ambient state or proving only that the unregularized ledger tends to zero
cannot close it.
