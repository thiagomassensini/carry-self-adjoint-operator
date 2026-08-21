# Continuation ledger: completed Green jet coefficients

This branch starts from the frozen merge of pull request #1:

```text
main merge: 8b2f1594f87503eb965b7eb801799d4c86f78963
PR head:   0978dbc61b14b39c178c04920a4d34fadbfaaae6
Lean:      v4.32.0
```

The frozen layer already supplies the exact completed scalar, its concrete
provenance-preserving C3 product ledger, the local division-free Green
representation interface, normalized Hilbert-valued Taylor jets, the
parity-split moment kernel, and the all-order finite Hankel consequence.

## Focus of this continuation

The next formal target is the coefficient identity currently exposed as the
`hcoefficients` hypothesis of
`hankelPair_posSemidef_of_completedNativeGreenFactors`:

```lean
IsComplexGreenWronskianMomentKernelGramRepresentation moments
  (completedGreenParityJet
    (normalizedCompletedGreenState
      completedNativeOperatorCharacteristic
      (completedNativeC3ProductLedgerState xiState)))
```

The intended derivation must stay at the level of relations already present
in the construction:

```text
two-variable division-free Green identity
  -> normalization at the nonzero Taylor center
  -> coefficient extraction in both variables
  -> even/even and odd/odd jet Gram blocks
  -> vanishing mixed-parity blocks
  -> unshifted and shifted moment kernels
```

The normalization, index shifts, factorials, conjugation order, and inner
product orientation must be derived explicitly.  They are not conventions to
be fitted after the fact.

## What is already closed

Once the coefficient identity is constructed, the existing theorem
`hankelPair_posSemidef_of_completedGreenMomentJets` gives, for every finite
order `N`, positive semidefiniteness of both

```text
hankelGram moments N
shiftedHankel moments N.
```

No order-specific positivity premise is needed.  The center nonvanishing
condition for the completed characteristic is also discharged internally in
`CompletedGreenMomentJets.lean`.

## Separate questions

Strict positivity still requires linear independence of the corresponding
finite even- and odd-jet prefixes.  The compatible infinite whitening tower,
its self-adjoint realization, and the passage from the finite functional
calculus are a different continuation and are not silently included in this
PR.

This ledger records a proof frontier.  It does not assert that the remaining
coefficient identity or any stronger spectral conclusion has already been
proved.

## Progress on this branch

`CompletedGreenJetCoefficientRecurrence.lean` now proves the algebraic core
in all orders.

First, the state normalization is derived without dividing the Wronskian:

```text
(2 * conj(F(w)) * F(z)) *
  inner(normalizedState(w), normalizedState(z))
= inner(state(w), state(z)).
```

Combining this with the local Green representation and cancelling only where
`F(z)` and `F(w)` are nonzero gives the exact polarized response identity

```text
(z - conj(w)) * inner(normalizedState(w), normalizedState(z))
= response(z) - conj(response(w)),

response(z) = Psi(z) / (2 * F(z)).
```

For the canonical companion `Psi = -F'`, this is one half of the negative
logarithmic derivative.  The existing division-free logarithmic-moment
recurrence has also been rewritten as the full convolution coefficient of
`q * Phi = -Phi'`; after `u = z^2`, its response coefficients are zero in
even degree and `moments(n)` in degree `2n+1`.

The centered reflection that makes this response odd is now a theorem rather
than a comment:

```text
operatorHeightParameter(-z) = 1 - operatorHeightParameter(z)
completedNativeOperatorCharacteristic(-z)
  = completedNativeOperatorCharacteristic(z).
```

The proof first identifies the operator scalar with the polynomially
regularized completed scalar on the open strip, then applies its exact
reflection relation.  No camera, cutoff, target height, or fitted coefficient
enters this parity theorem.

At the two-variable coefficient level, Lean now proves that

```text
(z - b) * K(z,b) = response(z) - response(b)
```

has a unique coefficient kernel.  Diagonal transport sends every coefficient
to the boundary coefficient of the same total degree.  Consequently, for all
`i,j`, not only for a fixed truncation,

```text
c(2i,   2j)   = moments(i+j)
c(2i+1, 2j+1) = moments(i+j+1)
c(2i,   2j+1) = 0
c(2i+1, 2j)   = 0.
```

Thus the parity blocks and both Hankel matrices are consequences of the
division-free coefficient transport; they are not independent positivity
assumptions.

## Exact remaining analytic seam

The end-to-end theorem no longer assumes an already assembled parity-split
Gram kernel.  Its remaining hypothesis is the narrower statement that the
ordinary Taylor-jet Gram coefficients of the concrete normalized Green state
satisfy the coefficient equation above.

To remove that last hypothesis, the concrete state realization must be shown
to admit the required local two-variable Taylor expansion (holomorphic in the
second variable and holomorphic after conjugating the first variable).  The
pointwise Green identity alone does not provide this regularity for an
arbitrary state map.  Once that analytic realization theorem is present,
coefficient uniqueness already closes every order simultaneously.

## Acceptance criteria

The continuation is ready to freeze only when:

1. the concrete coefficient identity no longer enters the end-to-end finite
   Hankel theorem as an external hypothesis;
2. every new declaration is imported by the root module and listed in the
   theorem registry when appropriate;
3. `scripts/audit.sh` passes with the committed toolchain and dependency
   manifest; and
4. the exact PR head passes the GitHub `Exact-checkout Lean theorem audit`.
