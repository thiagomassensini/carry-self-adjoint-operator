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

## State-free coefficient closure

The first formulation tried to identify the coefficients with iterated
derivatives of the given Hilbert-valued state.  That asks for more than the
Green representation actually supplies: the ambient inner-product space is
not assumed complete, and the state map is not independently assumed
analytic.

`GreenKernelCoefficientClosure.lean` now removes that artificial demand.  At
the canonical nonzero steps

```text
h_k = 1 / (k + 1) -> 0
```

it forms normalized forward differences

```text
Delta_(h_k)^n state(0) / (n! h_k^n).
```

Every such vector is an explicit finite linear combination of point-state
values; Lean proves the exact alternating binomial formula.  Therefore each
finite even or odd section is an honest Gram matrix before any limit is
taken.  Lean further proves the exact scalarization

```text
inner(forwardDifferenceJet(p), forwardDifferenceJet(q))
  = normalizedMixedForwardDifference(pointStateKernel, p, q).
```

Thus all subsequent coefficient work can be performed directly on the scalar
Green kernel.  Lean also proves that an entrywise limit of real positive
semidefinite matrices remains positive semidefinite.  Consequently, scalar
convergence of the forward-difference Gram entries to the parity-split moment
kernel implies both Hankel positivity towers at every finite order.

This is the RKHS/completion idea in a form that does not require constructing
or differentiating an auxiliary Hilbert space: finite point-state Grams are
used first, and only their scalar entries are passed to the limit.

## Exact remaining analytic seam

There are now two formal interfaces.  The earlier one asks directly for the
Taylor-jet coefficient equation.  The sharper one asks only for entrywise
scalar convergence of the canonical forward-difference Grams.

For unequal real sample points, the normalized polarized Green identity
rewrites the point-state kernel entirely in terms of the scalar response.  At
a collision `w = z` on the real axis its multiplier is
`z - conj(w) = 0`, so the cross-multiplied identity by itself reduces to
`0 = 0`.  Forward-difference Grams contain precisely such collision terms.

`CompletedGreenDiagonalClosure.lean` now proves that this degeneracy does not
leave a free diagonal once the normalized state is continuous.  Off the
diagonal, the kernel with one variable fixed at a real point is exactly the
slope of the scalar response.  The derivative theorem sends that slope to
the response derivative, while continuity of the state sends the same kernel
to its diagonal norm.  Uniqueness of limits gives the exact identity

```text
inner(normalizedState(x), normalizedState(x)) = response'(x).
```

At the centered origin the response is proved to vanish from the already
formalized even reflection of the completed characteristic; this is not a
new parity assumption.  The completed characteristic is also proved
holomorphic at the center, so local nonvanishing and continuity of the
normalization are discharged internally.  Therefore continuity of the
unnormalized concrete Green state is sufficient to force the center
diagonal.

The canonical enriched C3 Hilbert coordinate is now proved continuous at the
center directly from its literal finite Dirichlet coordinates.  Consequently
the full two-channel product ledger is continuous whenever its first factor
state is continuous.  Combining this with the two factor Green
representations gives the concrete theorem

```text
completedNativeC3ProductLedger_inner_self_zero_eq_responseDerivative.
```

Thus the product ledger's center diagonal is derived from the same factor
relations and continuity; it is not supplied independently.

Therefore the remaining proof has two scalar parts:

```text
off-diagonal Green response + exact binomial cancellation
continuous-state removable singularity + collision limit
  -> unique parity-split coefficient kernel.
```

The all-order coefficient recurrence already handles the last arrow once
those scalar coefficients exist: it identifies the even/even and odd/odd
moment blocks and kills the mixed blocks.

Thus no Hilbert-valued analytic regularity of an arbitrary state realization
needs to be postulated.  What remains is the scalar statement

```text
finite differences of the polarized Green response
  + all-order scalar control of the removable diagonal extension
  -> unique parity-split coefficient kernel.
```

The former pointwise diagonal ambiguity is therefore closed under the natural
continuity condition; no independent diagonal energy axiom or selected
minimal representative is needed.  The causal bracket theorem remains the
geometric uniqueness statement for the depth-indexed state, but it is not
needed merely to fill this scalar collision value.

What remains is genuinely all-order rather than pointwise: identify the
mixed normalized finite differences of the now continuously extended scalar
kernel with the coefficient kernel fixed by the recurrence.  For the concrete
product ledger one must also supply continuity of the factor-state
realization used by its first Hilbert channel.

This is a strictly smaller seam than the former external `hcoeff` premise.
The diagonal value itself is no longer an explicit hypothesis, but the
all-order scalar finite-difference limit is still an explicit hypothesis in
the newest positivity theorem, so the PR remains draft until that limit is
discharged for the concrete normalized Green state.

## Acceptance criteria

The continuation is ready to freeze only when:

1. neither the concrete coefficient identity nor the forward-difference Gram
   limit enters the concrete end-to-end finite Hankel theorem as an external
   hypothesis;
2. every new declaration is imported by the root module and listed in the
   theorem registry when appropriate;
3. `scripts/audit.sh` passes with the committed toolchain and dependency
   manifest; and
4. the exact PR head passes the GitHub `Exact-checkout Lean theorem audit`.
