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

## Acceptance criteria

The continuation is ready to freeze only when:

1. the concrete coefficient identity no longer enters the end-to-end finite
   Hankel theorem as an external hypothesis;
2. every new declaration is imported by the root module and listed in the
   theorem registry when appropriate;
3. `scripts/audit.sh` passes with the committed toolchain and dependency
   manifest; and
4. the exact PR head passes the GitHub `Exact-checkout Lean theorem audit`.
