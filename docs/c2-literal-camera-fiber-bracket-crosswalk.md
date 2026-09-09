# C2 literal camera to odd-core fiber bracket

This module records the arithmetic crosswalk between the literal C2 camera
stencil and the canonical odd-core fiber attached to an aligned index.

For `j`, the existing `C2AlignedBoxOddCoreCrosswalk` supplies

```text
m := c2AlignedIndexCore j
k := c2AlignedIndexDepth j
4 * (j + 1) = 2^k * m.
```

The new center theorem transports the upstream camera geometry
`alignedCenter 2 j` to this same value.  Consequently the formal C2 block is
definitionally the fiber bracket

```text
atom (2^k * m - 1) - 2 • atom (2^k * m) + atom (2^k * m + 1).
```

The evaluation theorem uses the existing `evalStencil` and
`centeredBracketStencil` bridge, so no second stencil representation is
introduced.

For the logarithmic observable, the centered term cancels exactly.  Under the
explicit condition `1 < 2^k * m`, the bracket is the sum of the two already
formalized leg defects

```text
log (1 - 1 / (2^k * m)) + log (1 + 1 / (2^k * m)).
```

The aligned camera specialization and its critical-amplitude multiple are
proved by reusing the odd-core factorization and the existing fiber log-defect
theorem.  The finite cutoff result is a pointwise reindexing of the existing
`finiteStencil` sum; the seed remains separate.

The closed form `log (1 - 1 / c^2)` is deliberately not added here.  The exact
two-leg defect sum is the primary statement and avoids introducing additional
real-log side conditions.
