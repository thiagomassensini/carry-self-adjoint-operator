# Crosswalk: C2 aligned boxes and odd-core fibers

This module starts from the pinned `CPFormal` APIs and the state at commit
`add2621dcfbfd8e394e7ca281dbb418e3d9370e7`.

## Exact factorization

For every aligned index `j`, the reused positional-depth theorem gives

```text
j + 1 = 2^r * m,    r = positionalDepth 2 (j + 1),    ¬ 2 ∣ m.
```

The module sets `k = r + 2`, accounting for the C2 center factor `4`, and
proves

```text
4 * (j + 1)     = 2^k * m
4 * (j + 1) - 1 = 2^k * m - 1
4 * (j + 1) + 1 = 2^k * m + 1.
```

Here `m` is `c2AlignedIndexCore j` and `k` is
`c2AlignedIndexDepth j`.  The left and right incidence APIs from
`CPFormal.Carry.C2AlignedBox` are reused directly.

## Depth and fibers

The center valuation is exactly `k`, using
`padicValNat_base_pow_mul` and the old `effectiveDepth_eq_centerDepth` result.
Both aligned legs therefore have effective depth `k` and are identified with
`c2FiberPoint m (-1) k` and `c2FiberPoint m 1 k` after the necessary casts.

The center logarithm transports to the existing fiber theorem:

```text
log (4 * (j + 1)) = k * log 2 + log m.
```

The existing Newton/Green amplitude identity is also applied at this same
`(m,k)` pair.  No new moment, operator, or spectral hypothesis is introduced.

## Leg correction

The literal legs retain the exact correction already proved for fibers:

```text
log (2^k*m + ε) - log (2^k*m)
  = log (1 + ε / (2^k*m)).
```

The new left and right theorems instantiate this for `ε = -1` and `ε = 1`.
The correction is not discarded or approximated.

## Reindexing

`weighted_reindex_alignedBox_fiber_terms` is a named specialization of the
existing exact `weighted_reindex_alignedBox` theorem.  The pointwise companion
theorems `c2LeftIncidenceTerm_eq_fiber` and
`c2RightIncidenceTerm_eq_fiber` rewrite each incidence term using the new
`(m,k,ε)` coordinates while preserving the old finite sum and its exact
aligned-box coverage.

The general inverse enumeration from arbitrary `(m,k,ε)` back to a unique
aligned index is intentionally not added here; it would require an additional
finite-domain statement beyond the existing aligned-box API.

## Provenance and audit

The source modules are:

* `C2AlignedBoxOddCoreCrosswalk.lean`
* `C2AlignedBoxOddCoreCrosswalkAudit.lean`

The old declarations reused are `C2AlignedBox`, `C2Depth`,
`C2WeightedReindex`, `C2OddCorePushforward`, and
`PositionalDecomposition`.  The new audit accepts only the project's standard
axioms `propext`, `Classical.choice`, and `Quot.sound`.
