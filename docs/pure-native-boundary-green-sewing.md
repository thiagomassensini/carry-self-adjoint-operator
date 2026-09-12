# Pure native boundary Green sewing

This branch starts from `ec1bc2b4ce9ccac3bf8be7d82909470d6b4ec162` on
`agent/native-boundary-archimedean-dressing-separation` and keeps the
archimedean dressing out of the primary comparison.

## Exact residual

The branch defines

```lean
canonicalCompletedC3PureNativeBoundaryMismatch z w hz hw
```

by the literal formula

```text
greenForm (canonicalCompletedC3GammaBoundaryState z hz)
  (canonicalCompletedC3GammaBoundaryState w hw)
  - canonicalNativeUndressedGreenForm z w
```

where `canonicalNativeUndressedGreenForm` is the Green form of

```lean
canonicalNativeUndressedScalarBoundaryPair z
  = (nativeHeightScalarBoundaryCompanion z, nativeHeightScalar z).
```

The definition contains no `nativeXiCompletionFactor`, `A`, `A'`, Xi, or
completed operator characteristic.  The direct equivalence
`canonicalCompletedC3PureNativeBoundaryMismatch_eq_existing` identifies this
residual with the earlier `canonicalC3GammaNativeUndressedBoundaryGreenMismatch`.

## Common structured ancestor and orientation

The native scalar chart is defined as the cutoff-one normalized structured
TFVD projection

```text
(canonicalC3BracketTfvdNormalizedLogJetReadout 1 z,
 canonicalC3BracketTfvdNormalizedValueReadout 1 z).
```

The order is `(logJet,value)`, because this is the order consumed by
`greenForm`.  On the genuine strip,
`canonicalCompletedC3StructuredNativeScalarBoundaryPair_eq_nativeUndressed`
proves that this projection is exactly `(-N',N)` using the existing normalized
value and log-jet tail crosswalks.  The Gamma projection is independently
identified with
`canonicalCompletedC3StructuredGammaBoundaryState`, whose source is the
same `canonicalCompletedC3StructuredOnePointState` green port.  Therefore the
pure residual is the difference between two Green forms of two projections of
one structured state; it is not a dressed residual in disguise.

The exact structured comparison is
`canonicalCompletedC3PureNativeBoundaryMismatch_eq_sameStructuredGreenForm_sub`.
The division-free spelling is
`canonicalCompletedC3PureNativeBoundaryMismatch_eq_gammaReadout_sub_nativeWronskian`.
The latter identifies the two terms as the Gamma boundary readout and the
native scalar Wronskian without introducing a denominator.

## Status of sewing

The proposition

```lean
CanonicalCompletedC3PureNativeBoundaryGreenSewing
```

is the source-locus statement `G_Gamma = G_N`.  The theorem
`canonicalCompletedC3PureNativeBoundaryGreenSewing_iff_mismatch_zero` proves
that this gate is exactly pointwise vanishing of the explicit pure residual.
No theorem in the current pinned API proves that residual vanishes, and no
nonzero witness for the pure residual is claimed.  Thus the native sewing gate
remains open as one precisely named boundary-chart compatibility channel.

The residual is skew-Hermitian,
`canonicalCompletedC3PureNativeBoundaryMismatch_skew`, and its diagonal has
zero real part,
`canonicalCompletedC3PureNativeBoundaryMismatch_diagonal_re_eq_zero`.
These are structural checks, not a vanishing result.

As a post-hoc audit only, on the genuine strip the old dressed raw defect
satisfies

```text
pure native mismatch
  = raw Gamma--Wronskian defect
    + archimedean transport correction.
```

This is `canonicalCompletedC3PureNativeBoundaryMismatch_eq_rawDefect_add_archimedeanTransportCorrection`.
The correction is not used to define or prove the primary pure mismatch.

## Geometric carrier reused

The existing cancellation carrier is exposed by the alias
`CanonicalCompletedC3PureNativeCancellationBoundaryCarrier`.  Its exact
reconstruction is reused by
`canonicalCompletedC3PureNativeCancellationBoundaryState_reconstructs`.
The Gpre glued boundary pencil is reused by
`canonicalCompletedC3PureNativeCancellation_greenDefect_eq_verticalWronskian`,
which delegates to
`CPFormal.Analytic.Cp.nativeGpreHilbertGluedGreenDefect_eq_verticalWronskian`.
Thus source, Green response, boundary return, provenance, and TFVD
reconstruction remain in the same carrier; no channel is declared zero or
discarded.

No Hankel, Jacobi, HP, camera limit, atlas limit, numerical calculation, or
old carrier is used in this branch.  The next minimum gate is a
source-locus theorem identifying the Gamma boundary projection with the
undressed scalar Green projection (or an exact geometric decomposition of
this remaining mismatch).

## Outcome

**Outcome B (single explicit residual channel):** the pure native mismatch
has been isolated and related to the common structured state and the Gpre
cancellation carrier, but `G_Gamma = G_N` is not proved.  The remaining gate
is exactly
`canonicalCompletedC3PureNativeBoundaryMismatch = 0`; no archimedean factor
is hidden in that definition.
