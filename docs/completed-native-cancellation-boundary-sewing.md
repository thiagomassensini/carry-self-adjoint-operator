# Completed native cancellation boundary sewing

This branch records the cancellation carrier forced by the finite C3/TFVD
construction. It does not claim the unresolved scalar Gamma sewing; it keeps
that equality as an explicit, kernel-checked residual.

## Finite cancellation data

For a supported base `base`, cutoff `cutoff`, and parameter `s`,
`CanonicalCompletedC3FiniteCancellationData base cutoff s` stores four
`CarryVerticalL2` states:

- `source` is `canonicalCompletedC3DirichletGradientBracketSource base cutoff s`;
- `greenResponse` is `canonicalCompletedC3DirichletGradientBracketGreenResponse base cutoff s`, definitionally the weighted Green response of that source;
- `boundaryReturn` is `canonicalCompletedC3DirichletGradientPrefixBoundaryReturn hbase cutoff s`;
- `prefixState` is the finite prefix at `finiteCameraWindow base cutoff + 1`.

The reconstruction field is exactly the existing theorem
`canonicalCompletedC3DirichletGradient_cancellationGreen_add_boundary_eq_prefix`.
Thus the response and boundary return are retained as separate pieces and
reconstruct the prefix; neither is declared zero.

## Completed carrier and native glued pencil

The completed cancellation carrier is the existing two-channel Hilbert carrier
`CanonicalCompletedC3CausalGreenBoundaryCarrier`, namely
`WithLp 2 (CarryVerticalL2 × CarryVerticalL2)`. Its first coordinate is the
completed causal Green response and its second coordinate is the completed
boundary return. The existing `canonicalCompletedC3CausalGreenBoundarySum`
recovers the ordinary completed TFVD state, and
`canonicalCompletedC3DirichletGradientCausalGreenBoundaryState_sum` proves this
reconstruction.

For a finite CPFormal provenance context `S`,
`canonicalCompletedC3CancellationNativeBoundaryPencil` pulls the existing native
G_pre glued boundary pencil back along that sum map. Consequently the value and
flux traces act on the reconstructed state while the provenance coordinates stay
inside `NativeGpreHilbertGluedBoundary S`.

The theorem
`canonicalCompletedC3CancellationNativeBoundaryPencil_greenDefect_eq_verticalWronskian`
is a direct specialization of
`nativeGpreHilbertGluedGreenDefect_eq_verticalWronskian`. It proves that the
full glued Green defect equals the weighted vertical Wronskian of the two
reconstructed states. This is the formal cancellation mechanism: provenance
coordinates are present and cancel inside the Green form supplied by CPFormal.
The corresponding state theorem and the finite-prefix reconstruction theorem
are also exported by the new module.

## Scalar completed trace

`CanonicalCompletedC3CancellationTraceCarrier` augments the two-channel
carrier with the existing scalar boundary pair. The canonical trace map is the
second projection, so it is a projection of the packaged state rather than a
new scalarization of the Green response. The theorem
`canonicalCompletedC3CancellationTraceState_trace_eq_scalarPair` is definitional,
and on the genuine critical strip
`canonicalCompletedC3CancellationTraceState_trace_eq_F_negFprime` gives the exact
orientation

```text
(-deriv completedNativeOperatorCharacteristic z,
 completedNativeOperatorCharacteristic z).
```

No new completion factor, source correction, or normalization is introduced.
The scalar pair is the already completed `(Psi,F)` boundary chart.

## Exact residual and status

The theorem
`canonicalCompletedC3CancellationTraceGlue_difference_eq_rawDefect` rewrites
the difference between the Gamma boundary Green form and the scalar trace Green
form as
`canonicalCompletedC3RawGammaWronskianDefect z w hz hw`.
The iff theorem
`canonicalCompletedC3CancellationTraceGlue_iff_rawDefect_zero` records that the
scalar trace sewing is equivalent to this residual being zero.

Therefore this branch closes the finite cancellation transport, the completed
two-channel carrier, and the provenance-preserving glued Green identity. It
does not prove `CanonicalNativeBoundaryCompletedReadoutSewing`, does not prove
that `canonicalCompletedC3RawGammaWronskianDefect` vanishes, and does not yet
make the Gamma kernel equal to `dslope`. The remaining seam is the exact
Green-form compatibility of the completed scalar trace with the Gamma chart;
no individual provenance or boundary channel is discarded to obtain it.

No camera atlas, atlas limit, moment sequence, Hankel matrix, Jacobi operator,
or HP construction is used by this module. No zero, zeta, or numerical input is
used.
