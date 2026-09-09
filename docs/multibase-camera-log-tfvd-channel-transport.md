# Multibase camera log–TFVD channel transport

This crosswalk starts from the exact prime-depth ledger already present in the
pin.  It keeps the camera label and the vertical sample coordinate distinct.
The carrier used for the finite channel family is

```lean
ℕ →₀ CarryVerticalL2
```

The outer index is a camera label.  Each value is an existing vertical TFVD
state.  This is an algebraic finite-support carrier; it does not introduce a
new completion, a camera-to-vertical index identification, or an orthogonal
metric on the outer family.

## Camera-resolved ledger and scalar synthesis

`cameraLogContributionVector n` has coordinate

```text
n.factorization p * Real.log p
```

and finite support contained in the factorization support of `n`.  The linear
map `cameraLogContributionSynthesis` sums these coordinates.  The kernel
equalities are:

```text
cameraLogContributionSynthesis_cameraLogContributionVectorComplex
cameraLogContributionSynthesis_eq_primeDepthLogLedger
cameraLogContributionSynthesis_eq_log
```

Thus the prime voices are retained until the explicit synthesis map.  The
complex version supplies the coefficient type used by the Dirichlet and TFVD
channels.  The positive Dirichlet value and its consecutive gradient are lifted
to finitely supported complex camera vectors by
`cameraResolvedLogDirichletValue` and
`cameraResolvedLogDirichletGradient`.  Their syntheses are exactly
`positiveLogDirichletValue` and `positiveLogDirichletGradient`, including the
existing `n + 1` and `n + 2` shifts.

The atlas decomposition is retained coefficientwise:

```text
cameraLogContributionVector n
  = cameraLogVerticalContribution n p
  + cameraLogHorizontalContribution n p
```

The two terms lie in `cameraVerticalLine p` and
`cameraHorizontalSpace p`, respectively.  No orthogonality is inferred from
this algebraic `IsCompl` decomposition.  The existing blind direction remains
explicit: `logEvalBlindVector ≠ 0` while
`logEval logEvalBlindVector = 0`.

## Multichannel TFVD prefix

`finiteCameraResolvedLogSlopePrefixState M time` stores, for each camera label,
the existing `CarryVerticalL2` realization of the finite log-gradient prefix.
Its support is a finite union of the factorization supports occurring in the
cutoff.  The synthesis theorem is:

```text
finiteCameraResolvedLogSlopePrefixState_synthesis_eq_primeDepth
finiteCameraResolvedLogSlopePrefixState_synthesis_eq_completedTfvd
```

Consequently the scalar synthesis of the camera-resolved state is exactly the
already existing `canonicalCompletedC3LogJetPrefixState (nativeLine time) M`.
No new vertical Hilbert space is constructed.

The finite analysis and reconstruction maps act coordinatewise through
`Finsupp.mapRange.linearMap`.  The generic theorem
`finsupp_synthesis_mapRange_commutes` gives the two commuting squares

```text
analysis after synthesis = synthesis after channelwise analysis
reconstruction after synthesis = synthesis after channelwise reconstruction.
```

Together with the existing
`nativeGpreFiniteTfvdReconstruction_analysis`, this yields
`cameraChannelTfvdReconstruction_analysis_synthesis`.  The TFVD identity itself
is reused; it is not reproved or changed.

## C2 specialization

For an odd core `m`, the existing factorization lemmas show that camera `2`
contributes no factorization coordinate to `m`.  For the center `2^k * m`:

```text
cameraLogContributionVector (2^k * m) 2 = k * Real.log 2
```

and the horizontal contribution of the core synthesizes to
`primeDepthLogLedger m`.  Hence

```text
log (2^k * m)
  = camera-2 contribution
  + synthesized horizontal core contribution.
```

The core term is in `cameraHorizontalSpace 2` by the existing atlas API.  This
is the precise vertical-2 plus prime-core ledger decomposition; it does not
claim that a horizontal subspace is a vertical subspace of another base.

## What this rodada proves

The kernel-checked result is the genealogy

```text
prime depth voices
  → finite camera-resolved ledger
  → camera-resolved Dirichlet value/gradient
  → multichannel CarryVerticalL2 prefix
  → existing scalar completed TFVD/Green pipeline.
```

The construction preserves camera voices until the final linear synthesis and
preserves the blind scalar direction.  It proves no Gram/moment identity,
whitening, spectral statement, or orthogonality claim.

## Next Orthogonalization Gate

1. **Carrier:** `ℕ →₀ CarryVerticalL2`, finite-support and algebraic.
2. **Separate voices:** yes, the outer camera coordinate is retained until
   `cameraChannelSynthesis`.
3. **Exact scalar recovery:** yes, by
   `finiteCameraResolvedLogSlopePrefixState_synthesis_eq_completedTfvd`.
4. **Blind direction:** the existing `logEvalBlindVector` is nonzero before its
   scalar readout and is killed by `logEval`; no embedding into the outer TFVD
   carrier is asserted.
5. **`V_p ⊕ H_p`:** transported for the finite real ledger at coefficient level;
   no equality of submodules with TFVD states is claimed.
6. **Outer inner product:** no natural `InnerProductSpace` on the outer
   finitely-supported family is supplied by this module.
7. **Cross-camera orthogonality:** not proved and not implied by `IsCompl`.
8. **Whitening/coisometry:** the finite atlas has its own camera Gram/readout
   APIs, but no theorem here identifies them with this channel carrier.
9. **Relations:** `cameraGram` and visible/blind data remain atlas-level;
   BR2 incidence transport and Naimark readout remain existing downstream
   structures, with no new isometry asserted between them and the channel
   family.
10. **Minimum next theorem:** provide a semantically justified outer inner
    product (or coisometry) whose Gram is the existing `cameraGram`, then prove
    that the single-camera support and its complement form an orthogonal Hilbert
    decomposition.  This is separate from the present algebraic direct sum.
