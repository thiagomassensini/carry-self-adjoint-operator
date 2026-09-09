# Prime-depth → TFVD log-jet crosswalk

## Provenance

- Base: `2bc8842714f9cd05fdeb22d6d25ffb0c3182e1f6`
- Branch: `agent/prime-depth-tfvd-logjet-crosswalk`
- The pinned `CPFormal` package is `65d50f6db1208708e109982ba97e1d51d3039956`.

The later `primos` modules named `CpPrimeTowerCarryMangoldtBridge` and
`CpPrimeDepthLogWaveBridge` are not exported by this pin.  The implementation
therefore does not change the dependency or copy those modules.  It uses the
current `CPFormal.Carry.Positional.positionalDepth` and
`CPFormal.Carry.Cp.log_eq_sum_vertical` APIs and exposes the smallest local
adapter, `primeDepthLogLedger`,

```text
∑ p ∈ n.primeFactors, (positionalDepth p n : ℝ) * Real.log p.
```

The adapter is a direct finite sum over the existing prime-camera depth API;
it is not a second factorization theory.

## Arithmetic bridge

For `n ≠ 0` and a prime `p`,

```text
positionalDepth p n = n.factorization p
```

by `Nat.multiplicity_eq_factorization`.  Consequently the main theorem is

```text
primeDepthLogLedger_eq_log
```

which states

```text
∑ p ∈ n.primeFactors, (positionalDepth p n : ℝ) * Real.log p = Real.log n.
```

The proof rewrites the prime support as `n.factorization.support` and reuses
`CPFormal.Carry.Cp.log_eq_sum_vertical`.  The companion theorem
`primeDepthLogLedger_eq_cameraVerticalLedger` identifies the same sum with the
existing camera-atlas vertical voice (`cameraVertical n p`).

## Dirichlet and slope channels

The following equalities preserve the native index shifts already present in
the pinned definitions:

- `positiveLogDirichletValue_eq_primeDepthLogLedger_mul` replaces the factor
  `log (n + 1)` by the ledger at `n + 1`.
- `natLogDirichletTerm_eq_primeDepthLogLedger_mul` replaces `log n` for
  positive `n`.
- `positiveLogDirichletGradient_eq_primeDepthSlope` replaces both factors in
  the consecutive log gradient, at `n + 2` and `n + 1`.
- `positiveLogDirichletGradient_nativeLine_eq_primeDepthPackagedNativeLogSlope`
  gives the same replacement after the existing native-line packaging.

No new Dirichlet generator was introduced.  These are coefficient identities
for the existing generator.

## All orders and TFVD state

For every Taylor order, the theorem
`nativeLogDirichletSlopeTaylorCoefficient_eq_primeDepthLedger_form` rewrites
both logarithmic factors in the existing
`nativeLogDirichletSlopeTaylorCoefficient`.  The ordinary amplitude and the
Taylor normalization remain unchanged.

The finite state
`finitePrimeDepthGeneratedLogSlopePrefixState` uses the ledger in the same
`CarryVerticalL2` and with the same packaged native samples as
`finitePackagedNativeLogSlopePrefixState`.  The exact state equality is

```text
finitePrimeDepthGeneratedLogSlopePrefixState M time
  = finitePackagedNativeLogSlopePrefixState M time
  = canonicalCompletedC3LogJetPrefixState (nativeLine time) M.
```

The first equality is
`finitePrimeDepthGeneratedLogSlopePrefixState_eq_nativeLogSlope`; the second
is the existing
`finitePackagedNativeLogSlopePrefixState_eq_completedTfvdLogJetPrefix`.

The enriched state
`finitePrimeDepthGeneratedC3HilbertPrefixState` changes only the log channel
and retains the ordinary channel verbatim.  It is exactly
`canonicalCompletedC3HilbertPrefixState` by
`finitePrimeDepthGeneratedC3HilbertPrefixState_eq_completedTfvd`.

The generic theorem
`primeDepthLogJetPrefix_readout_eq_canonical` transports any existing map from
the prefix through this equality.  Thus weighted bracket, Green, and trace
maps need no duplicated pipeline: rewriting the input state gives the
canonical readout.  The existing TFVD/Green equalities remain the authoritative
port statements, in particular
`finitePackagedNativeLogSlopePrefixState_eq_completedTfvdLogJetPrefix` and
`canonicalCompletedTfvdGreenPortState_eq_bracketGreenPort`.

The existing raw-jet convergence theorem
`canonicalCompletedC3DirichletGradientCoefficientRawJet_tendsto` was not
reproved or altered.  Its Taylor endpoint is now also available in the
prime-depth form above.

## C2 specialization

The existing C2 fiber identity is strengthened by replacing the core logarithm
with its prime-depth ledger:

```text
c2Fiber_centeredLog_eq_depth_add_primeCoreLedger

Real.log (c2FiberPoint m ε k - ε)
  = (k : ℝ) * Real.log 2 + primeDepthLogLedger m.
```

For the unshifted center this becomes

```text
c2Fiber_center_log_eq_depth_add_primeCoreLedger

Real.log (((2 ^ k * m : ℕ) : ℝ))
  = (k : ℝ) * Real.log 2 + primeDepthLogLedger m.
```

The aligned camera center has the corresponding form

```text
c2AlignedCenter_log_eq_currentDepth_add_primeCoreLedger

Real.log ((4 * (j + 1) : ℕ) : ℝ)
  = (c2AlignedIndexDepth j : ℝ) * Real.log 2
      + primeDepthLogLedger (c2AlignedIndexCore j).
```

The Newton/Green specialization is
`c2Fiber_centeredLog_amplitude_eq_green_and_primeDepthSeed`:

```text
log(centered fiber) * criticalAmplitude
  = log 2 * newtonJet 1
      + primeDepthLogLedger m * newtonJet 0.
```

It reuses the existing `c2Fiber_centeredLog_amplitude_eq_green_and_seed`; only
the exact core identity is rewritten.  No moment, Gram, or spectral claim is
made.

## What this round proves

The kernel-checked chain is

```text
prime positional depth
  → primeDepthLogLedger
  → Real.log / Dirichlet log term
  → consecutive native log slope
  → finite CarryVerticalL2 log prefix
  → existing completed TFVD state and readouts.
```

For C2 it is

```text
aligned center
  → (c2AlignedIndexCore, c2AlignedIndexDepth)
  → depth contribution k * log 2
  → prime-depth ledger of the odd core
  → existing Newton/Green modes.
```

This is an arithmetic/geometric crosswalk.  It does not identify a horizontal
subspace of one base with a vertical subspace of another, and it does not
introduce Hankel, Jacobi, Gamma, whitening, or a new Hilbert carrier.

## Axiom audit

The audit module
`CarrySelfAdjointOperator/PrimeDepthTfvdLogJetCrosswalkAudit.lean` prints the
axioms for all principal declarations.  The output for every one is exactly

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, `admit`, or newly declared axiom.

## Validation

The following completed successfully on the remote checkout:

```text
lake build CarrySelfAdjointOperator
lake build CarrySelfAdjointOperator.Audit
lake build CarrySelfAdjointOperator.KernelConstructionAudit
python3 -m json.tool audit/theorem-registry.json
```

The full project build was also run after integration and completed with exit
code `0` (`9475 jobs`).  Existing `ring` suggestions in upstream files are
informational warnings and are unrelated to this module.

`git diff --check` and `bash scripts/audit.sh` are the final pre-push checks;
their results are recorded in the task report together with the commit SHA.

## Next Geometric/Hilbert Gate

1. **Is the log-jet completely reconstructed from prime depth?** Yes for every
   positive integer coefficient and for every finite TFVD prefix.  The
   `n + 1` shift in the positive API is preserved explicitly.
2. **Before scalarization?** Yes.  The equality is between
   `CarryVerticalL2` states (and the enriched two-channel state), before any
   bracket, Green, trace, or scalar readout.
3. **Same carrier?** Yes: `finitePrimeDepthGeneratedLogSlopePrefixState` and
   the existing state both use `CarryVerticalL2`.
4. **Are weighted bracket and Green response preserved?** Any map applied to
   the prefix is preserved by `primeDepthLogJetPrefix_readout_eq_canonical`.
   The existing completed TFVD/Green port theorems then apply unchanged.  No
   new port was constructed.
5. **C2 separation?** Yes.  The current depth is the explicit
   `(k : ℝ) * log 2` term; the core is the exact sum of prime positional-depth
   charges.
6. **Subspace/projection API for the stronger horizontal/vertical claim?** The
   pin contains `factorizationVector`, `cameraVerticalLine`,
   `cameraHorizontalSpace`, and `isCompl_cameraVertical_horizontal` in
   `CpMultibaseCameraAtlasHilbert`.  Those are algebraic factorization-space
   results; no theorem in this round identifies them with the TFVD vertical
   `CarryVerticalL2` or with a cross-camera projection.
7. **Minimum next theorem for multibase orthogonalization?** A typed map from
   the factorization camera-log space (or its finite-support restriction) into
   the existing TFVD carrier, together with a theorem that its log evaluation
   agrees with the packaged log channel.  The current equality of scalar
   ledgers is not such an isometric/subspace map, so the Gram/Hilbert gate
   remains open.

## Residual pin boundary

The requested named `primos` bridge declarations are absent from the pinned
dependency.  This is why the local theorem is named `primeDepthLogLedger`
rather than pretending that an unavailable `primeDepthLogCoordinate` was
imported.  The arithmetic identity itself is proved in the current kernel;
only the upstream module name/cross-repository export remains a packaging
residual.
