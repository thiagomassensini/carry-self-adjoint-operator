# Completed native polarized TFVD/Green moment kernel

## Scope and outcome

This branch audits the two-parameter TFVD/Green route from the carry.  It does
not introduce a moment-defined vector, a new Hilbert completion, or a second
positive carrier.  The primary outcome is **Outcome C: exact residual
isolated**.  The local polarized ledger, its finite-head decomposition, and the
independent completion/tail correction are all exact.  The remaining equality
needed for a positive native Gram is the vanishing of the explicit completed
Wronskian-minus-Green residual; the current dependency graph does not prove
that vanishing.

The branch does not use `HasCompletedNativeRealAxisNormalizedGreenKernel` as a
hypothesis, and it does not claim `greenJetShiftedHankelFactorizationDefect =
0`.

## Gap map

| step | status | declaration/evidence |
|---|---|---|
| two-parameter polarized edge wedge | **CLOSED EXISTING / packaged THIS BRANCH** | `mixedScalarBoundaryWedge_eq_localTwoLeg_add_cross_add_residualCorrection`, wrapped by `canonicalNativePolarizedTfvdGreen_local_identity` |
| four local transport legs | **CLOSED EXISTING** | `ReflectedBoundarySynthesisData` and `mixedBoundaryResidualCorrection` |
| ordered cross provenance | **CLOSED EXISTING** | `twoLegBoundaryCrossProvenance` |
| finite two-parameter TFVD transport | **CLOSED EXISTING** | `finiteC3EnrichedTfvdPairBoundary_eq_greenForm_add_provenance_twoParameter` |
| finite head decomposition | **CLOSED EXISTING / packaged THIS BRANCH** | `canonicalNativePolarizedTfvdGreen_head_identity` |
| completion/head-tail decomposition | **CLOSED EXISTING / packaged THIS BRANCH** | `canonicalNativePolarizedTfvdGreen_completion_identity` |
| explicit total defect | **CLOSED THIS BRANCH** | `canonicalNativePolarizedTfvdGreenMomentKernelDefect_eq_ledger_total` |
| completed raw Wronskian minus finite Green | **CLOSED EXISTING / packaged THIS BRANCH** | `canonicalNativePolarizedTfvdGreenMomentKernelDefect_eq_wronskian_sub_green` |
| defect limit | **CLOSED EXISTING / packaged THIS BRANCH** | `canonicalNativePolarizedTfvdGreenMomentKernelDefect_tendsto` |
| completed raw Wronskian = completed Green | **OPEN** | equivalent to zero defect limit by `canonicalNativePolarizedTfvdGreenMomentKernel_eq_iff_defect_limit_zero` |
| positive native vector `beta` | **OPEN** | no concrete TFVD/Green Hilbert state with the required Gram is available |
| Gram representation of the completed Wronskian | **OPEN** | no unconditional `IsGreenWronskianMomentKernelGramRepresentation` |
| shifted Hankel factorization | **CONDITIONAL EXISTING** | `greenJetOddPrefixGram_eq_shiftedHankel_of_greenRepresentation` |
| unconditional `K_N = B_N^* B_N` | **OPEN** | requires the missing Gram representation |
| PSD/PosDef of shifted Hankel from this route | **OPEN/CONDITIONAL** | geometric prefix Gram is PSD, but comparison with shifted Hankel is conditional |
| Jacobi/height consequence | **CONDITIONAL** | existing downstream theorems consume the Gram/strictness hypotheses |

## Exact polarized ledger

The local wedge is the existing complex sesquilinear convention

```lean
mixedScalarBoundaryWedge valueZ companionZ valueW companionW :=
  companionZ * (starRingEnd ℂ) valueW -
    valueZ * (starRingEnd ℂ) companionW
```

Thus, for value `F` and companion `Psi`, it is
`Psi(z) * conj(F(w)) - F(z) * conj(Psi(w))`.  The new wrapper
`canonicalNativePolarizedTfvdGreen_local_identity` preserves the four legs
`left`, `right`, `jetLeft`, `jetRight`, the ordered cross term
`twoLegBoundaryCrossProvenance`, and the four readout residuals packed by
`mixedBoundaryResidualCorrection`.

At the finite level the direct parameter is `w` and the reflected parameter is
`reflectedParameter z`; the Green orientation is the existing
`greenForm`, namely the symplectic boundary pairing (for a pair `(a,b)` and
`(c,d)`, `⟪(a,b),(c,d)⟫_G = ⟪b,c⟫ - ⟪a,d⟫` in the code's orientation).
The exact finite-head wrapper is
`canonicalNativePolarizedTfvdGreen_head_identity`:

```text
mixedScalarBoundaryWedge(finiteBracketedDirichletChart z,
                         finiteCanonicalLogBracketChart z,
                         finiteBracketedDirichletChart w,
                         finiteCanonicalLogBracketChart w)
  = greenForm(finiteC3GenuineBracketGreenBoundaryPair w,
              finiteC3GenuineBracketGreenBoundaryPair (reflectedParameter z))
    + canonicalC3FiniteMixedStructuralDefect M z w.
```

The canonical ledger has four fields:

* `greenProvenance := canonicalMixedBoundaryGreenProvenance`;
* `crossProvenance := canonicalMixedBoundaryCrossProvenance`;
* `readoutResidual := canonicalMixedBoundaryReadoutResidualCorrection`;
* `completion := canonicalC3MixedTailCompletionDefect`.

The exact theorem
`canonicalNativePolarizedTfvdGreenMomentKernelDefect_eq_ledger_total`
shows that the named defect is their sum.  The dormant Green compensation is
retained in the underlying `TfvdSameSGreenProvenanceChannels` ledger; it is not
silently deleted by this grouping.

The completion identity is exact for every cutoff:
`canonicalCompletedC3RawMixedWronskian = finite mixed head +
canonicalC3MixedTailCompletionDefect`.  The tail correction tends to zero in
the existing strip, but this alone does not identify the completed Green
kernel.

## Completed residual

The branch defines

```lean
def canonicalNativePolarizedTfvdGreenMomentKernelDefect
    (M : ℕ) (z w : ℂ) : ℂ :=
  canonicalC3FiniteMixedTotalDefect M z w
```

This definition is entirely TFVD/Green-side: it mentions no moments, Hankel
matrices, Cholesky factors, or a pre-existing Green-kernel interface.  The
exact finite relation is

```lean
canonicalNativePolarizedTfvdGreenMomentKernelDefect M z w =
  canonicalCompletedC3RawMixedWronskian z w -
    greenForm (finiteC3GenuineBracketGreenBoundaryPair (3 * M) w)
      (finiteC3GenuineBracketGreenBoundaryPair
        (3 * M) (reflectedParameter z))
```

under the existing real-part hypotheses.  In the completed strip, the defect
converges to

```text
canonicalCompletedC3RawMixedWronskian z w
  - canonicalCompletedC3MixedRadialGreenKernel z w ... ...
```

by `canonicalNativePolarizedTfvdGreenMomentKernelDefect_tendsto`.  The theorem
`canonicalNativePolarizedTfvdGreenMomentKernel_eq_iff_defect_limit_zero` makes
the remaining seam exact: completed raw Wronskian equals completed reflected
Green if and only if this defect tends to zero.

No theorem in the current graph identifies the residual with zero.  It is a
sum of finite structural provenance/cross/readout channels plus the separate
completion channel, and its completed limit is the raw-minus-Green difference.
This is an explicit residual, not an assertion that positivity is merely
unknown.

## What was and was not constructed

The following were **not** constructed because the present API does not supply
the required identity:

* a `canonicalNativeTfvdGreenPositiveState` whose inner product is the
  completed raw Wronskian divided difference;
* a `canonicalNativeTfvdGreenJet` built only from such a state;
* an unconditional
  `IsGreenWronskianMomentKernelGramRepresentation`;
* an unconditional vanishing of
  `greenJetShiftedHankelFactorizationDefect`;
* an unconditional `K_N = B_N^* B_N` comparison with the shifted Hankel.

The adapter theorem
`canonicalNativePolarizedTfvdGreenMomentKernel_implies_shiftedFactorization`
only says that an independently supplied genuine Gram representation is
consumed by the already-existing shifted-Hankel theorem.  It is intentionally
not a proof of that hypothesis.

The geometric odd-prefix Gram itself remains PSD by the existing generic
result, but its equality with the shifted Hankel is still conditional on the
missing native Gram representation.  Strict positivity and the Jacobi/
self-adjoint height route therefore remain conditional on the same missing
representation and the existing concrete independence assumptions.

## Camera/primality and no-go boundaries

No `sixCamera`, camera limit, camera growth, or camera-dependent construction is
used in the new public theorem statements.  No Atlas camera is needed.  The
new wrappers use the already camera-free C3/TFVD transport.  The one-parameter
CPFormal finite theorem underneath the archaeology carries a prime parameter
for its historical representation, but no prime property is used by the new
polarized wrappers or by the residual theorem.

No `HasCompletedNativeRealAxisNormalizedGreenKernel` hypothesis is used to
define the defect.  No refuted positive carriers are used as the target:
the ordinary/logJet/residual static sum, old Green Taylor carrier, and
completed C3 positive sewing carrier are not asserted to be the native Gram.
The only import of `CompletedNativeTfvdGreenShiftedHankelFactorization` is for
the explicit conditional adapter.

The relevant prior no-go is therefore respected: the scalar completed
Wronskian/Green equality is not manufactured from a carrier already known to
be degenerate or to overcount the ordinary energy.  The remaining task is to
construct the actual lossless TFVD/Green state or prove the displayed residual
vanishes by a genuine two-parameter trace-glue identity.

## Next minimum theorem

The minimum next theorem is a camera-free trace-glue/Gram construction:
construct a natural TFVD/Green Hilbert state (including all retained
provenance, boundary, log-jet, cross, and completion information) and prove
that its polarized Gram is the completed raw Wronskian divided difference.  In
symbols, prove an identity of the form

```text
canonicalCompletedC3RawMixedWronskian z w
  = (z - conj w) * inner (beta w) (beta z)
```

with the exact code orientation.  Then use coefficient extraction or
forward differences to build the native jet and discharge
`greenJetShiftedHankelFactorizationDefect`.  Until that theorem is available,
`K_N = B_N^* B_N` from the native geometry is not justified.

## Verification

The module and its audit use only the permitted proof foundations reported by
Lean (`propext`, `Classical.choice`, and `Quot.sound`).  No `sorry`, `admit`,
new axiom, camera limit, numerical fit, zeta/zero/RH fact, or moment-defined
positive proxy is used.
