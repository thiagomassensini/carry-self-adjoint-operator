# Completed native TFVD–Green moment Gram bridge

This branch audits the camera-free seam between the completed TFVD/Wronskian
moment sequence and the Green jet Gram consumed by the completed native
operator interfaces. It starts from `d8dfee06a76765ca6d692b368353cf37f9440d15`
and does not use a camera limit.

## Result

The primary outcome is **Outcome C — exact residual isolated**.

The scalar TFVD/Wronskian identity is already exact:

```lean
cameraFreeTfvdWronskianMoment_eq_canonical
```

which is a direct wrapper of
`canonicalC3BracketTfvdMoment_eq_canonical`:

```text
canonicalC3BracketTfvdMoment M n
  = canonicalCompletedNativeLogDerivativeMoment n
```

for every cutoff `M` and order `n`. Thus the canonical moments are cutoff
independent before any camera construction.

The vector side is also already exact at the port level:

```lean
cameraFreeTfvdGreenPort_vector_intertwiner
cameraFreeTfvdGreenNaimark_forwardDifference_intertwiner
```

These wrap
`canonicalCompletedTfvdGreenPortState_eq_bracketGreenPort` and
`canonicalCompletedNativeGreenNaimark_forwardDifferenceParityJet_eq_bracket`.
They preserve the completed vector state and its all-order forward-difference
parity jets. They do not, by themselves, identify the inner products of the
actual completed Taylor jets.

## The target certificate and the exact defect

The existing definition is reused without modification:

```lean
HasCanonicalCompletedNativeGreenMomentJets xiState moments
```

unfolds to a `CompletedGreenMomentJetCertificate` for
`completedNativeOperatorCharacteristic`, the product ledger
`completedNativeC3ProductLedgerState xiState`, and the jet

```lean
completedGreenParityJet
  (normalizedCompletedGreenState
    completedNativeOperatorCharacteristic
    (completedNativeC3ProductLedgerState xiState))
```

The certificate contains three independent obligations:

1. the center belongs to `completedNativeHeightDomain`;
2. the two-variable division-free Green representation holds;
3. the **complex** Gram identity holds for the normalized completed Taylor
   parity jets.

The module defines the last gap explicitly:

```lean
canonicalCompletedNativeGreenMomentGramDefect xiState moments i j
```

is

```text
(greenWronskianMomentKernel moments i j : ℂ)
  - ⟪actual normalized completed Taylor jet i,
      actual normalized completed Taylor jet j⟫_ℂ.
```

The theorem

```lean
isComplexGreenMomentKernel_iff_canonicalGreenMomentGramDefect_zero
```

proves that the desired complex Green moment-kernel representation is exactly
`∀ i j, defect = 0`.

With the existing factor-level Green hypotheses, the theorem

```lean
hasCanonicalCompletedNativeGreenMomentJets_iff_defect_zero_of_factors
```

packages the same equivalence for the full canonical certificate. The factor
hypotheses are intentionally explicit; no unproved xi or native scalar Green
representation is smuggled into this branch.

## Forward-difference carrier and the remaining seam

The existing completed forward-difference construction gives a camera-free
limit jet:

```lean
canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
```

and proves

```lean
canonicalCompletedNativeGreenForwardDifferenceLimitParityJet_momentKernel
```

for the prescribed canonical moments. That theorem is stated after
restriction of scalars to the real inner product. It therefore supplies an
exact real Green Gram realization, but it does not assert that this selected
limit jet is the actual complex Taylor parity jet used by
`HasCanonicalCompletedNativeGreenMomentJets`.

The new definition

```lean
canonicalCompletedNativeGreenForwardDifferenceGramResidual
```

records precisely that difference:

```text
(real part of the complex pairing of the existing forward-difference limit
 jet)
 - (complex pairing of the actual normalized completed Taylor jets).
```

The key reduction is

```lean
canonicalCompletedNativeGreenMomentGramDefect_eq_forwardDifferenceResidual
```

which proves, entry by entry, that the target complex defect equals this
explicit residual. Consequently,

```lean
hasCanonicalCompletedNativeGreenMomentJets_of_forwardDifferenceResidual_zero
```

shows that factor Green representations plus vanishing of this residual are
sufficient for the full canonical moment-jet certificate.

The smallest unclosed equality is therefore the Taylor-to-forward-difference
Gram identity (including its complex orientation), not a camera limit and not
the scalar TFVD moment identity.

## Positivity and operator consequences

The existing Gram bridge already implies positive semidefiniteness of both
Hankel sectors from a complex Green moment-kernel representation. The new
module does not provide the missing factor representations or residual
vanishing, so it does not create an unconditional
`HasCanonicalCompletedNativeGreenMomentJets` instance.

Accordingly:

- both Hankel sectors are **conditionally PSD** through the existing
  `hankelPair_posSemidef_of_completedGreenMomentJets` API;
- both sectors are **not unconditionally PosDef** here, because parity
  independence for this actual Taylor jet certificate is not discharged;
- no unconditional finite Jacobi operator is added;
- no unconditional maximal self-adjoint height theorem is added.

The existing Jacobi cyclic crosswalk remains valid independently:
`completedJacobiCyclicMoment_eq_canonicalC3BracketTfvdMoment` identifies the
same scalar canonical sequence, but scalar moment equality is not substituted
for a Green inner-product identity.

## Positive-observable route

`PositiveObservableParityKernel.lean` and
`PositiveObservableNativeMomentBridge.lean` were audited. Their
`positiveObservable_isNativeMomentSequence_iff_defect_zero` route requires a
natural symmetric observable and source whose moments are already identified
with the completed TFVD/Green state. No such typed identification is present
in the current dependency graph, so that route was not forced and no fitted
operator was introduced.

## No-go results respected

The following existing obstructions were kept in force:

- `BR2CompletedGreenJetTransportObstruction.lean`: arbitrary finite
  incidence-to-jet transports cannot preserve the required all-order
  information. It does not obstruct the fixed completed infinite carrier,
  but it forbids inventing a finite replacement.
- `BR2RadialNormalizedComplexJetNoGo.lean`: the normalized radial product
  state is not a valid naive complex Taylor-jet source at the center. The
  branch therefore uses the existing real-axis forward-difference carrier
  rather than bypassing the obstruction.
- `ProjectiveValveMomentFrontier.lean`: the raw C3 valve is not silently
  promoted to the canonical native Green moment kernel.

None of these no-go theorems proves that no camera-free realization can ever
exist. They only rule out the corresponding naive or raw constructions.

## Audit table

| Statement | Current declaration | Status |
|---|---|---|
| TFVD/Wronskian coefficient is canonical moment | `canonicalC3BracketTfvdMoment_eq_canonical` (wrapped as `cameraFreeTfvdWronskianMoment_eq_canonical`) | Lean-proved, exact |
| Completed TFVD port equals bracket Green port | `canonicalCompletedTfvdGreenPortState_eq_bracketGreenPort` | Lean-proved, exact vector equality |
| Naimark forward-difference parity intertwiner | `canonicalCompletedNativeGreenNaimark_forwardDifferenceParityJet_eq_bracket` | Lean-proved, exact vector equality |
| Forward-difference limit jet has canonical real Gram | `canonicalCompletedNativeGreenForwardDifferenceLimitParityJet_momentKernel` | Lean-proved, real restriction-of-scalars Gram |
| Actual Taylor jet has canonical complex Gram | `HasCanonicalCompletedNativeGreenMomentJets` | Interface only; coefficient/Gram seam remains |
| Factor Green representations | `HasDivisionFreeGreenRepresentation` hypotheses | Not discharged for the concrete factors |
| Taylor Gram defect | `canonicalCompletedNativeGreenMomentGramDefect` | New exact definition |
| Defect reduction to forward-difference residual | `canonicalCompletedNativeGreenMomentGramDefect_eq_forwardDifferenceResidual` | Lean-proved, conditional on the existing real-axis kernel |
| Positive-observable realization of the same state | `positiveObservable_isNativeMomentSequence_iff_defect_zero` | Separate API; no typed TFVD/Green identification found |

## Mandatory answers

1. **TFVD moment identity used:**
   `canonicalC3BracketTfvdMoment_eq_canonical`, exposed by
   `cameraFreeTfvdWronskianMoment_eq_canonical`.
2. **Vector intertwiner used:**
   `canonicalCompletedTfvdGreenPortState_eq_bracketGreenPort` and its Naimark
   forward-difference specialization
   `canonicalCompletedNativeGreenNaimark_forwardDifferenceParityJet_eq_bracket`.
3. **Definition of `HasCanonicalCompletedNativeGreenMomentJets`:** the existing
   `CompletedGreenMomentJetCertificate` for the completed native characteristic,
   product ledger state, and normalized completed Green parity Taylor jets,
   with the complex `IsComplexGreenWronskianMomentKernelGramRepresentation`
   field.
4. **Green Gram identity:** not yet for the actual Taylor parity jet; the exact
   residual reduction is proved. The existing forward-difference limit jet has
   the canonical real Gram.
5. **Hankel PSD:** conditional on the missing certificate, via existing API;
   no new unconditional result here.
6. **Hankel PosDef:** not discharged; parity independence for the target actual
   Taylor jet remains a named requirement.
7. **Even/odd global independence:** not discharged for the target certificate.
8. **Finite Jacobi unconditional:** no.
9. **Maximal self-adjoint height unconditional:** no.
10. **Remaining hypotheses (verbatim at the new constructor):**
    `hxi : HasDivisionFreeGreenRepresentation nativeXiCompletionFactor
    nativeXiCompletionBoundaryCompanion xiState`,
    `hnative : HasDivisionFreeGreenRepresentation nativeHeightScalar
    nativeHeightScalarBoundaryCompanion canonicalCompletedOperatorC3HilbertState`,
    `hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel
    (completedNativeC3ProductLedgerState xiState)`, and
    `hresidual : ∀ i j,
    canonicalCompletedNativeGreenForwardDifferenceGramResidual xiState hkernel
    i j = 0`.
11. **Camera names in the final operator theorem:** none; no operator theorem
    was added and all new load-bearing statements are camera-free.
12. **Camera-limit argument:** none.
13. **No-go applicability:** the finite arbitrary-transport obstruction and the
    naive radial complex-jet obstruction were respected; neither rules out
    the fixed completed forward-difference carrier.

## Next Geometric/Hilbert Gate

The minimum next theorem is an exact, typed identity between the actual
normalized completed Taylor parity-jet Gram and the existing
forward-difference limit-jet Gram (or an equivalent polarization theorem that
makes `canonicalCompletedNativeGreenForwardDifferenceGramResidual` vanish).
Once that identity is available, the factor Green representations still have
to be supplied if they are not discharged elsewhere. Only then can
`HasCanonicalCompletedNativeGreenMomentJets` feed the existing Hankel/Jacobi
interfaces.

The route is therefore:

```text
exact TFVD/Wronskian moments
  + exact vector TFVD→Green intertwiner
  + [missing Taylor/forward-difference Gram identity]
  + [factor Green representations]
→ HasCanonicalCompletedNativeGreenMomentJets
→ Hankel PSD (and PosDef with existing independence)
→ existing Jacobi/self-adjoint machinery
```

No camera family, camera limit, or second operator is part of this bridge.
