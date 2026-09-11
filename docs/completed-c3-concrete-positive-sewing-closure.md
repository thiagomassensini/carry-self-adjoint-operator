# Completed C3 concrete positive sewing closure audit

## Scope and result

This branch starts at `147b29a0ebf1b7b71b342c49151f5d04711db94d` and audits the fixed concrete real-axis positive carrier used by the completed C3 construction. The result is **Outcome D: a genuine obstruction for this fixed realization**. The positive sewing predicate is false; the failure is witnessed at the central pair `(M, 0, 0)` for every cutoff `M`.

This module does not change the carrier, introduce a metric, or try to remove the retained residual coordinate. It names the exact difference between the oriented C3 readout and the existing channel-complete positive Gram. A different positive metric or a transported state remains a separate research problem.

## Definitions and exact readout expansion

The new definition is:

```lean
canonicalCompletedC3ConcretePositiveSewingDefect M x z :=
  canonicalCompletedC3AllCutoffOrientedRealKernelReadout M x z -
    canonicalCompletedC3RealAxisPositiveKernel (x : ℂ) (z : ℂ)
```

The oriented readout itself is defined by a removable real-axis closure. If `x = z`, it is the derivative of `completedGreenNormalizedResponse`; otherwise it is the oriented off-diagonal final readout divided by the named chart factor, characteristic factors, and separation factor. The structural bridge proves equality with the existing ledger readout, and, at points where both completed characteristics are nonzero,

```lean
canonicalCompletedC3AllCutoffOrientedRealKernelReadout_eq_dslope
```

identifies it exactly with

```text
dslope completedGreenNormalizedResponse x z.
```

Thus the defect has the exact nonzero-characteristic form

```text
dslope(completedGreenNormalizedResponse, x, z)
  - canonicalCompletedC3RealAxisPositiveKernel x z.
```

No asymptotic argument is used to remove `M`: the equality to `dslope` holds for every cutoff, and the new theorem `canonicalCompletedC3ConcretePositiveSewingDefect_cutoff_independent` proves cutoff independence directly.

## The three positive channels

The right hand side is the existing orthogonal sum

```text
ordinary Gram
+ logJet Gram
+ real residual Gram.
```

The theorem

```lean
canonicalCompletedC3RealAxisPositiveKernel_eq_sourceChannelSum
```

expands it as

```lean
inner ℂ ordinaryX ordinaryZ
+ inner ℂ logJetX logJetZ
+ ((inner ℝ residualX residualZ : ℝ) : ℂ).
```

The channels are exactly:

- `canonicalCompletedC3RealAxisOrdinaryState`;
- `canonicalCompletedC3RealAxisLogJetState`;
- `canonicalCompletedC3RealAxisResidualState`, embedded by the canonical complexification with zero imaginary coordinate.

There are no cross terms in this positive Gram, because the carrier is an orthogonal product. The C3 readout has a richer ledger (radial, provenance, off-diagonal, residual, tail, xi, and chart pieces). This round does not assert a separate equality for each readout piece, nor does it silently cancel readout cross terms. Their total discrepancy is retained as one explicitly named scalar channel residual:

```lean
canonicalCompletedC3ConcretePositiveSewingChannelResidual M x z
```

The exact identities are

```lean
canonicalCompletedC3ConcretePositiveSewingChannelResidual_eq_defect
canonicalCompletedC3ConcretePositiveSewingChannelResidual_eq_dslope_sub_sourceChannelSum
```

and

```lean
CanonicalCompletedC3ConcreteRealAxisPositiveSewing ↔
  ∀ M x z, nonzero-characteristic hypotheses →
    canonicalCompletedC3ConcretePositiveSewingChannelResidual M x z = 0.
```

Therefore the ordinary, logJet, and retained residual channels are closed as a decomposition of the positive state, but no independent readout-to-channel theorem was proved for ordinary or logJet. The only unresolved equality is the total readout-minus-source-channel sum above.

## Central witness

The existing exact calibration theorem gives

```lean
canonicalCompletedC3ConcreteDressedCentralMomentDefect_pos :
  0 < canonicalCompletedC3ConcreteDressedCentralMomentDefect.
```

The new central identities are

```lean
(canonicalCompletedC3ConcretePositiveSewingDefect M 0 0).re =
  -canonicalCompletedC3ConcreteDressedCentralMomentDefect
```

and the same formula for `canonicalCompletedC3ConcretePositiveSewingChannelResidual`. Consequently its real part is strictly negative and the complex defect is nonzero for every `M`:

```lean
canonicalCompletedC3ConcretePositiveSewingChannelResidual_zero_zero_re_neg
canonicalCompletedC3ConcretePositiveSewingDefect_zero_zero_ne_zero
```

Applying the sewing predicate at `M = 0`, `x = z = 0` yields a zero defect, contradicting that witness. The branch therefore proves directly

```lean
not_canonicalCompletedC3ConcreteRealAxisPositiveSewing_of_defect
```

and, through the existing sewing/kernel equivalence,

```lean
not_hasCompletedNativeRealAxisNormalizedGreenKernel_concreteC3_of_defect.
```

This is a no-go for the **fixed standard three-channel concrete state and metric**. It is not a no-go for every possible positive transport or for every possible Green realization.

## Consequences for the real HP route

The downstream constructor

```lean
completedNativeRealHPCarrierCertificate_of_concreteC3Kernel
```

is conditional on a `HasCompletedNativeRealAxisNormalizedGreenKernel` witness. Since the concrete witness is formally negated here, this branch does not construct the concrete HP certificate, strict Hankel positivity, or the maximal self-adjoint height operator. The existing conditional theorem, the even/odd independence proofs, and the Jacobi/self-adjoint machinery remain available under a future kernel witness; no new independence assumption or axiom was introduced.

The older complex Taylor-jet certificate is not used as a target and is not reconstructed. The central calibration theorem imported by this module refers to the already existing enriched zeroth jet only as part of its prior, formal strict-mismatch proof. No six-camera specialization, atlas-growth limit, BR2 base/radius choice, camera limit, or numerical fitting is used in the new reduction.

## Mandatory report

1. **Exact readout expansion:** diagonal branch is the derivative of `completedGreenNormalizedResponse`; off diagonal is the oriented final readout divided by the named chart/characteristic/separation factors. The structural theorems identify it with the existing ledger and then with `dslope` on the nonzero-characteristic real axis.
2. **Cutoff:** `M` disappears by exact equality to `dslope`, not by a limit.
3. **Ordinary term:** the inner product of `canonicalCompletedC3RealAxisOrdinaryState` values.
4. **LogJet term:** the inner product of `canonicalCompletedC3RealAxisLogJetState` values.
5. **Residual term:** the real inner product of `canonicalCompletedC3RealAxisResidualState` values, canonically coerced to `ℂ`.
6. **Cross terms:** none in the positive orthogonal Gram; the richer readout is not independently split, so any remaining total discrepancy is retained in the named channel residual.
7. **Ordinary closed:** closed on the positive-carrier side; no separate readout equality was claimed.
8. **LogJet closed:** closed on the positive-carrier side; no separate readout equality was claimed.
9. **Residual closed:** retained exactly in the positive carrier, but its equality with the C3 readout is part of the false total sewing equation.
10. **Full sewing:** false for the fixed concrete state.
11. **Unique residual formula:** `canonicalCompletedC3ConcretePositiveSewingChannelResidual`, equal to `dslope - (ordinary + logJet + residual)` and equal to the total defect.
12. **Real-axis kernel:** not constructed; its concrete negation is proved by `not_hasCompletedNativeRealAxisNormalizedGreenKernel_concreteC3_of_defect`.
13. **HP certificate:** not constructed for this state; only the existing conditional constructor remains.
14. **Even/odd independence:** no new hypothesis was needed; those theorems remain conditional on a kernel witness.
15. **Hankel PosDef:** not discharged for this concrete state because the required kernel witness is impossible.
16. **Maximal self-adjoint height operator:** not discharged unconditionally for this state.
17. **Six-camera:** none used.
18. **Atlas limit:** none used.
19. **Old complex Taylor Gram:** not used as a target or recovered; it appears only inside the imported, already-proved low-order calibration argument used to expose the central mismatch.
20. **Relevant no-go:** `canonicalCompletedC3RealAxisPositiveKernel_zero_zero_re_gt_nativeMoment`, `canonicalCompletedC3ConcreteDressedCentralMomentDefect_pos`, and the earlier `not_canonicalCompletedC3ConcreteRealAxisPositiveSewing`/kernel negation. The new defect witness makes the obstruction explicit rather than merely reusing the older predicate-level contradiction.
21. **Axioms:** new declarations use only `propext`, `Classical.choice`, and `Quot.sound` according to the audit prints.
22. **Build/audit:** the focused source and audit modules, the root library, and `KernelConstructionAudit`/`Audit` compile. Final `lake build`, `scripts/audit.sh`, `git diff --check`, and JSON validation are run before commit.
23. **Next minimum theorem:** the fixed state cannot satisfy the next equality. A future route must first give an independently derived alternative positive metric/state (or an exact correction theorem) whose `dslope` Gram equals its channel sum. Only after that new kernel theorem can the existing real HP certificate be instantiated.

## Outcome classification

**Outcome D — obstruction.** The standard concrete C3 positive carrier has a strictly nonzero central sewing defect. The result isolates the exact residual equality that would be needed for sewing and proves that it cannot hold for the current carrier. It does not assert that no other carrier or metric can realize the canonical real-axis kernel.
