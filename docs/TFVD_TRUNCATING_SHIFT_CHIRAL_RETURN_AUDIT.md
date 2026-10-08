# Finite TFVD shift versus the actual completed chiral return

## Checkpoint

- Repository: `thiagomassensini/carry-self-adjoint-operator`, exclusively `main`.
- Initial `HEAD = main = origin/main`: `5cb33f416930716832e6b5cb254befd91993c31c`.
- `git pull --ff-only`: already up to date; working tree initially clean.
- Status: **NO_GO_FINITE_TFVD_TRUNCATING_SHIFT_AS_CHIRAL_RETURN**.

This tests the first operator-identification obligation suggested by
`Downloads/Pastas/CARRY/TFVD_TRANSPORT_PULLBACK_2026-10-08.md`.
It rules out a faithful intertwining with that particular finite shift,
including its conjugate through ANY invertible finite TFVD chart.
It does not rule out a conservative ambient realization, a unitary return,
an additional projection/compression, or source-first storage positivity.
The closed N=5 result and open N=6 source sign are unchanged.

## Inventory and audited provenance

The note is a research map, not a Lean dependency or a proof premise.
Its auxiliary state is `C^M`; its truncating shift has zero first coordinate
and sends the previous coordinate to each later coordinate, discarding the
last one. Its invertible finite analysis A and reconstruction S give
`Ttilde = A T S`. The identity

```text
M - Ttilde* M Ttilde = S* (I-T*T) S,  M=S*S
```

is an algebraic pullback of the original defect. It cannot change the
operator's eigenvalue obstruction. This round does not declare that metric
to be the Cauchy metric, nor recreate a Hilbert metric in Lean.

Existing upstream declarations checked in the published main:

| Declaration | Exact role and carrier |
|---|---|
| `canonicalCarryTfvd_inner_eq_fourChannel` | For x,y in `CarryVerticalL2`, the original pairing expands into Green/Green, Green/return, return/Green and return/return at the carry amplitude ratio. Both boundary coordinates and every cross remain. |
| `carryTfvdMetricState_injective` | Full bracket plus trace retains the vertical carry source. It does not identify its analysis norm with the chiral Cauchy metric. |
| `canonicalC3SixSourceRoleAffineAssembly` | Global ordinary seed plus homogeneous six-role variation; logJet roles have zero seed. It does not manufacture a camera assignment or a metric realization. |
| `canonicalC3MixedPrefixHead_clockTransport` | Literal C3 adjacent material edges retain ordinary/log-gap channels, ordered crosses and synthesis residuals. The C2 step-two four-pair expansion is not automatically this adjacent ledger. |
| `radialIncidentSynthesis` | `(Fin N -> C) ->_linear[C] CanonicalCompletedNativeChiralCauchyCarrier`; complete original half-density synthesis. |
| `radialIncidentCoordinates` | `RadialIncidentSpan k N ~=_linear[C] (Fin N -> C)`; exact recovery from the original incident features. |
| `radialReturnedSynthesis_eq_incident_multiply` | The complete return is the incident synthesis with each coefficient multiplied by the actual completed chiral quotient at its original radial node. |
| `radialReturnTransfer` | `RadialIncidentSpan k N ->_continuous_linear[C] CanonicalCompletedNativeChiralCauchyCarrier`; the already constructed actual return. |
| `radialReturnTransfer_mem_incidentSpan` | The actual returned vector remains in the same incident span, so its exact coefficient action is intrinsic. |
| `radialReturnTransfer_polarized_balance` | Full source balance for independent inputs; all Cauchy crosses are retained. |
| `storage_one_eq_finiteTransfer_energy` | Storage equals the actual incident norm squared minus actual returned norm squared. This does not supply a sign. |

## Exact cheap test before any metric comparison

The new `finiteTfvdTruncatingShift M` is literally the finite shift from
the note. It is an AUXILIARY test map on `(Fin M -> C)`, not a new canonical
operator, material clock, vertical depth or spectral height operator.

If `T x = a x` with `a != 0`, then its first coordinate forces x_0=0.
The next coordinate forces x_1=0, and so on through the entire finite vector.
`finiteTfvdTruncatingShift_eigenvector_eq_zero` proves this for every M.
No energy premise or positivity certificate is involved.

For the native return, write

```text
q_i(k) = completedNativeHermiteBiehlerChiralQuotient
           (canonicalCompletedC3RadialTiltPoint k i).
```

The source-first centered value is exactly `q(0)=-1`. Source differentiability
and convergence of the original radial nodes imply, for every fixed i,
`eventually k, q_i(k) != 0`. This uses no moment sign and no source fitting.
The original return already satisfies, by COMPLETE vector synthesis,

```text
T_native(incidentVector(delta_i)) = q_i(k) incidentSynthesis(delta_i).
```

Suppose a linear injective U into a finite TFVD chart intertwines the native
return with `A T A^-1`. After reconstruction by `A^-1`, the image of delta_i
would be an eigenvector of the truncating shift with nonzero eigenvalue
q_i(k). The finite shift theorem forces that image to zero. Injectivity then
forces delta_i=0, a contradiction.

This is an algebraic obstruction before the metric question. In particular,
isometric intertwiners are also excluded, since they are injective; no metric
adjustment or normalization of the TFVD chart can remove this contradiction.

## Exact scope and quantifiers

`radialReturn_eventually_no_finiteTfvdShift_intertwiner` proves:

```text
for every N>0, eventually k,
for every M and every invertible complex-linear analysis A on C^M,
there is no injective complex-linear U : C^N -> C^M satisfying
  U(c_i q_i(k)) = A T A^-1 U(c), for ALL c.
```

Only node i=0 is needed, so one eventual threshold excludes all target cutoffs
M and all invertible analyses for that source cutoff. No uniform all-order
positivity statement is inserted. The obstruction already occurs at N=1.
It remains true for larger N, including our open N=6 gate.

`radialReturn_eventually_no_finiteTfvdShift_spanIntertwiner` proves the SAME
statement on the actual `RadialIncidentSpan k N`, with the actual existing
`radialReturnTransfer`. The proof uses its exact returned synthesis and
existing range membership; it does not replace the return by a fitted
coefficient operator or scalar observation. Its metric is untouched.

The argument does not forbid equality of some scalar readouts, an
unfaithful map, or a different operator obtained by compression of an
ambient conservative transport. A compression can change the algebraic
spectrum, so it is not covered by this conjugacy no-go.

## Single remaining structural obligation

A proposed positive ambient mechanism still needs a source-derived
FORM-PRESERVING intertwiner with the actual return. In minimal conceptual
form, for the complete incident span X and an ambient Hilbert carrier H:

```text
J_in : X ->_isometry[C] H,
J_out : X ->_isometry[C] H,
Q : H -> H unitary,
P : H -> H orthogonal projection,

J_out(actual native return in X) = P Q J_in(source vector).
```

These maps must come from existing geometry, preserving boundary,
ordinary/logJet orientation, residual, tails and completion. None of these
maps or the required equality is postulated or defined in this round.
The old finite shift does not provide it. If this equality were genuinely
proved, norm conservation and orthogonal projection would imply the source
storage sign; that implication is not used to assert its existence.

For the direct N=6 source route, the published exact remaining inequality
is still `nativeSourceTwelfthMixedNumerator(mu_0,...,mu_6) > 0`, followed by
the full remainder transfer. This test neither proves nor refutes that sign.

## Public declarations and audit

New module: `CompletedNativeChiralReturnTfvdShiftObstruction.lean`.
New dedicated audit: `CompletedNativeChiralReturnTfvdShiftObstructionAudit.lean`.

Public declarations:

```text
ChiralReturn.finiteTfvdTruncatingShift
ChiralReturn.finiteTfvdTruncatingShift_eigenvector_eq_zero
ChiralReturn.nativeRadialChiralQuotient_eventually_ne_zero
ChiralReturn.radialReturn_no_finiteTfvdShift_intertwiner
ChiralReturn.radialReturn_eventually_no_finiteTfvdShift_intertwiner
ChiralReturn.radialReturn_eventually_no_finiteTfvdShift_spanIntertwiner
```

All are checked with `#assert_prime_depth_source_axioms`, `#print axioms`
and the existing transitive `#assert_oriented_green_source` firewall.
The dedicated audit checks 6 public declarations and 5,257 source dependencies;
all footprints are within `[propext, Classical.choice, Quot.sound]`.
Canonical moment targets, HP/Stieltjes positivity, Hankel, spectral
Jacobi/height and BR2 do not supply a proof dependency. The narrow existing
classical-source exceptions and all audit rules are unchanged.

Validation on llm, Lean v4.32.0:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnTfvdShiftObstruction
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnTfvdShiftObstructionAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

All listed focused/full builds, both audit scripts and whitespace checks
passed. The source firewall passed without any changes to its rules.
Validation outcomes are tracked in
`research/chiral-tfvd-shift-obstruction-2026-10-08/validation.txt`.
Detailed logs are on llm in `/tmp/chiral-tfvd-shift-validation/`.
Published ref equality and clean tree are checked after commit/push.
