# Reflected logJet commutator / current mixed provenance audit

## Checkpoint and scope

Initial `HEAD = main = origin/main`:
`0875a32a90b718fd6378ac46c8c580f45bcda1c3`.
`git pull --ff-only` reported up to date; initial working tree clean.
Work is exclusively on `llm:/home/thlinux/carry-self-adjoint-operator`, branch
`main`. The pinned CPFormal sources remain unchanged at
`65d50f6db1208708e109982ba97e1d51d3039956`.

This continues the ordinary angular audit. It tests the suggested
ordinary/logJet commutator **plus residual**, rather than assuming the
ordinary-only correction is the current mixed form.

```text
PASS_REFLECTED_LOGJET_PREFIX_COMMUTATOR_RESIDUAL_CROSSWALK
NO_GO_DIRECT_REFLECTED_SAME_EDGE_AS_CURRENT_ADJACENT_MIXED_PROVENANCE
```

The no-go is for direct universal equality of two finite observations.
Its witness is canonical but is outside the critical strip (`s=0`).
It does not refute equality restricted to another parameter sector,
a nontrivial transport, completed sewing, or the complete corrected ledger.
No positivity or contractivity result is claimed.

## Audit before construction

The present mixed carrier already retains the required pairs:

```lean
CanonicalC3AllCutoffMixedSourceHilbert =
  WithLp 2 (CanonicalCompletedC3HilbertState ×
    WithLp 2 (CanonicalCompletedC3HilbertState × CanonicalCompletedC3HilbertState))

CanonicalCompletedC3HilbertState = CarryVerticalL2 × CarryVerticalL2
```

They are `zSource`, `wSource`, `reflectedZSource`, each with ordinary and
logJet coordinates. No carrier, Hilbert metric, completion or encoding is added.
The new functions are finite **observations**, not a lossless replacement of
this carrier or an inversion of a scalar trace. Existing prefixes and `lp`
membership provide the vector inputs; finite sums need no new Hardy bound.

| Observation | First roles | Second roles | Edge geometry | Conjugation |
|---|---|---|---|---|
| Historical `reflectedLogJetEdgeWedge` | ordinary/logJet at w | ordinary/logJet at reflected z | same material edge n | first role pair conjugated |
| Current `mixedLegs` boundary wedge | logJet at z | ordinary at w | consecutive material edges n, n+1, two legs per C3 cell | literal bilinear `sameSEdgeBoundaryWedge` |
| Current Green port term | ordinary at w | ordinary at reflected z | finite Green port of length 3M | existing sesquilinear `greenForm` |

These are different contractions of data already present in the carrier.
A matching index type or the presence of a logJet does not make them the
same form. The historical trio is `3m,3m+1,3m+2`; the current mixed legs are
`(3m,3m+1)` and `(3m+1,3m+2)`. These are material edges, not vertical depths.

Upstream APIs reused without changing their definitions:

- `reflectedLogJetEdgeWedge`;
- `TfvdWedgeTriple`, `.add`, `.total`;
- `canonicalEnrichedTfvdReflectedLogJetWedgeTriple_eq_canonical`;
- `canonicalReflectedLogJetWedgeTriple_eq_green_add_defect`;
- `canonicalLogJetGreenDefectTriple_eq_commutator_add_residual`;
- `finiteCanonicalLogJetGreenDefectTrace_eq_commutator_add_residual`;
- `finiteReflectedLogJetVertexFlux_eq_cutoff_add_crossBulk`;
- existing canonical Hilbert prefixes and their coordinate theorems.

## Provenance-preserving observation and two parameters

For a state x, the new observation reads only the four historical roles:

```text
E_x(n) = conj(wLog(n)) * reflectedZOrd(n)
         - conj(wOrd(n)) * reflectedZLog(n).

J_x(m) = (E_x(3m), E_x(3m+1), E_x(3m+2)).
```

`canonicalC3ReflectedLogRoleEdge_prefix` proves, for independent z,w and
n<3M, the literal substitution of `positiveDirichletGradient` and
`positiveLogDirichletGradient` at w and reflected z. No equality z=w,
parameter conjugation, or trace inversion is smuggled into that theorem.
The direct z-source remains retained in the input; this historical
observation does not consume it and is not an injective source map.

Only the historical specialization z=w=s is used in the subsequent old
commutator/cutoff identities. Their independent-parameter extension is not
asserted. For every m<M, the kernel identifies the whole three-role vector
with the existing enriched TFVD roundtrip, including the dormant edge.
It proves **before scalar synthesis**

```text
J_prefix(m) = GreenTriple(3,m,s)
                + CommutatorTriple(3,m,s)
                + ResidualTriple(3,m,s).
```

The residual is precisely the existing `canonicalLogJetCommutatorResidualTriple`,
not a new scalar subtraction renamed as a channel. It retains the vertex
flux absent from the commutator alone. The coefficients are those of the
existing prime-3 identity; none is chosen to fit a readout.

Only afterwards is `.total` summed over complete cells, yielding

```text
Trace_M = GreenFlux(3,3M,s) + CommutatorTrace(3,M,s) + ResidualTrace(3,M,s)
        = finiteReflectedLogJetVertexFlux(3M,s)
        = reflectedLogJetMovingCutoff(3M,s) + finiteReflectedLogJetCrossBulk(3M,s).
```

Both endpoint and cross bulk are retained. This is a reflected same-edge
ledger, not the current adjacent-edge ledger and not the whole completed
Wronskian. No cancellation or decay is postulated; no tails, Xi, chart or
archimedean terms are claimed to vanish. No Green energy sign is inferred.

## Canonical one-cell comparison

Use the actual finite prefix `canonicalC3AllCutoffMixedSourcePrefixState 1 0 0`.
It is well defined without infinite ℓ² membership at s=0.
The old endpoint/bulk identities give exactly

```text
Trace_1 = -(log 4)/12 - (log 2)/3 - (log 3)/12 ≠ 0.
```

The nonzero result uses strict positivity of the real logarithms of 2,3,4,
not approximate values or moments. The current mixed ordinary prefix at
w=0 vanishes. Therefore every adjacent-edge boundary wedge and its ordinary
Green port contribution vanish:

```text
greenProvenanceReadout 1 0 (reflectedParameter 0) samePrefix = 0.
```

Both sides are observations of the **same canonical finite vector**.
This is stronger than the earlier arbitrary-role probe, but it is still a
finite algebraic canary outside the critical strip. It cannot establish a
critical-strip mismatch, a limit mismatch or a sign for ChiralReturn.
Only the Green-provenance component is compared; the current off-diagonal,
readout residual, completion/tail channels are not substituted by this trace.

The theorem
`canonicalC3ReflectedLogRoleTrace_ne_currentMixedProvenance_one_zero`
therefore refutes direct universal identification even after the historical
commutator and residual have both been retained. Adding the historical
residual fixes its own same-edge ledger; it does not change its contraction
into the current adjacent-edge mixed one.

## One remaining obligation

The same carrier already retains the roles. The gap is **form transport**,
not a missing ordinary/logJet vector or a new positivity hypothesis:

```text
current adjacent-edge mixed provenance (independent z,w)
  ↔ source-derived shifted-edge commutator / boundary / cross ledger
```

Such a comparison must use the actual `mixedLegs` orientation and recover
its Green port with all current boundary, off-diagonal and readout terms.
It cannot be the direct equality to the historical reflected same-edge
trace refuted above. This audit introduces no encoder, hypothesis wrapper,
new metric, positive defect vector or fitted transport to fill that gap.
The completed Hilbert/Pythagorean sewing frontier remains open.

## Public declarations

- `canonicalC3ReflectedLogRoleEdge`;
- `canonicalC3ReflectedLogRoleTriple`;
- `canonicalC3ReflectedLogRoleTrace`;
- `canonicalC3ReflectedLogRoleEdge_prefix`;
- `canonicalC3ReflectedLogRoleTriple_prefix_eq_historical`;
- `canonicalC3ReflectedLogRoleTriple_prefix_eq_enriched`;
- `canonicalC3ReflectedLogRoleTriple_prefix_decomposition`;
- `canonicalC3ReflectedLogRoleTrace_prefix_eq_vertexFlux`;
- `canonicalC3ReflectedLogRoleTrace_prefix_decomposition`;
- `canonicalC3ReflectedLogRoleTrace_prefix_eq_cutoff_add_bulk`;
- `canonicalC3ReflectedLogRoleTrace_one_zero`;
- `canonicalC3CurrentMixedProvenance_one_zero`;
- `canonicalC3ReflectedLogRoleTrace_ne_currentMixedProvenance_one_zero`;

## Kernel and trust audit

All 13 public declarations receive `#assert_prime_depth_source_axioms` and
`#print axioms` in the dedicated audit. The source firewall traverses types
and proof values: **3524 reachable declarations**, with no canonical moments,
HP/Stieltjes certificate, Hankel, Jacobi/height, Herglotz or BR2 inputs.
Axioms are at most `[propext, Classical.choice, Quot.sound]`.

Validation commands:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedC3ReflectedLogJetCommutatorCrosswalk
lake build --wfail CarrySelfAdjointOperator.CompletedC3ReflectedLogJetCommutatorCrosswalkAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

All listed commands passed. Root build: 9532 jobs; main Audit: 9728 jobs.
The full script ended with `kernel audit passed`; static audit and
`git diff --check` passed. No new warning was accepted under `--wfail`.

Logs are retained on llm under `/tmp/reflected-logjet-validation/`.
Modified files: new module and audit, root imports, theorem registry,
this report, README frontier paragraph and append-only checkpoint entry.
No dependency, Foundation or existing canonical declaration was changed.
Final published SHA and synchronized/clean Git state are recorded in the
handoff rather than self-referenced inside the commit.
