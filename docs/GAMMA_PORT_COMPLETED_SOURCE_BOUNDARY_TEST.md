# Completed source versus the upstream Gamma camera boundary

## Checkpoint and scope

Audited carry main: `ecdaf2456c3dc3a6105eeae17f505826d085e58c`.
`git pull --ff-only` reported up to date; initial working tree was clean,
and HEAD/main/origin/main agreed. Work remains on main.

Upstream published native-carry-spectral-weyl main was inspected at
`248249ce098491f4194209d8e698dc5965f1405d`. Its local checkout is on another
branch and was not switched or modified. Carry still uses the pinned
dependency `298d83c9351e308a5213b9f5ac32e44087f98a9f`; the inspected
Finite/Boundary/Limits source has no diff against that pin. No dependency
upgrade is needed or performed.

This is the next source/boundary test, not another positivity proof.
Statuses:

- `PASS_COMPLETED_RESPONSE_GAMMA_PORT_LEAK_DECOMPOSITION`;
- `NO_GO_GAMMA_PORT_ONLY_REALIZATION_OF_COMPLETED_RESPONSE`.

The no-go is a single exact witness against a global, literal port-only
realization of the same vector at the same parameter. It does not refute
eventual radial sewing, another carrier, or positivity of the completed
scalar kernel.

## Upstream maps and their actual obligations

| Construction | Domain/codomain or role | Provenance/status |
|---|---|---|
| `returnMetric` | finite endpoint matrix `I + P†P` | Existing endpoint+bulk isometry and Poisson relation imply exact return cancellation; no completed scalar source identification |
| `sourceExtendedRelation_weyl_green_identity` | source relation in `H × H` to boundary relation in `B × B`, over an RCLike field | Preserves the polarized Green form for a formally symmetric operator and injective port |
| `carrySourceRelation_weyl_green_identity` | real logarithmic domain/ambient Naimark relation to real camera boundary | Concrete all-bases specialization |
| `carryGammaSource z hz` | `RealifiedCameraComplexification →L[ℝ] RealifiedNaimarkComplexification` | Existing bounded resolvent applied to the Naimark port |
| `GreenCameraCoupling.stateReadout` | `H →L[ℝ] RealifiedCameraComplexification` | Explicit input; the generic Green split does not construct a completed-native source readout |
| `GreenCameraCoupling.externalGammaSource` | external Green data to realified Naimark response | Always factors through `carryGammaSource`; retains only the camera source supplied by the readout |

`CompletedGammaTwoParameterGreenIdentity` already complexifies the same two
quadratures and uses all four real source-relation identities to obtain the
complex polarized Gamma Green identity. That bridge is not rebuilt here.
Static Green Poisson and spectral Gamma/Weyl remain distinct maps.

## Same completed source, before scalar trace

Write

```text
u(z) = completedC3SymplecticNaimarkState (operatorHeightParameter z) hs
a(z) = canonicalCompletedC3AmbientInducedSourceLimit z hs
p(z) = canonicalCompletedC3CoisometricCompressedSourceLimit z hs
l(z) = canonicalCompletedC3CoisometricNaimarkLeakLimit z hs
R(z) = logarithmicResolventBlock z hz
```

All four vectors already exist. The full induced source is `(z-Y)u` and
has the existing lossless decomposition

```text
a = port p + l.
```

The new exact test transports the entire decomposition:

```text
u = Gamma(z) p + R(z) l.
```

Here Gamma is precisely the upstream map, not a fitted response. The
completed ambient resolvent-domain embedding theorem supplies `u = R(z)a`.
No normalization, camera weight, source amplitude, or metric is changed.

The structured completed source already also carries the scalar `(F,-F')`
trace. Its direct vector and trace are separate projections. This proof uses
the direct vector; it neither reconstructs a Hilbert vector from two scalars
nor asserts that the trace projection is invertible.

## Exact membership test and universal port-only obstruction

The new theorems prove

```text
a ∈ range port  ↔  l = 0
(∃ camera source p', Gamma(z)p' = u)  ↔  l = 0.
```

The second statement quantifies over every camera source, not just the old
canonical TFVD camera choice. Resolvent injectivity proves the necessity.
The canonical coisometric source proves sufficiency.

At the existing `noLeakWitnessHeight`, the retained induced-source leak is
nonzero. Thus there is no camera source at all whose upstream Gamma response
equals this complete vector at that same parameter. No new numerical test,
zero table, moment sign, or spectral fitting supplies this witness.

This also rules out using a generic `GreenCameraCoupling.externalGammaSource`
to reproduce this exact vector at every parameter: whatever its readout,
its output at the witness would be a Gamma response of a camera source.
This is a logical consequence of the new existential no-go, not a newly
postulated coupling interface.

## Polarization and all cross terms

Let `g(z) = Gamma(z)p(z)` and `d(z) = R(z)l(z)`, viewed through the existing
canonical complex Naimark view. The new polarized theorem gives

```text
inner u(z) u(w)
  = inner g(z) g(w) + inner g(z) d(w)
    + inner d(z) g(w) + inner d(z) d(w).
```

The two ordered cross terms remain distinct, with conjugate-linearity in
the first argument. Orthogonality of the original port/leak source split
does not establish orthogonality after resolvent transport. No orthogonality
or sign of the resolved cross terms is asserted here. All statements concern
the fully completed vectors; the same identities may be linearly synthesized
before pairing, without dropping any terms.

This is not a claim that `d` supplies a positive complementary channel for
the scalar completed Wronskian. Nor is resolved leak the same as the ambient
leak boundary readout already proved zero. Those objects are kept separate.

## Remaining source-specific obligation

The full ambient source already has its positive response Gram identity,
but its boundary form is not identified with the scalar completed Wronskian.
The prior candidate-specific seam remains exactly the existing four-channel
equation:

```lean
canonicalCompletedC3CoisometricWronskianFourChannelDefect
  z w hz hw hzStrip.1 hwStrip.1 = 0
```

Equivalently, its weighted complete synthesis must vanish for the radial
camera candidate if that candidate is to give the exact signed source
pairing. This is stronger than bare positivity and is not assumed here.
The new source test shows why one cannot discharge it simply by declaring
the full response to be Gamma of a camera readout: the induced-source leak
is a genuine missing coordinate for that literal identification.

No general division-free Hilbert Green witness, storage sign, contractivity,
moment Gram, strictness, or spectral conclusion follows in this increment.

## Public declarations and validation

New module: `CompletedNativeChiralReturnGammaPortTest.lean`.
Five theorems, no new carrier or source definition:

- `canonicalCompletedC3AmbientInducedSource_mem_port_iff_leak_zero`;
- `canonicalCompletedC3AmbientResponse_eq_gammaPort_add_resolvedLeak`;
- `canonicalCompletedC3AmbientResponse_exists_gamma_iff_leak_zero`;
- `canonicalCompletedC3AmbientResponse_no_gammaPort_at_witness`;
- `canonicalCompletedC3AmbientResponse_inner_eq_gammaLeak_fourTerms`.

The dedicated audit checks axioms and the transitive source firewall for all
five roots. It passed for 6049 reachable declarations, with only
`[propext, Classical.choice, Quot.sound]`. No HP/Stieltjes certificate,
canonical moment target, Hankel/Jacobi-height positivity, Herglotz input,
or BR2 declaration is reachable from these roots.

Validation commands:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnGammaPortTest
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnGammaPortTestAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

Focused logs: `/tmp/chiral-gamma-port-build.log`,
`/tmp/chiral-gamma-port-audit.log`; complete validation logs are retained in
`/tmp/chiral-gamma-port-validation/` on llm. Publication is contingent on all
commands passing; final Git agreement is recorded in the delivery.

All listed validation commands passed before publication. The complete log
result is `FULL_VALIDATION_PASSED`; the full kernel script ended with
`kernel audit passed`. No new source warnings, placeholders, axioms, trust
escapes, dependency edits, or Foundation changes were introduced.

Files changed: the new theorem/audit modules, root imports, public theorem
registry, this report, README, and the append-only research checkpoint.
