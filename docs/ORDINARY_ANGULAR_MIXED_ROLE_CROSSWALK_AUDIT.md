# Ordinary angular / mixed-role Green crosswalk audit

## Checkpoint and scope

- Audited initial `HEAD = main = origin/main`:
  `8521cf31e399a2644b85918cb4cf16041269d343`.
- `git pull --ff-only`: already up to date; initial working tree clean.
- Historical map supplied by the user:
  `FORMALIZACAO_LEAN4_TEORIA_DO_CARRY_AO_OPERADOR_GENUINE.md`.
  Its `primos` snapshot is historical (`975f709...`), not the current authority.
- The formulas used below were checked in the actual pinned CPFormal checkout:
  `65d50f6db1208708e109982ba97e1d51d3039956`.
- No package revision, existing carrier, metric, completion or Foundation was changed.

Statuses:

```text
PASS_ORDINARY_ANGULAR_PREFIX_GREEN_CROSSWALK
NO_GO_ORDINARY_ONLY_CORRECTION_AS_FULL_MIXED_PROVENANCE
```

The second status concerns substitution on **all states of the current mixed
carrier**, not a constrained canonical orbit. Neither status proves positivity,
contractivity, complementary-channel existence, or division-free Hilbert sewing.

## Type and role audit

| Object | Type / parameters | Roles and provenance |
|---|---|---|
| `CarryVerticalL2` | complex vertical Hilbert carrier, coordinates `ℕ` | Existing bundled ordinary and log-gradient prefixes; the indices below are consecutive material edges. |
| `CanonicalCompletedC3HilbertState` | `CarryVerticalL2 × CarryVerticalL2` | Ordinary, logJet. |
| `CanonicalC3AllCutoffMixedSourceHilbert` | `WithLp 2 (CanonicalCompletedC3HilbertState × WithLp 2 (CanonicalCompletedC3HilbertState × CanonicalCompletedC3HilbertState))` | `zSource`, `wSource`, `reflectedZSource`, each retaining both roles. |
| `canonicalC3AllCutoffMixedSourcePrefixState M z w` | `CanonicalC3AllCutoffMixedSourceHilbert` | Existing prefixes of length `3*M` at `z`, `w`, `reflectedParameter z`. |
| `canonicalAngularGradientBlock m s` | `ℂ` | Historical ordinary block with weights `1,2,0`: `-(g_s(3m)+2*g_s(3m+1))`. |
| `finiteCanonicalAngularLocalGreenCorrection M s` | `ℂ` | Ordinary/ordinary reflected correction, including the dormant third edge. |
| `finiteCanonicalAngularPairingOffDiagonal M s` | `ℂ` | Every ordered pair of distinct synthesized angular blocks. |
| New ordinary observations | `ℕ → CanonicalC3AllCutoffMixedSourceHilbert → ℂ` | Read the retained ordinary coordinates. They are observations, not lossless encoders or linear maps. |
| `canonicalC3BracketTfvdMixedGreenReadout M z w` | `ℂ` | Existing finite bracket Green readout. Only its ordinary reflected port component is identified below, with `z=w=s`. |
| `CanonicalC3AllCutoffMixedSourceHilbert.greenProvenanceReadout M direct reflected x` | `ℂ` | Existing ordinary/logJet edge wedge minus the ordinary Green port pairing. It is not the historical ordinary-only correction. |

The new observations retain the input carrier unchanged. Their output does
not claim to recover that carrier, its logJet role, trace or completion.
Finite sums need no new membership or boundedness theorem; the canonical
prefixes and finite-support probes use existing `CarryVerticalL2` membership.
There is no replacement of complete vector synthesis by a trace inverse.

## Exact ordinary sewing

Write `g = ordinary(s)`, `h = ordinary(reflectedParameter s)`, both cut off
at `3*M`, and `b_m(g)=-(g_(3m)+2*g_(3m+1))`. The local correction is exactly

```text
L_M = Σ_(m<M) [2 conj(g_(3m)) h_(3m+1)
              +2 conj(g_(3m+1)) h_(3m)
              +3 conj(g_(3m+1)) h_(3m+1)
              - conj(g_(3m+2)) h_(3m+2)].
```

The off-diagonal term `O_M` reuses `finiteOffDiagonalPortWronskian` and
contains every ordered distinct-block term. Scalar synthesis is performed
before forming the scalar pairing `A_M`. The kernel proves

```text
A_M = inner ℂ g h + L_M + O_M.
```

This is `canonicalC3OrdinaryAngularPrefix_ledger`. It reuses
`finiteCanonicalAngularScalarPairing_eq_green_add_correction` and
`finiteReflectedGradientPairing_eq_inner_completedC3Prefixes`.
All three new canonical-prefix observations are proved literally equal
to their historical counterparts; there is no coefficient adjustment.

The existing Green-port coefficient then yields

```text
canonicalC3BracketTfvdMixedGreenReadout M s s
 = (cpRadialDifference 3 (criticalDisplacement s.re) : ℂ)
     * (A_M - L_M - O_M).
```

This is `canonicalC3BracketGreenReadout_eq_radial_mul_correctedAngular`.
Its proof uses the existing bracket Green equality and the existing radial
coefficient-times-prefix-Gram theorem. The order of inner arguments and
conjugation is preserved. It is a **reflected ordinary finite-port crosswalk**,
not a completed Wronskian identity or a two-independent-parameter sewing.
No claim that its radial factor or reflected pairing is nonnegative is made.
No boundary, tail, Xi, archimedean or chart term is silently canceled.
Those completed channels remain outside this finite identity.

## Decisive mixed-role canary

The finite-support probe is an actual element of the same mixed carrier:

```text
zSource          = (ordinary = 0, logJet = a * δ_materialEdge1)
wSource          = (ordinary = δ_materialEdge0, logJet = 0)
reflectedZSource = (ordinary = 0, logJet = 0).
```

For every complex `a`, the kernel proves

```text
ordinary local correction       = 0
ordinary off-diagonal correction = 0
greenProvenanceReadout 1 0 0 probe(a) = -a.
```

In the first cell, the first-leg wedge is `0*0 - 1*a = -a`; the other
wedge and the Green port paired with the zero reflected source contribute
zero. The sign comes from `sameSEdgeBoundaryWedge` as actually defined,
not a transported real-inner convention.

At `a=1`, this gives the exact contradiction `0 ≠ -1`. Consequently

```text
¬ ∀ x : CanonicalC3AllCutoffMixedSourceHilbert,
    localCorrection 1 x + offDiagonal 1 x
      = greenProvenanceReadout 1 0 0 x.
```

The labels `0,0` are arbitrary finite port parameters in this probe, not
physical-strip samples or a height/time/depth identification. The probe
is not claimed to be a canonical ordinary/logJet source orbit. Therefore
this result **does not exclude** a crosswalk on that constrained orbit.
It excludes treating the ordinary-only correction as the full mixed form
on the ambient carrier. No positivity inference follows from the probe.

## Upstream alternative and one remaining seam

The current CPFormal already contains the logJet counterpart:

- `canonicalEnrichedTfvdCpLogJetCommutatorWedgeTriple_eq_canonical`;
- `canonicalReflectedCpLogJetCommutatorWedge_eq_neg_log_mul_green`;
- `canonicalLogJetGreenDefectTriple_eq_enriched_commutator_add_residual`;
- `finiteCanonicalLogJetGreenDefectTrace_eq_cutoff_add_bulk_sub_green`;
- `finiteCanonicalLogJetGreenDefectTrace_eq_commutator_add_residual`.

These maintain the three material edge roles and explicitly retain the
vertex/cutoff residual. They were audited as a next route, not imported as
a proof of current mixed sewing or of a nonnegative complementary channel.
In particular, the commutator alone is not the whole logJet defect.

**Single remaining sewing obligation:** establish the provenance-preserving
comparison between the existing two-parameter canonical **ordinary/logJet**
finite mixed ledger and the existing enriched logJet commutator-plus-residual
ledger. The reflected single-parameter ordinary identity above does not
provide that comparison. No encoder, assumption wrapper or target-fitted
metric is introduced to fill it.

This is a finite role comparison before any completion limit. It must
preserve the constrained ordinary/logJet source relationship, independent
parameter orientation, the dormant edge, cutoff/vertex terms, and all
ordered cross terms before returning to completed Pythagorean sewing.

## Public declarations

- `canonicalC3OrdinaryAngularBlockReadout`;
- `canonicalC3OrdinaryAngularLocalCorrectionReadout`;
- `canonicalC3OrdinaryAngularOffDiagonalReadout`;
- `canonicalC3OrdinaryAngularScalarReadout`;
- `canonicalC3OrdinaryAngularBlockReadout_prefix`;
- `canonicalC3OrdinaryAngularLocalCorrectionReadout_prefix_eq_historical`;
- `canonicalC3OrdinaryAngularOffDiagonalReadout_prefix_eq_historical`;
- `canonicalC3OrdinaryAngularScalarReadout_prefix_eq_historical`;
- `canonicalC3OrdinaryAngularPrefix_ledger`;
- `canonicalC3BracketGreenReadout_eq_radial_mul_correctedAngular`;
- `canonicalC3AngularLogRoleProbe`;
- `canonicalC3OrdinaryAngularRoleProbe_corrections_zero`;
- `canonicalC3AngularLogRoleProbe_mixedProvenance`;
- `not_ordinaryAngularCorrection_eq_mixedGreenProvenance_on_all_sources`;

## Trust and validation

The dedicated audit applies `#assert_prime_depth_source_axioms` and
`#print axioms` to all 14 public declarations. Its source dependency
firewall traverses both types and proof values: **5710 reachable declarations**,
with no canonical moments, HP/Stieltjes certificates, Hankel, Jacobi/height,
Herglotz or BR2 inputs. The footprint is at most
`[propext, Classical.choice, Quot.sound]`.

Commands:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedC3OrdinaryAngularMixedRoleCrosswalk
lake build --wfail CarrySelfAdjointOperator.CompletedC3OrdinaryAngularMixedRoleCrosswalkAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

All listed commands passed. Root build: 9531 jobs; main Audit: 9726 jobs.
The full script ended with `kernel audit passed`; static audit and
`git diff --check` passed. No new warning was accepted under `--wfail`.

Logs are retained on `llm` under `/tmp/ordinary-angular-role-validation/`.
The audit includes kernel checking, a trust-escape scan and registry validation.
No historical package or existing theorem was modified.

Files changed: the new crosswalk module and dedicated audit, root imports,
`audit/theorem-registry.json`, this report, README source-frontier paragraph,
and an append-only `docs/CHECKPOINT_AUTO_ADJUNTO.md` entry.
The published final SHA and final clean/synchronized Git state are reported
in the delivery, rather than embedded in the commit that they describe.
