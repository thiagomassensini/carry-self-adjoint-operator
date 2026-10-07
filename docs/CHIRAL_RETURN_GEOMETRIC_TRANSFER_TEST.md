# Exact finite transfer of the completed chiral return

## Checkpoint and scope

Initial published main: `8fd27ece4200b60e6bf02c9dccc9214870da3932`.
`git pull --ff-only` reported up to date; HEAD, main and origin/main agreed;
the initial working tree was clean. Work stays on main.

Status: `PASS_FINITE_COMPLETED_SOURCE_RETURN_TRANSFER`.
The positivity frontier remains `PARTIAL_COMPLETED_SOURCE_ENERGY_POSITIVITY`.

The question tested is whether the actual incident synthesis determines an
actual returned vector in the original Cauchy geometry. It does, for every
finite family. This is not yet a source-derived compression of an ambient
isometry and does not prove contractivity. The historical discussion about
bounded factorization supplied a diagnostic: boundedness must be separated
from the quantitative constant one. Main declarations are the authority.

## Existing maps audited

| Object | Lean type / carrier | Provenance and limitation |
|---|---|---|
| `ChiralReturn.sourceValue k c r` | `CanonicalCompletedNativeChiralCauchyCarrier` | Complete characteristic F, divided by the original positive chiral coordinate, then finite Cauchy synthesis. |
| `ChiralReturn.sourceCompanion k c r` | Same Cauchy carrier | Literal complete companion −F′ and the same denominator/synthesis. |
| `source_pair_eq_bracketTfvd` | Equality of the two vector syntheses with completed TFVD trace readouts at every cutoff M | Preserves exact completed response. It does not invert the trace into a full structured TFVD state. |
| `completedScalarBoundaryPositivePolarization`, `completedScalarBoundaryNegativePolarization` | `CompletedScalarBoundaryTraceCarrier → CompletedScalarBoundaryTraceCarrier` | Two projections of the full boundary pair. Being contractions of that full pair does not make the second a contraction of the first. |
| `canonicalCompletedC3FullWronskianPositivePolarization`, `canonicalCompletedC3FullWronskianNegativePolarization` | `CanonicalCompletedC3FullWronskianOperatorCarrier → CanonicalCompletedC3FullWronskianOperatorCarrier` | Existing full-source chiral splitting. Sum of energies and signed difference have different roles. |
| `canonicalCompletedC3NaimarkPortEscapeReadout` | `RealifiedNaimarkComplexification →L[ℝ] CanonicalCompletedC3NaimarkPortEscapeCarrier` | Exact ambient port/escape energy conservation. The target is `WithLp 2 (RealifiedCameraComplexification × RealifiedNaimarkComplexification)`, not the Cauchy carrier. |
| `canonicalCompletedC3NaimarkPortEscapeSynthesis` | Reverse bounded real map | Reconstructs that ambient state. No existing identity identifies its port compression with the actual Cauchy return below. |
| Completed Gamma/resolved-leak and coisometric four-channel balances | Existing camera/ambient carriers and source readouts | Ordered channel pairings remain necessary. Their port-only no-go is preserved. |

No common-carrier intertwiner establishing that the actual Cauchy return is
one of these ambient contractions was supplied by this audit. This is not a
no-go for a future such intertwiner.

## Natural finite domain and unchanged metric

Namespace of all new declarations:
`CarrySelfAdjointOperator.ChiralReturn`.

The Hilbert carrier is unchanged:

```lean
CanonicalCompletedNativeChiralCauchyCarrier :=
  Lp ℂ 2 (volume : Measure unitInterval)
```

Write `u_(k,i) = completedNativeRadialChiralCauchyState k i` and
`q_(k,i) = completedNativeHermiteBiehlerChiralQuotient
(canonicalCompletedC3RadialTiltPoint k i)`.
The source monomials are the original half densities scaled by `sqrt(k+1)`;
their native pairing is `(k+1)/(i+j+2)`.

```lean
radialIncidentSynthesis (k N : ℕ) :
  (Fin N → ℂ) →ₗ[ℂ] CanonicalCompletedNativeChiralCauchyCarrier

radialReturnedSynthesis (k N : ℕ) :
  (Fin N → ℂ) →ₗ[ℂ] CanonicalCompletedNativeChiralCauchyCarrier
```

These are respectively `∑ i, c i • u_(k,i)` and
`∑ i, c i • (q_(k,i) • u_(k,i))`. No quotient, coefficient, source or sampling
point is changed.

`radialIncidentSynthesis_injective` is proved from the half-density monomial
provenance: an Lp-zero finite synthesis is zero almost everywhere, continuity
makes its polynomial factor zero on the real interval, and infinitely many
roots force every coefficient to vanish. This holds for every k and N,
including the empty family. No positivity hypothesis or target Gram enters.

```lean
RadialIncidentSpan (k N : ℕ) := (radialIncidentSynthesis k N).range
radialIncidentCoordinates (k N : ℕ) :
  RadialIncidentSpan k N ≃ₗ[ℂ] (Fin N → ℂ)
```

This is coefficient recovery on the incident span. Its norm is inherited
from the original Cauchy Lp; the coordinates are NOT claimed isometric.
Recovery is determined only by the incident monomials, independently of q
or any desired kernel. It is not interpolation of prescribed target Grams
and not reconstruction of a full TFVD state from scalar traces.

## Actual transfer and full polarization

```lean
radialReturnTransfer (k N : ℕ) :
  RadialIncidentSpan k N →L[ℂ] CanonicalCompletedNativeChiralCauchyCarrier
```

It is returned synthesis composed with incident coordinate recovery.
Continuity follows from finite-dimensionality of the domain. Its action is
unique on every incident synthesis, and the return remains in the SAME
incident span (`radialReturnTransfer_mem_incidentSpan`). No k- or N-uniform
norm estimate or infinite extension is inferred from finite dimension.

On the original nonzero positive chiral denominators:

```text
A(c) = C(c,1) + I V(c,1)
T A(c) = C(c,1) − I V(c,1).
```

Here C and V are exactly `sourceCompanion` and `sourceValue`. All tails,
Xi/archimedean/chart completion remain those of the existing characteristic
and completed trace theorem. No homogeneous finite material head replaces
this complete source. These are source-readout identities, not a claim
that the Cauchy pair encodes all independent structured TFVD coordinates.

For arbitrary independent c,d, the new polarized theorem proves exactly:

```text
inner A(c) A(d) − inner (T A(c)) (T A(d))
  = polarizedSourceBalance k c d 1 1.
```

Mathlib conjugates the first argument. This theorem retains both coefficient
families until AFTER full vector synthesis; it drops no cross terms. The
existing adjacent-clock corrected ledger therefore remains the same signed
source balance. The transfer is fixed at radius one, the original storage
gate; no identification of radius, material time, depth or height is made.

## Canaries and quantitative frontier

For every i : Fin N, the basis action is kernel checked:

```text
T A(single i 1) = q_(k,i) • u_(k,i).
```

This covers samples zero and one whenever present, and all higher finite
samples. It is an exact native-source test, not a fitted low-order proxy.
There is no assertion of a new sign for their combined synthesis.

The integrated storage identity is unconditional:

```text
Re storage k c 1 = ‖A(c)‖² − ‖T A(c)‖².
```

Thus the kernel proves:

```lean
‖radialReturnTransfer k N‖ ≤ 1 ↔
  ∀ c : Fin N → ℂ, 0 ≤ (storage k c 1).re
```

Under the existing strip/denominator regularity this is also exactly the
old complete four-channel camera-correction bound. Neither side is used as
a premise to establish the other as a fact. The all-order equivalence keeps
the original order of quantifiers, with no cutoff uniform in N:

```lean
(∀ N : ℕ, ∀ᶠ k : ℕ in Filter.atTop, ‖radialReturnTransfer k N‖ ≤ 1) ↔
  ∀ N : ℕ, ∀ᶠ k : ℕ in Filter.atTop,
    ∀ c : Fin N → ℂ, 0 ≤ (storage k c 1).re
```

**Single remaining obligation:**

```lean
∀ N : ℕ, ∀ᶠ k : ℕ in Filter.atTop,
  ‖ChiralReturn.radialReturnTransfer k N‖ ≤ 1
```

A geometrically proved ambient compression could prove this bound, but none
is postulated here. The finite transfer's existence, uniqueness and ordinary
boundedness do not provide constant one. No positivity or strictness PASS.

## Public declarations

- `radialIncidentSynthesis`, `radialReturnedSynthesis`
- `radialIncidentSynthesis_injective`, `RadialIncidentSpan`
- `radialIncidentCoordinates`, `radialIncidentVector`
- `radialIncidentVector_coe`, `radialIncidentVector_norm`
- `radialReturnTransfer`, `radialReturnTransfer_exact`
- `radialReturnTransfer_unique`
- `radialReturnedSynthesis_eq_incident_multiply`
- `radialReturnTransfer_mem_incidentSpan`
- `radialReturnTransfer_source_pair`
- `radialReturnTransfer_polarized_balance`
- `storage_one_eq_finiteTransfer_energy`
- `radialReturnTransfer_norm_le_one_iff_storage`
- `radialReturnTransfer_eventually_norm_le_one_iff_storage`
- `radialReturnTransfer_basis`
- `radialReturnTransfer_norm_le_one_iff_cameraCorrection`

## Audits and publication

The dedicated audit checks all 20 public definitions/theorems with
`#assert_prime_depth_source_axioms`, `#print axioms` and the transitive
`#assert_oriented_green_source` firewall. Both declaration types and values
are traversed: 6719 reachable declarations. No canonical moment, HP,
Stieltjes, Hankel, Jacobi/height, Herglotz or BR2 input is reachable. Maximum
footprint: `[propext, Classical.choice, Quot.sound]`.
Historical imports used by the global audit suite are not proof inputs.

Validation commands:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnFiniteTransfer
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnFiniteTransferAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

All seven validation steps completed successfully: focused module, focused
source/axiom audit, full root build, full root Audit, static audit, complete
kernel suite and `git diff --check`. Logs are retained on llm under
`/tmp/chiral-finite-transfer-validation/{module,focused-audit,root,root-audit,static,kernel-suite,diff}.log`.
The dedicated audit output records the 6719-declaration source closure and
all permitted footprints. No trust escape or placeholder was found.

Files: new module and dedicated audit; root module and Audit registrations;
`audit/theorem-registry.json`; this report; README; append-only research
checkpoint. Correct audited changes are committed directly to main. The
publication SHA and final clean/synchronized state are reported in delivery.
