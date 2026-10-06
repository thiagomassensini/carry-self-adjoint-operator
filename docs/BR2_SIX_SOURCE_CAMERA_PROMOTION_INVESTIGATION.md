# BR2 enriched pre-recovery → six-source camera promotion

## Result and starting point

Repository: `thiagomassensini/carry-self-adjoint-operator`, current `main`.
Initial `HEAD = main = origin/main`:
`ff90e00b213b05b9d48c9f77459ac7f5d3d8f6c1`.
The initial tree was clean and `git pull --ff-only origin main` was up to date.

**STATUS: PARTIAL_BR2_SIX_SOURCE_CAMERA_PROMOTION.**

A concrete kernel-checked test supports the proposed enriched-data mechanism:
the C3 pre-recovery states for BR2 indices `0` and `2` have a **nonzero
value-provenance coordinate pairing**, although their bracket pairing is zero.
The calculation does not identify that coordinate with a visible camera
channel or with `h₁`. No `incidenceLift`, `promotion`, or `U` realizing the
requested camera interface was constructed.

The first absent geometric arrow is the lift from the complete BR2
pre-recovery datum into the six parameter/channel roles. We stop at that
arrow; the geometric finite-camera Gram and its visible02 canary cannot be
asserted without it. This is an inventory finding, not a theorem that no
such lift can exist.

## Type audit before new code

Write `D(S) = NativeGpreFiniteTfvdAnalysisCarrier S` and
`D₆(S) = CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S`.

```text
(ℕ →₀ ℝ)
  │ br2CausalTfvdPreRecoveryIncidenceMap q S       [exists, real-linear]
  ▼
D(S) = (CarryVerticalL2 × (ℂ × ℂ)) × (boundaryValue × boundaryNumberFlux)
  │ geometric placement in the six source roles [FIRST MISSING ARROW]
  ▼
D₆(S)
  │ role-aware camera resolution                [canonical parameter families exist]
  ▼
CanonicalC3SixSourceRole → (ℕ →₀ D(S))
  │ no identification of role with camera slot
  │ scaffold promotion expects ℕ →₀ D(S), not this retained six-role family
  ▼
ℕ →₀ D(S)
  │ cameraChannelTfvdReconstruction q hq0 hq1 S  [exists, complex-linear]
  ▼
CameraResolvedCarryVertical = ℕ →₀ CarryVerticalL2
  │ restrictCameraResolvedCarryVertical
  │   canonicalC3SixCameraSlotLabel               [exists, complex-linear]
  ▼
FiniteHilbertFamily CanonicalC3SixCameraSlot CarryVerticalL2
```

The two scaffold aliases and their composition already exist:

- `BR2IncidenceToCanonicalC3SixSourceAnalysis S`;
- `CanonicalC3SixSourceToCameraChannelAnalysis S`;
- `br2CanonicalC3SixSourceFiniteCameraIncidenceMap`.

They consume supplied maps; they do not supply their geometric instances.
`CanonicalC3SixSourceRole` is parameter provenance times ordinary/logJet.
`CanonicalC3SixCameraSlot` is geometric leg times a `Fin 3` coordinate.
No enumeration equates them in this round. The enriched `GpreGraphRole`
value/numberFlux pair is likewise not the ordinary/logJet pair: the former
number-flux coefficient uses the native tower level. No log-gradient
identification is inferred from that name or from the underlying function
types.

### The ordinary promotion is already present on main

The old log-only file's scope must be read with its later companions.
`CompletedNativeCameraResolvedOrdinaryGradientPromotion.lean` supplies:

- `canonicalCameraResolvedOrdinaryValueLedger`: global boundary seed plus
  factorization-resolved boundary-free values;
- `cameraResolvedOrdinaryDirichletGradient`: consecutive differences of
  those values;
- `cameraResolvedSeededClockOrdinaryTfvdAnalysis`;
- `cameraResolvedSeededClockOrdinaryParameterAnalyses`: the boundary seed
  remains a separate field;
- `cameraResolvedSeededClockAffineSixSourceRoleAnalyses`;
- exact synthesis theorems for each role and for the complete six-source
  datum.

The ordinary value resolver subtracts its global seed before resolving
prime-camera voices; consecutive differences cancel the same global seed.
It is not an alias for the logJet input. These results already close the
ordinary **parameter-family** camera resolution; no new ordinary resolver
was invented here.

`CompletedNativeIndependentReflectedSixSourceLift.lean` independently
retains camera analyses for all six roles, with `u`, fixed `0`, and an
independent reflected input `v`. Its fixed-atlas camera sum recovers the
canonical analysis; physical reflection is imposed only in the final
section. This is a parameterized construction, not a real-linear map from
arbitrary BR2 incidence data into those roles. Its camera-indexed datum
retains all six roles; it does not instantiate the scaffold's single-analysis
per-camera promotion.

The corrected Green pair sums in the same file are `greenForm` pairings.
The full response also retains structural, tail, Hermitian-weight and chart
terms. Their existing scalar equalities are not positive Hilbert visible
Gram identities for the BR2 ledger.

## Concrete enriched correlation test

No target moment occurs in the definitions or proofs of the new canary.

Use the existing native context constructor

```lean
nativeGpreCanonicalActiveCommutatorContext ⟨2, Nat.prime_two⟩ 1 4
```

Prime `2`, arithmetic time `1`, analytic edge `4` give the positive native
provenance cell `2 * (4+1) = 10` and tower level `5`. The existing active-context
theorem proves its value coefficient is nonzero. The new address theorem
also proves that cell `10` is `alignedCenter 3 2 + 1`, the right leg of the
second even C3 bracket. No edge index was relabeled as depth or parameter role.

Let `c` be this context, `S = {c}`, and

\[
a=\operatorname{nativeGpreTowerCoordinateCoefficient}(c.\mathrm{withRole}\ value),
\qquad a\ne0.
\]

At the admissible TFVD parameter `q = 1/2`, the existing causal Green finite
coordinate formula gives exactly

\[
\operatorname{causal}(B₀)(10)=\frac1{64},\qquad
\operatorname{causal}(B₂)(10)=-\frac12.
\]

These are rational identities proved by finite sums and kernel-checked
arithmetic, not floating-point probes. The parameter was selected for an
exact small diagnostic; no value was calibrated against a moment.

The retained value-role coordinates of the actual enriched analyses are
therefore `a/64` and `−a/2`, giving

\[
\boxed{
\langle value(B₀)(c),value(B₂)(c)\rangle_{\mathbb C}
=-\frac{a^2}{128}\ne0.
}
\]

The coefficient is real and active by native geometry. The full enriched
analysis is retained; this is an examination of one of its coordinates,
not a replacement of the state by a one-dimensional carrier.

**Conclusion of the test:** enriched data do not have zero pairings in all
provenance coordinates. A route that drops the provenance and keeps only
the bracket discards this actual correlation. No magnitude/sign of a final
visible six-source coefficient follows from this observation alone.

### Trace and seed audit

The new theorem
`br2CausalTfvdPreRecoveryIncidenceState_trace_eq_zero` proves that the TFVD
trace of every supported causal BR2 prototype is `(0,0)`. This does not
remove the trace field or the native value/number-flux fields: they remain
in the full analysis. It identifies which field supplied the new canary:
value provenance, rather than a nonzero incoming TFVD trace.

The new exact recovery theorem
`br2CausalTfvdPreRecoveryIncidenceState_eq_analysisGreenBracket` also proves
that this causal enriched datum is determined by its bracket through the
existing Green map and full analysis. Thus the nonzero coordinate correlation
is not evidence of additional independent source degrees of freedom. A
bracket-only Gram fails to display this transformed-coordinate pairing,
but the underlying enriched values are recoverable. No metric-preserving
camera promotion or canonical coefficient identity follows from recovery.

The canonical ordinary parameter ledger has a global unit Dirichlet seed.
It cannot be identified with this zero causal TFVD trace. A source-role lift
must justify the boundary/parameter provenance rather than copying a unit
seed, duplicating the BR2 datum into six slots, or assigning source roles to
camera labels.

## Instantiation and requested canaries

| Requested object/test | Result |
|---|---|
| `incidenceLift` | No geometric instance; first missing arrow specified below |
| `promotion` | Canonical role-wise parameter families exist; no arbitrary-datum instance constructed |
| `U` | Not constructed |
| `total00`, `total02`, `total11` for `U` | Not tested because `U` is absent |
| Raw BR2/known total bracket-Parseval values | Already `6`, `0`, `6`; existing theorem reused as background, not reproved |
| Enriched value-provenance `02` | **Proved exactly `−a²/128 ≠ 0`** |
| `visible02 = h₁` | Not proved or refuted for a geometric promoted candidate |
| `blind02 = −h₁` | Existing conditional Parseval consequence; its realizing premise remains unproved here |

The zero total BR2 pairing and a nonzero enriched coordinate pairing are
compatible. The raw enriched storage carrier is not asserted to be an
isometric finite-camera family. Its coordinate pairing is not the total
Parseval Gram. The required energy-preserving camera promotion remains a
substantive construction.

## One first typed gap

To obtain the preferred incidence lift by preserving the complete
pre-recovery data, the missing geometric map has signature

```lean
NativeGpreFiniteTfvdAnalysisCarrier S →ₗ[ℝ]
  CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S
```

Its composition with `br2CausalTfvdPreRecoveryIncidenceMap q S` has exactly
the already named type `BR2IncidenceToCanonicalC3SixSourceAnalysis S`.
This map must justify the three parameter roles, their ordinary/logJet
channels and boundary provenance from the existing geometry. No instance
was chosen merely because any zero/duplicate linear map inhabits its type.

This is the **first** obstacle, so no metric or visible canary is claimed
for a hypothetical downstream composition. The role-wise camera functions
already present do not by themselves resolve this input bridge. No
conclusion of impossibility for the theory or for an enriched compression
is drawn.

## New declarations and trust footprint

Module: `CarrySelfAdjointOperator/BR2EnrichedPreRecoveryCorrelationCanary.lean`.
All names below are in `CarrySelfAdjointOperator`:

- `br2EnrichedCorrelationContext`;
- `br2EnrichedCorrelationAtlas`;
- `br2EnrichedCorrelationContext_cell`;
- `br2EnrichedCorrelationContext_cell_eq_second_even_right_leg`;
- `br2EnrichedCorrelationContext_valueCoefficient_ne_zero`;
- `br2CausalTfvdPreRecoveryIncidenceState_eq_fullAnalysis`;
- `br2CausalTfvdPreRecoveryIncidenceState_value_apply`;
- `br2CausalTfvdPreRecoveryIncidenceState_eq_analysisGreenBracket`;
- `br2CausalTfvdPreRecoveryIncidenceState_trace_eq_zero`;
- `br2CausalGreenResponse_C3_zero_two_at_ten`;
- `br2EnrichedPreRecovery_value02_pairing_eq`;
- `br2EnrichedPreRecovery_value02_pairing_ne_zero`.

All definitions and theorems are registered and have executable dependency
guards plus `#print axioms` in the scoped audit. Their dependency sets are
`[propext, Classical.choice, Quot.sound]`. No dependency was added and no
existing statement, positivity bound or no-go was modified.

## Validation and integration

Focused module and scoped audit builds passed with `--wfail`.
The full command ledger is appended after execution. The commit carrying
this report is located by
`git log --format='%H %s' -- docs/BR2_SIX_SOURCE_CAMERA_PROMOTION_INVESTIGATION.md`;
its exact SHA is supplied in the final handoff.


### Executed validation ledger

All commands completed with exit status **0** on the canonical SSH checkout,
with `/home/thlinux/.elan/bin` on `PATH`:

```text
lake build --wfail CarrySelfAdjointOperator.BR2EnrichedPreRecoveryCorrelationCanary
lake build --wfail CarrySelfAdjointOperator.BR2EnrichedPreRecoveryCorrelationCanaryAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

The final complete audit rebuilt/checked the final source, including the
Green-bracket recovery theorem, and ended with `kernel audit passed`.
The scoped executable guards and all twelve `#print axioms` outputs passed
with exactly `[propext, Classical.choice, Quot.sound]`.
The complete static audit scanned the local Lean surface for trust escapes
and validated the theorem registries. No GitHub Actions status is inferred
from these canonical server kernel checks.
