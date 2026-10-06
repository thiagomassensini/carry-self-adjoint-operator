# Nonseparable camera Parseval source transport: directed investigation

## Checkpoint and result

Repository: `thiagomassensini/carry-self-adjoint-operator`.
Initial `HEAD = main = origin/main`:
`0eb9c94c5150430e11150065d223624cbfc70f60`.
`git pull --ff-only origin main` reported up to date; the initial tree was clean.

**STATUS: PARTIAL_GEOMETRIC_PARSEVAL_SOURCE_TRANSPORT.**
**Remaining construction: MISSING_NONSEPARABLE_SOURCE_INTERTWINER.**

The directed source audit found no instantiated, geometrically derived
`CanonicalCompletedNativeTfvdCameraParsevalTransport C` with the visible
six-source coefficient theorem. This is a source inventory result, not a
mathematical proof that such a transport cannot exist. No new transport was
fabricated, no target-derived factorization was used, and the previous
unconditional six-frame upper bound was reused as background only.

The new kernel result excludes a precisely delimited class: a transport
whose C3 even-zero and even-one vectors have zero pairing between *every*
pair of outer source coordinates cannot realize the visible coefficient.
This condition is stronger than orthogonality of the total transported
vectors, which is required by source isometry and must remain true.

## Types and upstream candidates

Write `H = CanonicalCompletedTfvdGreenHilbertCarrier = CarryVerticalL2`
and `F(I,E) = FiniteHilbertFamily I E = PiLp 2 (fun _ : I => E)`.
The desired map is complex-linear `H → F(state,H)` and preserves the
complete source inner product. The following inventory preceded new code.

| Existing map/object | Domain → codomain | Linearity / metric | BR2/parity and coordinate behavior | Available readout theorem / missing link |
|---|---|---|---|---|
| `br2CameraBracketProjectiveHilbertMap` | `(ℕ →₀ ℝ) → H` | real-linear, injective | exact BR2 incidence realization; parity index retained | incidence maps to literal bracket; no camera compression |
| `br2FiniteTfvdHilbertRecovery` | `NativeGpreFiniteTfvdAnalysisCarrier S → H` | real-linear, exact reconstruction on analyzed input; no claim that channel norm is the source norm | recovery of BR2 analysis gives the same raw parity jet | `br2FiniteTfvdHilbertRecovery_comp_analysisMap`; recovering the raw bracket does not produce the target Gram |
| `br2CameraBracketProjectiveTfvdParityJet` | `ℕ ⊕ ℕ → NativeGpreTfvdProjectiveAnalysisCarrier` | family of coherent analyzed incidences, with independence transported through reconstruction | retains all finite atlas data | not a finite camera Hilbert state family or the required source isometry |
| `br2CausalTfvdPreRecoveryIncidenceMap` | `(ℕ →₀ ℝ) → NativeGpreFiniteTfvdAnalysisCarrier S` | real-linear | retains bracket, trace, and provenance data before recovery | bracket projection is the literal BR2 bracket; no typed map from all retained data to `F(state,H)` |
| `canonicalCompletedGreenFrameAnalysisCLM` | `H → CanonicalCompletedGreenFrameCarrier` | continuous complex-linear, injective; raw analysis is not asserted isometric | all-bases Green analysis | injectivity does not identify the six-source visible coefficient |
| `canonicalCompletedGreenFrameParsevalAnalysis` | `H →ₗᵢ[ℂ] CanonicalCompletedGreenFrameCarrier` | complex linear isometry | preserves complete inner product; four concrete Green channels | `canonicalCompletedGreenFrameParsevalAnalysis_inner`; no existing identification with the finite camera input `F(state,H)` and its required visible compression |
| `br2CausalTfvdParsevalGreenFrameIncidenceMap` | `(ℕ →₀ ℝ) → CanonicalCompletedGreenFrameCarrier` | real-linear | projects the restored bracket before Parseval; other pre-recovery data remain in their original carrier | isometric bracket realization is already guarded against treating its total Gram as the target |
| `finiteHilbertMatrixSynthesis A` | `F(input,H) → F(output,H)` | complex-linear | mixes outer coordinates through a real matrix; acts identically on the internal `H` coordinate | exact weighted inner-product formula; requires a source family as input |
| `finiteCanonicalCameraHilbertSynthesis C` / `finiteCanonicalCameraHilbertReadout C` | `F(camera,H) → F(state,H)` / reverse | complex-linear; synthesis is isometric when row Gram is PD | outer camera mixing, no BR2 input family constructed | readout/synthesis roundtrip; visible/blind Parseval split already proved |
| `CanonicalCompletedNativeTfvdCameraParsevalIncidenceTransport.ofGlobal` | global candidate → incidence candidate | constructor by composition with projective incidence map | preserves the supplied global candidate's parity images | requires the global candidate; it does not construct its `sourceTransport` |
| `nativeC3SeededClockTfvdSixSourceAnalysis M q S z w` | parameterized six-source state → `CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S` | six copies of existing complex-linear TFVD analysis applied to ordinary/log channels | retains `z`, `w`, reflected `z`, incoming seed/clock data before reconstruction | reconstruction gives the actual mixed-source prefix; its coefficient theorem comes from the synthesized scalar boundary ledger, not a BR2-to-camera isometry |
| `cameraChannelTfvdAnalysis` / `cameraChannelTfvdReconstruction` | `ℕ →₀ H` ↔ `ℕ →₀ NativeGpreFiniteTfvdAnalysisCarrier S` | complex-linear, channelwise recovery | outer prime-camera labels retained; applies the same internal map to each channel | synthesis commutes with TFVD; no isometric map from arbitrary `H` to a fixed finite camera family |
| `canonicalCompletedC3NaimarkPortEscapeIsometry` | `RealifiedNaimarkComplexification →ₗᵢ[ℝ] CanonicalCompletedC3NaimarkPortEscapeCarrier` | real linear isometry | preserves intrinsic camera port and orthogonal escape | actual lossless split, but begins in an existing Naimark ambient state; not a complex-linear BR2 source entry |
| `NaimarkProjectorIntertwiningSeam` | proposition about supplied `E,J,R,V,U,Ustar` | conditional algebra of linear maps | readout and synthesis commuting squares | no state-to-ambient embedding is supplied; the file explicitly separates this missing construction |

Files inspected also include
`CompletedTfvdGreenAllOrderIntertwining.lean`,
`CompletedNativeTfvdSixSourceCenterLegBridge.lean`,
`EnrichedMovingCameraCompletedNaimarkCrosswalk.lean`,
`MultibaseTfvdCameraGramHilbertTransport.lean`,
`MultibaseCameraLogTfvdChannelTransport.lean`,
`BR2GreenFrameDslopeLimitBridge.lean`, and
`CompletedNativeTfvdPreRecoveryIncidenceAudit.lean`.

A directed search for uses of the transport structure, `sourceTransport :=`,
`incidenceTransport :=`, and the canonical Hilbert camera readout confirmed
that the global camera transport occurs as an interface/argument; the
incidence `ofGlobal` constructor consumes it. The audited finite-camera
maps are not an upstream instantiation of it.

The six-source normalized response includes the actual reconstructed Green
boundary, scalar structural term, completed tail term, mixed weight, and
archimedean chart channel. Its equality with the canonical scalar response
is already proved. That scalar equality does not construct a linear map of
arbitrary BR2 vectors into a finite camera state family. No radial complex
Taylor target was introduced here.

## Exact source-correlation obligation

Let `R = finiteCanonicalCameraReadout C`, `P = Rᵀ R`, and let `U` be a
candidate's source transport. The newly proved identity is

\[
\langle R Ux,R Uy\rangle
 = \sum_{a,b} P_{ab}\langle (Ux)_a,(Uy)_b\rangle.
\]

`visible_inner_eq_sourceChannelGram` is an immediate specialization of the
existing matrix-synthesis inner-product theorem. It adds no metric, weights,
state, or moment-based construction. Its all-order counterpart is
`realizesSixSourceVisibleCoefficient_iff_sourceChannelGram`.

For C3, write `B₀` for even zero and `B₂` for even one. The source isometry
must preserve `⟨UB₀,UB₂⟩ = 0`. Nonetheless, its individual channel pairings
must not all vanish: their **camera-weighted** sum must be `h₁ ≠ 0`.
Nonseparability is necessary but is not itself a coefficient theorem.
Here "channel pairings" includes both `a = b` and `a ≠ b`; the new theorem
does not require the nonzero pair to have distinct outer indices.

The new no-go assumes only that all these channel pairings vanish and then
uses the existing exact six-source coefficient identity and existing
`canonicalCompletedNativeLogDerivativeMoment_one_ne_zero`. It does not
assume positivity, a correction, or a loss map.

For any candidate that does realize the visible coefficient, the existing
camera Parseval split forces

\[
\langle B U B₀,B U B₂\rangle=-h₁.
\]

This is `blind_even01_eq_neg_nativeMoment_one_of_realizes`. It is explicitly
conditional on the coefficient realization; no realizing candidate has
been constructed by this theorem.

## Canary results

No geometrically justified `U` with the required type was found, so the four
canaries cannot be reported as passed for a new concrete candidate.

| Canary | Exact required visible value | Result of this round |
|---|---|---|
| even00 | `h₀` | open for a concrete geometric transport |
| even01 | `h₁` | impossible for the entire class with all even01 source-channel pairings zero; any realizing transport has a nonzero channel pairing and blind pairing `−h₁` |
| odd00 | `h₁` | open for a concrete geometric transport |
| mixed00 | `0` | open for a concrete geometric transport; total source orthogonality alone does not prove visible mixed orthogonality |

The earlier literal-BR2 and rank-one no-gos are preserved. The new result
extends the diagnostic beyond rank one, without excluding all nonseparable
geometric maps or the theory.

## New Lean declarations

Module: `CompletedNativeTfvdCameraSourceCorrelationGate.lean`.
Namespace prefix:
`CarrySelfAdjointOperator.CanonicalCompletedNativeTfvdCameraParsevalTransport`.

1. `visible_inner_eq_sourceChannelGram`.
2. `realizesSixSourceVisibleCoefficient_iff_sourceChannelGram`.
3. `visible_inner_eq_zero_of_sourceChannelOrthogonal`.
4. `not_realizesSixSourceVisibleCoefficient_of_even01_sourceChannelOrthogonal`.
5. `exists_even01_sourceChannel_pairing_ne_zero_of_realizes`.
6. `blind_even01_eq_neg_nativeMoment_one_of_realizes`.

All six are guarded and printed in
`CompletedNativeTfvdCameraSourceCorrelationGateAudit.lean`, imported by the
central audit and recorded in `audit/theorem-registry.json`.
Each uses exactly `[propext, Classical.choice, Quot.sound]`.
No new transport, measure, Hilbert space, operator, positive factorization,
or local mathematical assumptions were added to existing statements.

## One remaining construction

Construct from the upstream geometric data an actual
`candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C` satisfying

```lean
candidate.RealizesSixSourceVisibleCoefficient M q hq0 hq1 S base radius
```

Its underlying missing map has type

```lean
CanonicalCompletedTfvdGreenHilbertCarrier →ₗ[ℂ]
  FiniteHilbertFamily state CanonicalCompletedTfvdGreenHilbertCarrier
```

and must preserve inner products. The exact coefficient obligation is the
weighted source-correlation equation above, for every parity pair. The
camera and source-channel maps must be supplied geometrically, independently
of those target coefficients. The finite TFVD-to-camera/Naimark embedding
is the first absent typed arrow found in the directed inventory.

Once a genuine realizing candidate exists, reuse
`realizesSixSourceVisibleCoefficient_iff_energyExcess`; no independent blind
Gram proof or arbitrary loss map is needed. A HP/Stieltjes handoff still has
the existing visible-incidence faithfulness guard. Source isometry and a
visible/blind split alone do not prove global injectivity of the compressed
visible map; this round does not discharge or hide that guard.

## Role of the numerical finite operator

The user also pointed to
`/home/thlinux/Downloads/native_carry_r2_height_operator_parallel_order_audit_verbose.py`.
It was inspected read-only and not executed or modified. Its order is:
material sample germs → scalar finite camera plus tail → scalar dressing →
logarithmic moments → Chebyshev Jacobi → eigensystem → height matrix.
It supplies numerical target values for future canary tests, not the
upstream BR2 source transport. Constructing `U` from its moment/Jacobi
factorization would violate the provenance direction of this round.
Comparisons must use moments before `rescaled_moments`, since that function
changes their scale. No numerical evidence was promoted to a Lean theorem.

## Additional user-supplied camera/POVM notes

Four files were inspected in full, read-only, during the same round:

- `/home/thlinux/Downloads/INVARIANCIA_C2_HAAR_DUPLO_LOG4.md`;
- `/home/thlinux/Downloads/OPERADOR_ESPECTRAL_CAMERAS_DEFECT_WEYL (1).md`;
- `/home/thlinux/Downloads/SEGUNDO_MOMENTO_CENTRADO_DEFECT_PROBES_E_POVM (1).md`;
- `/home/thlinux/Downloads/LIMITE_ALL_BASES_LOWER_FRAME_E_COLAPSO_BULK.md`.

Their mathematical claims and numerical audits are blueprint evidence,
not new Lean premises or kernel-checked results of this round.

The most relevant construction in the notes is the geometric operator-valued
measure `D(x) M₀ D(x) dx`, where `M₀` is the periodic camera-profile Gram and
`D(x)` selects each camera's physical horizon. Its proposed normalized
isometric dilation is

\[
(Vv)(x)=R D(x)G_{\mathcal C}^{-1/2}v,
\qquad M₀=R^*R.
\]

This is materially different from `Ux = (a_k x)_k`: the support depends on
the outer camera as well as the interior variable. It gives a useful
architecture for the missing nonseparable map, independently of the target
moments. However, its source is a **finite camera-coordinate space** and its
target is a continuous `L²` space built from periodic profiles. The required
source here is the arbitrary BR2 completed vertical carrier, and the target
is the existing finite family of that same carrier. The notes supply no
map identifying these types and no readout theorem identifying this POVM's
logarithmic camera moments with the completed six-source coefficients.
A dilation of this new measure was therefore not introduced as a substitute
for the requested existing camera transport.

The C2/Haar note correctly distinguishes a representation shear with a
matched physical horizon from a change of horizon. A pure outer shear alone
does not remove the already proved rank-one obstruction when the full
source remains rank one. The notes' support-dependent `D(x)` is the feature
that could go beyond that obstruction. It still requires the absent BR2
entry and the four visible canaries before any six-source claim.

The endpoint/return architecture was also checked against the actual local
`CompletedNativeReturnMetricReadoutCrosswalk.lean`. It already provides
`canonicalNativeGreenFrameExternal`, `canonicalNativeGreenFrameBulk`,
`canonicalNativeGreenFramePoisson`,
`canonicalNativeGreenFramePoisson_intertwines`, and
`canonicalNativeGreenFrameReturnMetric_isometry`. Their source is
`GreenFrame.Concrete.State`; the endpoint codomain is
`ConcreteExternalSpace`, with return into `BulkGreenSpace`.
The precise local theorem
`canonicalNativeGreenFrameReturnReadout_eq_state_inner` says that the full
endpoint-plus-return pairing recovers the original state Gram. It does not
supply the different compressed visible Gram required here. The existing
`canonicalNativeReturnMetricCentralDefect_pos` likewise guards against
identifying the concrete ordinary-gradient return energy with `h₀`.
No return metric was changed to bypass that guard.

The all-bases note warns that a fixed finite endpoint atlas can have a kernel,
while uniform growth of the atlas can collapse the bulk. It supports keeping
all source channels and checking an actual energy identity; it is not a
proof of a completed six-source coefficient realization. No base weights,
new measure, or limiting atlas were chosen in this round.

Thus the files refine the architecture to a **coordinate-dependent geometric
analysis**, followed by the existing camera split. They do not close the
single missing BR2-to-camera transport with its coefficient equation.

## Validation and integration

Focused module and scoped audit builds passed with `--wfail`. All six
`#print axioms` outputs and executable guards passed.
Full library build, central audit, static audit, complete kernel audit, and
`git diff --check` are recorded in the validation ledger appended after
execution below. No new dependency was added.

The commit carrying this report is identified by
`git log --format='%H %s' -- docs/NONSEPARABLE_CAMERA_PARSEVAL_TRANSPORT_INVESTIGATION.md`;
the final handoff gives the exact commit SHA. A commit's own SHA cannot be
embedded in that same commit's contents.


### Executed validation ledger

All commands below completed with exit status **0** on the canonical SSH
checkout, with `/home/thlinux/.elan/bin` on `PATH` for Lean commands:

```text
lake build --wfail CarrySelfAdjointOperator.CompletedNativeTfvdCameraSourceCorrelationGate
lake build --wfail CarrySelfAdjointOperator.CompletedNativeTfvdCameraSourceCorrelationGateAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

The static audit scans the complete local Lean surface for trust escapes and
validates the registries. The complete audit ended with `kernel audit passed`.
The scoped audit prints all six dependency sets and rejects dependencies
outside `[propext, Classical.choice, Quot.sound]`.
These are actual Lean kernel checks on the canonical server checkout;
no GitHub Actions result is inferred from them.
