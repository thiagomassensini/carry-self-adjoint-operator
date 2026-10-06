# Oriented completed source: division-free Green audit

## Status and checkpoint

**PARTIAL_ORIENTED_COMPLETED_SOURCE_DIVISION_FREE_GREEN_REPRESENTATION**.

Audited published `main`: `19ba7534471e9c13271f2476ea354851167e4e94`.
`git pull --ff-only` reported already up to date; HEAD, local main and
origin/main agreed. Initial working tree was clean. This round works only on
main. The final published commit is the commit containing this report; its
hash and remote agreement are recorded in the delivery, not recursively in
its own contents.

The kernel proves boundary recovery, two state-presentation equalities,
a failure of the current maximum norm to be a Hilbert norm, the limited
scope of the real-axis wrapper, and a zero-cutoff completion obstruction.
It does **not** supply a new division-free Hilbert representation,
contractivity, storage nonnegativity, or moment positivity.

No canonical definition or metric has been modified. Existing source moment
recurrence, normalized vector jets, signed projective pairing and corrected
Green ledger identities remain the upstream checkpoints.

## Exact division-free target and conventions

In `DivisionFreeGreenConfinement.lean`:

```lean
completedGreenWronskian F C z w =
  C z * (starRingEnd ℂ) (F w) - F z * (starRingEnd ℂ) (C w)

HasDivisionFreeGreenRepresentation F C state :=
  ∀ z w : ℂ,
    completedGreenWronskian F C z w =
      (z - (starRingEnd ℂ) w) * inner ℂ (state w) (state z)
```

Here `F = completedNativeOperatorCharacteristic` and
`C = completedNativeOperatorBoundaryCompanion = -F'`.
The inner product is conjugate-linear in its first argument. The global
predicate quantifies over all complex parameters; the existing on-domain
variant has an explicitly restricted domain. Neither follows from equality
of real-axis scalar readouts.

`hasCanonicalCompletedNativeRealAxisNormalizedGreenKernel_of_divisionFreeGreen`
already promotes a division-free identity plus continuity. It is a consumer;
no new application is possible without an actual source witness. Likewise
`canonicalCompletedC3AllCutoffOrientedRealKernelReadout_eq_parsevalInner`
requires `HasCompletedNativeRealAxisNormalizedGreenKernel state`; it has not
been used as a positivity premise.

## Carrier and map inventory

Notation in this table: `H = CarryVerticalL2 = ℓ²(ℕ, ℂ)`,
`G = CanonicalCompletedGreenFrameCarrier = GreenFrame.Concrete.ConcreteAnalysisSpace`,
`R = NativeGpreTfvdCompletedPrecompressionSource`.
These are abbreviations for the actual types, not new carriers.

| Existing object | Lean type / scalar structure | Retained data and provenance | Continuity / metric status |
|---|---|---|---|
| `CanonicalCompletedC3HilbertState` | `H × H` | Ordinary and log-jet completed differences | Each factor is complex Hilbert; the outer ordinary product uses the maximum norm |
| `canonicalCompletedC3GreenFramePairIntertwiner` | `CanonicalCompletedC3HilbertState →L[ℂ] (G × G)` | Raw concrete Green analysis applied separately to both channels | Bounded and injective; raw analysis is not asserted isometric |
| `canonicalCompletedGreenFrameSynthesis` | `G →L[ℂ] H` | Existing inverse-frame/adjoint synthesis | Bounded; synthesis after analysis is exactly identity |
| `R` | `NativeGpreTowerHilbert × NativeGpreTowerHilbert`, with `NativeGpreTowerHilbert = ℓ²(ℕ, ℝ)` | Two real precompression coordinates; canonical source uses its fixed residual generator | Real complete normed product; not already a complex Hilbert channel |
| `CanonicalCompletedC3OrientedGreenFrameCarrier` | `(G × G) × R` | Both raw analyzed channels and the retained real residual | Complete real normed product; its current maximum norm fails the parallelogram identity |
| `canonicalCompletedC3OrientedGreenFramePrefixState M s` | Oriented carrier | Finite ordinary/log prefixes and real reflected pairing residual | Defined for all `s`; zero at `M = 0` |
| `canonicalCompletedC3OrientedGreenFrameState s hs` | Oriented carrier, with summability-domain proof `hs` | Completed gradient/log sequences and `infiniteReflectedGreenEnergy s` residual | Existing cutoff norm convergence is not a proof of continuity in the complex parameter |
| `canonicalCompletedC3RealAxisOrientedGreenFrameStateComplex` | `ℂ → CanonicalCompletedC3OrientedGreenFrameCarrier` | Previous source evaluated at `operatorHeightParameter (z.re : ℂ)` | A real-axis wrapper; discards imaginary parameter dependence |
| `CanonicalCompletedC3RealAxisResidualHilbert` | `WithLp 2 R` | The existing real residual with the existing product Hilbert structure | Real Hilbert and complete |
| `CanonicalCompletedC3RealAxisPositiveCarrier` | `WithLp 2 (G × WithLp 2 (G × RealHilbertComplexification CanonicalCompletedC3RealAxisResidualHilbert))` | Existing orthogonal ordinary/log Parseval channels plus complexified residual | Complex Hilbert and complete; it is already present in main |
| `CanonicalC3BracketTfvdCompletionState M` | Structure with `transport : FiniteC3EnrichedTfvdPairTransportData M`, `valueTail : ℂ`, `logJetTail : ℂ` | Enriched head, both exact tails, Green port | Structured completion data; no global Hilbert kernel is claimed by its scalar projections |
| `CanonicalC3BracketTfvdCompletionState.greenPort` | `CanonicalC3BracketTfvdCompletionState M → FiniteC3GreenPortCarrier (M * 3)` | The transport's bracket Green port | Does not itself incorporate the two tail fields |
| `canonicalC3BracketTfvdCompletedTracePair` | `(M : ℕ) → ℂ → ℂ × ℂ` | Tail-completed, chart-normalized and Xi-completed `(F,-F')` | Equality on the completed domain is proved; a trace is not an inverse to the full structured state |
| `canonicalCompletedC3AllCutoffOrientedFinalReadout` and real-kernel readout | Parameter-dependent scalar readouts of the oriented mixed source / completed ledger | Radial Green plus provenance, off-diagonal, readout, tail and archimedean/chart terms | Exact ledger / dslope identities; not a one-point Hilbert Gram identity |

`GreenFrame.Concrete.State` is the positive-natural-index ℓ² source, related
to `H` by the existing reindexing isometry. Its raw all-bases analyzed carrier
contains external seed/residual and depth-one/bulk Green coordinates. This
is different from the finite C3 symplectic Green port and its scalar
Wronskian. Their existing intertwining/readout identities do not identify
all these forms as one positive norm defect.

## What the kernel added

Module: `CompletedC3OrientedGreenSourcePresentationAuditBridge.lean`.

1. `canonicalCompletedGreenFrameSynthesis_preserves_weightedTrace`:
   both vertical trace coordinates of every input survive raw analysis and
   the existing bounded synthesis.
2. `canonicalCompletedGreenFrameSynthesis_weightedTfvd_reconstruction`:
   the recovered input still satisfies the complete weighted TFVD identity,
   including boundary return.
3. `canonicalCompletedC3OrientedRecoveredHilbertPresentation`:
   recover the ordinary/log pair with existing synthesis, apply existing
   Parseval analysis, and retain the real residual in the existing
   complexification and `WithLp 2` carrier. This map depends on no moment,
   height spectrum or target kernel. No isometry on the whole ambient raw
   analysis carrier is asserted.
4. `canonicalCompletedC3OrientedRecoveredHilbertPresentation_eq_existing`:
   on the actual real-axis wrapped source this presentation equals
   `canonicalCompletedC3RealAxisPositiveState`, exactly.
5. `canonicalCompletedC3OrientedRecoveredHilbertPresentation_dressed_eq_existing`:
   applying the unchanged existing factor `sqrt(2) * F(z)` gives exactly
   `canonicalCompletedC3ConcreteRealAxisGreenState`. It is not a new witness.
6. `canonicalCompletedC3OrientedRealAxisWrapper_eq_of_re_eq`:
   equal real parts give equal source states.
7. `canonicalCompletedC3OrientedGreenFramePrefixState_zero`:
   every oriented zero-cutoff prefix is zero.
8. `canonicalC3BracketTfvdCompletedTracePair_zero_value_ne_zero`:
   the completed value at cutoff zero and spectral center is nonzero.
9. `canonicalCompletedC3OrientedRealAxisWrapper_radial_eq_center`:
   every canonical imaginary radial sample has the same wrapped source as
   the center. This is a parameter-scope check, not a chiral kernel no-go.
10. `no_linear_orientedPrefix_completedValue_readout`:
    no homogeneous real-linear functional on this oriented prefix alone
    yields the completed value at the center for every cutoff.
11. `canonicalCompletedC3OrientedGreenFrameCarrier_not_parallelogram`:
    two independent Green channel coordinates refute the parallelogram law
    for its current maximum norm. Thus that norm cannot be its Hilbert norm.

There are ten new theorems and one audit-presentation definition. Each is
registered in the root audit and public theorem registry.

The presentation uses precisely the old synthesis and Parseval maps; the
existing bounds justify membership and bounded components. It preserves the
residual as a separate coordinate and recovers both original vectors on the
actual analysis range. It does not assert reconstruction of arbitrary raw
coefficients outside that range or recovery of unrelated completion data.

## Center and radial canaries; old no-gos

* `z = 0`, `w` regular: the scalar completed Wronskian/readout identity already
  exists. No corresponding Hilbert division-free equality was proved here.
* `z = w = 0`: the division-free identity itself reads `0 = 0` for a real
  characteristic/companion. It cannot calibrate a Hilbert norm. The removable
  normalized diagonal is the relevant metric test.
* Main already proves
  `not_hasCompletedNativeRealAxisNormalizedGreenKernel_concreteC3_of_defect`
  and `not_hasCompletedNativeRealAxisNormalizedGreenKernel_concreteC3`.
  The older completed sewing/calibration results expose the central defect.
  The new equality of dressed states shows that recovery, Parseval and
  complexification alone do not escape this rejected candidate.
* The old negative-kernel proofs were inspected as existing constraints;
  they are **not premises** of the new source-first capstones. No moment
  inequality was imported into those proofs.
* At every first/nontrivial canonical radial pair the real-axis wrapper
  erases imaginary parameter variation, as the new theorem proves. A family
  on `ℂ` by this wrapper is not automatically a genuine complex-source family.
* The prefix-only completion failure is exact at cutoff zero. Its scope is
  a homogeneous linear functional on prefixes, not a no-go for completed
  states, affine source data, larger source families or other geometries.

The other Taylor, causal chiral and concrete sewing no-gos do not supply a
positive witness. No candidate derived from them has been silently promoted.

## Tail / Xi / chart distinction

The ordinary/log gradient vectors do retain their two vertical boundary
coordinates, but those coordinates are not the completed characteristic
trace. In particular, `valueTail` and `logJetTail` live beside the finite
transport; the Xi/product-rule and chart corrections enter the completed
readout using their existing parameter-dependent factors. The precompression
residual is the reflected energy residual, not a storage location for all
these independent exact tails.

The all-cutoff limit supplies the complete gradient/log sequences. Equality
of scalar completed readouts does not prove that their corrections are
orthogonal positive Hilbert coordinates. No decision to add tails, Xi or
chart as new Hilbert channels is justified without the missing mixed-form
sewing. Neither multiplication by the common completion factor nor inclusion
of the existing real residual changes the state-presentation no-go above.

Continuity of a new complete complex state was not proved, because no
new state satisfying the division-free identity was constructed. This is
not a separate competing gap: the only outstanding construction is the
continuous Hilbert sewing witness itself.

## Canonical TFVD / Projective-Valve Provenance Crosswalk

### Historical note actually available

The supplied name ends in `(2).md`. The file located and read in full is
`/home/thlinux/Downloads/NOTA_CANONICA_TFVD_VALVULA_PROJETIVA_GEOMETRIA_ADITIVA_MULTIPLICATIVA_2026-09-15.md`
(3012 lines; SHA-256
`7b4b7946413191eb5135be5d835346242962454041635316a2ce4bf12bd94e33`).
No assertion is made that it is byte-identical to the unavailable `(2)` copy.
It is a historical architectural map only. The names and definitions below
were checked in the current repository or its pinned dependency sources.

### Boundary and reconstruction

For `x : CarryVerticalL2`, the current trace is

```text
carryWeightedVerticalTrace q x = (x 0, (q : ℂ)⁻¹ * x 1 - x 0).
```

The current identity is exactly

```text
carryVerticalL2WeightedGreen q (carryWeightedVerticalCenteredBracket q x) n
+ carryWeightedVerticalReturn q hqpos.le hq1 (carryWeightedVerticalTrace q x) n
= x n.
```

`carryWeightedVerticalTfvd_apply`, `carryWeightedVerticalTfvd_identity`,
`primeCarryWeightedVerticalTfvd_identity`, and
`baseCarryWeightedVerticalTfvd_identity` are current kernel-checked APIs.
No bracket-only replacement was used. The new synthesis lemmas explicitly
retain the two trace coordinates, for each of ordinary and log-jet.

`DiscreteProjectiveReconstruction` supplies `reconstruct_encode`,
`encode_reconstruct`, and `reconstructionEquiv` for arbitrary sequences.
Its reconstruction data contain initial value, initial slope and normalized
projective mass. `ProjectiveValveFundamentalTheorem` and
`ProjectiveValveEquivalence` prove the corresponding curvature and
boundary/mass uniqueness identities. These are algebraic roundtrips, not
isometries of the completed spectral source.

| Historical reconstruction coordinate | Actual current location | Classification |
|---|---|---|
| Vertical initial value and slope | Recovered from each full gradient/log vector by `carryWeightedVerticalTrace` after bounded synthesis | **EXACT_CROSSWALK** for these vector sequences |
| Integrated interior/projective bracket mass | Formal sequence/series reconstruction after amplitude ungauging | Kernel-checked algebraic crosswalk; no moment metric conclusion |
| Incoming material seed | Seeded source ledger / separate initial source data | Not identified with the vertical gradient trace |
| Exact completed value/log tail | `CanonicalC3BracketTfvdCompletionState.valueTail` and `.logJetTail` | Separate structured completion fields |
| Xi / chart correction | Existing normalized completed readouts and corrected kernel ledger | Scalar/structured source factors; no positive channel norm proved |
| Precompression residual | `infiniteReflectedGreenEnergy s • completedTfvdResidualGenerator` | Retained real residual, not an inverse of all completion traces |

For the full completed spectral source this is **PARTIAL_CROSSWALK**, not
“only boundary coordinates are missing”. The formal-depth mass equivalence
and spectral two-parameter Green kernel also live at distinct semantic levels.

### Valve naturality and its limits

`CompletedC3ValveNaturality.lean` already gives:

* `carryAmplitudeUngauge_gauge` and the first/second difference gauge identities;
* `mk_discreteValveGreenSum_eq_greenChannelSeries`;
* `canonicalCpLogBlockGradientSeries_eq_add` and
  `canonicalCpLogBlockProjectiveCurvature_eq_add`;
* `projectiveValveMass_canonicalCpLogBlock_eq_mul` and
  `projectiveValveMass_canonicalCpLogBlock_eq_projectiveGreenMass`;
* ordinary/log-jet C3 initial coefficient identities and the existing
  completed value/companion packing identities.

In particular, the additive discrete Green sum is literally the
multiplicative valve's `greenChannelSeries` of the formal bracket series.
This is not a theorem identifying that formal-series operation with the
current all-bases Green-frame inner product or the full completed Wronskian.
The file expressly leaves Gamma/Wronskian sewing as a separate gate.

The projective-depth coordinate and inverse APIs prove the Jacobian/inverse
identities for `Y = X/(1-X)`. They do not identify this variable with the
spectral even variable `v = t²`. No such renaming was made here.

`ProjectiveValveNativeIncidence` contains a projective injection and a Hilbert
passage using the BR2 realization. It was read for genealogy only and is not
used in any new proof. Injectivity and preserved linear relations do not
supply isometry or the moment kernel. `ProjectiveValveMomentFrontier` retains
the independent boundary plus transport/shift obligations, and the literal
C3 `(0,2)/(1,1)` mismatch. Those obstructions were respected.

`NativeMomentProjectiveValveBridge` is a downstream compatibility of the
log-derivative valve and reciprocal characteristic. Its moment valve is not
used to define a state. Projective mass is not identified with a positive
Hilbert norm.

### Answers to the ten complement questions

1. **TFVD identity:** relevant to faithful recovery, not a proof of metric sewing.
2. **Two boundary degrees:** recoverable through weighted trace of each full
   synthesized gradient/log vector; exact completion traces are elsewhere.
3. **Valve naturality:** existing algebraic crosswalks remove ambiguity but
   do not provide the missing completed Hilbert mixed-form morphism.
4. **Same Green series?** Yes for discrete Green sum and formal valve series;
   no current theorem makes it the completed Green-frame kernel.
5. **Reconstruction equivalence:** vector recovery preserves the underlying
   sequences; no lossless equivalence of the entire spectral completion to
   that three-field formal reconstruction is claimed.
6. **Projective incidence:** audit only, not a metric ingredient or new proof input.
7. **Moment frontier:** boundary/shift and C3 literal no-gos remain separate constraints.
8. **`Y = v`:** never used.
9. **Different carrier?** Natural Hilbert re-presentation equals the old
   rejected state; no structurally distinct positive witness was constructed.
10. **Valve contribution:** confirmed genealogy and boundary scope; did not
    solve the independent metric identity.

## One remaining typed construction

The single frontier is a **continuous source-derived Hilbert sewing witness**.
As an obligation, not a new assumption wrapper or an implementation:

```lean
-- Find an existing/naturally completed complex Hilbert E and state : ℂ → E
-- such that the same full source satisfies:
HasDivisionFreeGreenRepresentation
  completedNativeOperatorCharacteristic
  completedNativeOperatorBoundaryCompanion state
∧ Continuous state
```

Its product must realize the entire corrected mixed Wronskian, not merely
sum squared norms of recovered ordinary/log and residual channels. The
current real-axis wrapper plus its existing Hilbert presentation is not this
witness. No specific additional Hilbert coordinate or new metric is chosen
without a source-level form identity that justifies it.

## Audit, dependencies and publication

Dedicated audit:
`CompletedC3OrientedGreenSourcePresentationAuditBridgeAudit.lean`.
Every new public declaration has `#print axioms` and an allowed-footprint
assertion (at most `propext`, `Classical.choice`, `Quot.sound`).
`#assert_oriented_green_source` traverses declaration types **and** proof/definition
values and rejects HP certificates, canonical target moments, Stieltjes,
Hankel, Jacobi/height operators, Herglotz and BR2 declarations.

The scan uses `Lean.privateToUserName` for private declarations: a generic
ℓ² reindexing helper happens to be stored in the historical
`BR2GreenFrameIncidenceTransport` file, but does not use a BR2 source. The
helper's entire proof is still traversed. Imported module names are not
mistaken for dependencies on their unrelated incidence theorems. No BR2
incidence, jet or certificate occurs in the audited proof closure. The focused
audit checked 6214 reachable declarations and passed.

Commands executed for final validation:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedC3OrientedGreenSourcePresentationAuditBridge
lake build --wfail CarrySelfAdjointOperator.CompletedC3OrientedGreenSourcePresentationAuditBridgeAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

Validation logs are retained on the build host under
`/tmp/oriented-green-focused-audit.log` and `/tmp/oriented-green-validation/`.
All listed commands passed before committing or pushing: both focused builds,
the full package and root audit with `--wfail`, `static audit passed`,
`kernel audit passed`, and `git diff --check`. Placeholder/control-character
scans of the new Lean modules and report passed; the registry parses as JSON.
The dedicated source audit checked 6214 declarations; all new declarations
have only `[propext, Classical.choice, Quot.sound]` (or a subset).

Modified tracked files: `CarrySelfAdjointOperator.lean`,
`CarrySelfAdjointOperator/Audit.lean`, `audit/theorem-registry.json`,
`README.md`, and append-only `docs/CHECKPOINT_AUTO_ADJUNTO.md`.
Added: the presentation module, its audit and this report. Foundation,
dependency sources and canonical objects are unchanged.

## Main-question answers

1. Existing oriented raw carrier audited; its existing complex Hilbert
   presentation was reused for an equality test, not declared a new witness.
2. Its definitions are source-facing and independent of target moments.
3. Ordinary, log-jet and real precompression residual are retained.
4. Residual stays a separate complexified coordinate in the presentation.
5. Exact tails/Xi/chart remain existing structured data/readout factors; no
   arbitrary orthogonal coordinates were introduced for them.
6. **Division-free Hilbert representation: open.**
7. No new complete complex-family continuity theorem was needed or proved.
8. **Normalized positive kernel: not derived.**
9. Old concrete C3 no-go respected by exact state equality, with no fitted factor.
10. Oriented scalar ledger was not converted to a positive inner product.
11. All-order chiral storage nonnegativity remains open.
12. BR2 was not a source or proof input.
13. The single remaining construction is the continuous full-source Hilbert sewing above.
14. README records only the proved audit frontier.
15. Final commit/remote equality/clean tree are recorded in the delivery after validation.

**Conclusion:** full reconstruction preserves information, but does not
identify the completed mixed Green form with a positive Hilbert product.
The new local obstructions exclude current maximum-norm use and redundant
presentation repair; they do not refute a larger geometric sewing theory.


## 2026-10-06 — Directed consultation of `llm:~/momentos/`

### Checkpoints and preservation

This follow-up starts from normative main
`f005b9c82fa774af27079b2b1669b8a724800b69` after `git pull --ff-only`
reported already up to date. The main working tree was clean.
The research archive is `/home/thlinux/momentos` on `llm`, at
`206b06b` (`Add canonical TFVD valve note`). It has four preexisting untracked
campaign `run.json` files. No archive file, campaign, checkpoint or
experimental worktree was changed or executed.

The archive is historical/numerical evidence, not a replacement formal base.
Its README explicitly separates completed moment identification from the
still-needed Green metric sewing. It is not one Lean project at its root.

### Exact comparison with main

Seventeen Lean files copied into the archive's `CarrySelfAdjointOperator/`
bundle directories were compared byte for byte with their same-named main
modules. **All seventeen are identical**:

| Bundle | Compared modules, including audits |
|---|---|
| `c2_base_two_work` | `C2BaseTwoGreenLedger`, its audit |
| `c2_green_bridge_work` | `C2GlobalGreenBridge`, its audit |
| `c2_green_temporal_mean_work` | `C2GreenTemporalMeanCanary`, its audit |
| `c2_green_whitening_genealogy_work` | `C2GreenWhiteningGenealogy`, its audit |
| `c2_material_log_transport_work` | `GreenStateMaterialLogGenerator`, its audit |
| `c2_pre_stencil_work` | `C2GreenPreStencilCanary`, its audit |
| `green_material_unitary_evolution_work` | `GreenStateMaterialEvolution`, `GreenParsevalMaterialEvolution`, `GreenMaterialEvolutionAudit` |
| `green_parseval_material_operator_work` | `GreenParsevalMaterialLogOperator`, its audit |

These results supply no unported new source witness. Their proven scope is
valuable: conservative pre-stencil recovery, a genuine stencil frame defect,
and unitary transport of the material log generator. A positive base-two
camera contribution or positive temporal mean on its specific C2 input is
not nonnegativity of the full completed chiral mixed pairing for every
coefficient vector. Material time is not the radial sample index.

The archived canonical valve note has SHA-256
`7b4b7946413191eb5135be5d835346242962454041635316a2ce4bf12bd94e33`,
identical to the historical note already read in the main investigation.
It therefore supplies no additional version of that genealogy.

### Useful scalar-completion evidence

`AUDITORIA_CORRECTED_MOMENTS_VS_CANONICAL_RECURRENCE.md` explicitly distinguishes
raw `U(t²) = |Z(t)|²` from the normalized completed characteristic `Φ(u)`.
Its scalar germ identity is

\[
\Phi(u)^2 = \frac{U(u)}{U(0)}(1+4u)
 \prod_{m\ge1}\left(1+\frac{u}{(2m+1/2)^2}\right)^{-1}.
\]

That report identifies historical corrected moments and the canonical scalar
recurrence, but explicitly states that the product-limit deduction and
Python identification are **not a new compiled Lean bridge**. Its high
precision results do not construct the missing Hilbert mixed-form witness.
The current source-first moment identification remains closed independently.

`native_carry_tail_boundary_autoadjoint_test.py` expressly calls its finite
boundary factor an inserted candidate and its comparison a scalar completion
benchmark, not a geometric TFVD return construction. No run of that script,
Jacobi construction, spectral fitting or matrix factorization was used here.

### Current formal counterpart: the triangular dressing

The following existing main declarations were checked directly in
`NativeBoundaryArchimedeanDressingSeparation.lean`:

* `nativeArchimedeanBoundaryDressing`;
* `canonicalNativeUndressedScalarBoundaryPair_eq_normalizedTfvdTrace`;
* `canonicalCompletedC3ScalarBoundaryPair_eq_nativeArchimedeanBoundaryDressing`;
* `canonicalCompletedC3ScalarGreenForm_eq_scaledNative_add_archimedeanCorrection`;
* `canonicalArchimedeanBoundaryGreenCorrection_eq_derivative`.

Let `A = nativeXiCompletionFactor`, `Z = nativeHeightScalar`, and
`F = A * Z`. The companion transformation is precisely

\[
(-Z',Z)\longmapsto\bigl(A(-Z')-A'Z,\ AZ\bigr).
\]

Thus completion is not common scalar multiplication of both traces.
With the existing C3 Green-form argument order, its full product rule is

\[
\mathcal G_{\rm completed}(z,w)
 = \overline{A(z)}A(w)\mathcal G_{\rm native}(z,w)
 + \bigl(\overline{A'(z)}A(w)-\overline{A(z)}A'(w)\bigr)
   \overline{Z(z)}Z(w).
\]

The exact theorem has the existing genuine-strip hypotheses. It is a scalar
Green-form identity, including the derivative correction and all its signs;
it does not claim that either summand separately is a positive Hilbert
kernel. No orthogonality, positivity of a new completion channel or lossless
lift from its scalar traces is inferred.

This gives a concrete audit target for future sewing: preserve this whole
mixed correction in the source-level metric identity. The previous
repackaging equality and no-gos remain unchanged.

### The tempting product-state route is still conditional

The archived `CompletedGreenMomentJets.lean` already has
`completedNativeC3ProductLedger_greenRepresentationOn_of_factors`.
The current main still has it, and its premises still include BOTH

```lean
hxi : HasDivisionFreeGreenRepresentation
  nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState

hnative : HasDivisionFreeGreenRepresentation
  nativeHeightScalar nativeHeightScalarBoundaryCompanion
  canonicalCompletedOperatorC3HilbertState
```

`weightedProductGreenState`, `HasDivisionFreeGreenRepresentation.mul`, and
`completedNativeC3ProductLedgerState` already provide the product packaging.
They do not construct those two factor representations. They cannot be
cited as an unconditional completed witness. No additional direct sum or
assumption wrapper was created.

The archived structural Green-frame readout and BR2 dslope bridge likewise
receive `hkernel`; they do not prove it. Their presence does not change the
source-first dependency firewall.

### Result of the consultation

**ARCHIVE_PROVENANCE_CONFIRMED; DIVISION_FREE_HILBERT_SEWING_STILL_OPEN.**

The archive helps identify the exact completion correction that a metric
sewing must preserve. It contains no newly discovered unconditional witness
for the current gate. The single typed obligation remains the continuous
full-source Hilbert division-free representation stated above. This follow-up
adds documentation only, no Lean theorem, no sign premise and no new carrier.

Validation passed: the full package and root audit with `--wfail`,
`static audit passed`, `kernel audit passed`, and `git diff --check`.
Logs are retained under
`/tmp/momentos-consultation-validation/`. Archive dirty files remain untouched.


## Follow-up: vector completion and signed mixed-form sewing

Starting from `4df95cc`, `CompletedNativeChiralReturnCompletionSplit` now
splits the actual Cauchy source companion into its xi-weighted native part
and its completion derivative part. Both have the same completed TFVD trace
provenance at every cutoff. Their skew pairings realize the weighted native
Green form and the existing archimedean correction, with all cross terms
retained. The analytic-center cancellation and one-/two-sample canaries
passed. The new fifteen public declarations passed the source dependency
firewall and standard trust footprint. This is a signed-form crosswalk, not
a positive Hilbert witness or contractivity proof. The continuous full-source
division-free Hilbert sewing remains open. See
[the vector-split report](CHIRAL_RETURN_COMPLETION_VECTOR_SPLIT.md).
