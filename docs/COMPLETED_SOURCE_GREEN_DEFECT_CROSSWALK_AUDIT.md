# Complete source → Green defect crosswalk audit

## Checkpoint and status

Audited main: `c7d46e3093fa39359a0c47a43159b5b12e1ac466`.
`git pull --ff-only` reported up to date; HEAD, main and origin/main agreed.
Initial working tree was clean. No dependency checkout was modified.

**PARTIAL_COMPLETED_SOURCE_TO_GREEN_PORT** — an exact corrected Green ledger
crosswalk is now proved. The isolated finite C3 Green form and the all-bases
material stencil defect are not identified with the complete mixed orientation.
`SEMANTIC_GREEN_CARRIERS_DIFFER` describes the audited carrier distinction;
it is not a theorem that no future morphism can exist.

No positivity, contractivity or spectral conclusion is asserted.

## Exact type map

Namespaces below: `CSAO = CarrySelfAdjointOperator`,
`NC3 = NativeCarryC3Crosswalk`, `GF = GreenFrame.Concrete`.
Aliases denote the existing types, not newly introduced carriers.

| Object | Exact Lean type/signature | Parameters and provenance | Producer → consumer |
|---|---|---|---|
| `CSAO.ChiralReturn.sourceValue` | `(k : ℕ) → {N : ℕ} → (Fin N → ℂ) → ℝ → CanonicalCompletedNativeChiralCauchyCarrier` | completed value `F`, sample grid, normalized by the existing positive chiral coordinate | completed trace, then Cauchy vector synthesis → mixed inner product |
| `CSAO.ChiralReturn.sourceCompanion` | same signature | companion literally `-deriv F`, same coefficients, grid and normalization | completed trace, then Cauchy vector synthesis → mixed inner product |
| `canonicalC3BracketTfvdCompletedTracePair` | `(M : ℕ) → ℂ → ℂ × ℂ` | height coordinate; TFVD head plus exact tails, chart quotient/derivative and xi completion | canonical completion state → Wronskian or source Cauchy synthesis |
| `CanonicalC3BracketTfvdCompletionState` | `(M : ℕ) → Type` | fields `transport : NC3.FiniteC3EnrichedTfvdPairTransportData M`, `valueTail : ℂ`, `logJetTail : ℂ` | `canonicalC3BracketTfvdCompletionState M s` → scalar trace and separate Green-port projection |
| `CanonicalC3BracketTfvdCompletionState.greenPort` | `{M : ℕ} → CanonicalC3BracketTfvdCompletionState M → NC3.FiniteC3GreenPortCarrier (M * 3)` | preserves the transport port; does not reconstruct it from the completed trace | `state.transport.greenPort` → finite symplectic Green/Naimark quadratures |
| `NC3.finiteC3GenuineBracketGreenBoundaryPair` | `(M : ℕ) → ℂ → NC3.FiniteC3GreenBoundarySpace M × NC3.FiniteC3GreenBoundarySpace M` | raw strip parameter `s`; radial phase-normalized bracket and consecutive Dirichlet gradient | Genuine bracket transport → `Boundary.greenForm` |
| `canonicalC3BracketTfvdMixedGreenReadout` | `(M : ℕ) → ℂ → ℂ → ℂ` | raw strip parameters; direct port at `w`, reflected port at `reflectedParameter z` | both retained ports → two Naimark skew quadratures → complex readout |
| `canonicalCompletedC3SixCameraSource` | `ℂ → RealifiedCameraComplexification` | height input; internally uses `operatorHeightParameter` | cutoff-one enriched port → faithful real/imaginary six-camera packing |
| `canonicalCompletedC3SixCameraSymplecticGreenReadout` | `ℂ → ℂ → ℂ` | raw strip inputs; direct `w`, reflected `z` | two cutoff-one enriched ports → fixed symplectic Naimark readout |
| `GF.State` | `ℓ²(PNat, ℂ)` | positive material integer coordinates | material packaging → raw Green analysis or material log generator |
| `GF.greenAnalysis` | `(omega : GF.AdmissibleInfinitePartition) → GF.State → ℓ²(GF.GreenEvent, ℂ)` | all-bases events, current/parent/grandparent stencil with carry amplitudes | `greenCoordinate omega e f` → summed event energy |
| `CSAO.C2GreenPreStencilCanary.directGreenAnalysis` | `(omega : GF.AdmissibleInfinitePartition) → GF.State → ℓ²(GF.GreenEvent, ℂ)` | unchanged current coordinate times the same event amplitude, before stencil replacement | `directGreenCoordinate omega e f` → conservative split and stencil defect |

The last declaration does **not** live at `GF.directGreenAnalysis` in this main.
Its actual namespace is recorded above.

Carrier expansions:

* `CanonicalCompletedNativeChiralCauchyCarrier = MeasureTheory.Lp ℂ 2 (volume : Measure unitInterval)`.
* `NC3.FiniteC3GreenBoundarySpace M = EuclideanSpace ℂ (Fin M)`.
* `NC3.FiniteC3GreenPortCarrier M = FiniteC3GreenBoundarySpace M × FiniteC3GreenBoundarySpace M`.
* `RealifiedCameraComplexification = WithLp 2 (CameraHilbert × CameraHilbert)`.

The Cauchy carrier index is an internal interval coordinate, not a material
integer, C2 depth, Green event depth or height coordinate.

## Actual provenance chain and its scope

All arrows used in the new identities are kernel-checked or definitional:

```text
canonical structured TFVD completion state (transport + two exact tails)
    ├─ completed normalized trace (F, -F')
    │     → two Cauchy vector syntheses V,C
    │     → complete ordered mixed pairing
    └─ Green port, ordinary/log-jet heads, local boundary cells
          → existing six-channel corrected Green/Wronskian ledger
```

`canonicalC3BracketTfvdCompletionState_transport_components` identifies all
three simultaneous transport projections. The completed readout theorems
and `canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime` identify the
trace only **after** the head/tail/completion synthesis.
`source_pair_eq_bracketTfvd` remains unchanged and valid at every cutoff.
No new TFVD encoder, trace inverse or state reconstructed from `(F,-F')` is used.

`finiteC3GenuineBracketGreenBoundaryPair_eq_nativeGreenPair` is a literal
finite-port equality. Its coordinates are the same completed ordinary-gradient
prefix, with the first coordinate multiplied by the radial C3 factor.
`greenForm_finiteC3GenuineBracket_eq_coefficient_mul_prefixGram` preserves that
factor and the reflected pairing; it does not identify the result with the
completed characteristic Wronskian.

`canonicalEnrichedC3SourcePort_eq_completedTfvdGreenLedgerC3Port : ∀ s : ℂ, ...`
identifies the cutoff-one private port with the seeded completed TFVD ledger
port. `canonicalCompletedC3SixCameraSource_eq_completedTfvdGreenCameraState :
∀ z : ℂ, ...` then identifies the faithful six-camera vector at height `z`
with the public camera state at `operatorHeightParameter z`. This is a port
packing equality, not a Cauchy/source-vector isometry.

`canonicalC3FourTraceSixCameraSource_greenPort_eq_bracket` identifies the
pair of ports with the direct `w` and reflected `z` Genuine bracket ports.
`canonicalC3FourTraceSixCameraSource_greenReadout_eq_greenForm` reads precisely
that pair, retaining the separate direct, reflected and quarter-turned
Naimark vectors before the complex skew readout. These maps preserve the
Green form already present; they do not add the missing completion terms.

## Exact identity proved, including signs and every cross term

For the existing samples set

$$
z_i=\texttt{canonicalCompletedC3RadialTiltPoint}(k,i),\qquad
d_i=\frac{c_i r^{i+1}}{P(z_i)},\qquad
K_{ij}=\langle v_i,v_j\rangle.
$$

Here `P` is the existing positive Hermite–Biehler coordinate and `v_i` is the
existing Cauchy state. No weight was selected or changed.

The Mathlib convention is conjugate-linear in the first argument. Therefore

$$
W_{ji}=C(z_j)\overline{F(z_i)}-F(z_j)\overline{C(z_i)}
$$

has the right sample **first**. The new finite theorem proves

$$
4\Im\langle V,C\rangle
=2\Im\sum_{i,j}\overline{d_i}d_j K_{ij}W_{ji}.
$$

For every cutoff, the existing completed trace identifies `W` with
`canonicalC3BracketTfvdCompletedWronskianReadout M` on the strip. Thus the
formula includes every ordered pair, including `i ≠ j`; no orthogonality,
mask, temporal averaging or dropped cross term is used.

Let `L_M(z,w)` be the **existing**
`canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w`. The exact upstream
ledger gives

$$
W_M(z,w)=\frac{
 \omega_\xi(z,w)G_M(z,w)
 +L_M.\mathrm{greenProvenance}
 +L_M.\mathrm{offDiagonal}
 +L_M.\mathrm{readoutResidual}
 +L_M.\mathrm{tailCompletion}
 +L_M.\mathrm{archimedeanChart}}
 {\omega_Q(z,w)}.
$$

`G_M` is exactly the existing `canonicalC3BracketTfvdMixedGreenReadout` and
hence the finite-port `greenForm`. The chart denominator is nonzero by the
existing strip theorem; no new premise is postulated.

`source_cross_eq_corrected_green_ledger` substitutes this ledger **inside the
entire double sum**. `source_cross_eventually_eq_corrected_green_ledger`
removes the strip premise on each shrinking finite sample family, with order

```lean
∀ N, ∀ᶠ k in Filter.atTop, ∀ M, ∀ c : Fin N → ℂ, ∀ r : ℝ, ...
```

The threshold is independent of cutoff, coefficients and internal radius.
It applies in particular at `r = 1`. It does not assert a vector limit or an
infinite source-to-port operator.

The universal form `Boundary.greenForm (V,C) (V,C)` on the **Cauchy** carrier
also equals `inner C V - inner V C`; hence the new theorem records
`4 Im inner V C = -2 Im greenForm (V,C) (V,C)`.
This is specialization of the existing skew form, not an identification of
Cauchy vectors with finite C3 port vectors.

## Trace projection is not a lossless Green-port statement

The structured state stores its heads, boundary cells, Green port and tails
separately. The trace consumes the value/log-jet readouts and tails, while the
Green projection consumes `transport.greenPort`. On the ambient transport
structure those fields are independent. Equality of the two scalar completed
traces alone supplies no equality of ports or boundary cells.

The present proof uses the **canonical structured source** and its existing
ledger, not a reverse map from the trace. Consequently we do not announce a
no-go for the canonical source or fabricate a trace inverse.

## Polarized camera residual: what vanishes, what does not follow

The following are genuine completed four-trace equalities on `bracketDomain`:

* `completedCameraCrossLeftTraceState_eq_rightTraceState` (camera ≥ 2);
* `completedCameraCrossRightTraceState_eq_weightedTfvdTraceState`;
* `completedCameraCrossLeftTraceState_eq_weightedTfvdTraceState` (camera ≥ 2);
* `completedHeightPolarizedCameraCrossResidualChannelState_eq_zero`.

They compare the camera-cross left/right value and log-jet traces. Their
zero residual is not the entire structural Green/Wronskian defect. The same
module explicitly retains the full structural state: its second coordinate
at equal raw parameters is a negative radial reflected-gradient pairing
(`canonicalC3FiniteMixedHeightFullPolarizedStructuralResidualState_second_eq`).
The one-camera four-channel comparison has its own no-go. We therefore do
not use the zero camera residual to cancel the five correction channels.

`CompletedNativeTfvdSixSourceChiralDefect` already identifies the six-source
radial kernel with the signed Cauchy multiplier defect, via `dslope` and
forced amplitude congruence. This is not a positive complement. It is only
an audit reference here: none of its moment-identification results enter
the new proof dependency closure.

`CompletedNativeRadialTiltSamplePositivity` has a positive gamma sample Gram,
but equality with `dslope` uses independent boundary/defect gates. Its
conditional gamma/moment/positivity route is not a premise of this crosswalk.

## C3 Green vs all-bases GreenFrame stencil

The finite C3 form is

$$
\mathcal G(x,y)=\langle x_2,y_1\rangle-\langle x_1,y_2\rangle,
$$

skew-Hermitian on pairs of finite complex gradient ports. Direct and
reflected parameters are separate. Its diagonal is purely imaginary; it is
not itself a nonnegative Hilbert Gram.

The old `GreenFrame.Concrete` defect is a **real quadratic energy difference**
on one material `State`:

$$
\|\texttt{greenAnalysis}\,f\|^2-
\|\texttt{directGreenAnalysis}\,f\|^2.
$$

`concreteAnalysis_norm_defect_eq_stencil_defect` proves this for arbitrary
material `f`. `c2GlobalRawGreenDefect_eq_stencil_defect` restricts it to the
authorized odd C2 physical source. `rawGreenDefect_eq_diagonal_add_cross_tsum`
then splits it into a nonnegative diagonal and the full signed cross sum;
`globalCrossDefect_timeAverage` controls the temporal mean, not its pointwise
sign. None of these theorems accepts the current completed C3/Cauchy source.

`C2GreenWhiteningGenealogy` identifies the raw frame defect and only then
normalizes that raw frame. `GreenParsevalMaterialLogOperator` transports the
material log generator along that Parseval isometry onto its range and a
zero extension. `GreenStateMaterialEvolution` transports the material phase
orbit. They do not intertwine the present mixed source orientation with the
raw stencil defect. No whitening/Parseval map is used in the new proof.

The existing `nativeLogHilbertEquivGreenState` is a legitimate material-index
repackaging of an ℓ² sequence. It does not preserve the present completed
Wronskian form by any theorem audited here: reindexing an ordinary-gradient
channel alone leaves the other completed channels and the form comparison
unresolved. A carrier reindexing is not the missing source/form intertwiner.

Thus there is no proved identification with the C2 diagonal/cross energy
ledger in this round. It is not justified by the common word “Green”.

## Base 2 and parameter firewall

`baseTwoDefect_pos` is restricted to `c2GlobalGreenInputIsometry t V` for
nonzero `V : CoreState`. Its proof uses odd material support, zero direct
base-two channel and the corresponding event mask. No theorem identifies
the completed C3 source with that source/support/mask/form. This result is
not transported here.

Material time, radial sample index `k`, internal Cauchy radius `r`, complex
height chart, raw Dirichlet parameter, Green event depth and C2 positional
depth remain distinct. The only conversions used are the existing
`operatorHeightParameter` and `reflectedParameter` inside the C3 ledger.

## One first typed gap

To identify the **complete** orientation with the old raw stencil defect,
the missing finite-family morphism has at minimum the type

```lean
J_M_k_N : (Fin N → ℂ) →L[ℂ] GreenFrame.Concrete.State
```

constructed from the same canonical complete TFVD states at the radial
samples, before discarding their completion/provenance channels. It must
satisfy, without fitting its definition to this equation,

```text
norm²(greenAnalysis canonicalCarryInfinitePartition (J_M_k_N c))
 - norm²(directGreenAnalysis canonicalCarryInfinitePartition (J_M_k_N c))
 = 4 * Im(inner sourceValue(k,c,1) sourceCompanion(k,c,1)).
```

The right side is now the explicitly proved corrected Green double ledger.
No such map is defined or assumed here. The current trace projection,
faithful finite-port camera packing and material Parseval maps do not supply
this source-to-stencil morphism. A future map must preserve **all** ledger
channels, rather than assuming their cancellation. This is one map with a
form-preservation obligation, not a new assumption interface.

## New declarations and provenance

All are in `CarrySelfAdjointOperator.ChiralReturn`:

1. `source_cross_eq_cauchy_greenForm` — existing skew form on existing Cauchy vectors.
2. `mixed_synthesis_eq_wronskian_sum` — finite sesquilinear expansion; no source fitting.
3. `source_cross_eq_bracketTfvd_wronskian_sum` — existing completed trace identity at every cutoff.
4. `bracketTfvd_wronskian_eq_corrected_green_ledger` — existing sewing plus certified chart division.
5. `source_cross_eq_corrected_green_ledger` — composition inside every ordered pairing.
6. `source_cross_eventually_eq_corrected_green_ledger` — existing uniform eventual regularity.

No new carrier, source, metric, frequency, moment, height, fitted operator or
hypothesis wrapper was introduced. All existing canonical definitions are
unchanged. Normalization, membership and source synthesis remain those
proved upstream. These theorems do not depend on moments or a height layer.

## Validation and files

Focused axiom/dependency audit and full validation results are recorded after
execution below. Relevant full logs are retained on `llm` under
`/tmp/chiral-green-{build,audit,root,full-audit,static,kernel}.log`.

Modified/added files:

* `CarrySelfAdjointOperator/CompletedNativeChiralReturnGreenFormCrosswalk.lean`;
* its dedicated `...Audit.lean`;
* root import `CarrySelfAdjointOperator.lean`;
* `CarrySelfAdjointOperator/Audit.lean`;
* `audit/theorem-registry.json`;
* `README.md`;
* this report;
* append-only research checkpoint `docs/CHECKPOINT_AUTO_ADJUNTO.md`.

Final answer to the structural question: an exact **signed corrected Green
ledger** identity is now proved. A positive geometric energy defect is not.
The morphism to the old GreenFrame stencil is still absent. No positivity
or canonical-source no-go follows from this audit.


### Recorded validation

* `lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnGreenFormCrosswalk`: passed.
* `lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnGreenFormCrosswalkAudit`: passed; all six public declarations have only `[propext, Classical.choice, Quot.sound]`.
* The focused audit traverses both types and proof/definition values: **6157** reachable declarations. It rejects canonical log-derivative moments, HP certificates, Stieltjes, any Herglotz declaration, Hankel, Jacobi, height operators, moment-Gram positivity and BR2.
* `lake build --wfail CarrySelfAdjointOperator`: passed.
* `lake build --wfail CarrySelfAdjointOperator.Audit`: passed.
* `bash scripts/static_audit.sh`: passed.
* `bash scripts/audit.sh`: passed, including recovered C2 Green checks.
* `git diff --check`: passed; staged whitespace and control-byte checks are performed before commit.

The `ring_nf` replay suggestions in pre-existing modules are informational;
there are no new warnings/errors in the new module or its audit.
Final working tree and published-main equality are verified after commit/push,
with the exact resulting SHA reported in the delivery. The report's base SHA
is intentionally the audited input, not a self-referential commit SHA.
