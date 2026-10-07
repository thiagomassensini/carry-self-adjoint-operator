# Completed adjacent clock / corrected chiral energy frontier

## Checkpoint

Initial `HEAD = main = origin/main`:
`499d5c3556dce18898c736ba221d3af38a0099d7`.
`git pull --ff-only`: up to date; initial tree clean.
Work stays on `llm:/home/thlinux/carry-self-adjoint-operator`, branch `main`.
Dependencies, Foundation, canonical source objects and all metrics are unchanged.

```text
PASS_COMPLETED_ADJACENT_CLOCK_CHANNELS
PASS_COMPLETED_CHIRAL_CLOCK_LEDGER_CROSSWALK
PARTIAL_COMPLETED_SOURCE_ENERGY_POSITIVITY
```

The completion and exact full-source crosswalk close. The uniform sign of
storage and a positive complementary channel remain open.
No contractivity, Pick/Herglotz PSD, Stieltjes, Gram or strictness result is claimed.

## Audit before construction

The source remains the existing ordinary/logJet Hilbert family. Its actual
mixed legs are adjacent material edges, not the historical conjugated
same-edge contraction. The previous finite product-rule transport is reused.

The current global structured carrier is
`CanonicalCompletedC3AllCutoffKernelLedgerHilbert`, retaining direct and
reflected Naimark ports, the quarter-turn reflected port, the structural
provenance/off-diagonal/readout triple, exact tail, Xi weight and the
archimedean/chart channel. It is not replaced by the new scalar observation.

Relevant current identities checked:

| Existing identity | What it supplies | What it does not supply |
|---|---|---|
| `summable_norm_positiveDirichletGradient`, `summable_norm_positiveLogDirichletGradient` | Source-specific absolute summability before scalarization | No storage sign |
| `finiteC3MixedRadialGreen_tendsto_completed` | Same radial Green limit | No positive full kernel |
| `canonicalCompletedC3AllCutoffKernelLedgerState_finalReadout_eq_completedWronskian` | Completed source numerator at every cutoff, all completion channels retained | No Hilbert norm identity |
| `CanonicalCompletedC3AllCutoffKernelLedgerHilbert.norm_sq_eq_channel_sum` | Orthogonal total energy of the retained ledger | Its signed weighted final readout is not identified with that energy |
| `ChiralReturn.chiral_pairing_total` | Conservative total incident/return energy | No ordering of the two energies |
| `ChiralReturn.polarizedSourceBalance_eq_greenForm` | Full symplectic signed orientation | No positive complementary channel |
| `ChiralReturn.storage_re_eq_coisometricEnergy_sub_fourChannelBalance` | Source camera energy minus the actual geometric correction | No upper bound on that correction |

The existing Gamma-port source test and its four ordered resolved-leak
pairings were also checked by declaration. They do not justify erasing
leak/cross terms or replacing the complete response by Gamma of a port.
No old no-go or positivity gate is reopened.

## Absolute completion, without canceling channels

Let `(A_n,J_n)` denote the independently defined adjacent clock channels
from the preceding module. A is the shared-material-node log frequency
multiplying the ordinary adjacent wedge. J contains the two literal outer
sample/log-gap terms. Their definitions use no moments or prescribed Gram.

The new source bounds are:

```text
||positiveLogGap(n)|| ≤ 1
||positiveDirichletValue(z,n)|| ≤ 1                    if Re(z)>0
||J_n(z,w)|| ≤ ||g_w(n+1)|| + ||g_w(n)||
||mixedWedge_n(z,w)|| ≤ C_z (||g_w(n+1)|| + ||g_w(n)||),
    C_z = ||canonicalCompletedC3LogJetState z hz||.
```

The first bound is derived from `log(b/a) ≤ b/a-1`, with positive
material integers `a=n+1`, `b=n+2`. The value bound uses the existing norm
formula and real-power decay. The clock bound uses evaluation bounded by
the norm of the existing logJet l2 state. No raw nodal l2 state is built.

The independently defined A obeys a summable majorant with constant C_z+1,
using the already-proved local identity `mixedWedge = A+J` only in the proof.
It is **not** redefined by subtraction from a requested target.
Thus both `Σ ||A_n||` and `Σ ||J_n||` are finite for Re(z)>0, Re(w)>0.

Whole C3 block observations are retained as a pair:

```text
block(m) = (A_(3m)+A_(3m+1), J_(3m)+J_(3m+1)).
```

Both projections are absolutely summable independently. The new completed
observation is the pair of their tsums, `canonicalC3CompletedAdjacentClockChannels`.
The actual finite `Fin M × Fin 2` family is proved equal to these whole-cell
partial sums. Their pair converges componentwise before its two entries
are added. This is a completed **observation of the existing source**, not
a new positive state/metric or an inverse of a scalar trace.

For the natural strip domain, with Re(reflected z)>0 for the Green port,

```text
current Green provenance_M → A_infty + J_infty - existing radial Green kernel.
```

The parameters z,w remain independent. C3 material edge selection is the
existing one; no edge is identified with C2 depth or a camera label.

## Exact completed corrected ledger

`canonicalCompletedC3AdjacentClockCorrectedReadout M z w` is defined by the
source-derived clock channels at `operatorHeightParameter z,w`, followed by
unchanged ordered crosses, four synthesis residuals, exact head/tail
correction, Xi weight, and archimedean/chart completion:

```text
XiWeight(z,w) * [A_M + J_M + offDiagonal_M + readoutResidual_M + tail_M]
    + archimedeanChart(z,w).
```

It is an expanded final observation, not a new source vector. Its equality
to the final readout of the same existing structured global ledger is proved
without any strip or sign hypothesis. The ledger's Green-port and provenance
terms combine through the actual finite clock transport; the structured
input and its independently retained coordinates are unchanged.

On the already-required genuine strip domain, it equals

```text
chartWeight(z,w) * completedGreenWronskian(F,-F',z,w)
```

at **every** cutoff M. This uses the old completed source identity only after
the geometric readout equality is established. It introduces no moment,
HP/Stieltjes certificate, positive-kernel or complementary-norm hypothesis.
The `operatorHeightParameter` here is the existing source chart, not a
height operator or spectral data used to construct the state.

The zero-material-cutoff canary proves exactly:

```text
correctedReadout_0 = XiWeight * exactTail_0 + archimedeanChart.
```

It does not claim this value is always nonzero. It proves that dropping the
material head does not authorize dropping the completed source channels.

## Full independently polarized source balance

`ChiralReturn.polarizedSourceBalance_eq_adjacentClockCorrectedLedger`
transports the same balance to this corrected readout under the original
geometric strip condition. It preserves:

- independent coefficients c,d;
- independent internal radii r,s;
- all ordered pairs of samples i,j;
- the existing conjugate-linear-first Cauchy pairing;
- Hermite--Biehler denominators and chart weight;
- the correct readout parameter order `(sample_j,sample_i)`;
- every source completion/cross channel above.

Material cutoff M, shrinking radial index k, source chart parameters and
Cauchy internal radii are not identified. No new grid is chosen. The old
strip/regularity API supplies eventual applicability for each finite family;
this does not provide a uniform sign for all coefficient vectors.

## Exact remaining sign and why Pitagoras has not closed

The pre-existing geometric camera source and its four-channel correction
satisfy the old energy identity. The new theorem
`ChiralReturn.storage_nonnegative_iff_coisometricCorrection_le_energy`
exposes its precise consequence, on the same regular source domain:

```text
Re storage >= 0
  iff
Im(coisometricFourChannelBalance(c,c,r,r))
  <= ||coisometricSourceSynthesis(c,r)||².
```

The proof reuses the existing balance and real algebra. It proves neither
inequality, and adds no positivity premise or assumption wrapper.

The ONE remaining obligation is that geometric correction bound uniformly:
for every N, eventually in the canonical radial index k, for **all** c,
at internal radius 1. Equivalently, the original completed-source storage
must be nonnegative with precisely those quantifiers.
A source-derived complementary Hilbert channel whose full polarized norm
realizes this balance would suffice. No such channel is supplied by the
current identities audited here. Orthogonal energy of the global ledger
controls a sum of squared component norms; its complex weighted readout and
the incidence-minus-return balance are different expressions. Absolute
convergence cannot order those two energies.

No sign is inferred termwise, no local positivity of the flux integrand is
required, and no cross term is discarded. The decomposition and source
completion close; the all-coefficient energy bound remains a mathematical
frontier, not a hidden Lean placeholder.

## New declarations

- `canonicalC3PositiveLogGap_norm_le_one`;
- `canonicalC3PositiveValue_norm_le_one`;
- `canonicalC3AdjacentClockReturn_norm_le`;
- `canonicalC3AdjacentMixedWedge_norm_le`;
- `summable_norm_canonicalC3AdjacentClockReturn`;
- `summable_norm_canonicalC3AdjacentOrdinaryClock`;
- `canonicalC3AdjacentClockBlockChannels`;
- `canonicalC3AdjacentClockBlockChannels_summable_norm`;
- `canonicalC3CompletedAdjacentClockChannels`;
- `canonicalC3AdjacentClockFiniteSum_eq_blocks`;
- `canonicalC3AdjacentClockChannels_tendsto_completed`;
- `canonicalC3MixedGreenProvenance_tendsto_clockCompletion`;
- `canonicalCompletedC3AdjacentClockCorrectedReadout`;
- `canonicalCompletedC3AdjacentClockCorrectedReadout_eq_existingLedger`;
- `canonicalCompletedC3AdjacentClockCorrectedReadout_eq_sixChannelReadout`;
- `canonicalCompletedC3AdjacentClockCorrectedReadout_eq_completedWronskian`;
- `canonicalCompletedC3AdjacentClockCorrectedReadout_eq_correctedGreenNumerator`;
- `canonicalCompletedC3AdjacentClockCorrectedReadout_zero`;
- `ChiralReturn.polarizedSourceBalance_eq_adjacentClockCorrectedLedger`;
- `ChiralReturn.storage_nonnegative_iff_coisometricCorrection_le_energy`;

## Trust and validation

All 20 declarations have `#assert_prime_depth_source_axioms` and `#print axioms`.
Type/value dependency closures: 3553 declarations for completion and 7030
for the corrected full ledger, including the energy-bound equivalence.
The source firewall rejects canonical moments, HP/Stieltjes certificates,
Hankel, Jacobi/height operators, Herglotz and BR2 dependencies. The imported
historical module graph is larger; the firewall checks actual declarations
reachable from each new type and proof, rather than treating a module import
as use of every theorem it contains.
Footprint is at most `[propext, Classical.choice, Quot.sound]`.

Commands:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedC3AdjacentClockCompletion
lake build --wfail CarrySelfAdjointOperator.CompletedC3AdjacentClockCompletionAudit
lake build --wfail CarrySelfAdjointOperator.CompletedNativeAdjacentClockCorrectedLedger
lake build --wfail CarrySelfAdjointOperator.CompletedNativeAdjacentClockCorrectedLedgerAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

All commands passed on llm. Root build: 9535 jobs; main Audit: 9734 jobs.
The full script ended with `kernel audit passed`; static audit and
`git diff --check` passed. No new warning was accepted under `--wfail`.

Logs retained on llm: `/tmp/adjacent-completed-ledger-validation/`.
Modified files: the two modules and audits, root imports, theorem registry,
this report, README frontier paragraph, append-only checkpoint entry.
No existing mathematical declaration, source, metric or dependency is changed.
Final SHA and clean/synchronized Git state are recorded in the handoff.
