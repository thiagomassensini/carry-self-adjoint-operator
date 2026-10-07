# Adjacent material-clock / mixed Green boundary transport

## Checkpoint and status

Initial `HEAD = main = origin/main`:
`b1541f7924358be30a8a45d06aa9ee7a9024aec8`.
`git pull --ff-only` reported up to date; initial working tree clean.
All changes are on `llm:/home/thlinux/carry-self-adjoint-operator`, branch
`main`, with existing dependency pins and Foundation unchanged.

```text
PASS_FINITE_ADJACENT_CLOCK_GREEN_BOUNDARY_TRANSPORT
```

This closes the **finite form transport for the actual adjacent-edge mixed
ledger**. It does not construct a positive Hilbert Green kernel, prove a
completed limit of individual channels, or prove ChiralReturn contractivity.
The historical same-edge no-go remains intact.

## Audit: the actual orientation

The source is still
`canonicalC3AllCutoffMixedSourcePrefixState M z w : CanonicalC3AllCutoffMixedSourceHilbert`.
Its three retained states are ordinary/logJet pairs at z, w, reflected z.
The existing `mixedLegs` uses ordinary at w and logJet at z on consecutive
material edges. The Green port uses ordinary at w and reflected z.
Those roles are not identified with each other.

For `mr : Fin M × Fin 2`, the material edge is

```text
n = 3 * mr.first + mr.side,
```

and the pair is `(n,n+1)`. The first leg uses `(3m,3m+1)`; the second
uses `(3m+1,3m+2)`. Both pairs, and thus all three gradients, are retained.
The shared material node has integer `n+2`. This is not a C2 depth, not
an external camera index and not an operator height.

The generic `canonicalC3MixedLegWedge_at_materialIndex` proves this
coordinate identity even for arbitrary states of the existing carrier.
Canonical specialization then uses the already bundled ordinary/logJet
prefixes; no selected inverse of a trace is used.

The historical prime-camera commutator and reflected same-edge contraction
are not reused as this adjacent form. Instead, the proof derives the two
literal discrete product rules for the **existing material log gradient**.
It constructs no new clock operator, carrier norm or multiplicative valve.

## Source-first local identity

Write

```text
f_z(n) = positiveDirichletValue z n       -- material integer n+1
 g_z(n) = f_z(n+1) - f_z(n)
 c_z(n) = positiveLogDirichletGradient z n
 L(n)   = positiveLogVertexWeight n = log(n+1)
 d(n)   = positiveLogGap n = L(n+1)-L(n).
```

Both exact product rules are proved directly from these existing definitions:

```text
c_z(n) = L(n+1) g_z(n) + d(n) f_z(n)
       = L(n)   g_z(n) + d(n) f_z(n+1).
```

They are the two orientations of the discrete product rule for
`Delta(log * value)`. No moment equality or fitted scalar enters either proof.

At adjacent edges, use the right-endpoint rule at n and left-endpoint
rule at n+1. The common frequency is **L(n+1) = log(n+2)**. Define
independently the two local source observations:

```text
A_n(z,w) = L(n+1) [g_w(n+1) g_z(n) - g_w(n) g_z(n+1)]
J_n(z,w) = d(n) g_w(n+1) f_z(n)
             - d(n+1) g_w(n) f_z(n+2).
```

The kernel proves for all independent complex z,w and all natural n:

```text
g_w(n+1) c_z(n) - g_w(n) c_z(n+1) = A_n(z,w) + J_n(z,w).
```

This is the literal `sameSEdgeBoundaryWedge` orientation. It is bilinear,
without introducing conjugation into this local wedge. The existing
sesquilinear `greenForm` retains its own original argument order later.

`canonicalC3AdjacentClockChannels z w n : ℂ × ℂ` stores `(A_n,J_n)`.
`canonicalC3AdjacentClockChannelFamily M z w : Fin M × Fin 2 → ℂ × ℂ`
retains those observations separately at each leg before global synthesis.
These are observations of the unchanged source, not a lossless replacement
of the source or a newly asserted positive Hilbert Gram.

J is called a log-gap return only as an endpoint term of this product rule.
It is **not** identified with `ChiralReturn`'s returned synthesis or with a
positive complementary/escape channel. No sign of J is claimed.

## Finite Green and full head transport

Let x be the same canonical mixed prefix. The kernel proves

```text
x.greenProvenanceReadout M w (reflectedParameter z)
  = Σ_legs A + Σ_legs J
      - greenForm (greenPort(3M,w,x.wSource))
                  (greenPort(3M,reflected z,x.reflectedZSource)).
```

This is `canonicalC3MixedPrefixGreenProvenance_clockTransport`.
It is not a new residual defined by subtracting the target. Its proof
substitutes the source product-rule identity in each existing mixed leg,
then uses finite sum distributivity. Both local components are retained.

The unchanged complete finite head synthesis then satisfies

```text
mixedScalarBoundaryWedge(valueHead_z, i*logHead_z, valueHead_w, i*logHead_w)
  = (Σ_legs A + Σ_legs J)
      + x.offDiagonalReadout M
      + x.heightResidualReadout M.
```

`canonicalC3MixedPrefixHead_clockTransport` reuses the existing universal
mixed boundary synthesis theorem. The off-diagonal readout retains every
ordered distinct-leg cross term. The last term is the existing correction
formed from all four synthesis discrepancies; none is erased or renamed.
The historical `heightResidualReadout` name refers here to the final
multiplication by i, not an input from a height operator.

Consequently the existing Green port, local clock channels, ordered crosses
and boundary readout residual remain in the same finite ledger. The head
readout includes its certified unit seed. No premature local scalar sum is
substituted for complete head synthesis without these cross/residual terms.

## Boundary provenance of the return samples

The new proof also recovers each required sample from the same finite
ordinary source:

```text
f_z(n) = 1 + Σ_(j<n) g_z(j)
       = 1 + Σ_(j<n) ordinaryCompletedPrefix(z,3M)(j),  n ≤ 3M.
```

The seed 1 is proved from `positiveDirichletValue z 0`; it is global, not
assigned to a camera. The initial slope remains the first gradient.
This is a finite **affine** reconstruction, not a homogeneous linear
readout from the gradient alone.

`canonicalC3AdjacentClockReturn_eq_seededPrefix` rewrites both f_z(n)
and f_z(n+2) in J using this very prefix. For every actual mixed leg,
`n+2 ≤ 3M`; the last outer node uses all 3M retained gradients. Material
samples run through integer 3M+1. No raw nodal ℓ² state, harmonic energy
limit or new bounded prefix-sum theorem is asserted.

## Canaries and diagonal mechanism

The dedicated audit checks the actual first-cell legs `(0,0)` and `(0,1)`
for arbitrary z,w. Their shared-node frequencies are log 2 and log 3.
Both local mixed pairings equal their two source-derived channel sum.
These tests use no h0/h1 or numeric fitting.

For **any** complex s, the ordinary part A_n(s,s) vanishes algebraically.
Thus the exact same-parameter provenance simplifies to

```text
Σ_legs J(s,s) - the unchanged reflected ordinary Green port form.
```

This identifies where the diagonal adjacent-clock contribution lives;
it does not prove that J, this difference or the completed quadratic storage
is nonnegative. The historical same-edge finite counterexample is neither
removed nor contradicted by this different contraction.

## Scope and one remaining gate

All finite theorems are unconditional, with independent z,w unless the
same-parameter theorem explicitly specializes them. They do not pass M→∞
for A and J separately. Tail, Xi, archimedean/chart completion and the full
corrected Green/TFVD ledger are unchanged; no decay or cancellation of those
completed channels is inferred from this finite algebra.

The remaining geometric positivity/Pythagorean gate is still the original
complete-source sign, with the correct quantifiers:

```lean
∀ N : ℕ, ∀ᶠ k : ℕ in Filter.atTop,
  ∀ c : Fin N → ℂ, 0 ≤ (ChiralReturn.storage k c 1).re
```

A source-derived complementary norm identity for the full independently
polarized balance would suffice. This audit constructs no such positive
channel. It provides the actual local clock-gap terms and retains the
existing complete synthesis corrections needed for that next investigation;
it does not replace the gate by a positivity assumption.

## Public declarations

- `canonicalC3LogGradient_right_productRule`;
- `canonicalC3LogGradient_left_productRule`;
- `canonicalC3AdjacentClockChannels`;
- `canonicalC3AdjacentClockChannels_eq_mixedWedge`;
- `canonicalC3AdjacentMaterialLegIndex`;
- `canonicalC3MixedLegWedge_at_materialIndex`;
- `canonicalC3AdjacentClockChannelFamily`;
- `canonicalC3MixedPrefixLeg_clockTransport`;
- `canonicalC3MixedPrefixGreenProvenance_clockTransport`;
- `canonicalC3MixedPrefixHead_clockTransport`;
- `canonicalC3AdjacentClockChannels_sameParameter_first`;
- `canonicalC3MixedPrefixGreenProvenance_sameParameter`;
- `canonicalC3Sample_eq_seed_add_gradientPrefix`;
- `canonicalC3Sample_eq_seed_add_completedGradientPrefix`;
- `canonicalC3AdjacentClockReturn_eq_seededPrefix`;

## Trust and validation

All 15 declarations receive `#assert_prime_depth_source_axioms` and
`#print axioms`. The dedicated source firewall traverses proof values and
types: **3481 reachable declarations**, rejecting canonical moments,
HP/Stieltjes certificate, Hankel, Jacobi/height operator, Herglotz and BR2
inputs. Footprint is at most `[propext, Classical.choice, Quot.sound]`.
The first-cell and diagonal canaries are kernel checked in the same audit.

Validation commands:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedC3AdjacentClockGreenTransport
lake build --wfail CarrySelfAdjointOperator.CompletedC3AdjacentClockGreenTransportAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

All listed commands passed. Root build: 9533 jobs; main Audit: 9730 jobs.
The full script ended with `kernel audit passed`; static audit and
`git diff --check` passed. No new warning was accepted under `--wfail`.

Logs are retained on llm under `/tmp/adjacent-clock-validation/`.
Modified files: new module and audit, root imports, theorem registry,
this report, README frontier paragraph and append-only checkpoint entry.
No dependency, Foundation, canonical source, clock or metric is changed.
Final published SHA and synchronized/clean Git state are recorded in the
handoff rather than self-referenced inside the commit.
