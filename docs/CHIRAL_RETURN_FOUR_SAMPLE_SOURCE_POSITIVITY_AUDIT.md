# Source-first positivity of the four-sample boundary cancellation sector

## Checkpoint and scope

Date: 2026-10-07. Initial published main:
`0564d6f1e68eed3d2b27d220e1a28caacdb1eafd`.
`git pull --ff-only` reported up to date; the initial working tree was clean.
Only the normative carry-self-adjoint-operator main is changed.

New finite status: `PASS_SOURCE_FIRST_FOUR_SAMPLE_CANCELLATION_POSITIVITY`.
The proof also covers the entire four-sample, three-jet cancellation sector,
with one eventual radial threshold for all nonzero coefficients in that sector.
Overall status remains `PARTIAL_COMPLETED_SOURCE_ENERGY_POSITIVITY`.
No all-order return contraction or full four-sample PSD is claimed.

## Source provenance and forbidden inputs

The proof reuses the full completed characteristic F and actual source
q=-F'/F. Its raw even derivatives come from the upstream positive theta
cosine source. It uses the existing refined integral quadrature/tail bounds
and the purely polynomial theorem
`xiEighthMoment_numerator_lower_bound_of_refined_box`.

That polynomial theorem is reused directly from
`CompletedNativeEighthBernsteinCertificate`. Although its historical consumer
is a shifted determinant, NO Hankel/shifted-Hankel declaration, canonical
logarithmic moment, HP/Stieltjes certificate, height/Jacobi operator or BR2
construction is a premise or reachable dependency of the new capstones.
The dedicated source firewall verifies this declaration-level distinction.

There are no new weights, metrics, fitted constants, positive dilations or
states manufactured from a target Gram. No new TFVD/Green source encoder is
introduced. The existing full trace/source synthesis and source-amplitude
coordinate change are reused. Analytic expansion is applied to the completed
response AFTER the existing complete source synthesis/readout, not to a
head-only state or a purported inverse of scalar traces.

## Raw integral sign before canonical moment identification

Write a=mu_0, b=mu_2, c=mu_4, d=mu_6, e=mu_8, where
mu_(2j)=`completedNativeXiCosineMoment j`. These are the raw source integrals,
not the canonical logarithmic moment sequence.

The source determines

```text
A = 3 b^2 - a c,
B = 30 b^3 - 15 a b c + a^2 d,
C = 630 b^4 - 420 a b^2 c + 35 a^2 c^2 + 28 a^2 b d - a^3 e.
```

The new exact polynomial identity is

```text
10 A C - 21 B^2 = a^2 P,
P = xiEighthMomentNumerator(a,b,c,d,e).
```

The refined theta integral box proves P>=1/10^10. The existing raw source
inequality mu_0 mu_4 < 3 mu_2^2 proves A>0; also a>0. Hence C>0. The square
B^2 is retained, without requiring a sign for B.

All ten box bounds are derived from the first-mode integral certificate,
the full refined theta-tail majorant and the existing exact raw cosine/tail
identities. The norm/sign is not imported from a moment positivity consumer.

## Actual source derivative and division-free recurrence

The local source q is analytic at zero because F is analytic and F(0)!=0.
Its product identity is q F=-F'. Differentiating this identity by analytic
Leibniz gives the raw derivative recurrence

```text
sum_{j<=n} choose(n,j) D^j q(0) D^(n-j) F(0) = -D^(n+1) F(0).
```

The even characteristic germ and the raw integral derivatives give

```text
q(0)=D^2q(0)=D^4q(0)=D^6q(0)=0,
D q(0)=b/a,
D^3 q(0)=A/a^2,
D^5 q(0)=B/a^3,
D^7 q(0)=C/a^4 > 0.
```

The last equality is complex with its right side a real embedding. The sign
is obtained BEFORE any identification with canonical moments. No target
recurrence or moment equality transports this derivative formula.

## Exact analytic remainder of the actual four samples

The source-independent third-difference vector is v=(1,-3,3,-1). The existing
Cauchy pairing gives its exact storage, in source-amplitude input coordinates,

```text
Re S_k(sourceInput(v),1) = (k+1)/70 * Re H(h_k),
h_k = canonicalGreenJetStep k = 1/(k+1),
H(h) = -I [14 q(Ih) - 14 q(2Ih) + 6 q(3Ih) - q(4Ih)].
```

These are exactly the existing four radial tilt points. The weights 14,-14,6,-1
are the previously proved Cauchy canary coefficients; no value is fitted.
They cancel the odd powers 1,3,5. The source's even jets vanish by parity.

Mathlib's analytic Taylor factorization, with its remainder preserved, proves

```text
exists R analytic at zero, eventually h near zero,
  H(h) = h^7 D^7q(0) + h^8 R(h).
```

Thus H(h_k)/h_k^7 -> D^7q(0), including the exact higher source terms.
A seventh-degree polynomial NEVER replaces the full completed source.
Continuity of R at zero is sufficient for this fixed finite combination;
no uniform estimate over all coefficient families or orders is inferred.

The kernel derives

```text
(k+1)^6 Re S_k(sourceInput(v),1) -> Re D^7q(0)/70,
```

and the quantitative eventual lower margin

```text
Re D^7q(0) / [140 (k+1)^6] < Re S_k(sourceInput(v),1).
```

No explicit numerical cutoff k_0 is claimed. The derivatives, normalization
and radial scale are those of the actual source/grid, not spectral fitting.

## Whole finite cancellation sector, not just one chosen coefficient vector

The existing map J records endpoint degree jets in the Cauchy polynomial
geometry. Its four-sample three-jet kernel satisfies

```text
d in radialBoundaryJetKernel 4 3 -> d = d_0 * (1,-3,3,-1).
```

This follows from the three explicit linear equations J_0=J_1=J_2=0.
It neither changes the metric nor identifies degree jets with C2 depth.

Full storage is homogeneous with every cross term retained:

```text
S_k(z c,r) = |z|^2 S_k(c,r).
```

Consequently, the same eventual radial threshold gives

```text
forall d in ker(J_0,J_1,J_2), d!=0 ->
  0 < Re S_k(sourceInput(d),1).
```

Using the PREVIOUS exact all-order boundary cancellation identity, this is
also strict positivity of the pairing with the exact higher vector remainder:

```text
0 < Re <A(d), radialCompletedOddSourceRemainderSynthesis k 4 3 d>.
```

This is the whole one-dimensional cancellation sector of the four-sample
source. It is not every vector in the four-dimensional source, nor all N.
All full-source tails and completion factors remain unchanged.

## Remaining single all-order obligation

The original combined lower bound of
`radialReturnTransfer_eventually_norm_le_one_iff_green_boundary_tower`
is still required for every finite N and all coefficient families. This
round proves a genuinely positive higher-remainder sector that was previously
uncontrolled; it does not bound its mixed pairings with the retained boundary
sectors or the analogous sectors at arbitrary N.

The next block to control is the interaction between the cancellation sector
and the other source directions. Positive diagonal sector energies alone
cannot prove positivity of the complete polarized form.

## Public declarations and trust

Two new modules:

- `CompletedNativeChiralReturnSeventhSourceJet`
- `CompletedNativeChiralReturnFourSamplePositivity`

A dedicated `CompletedNativeChiralReturnFourSamplePositivityAudit` registers
all 22 new public declarations with `#print axioms`,
`#assert_prime_depth_source_axioms`, and `#assert_oriented_green_source`.
It is imported by root Audit; both source modules are imported by the root.

Allowed footprint: at most `[propext, Classical.choice, Quot.sound]`.
The exact source dependency closure excludes canonical moments, HP/Stieltjes,
Hankel/Jacobi/height, Herglotz positivity consumers and BR2.

Validation logs are preserved on llm in `/tmp/chiral-four-sample-validation/`.
Server-side Lean checks and GitHub Actions results are reported separately.
GitHub Actions startup failures from the preceding checkpoint do not supply
or invalidate a Lean proof; no CI-success claim is inferred from server builds.

## Executed validation

All checks below completed successfully on the llm main checkout:

```text
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnSeventhSourceJet
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnFourSamplePositivity
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnFourSamplePositivityAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

The focused firewall checked 5,562 reachable declarations. All 22 printed
axiom lists are subsets of `[propext, Classical.choice, Quot.sound]`.
The trust-escape / placeholder scan returned no matches. README records the
finite sign and its exact limit without upgrading the all-order status.

Files added: the two source modules, dedicated audit and this report.
Files updated: root imports, root Audit import and README.
After commit/push, HEAD/main/origin-main/GitHub equality and a clean worktree
are checked separately. Publication does not assume a successful Actions run.
