# Projective/chiral finite-difference moment pairing

## Checkpoint

Initial canonical main:
`384ae67c156cde5d81e07247dfc6d7179eeb1b44`.
`git pull --ff-only` reported up to date; `HEAD`, `main`, `origin/main` and
GitHub's `refs/heads/main` agreed, and the working tree was clean.
No experimental branch is used.

STATUS: `PASS_PROJECTIVE_CHIRAL_FORWARD_DIFFERENCE_MOMENT_PAIRING`.

**PASS_PAIRING ≠ PASS_POSITIVITY.**

## Interface audit before new definitions

| Arrow / existing interface | Classification | Exact scope |
|---|---|---|
| Completed characteristic → positive Hermite–Biehler amplitude, chiral quotient and radial Cauchy feature | DEFINITIONAL | `canonicalCompletedNativeRadialProjectiveChiralState` packages both coordinates; no moment or BR2 input |
| Projective state pair → signed form | DEFINITIONAL | `canonicalCompletedNativeProjectiveChiralForm`, a difference of two existing L² inner products with forced factor 1/2 |
| Signed sample form → polarized dslope | KERNEL_CHECKED | `canonicalCompletedNativeRadialProjectiveChiralForm_eq_dslope`, under finite regularity; its eventual regularity theorem discharges those premises in each centered finite germ |
| Kernel sample grid → normalized mixed differences | KERNEL_CHECKED | Existing `completedGreenKernelTwoStepShiftedForwardDifference`, explicit finite sums and conjugated first normalization |
| Shifted radial polarized dslope differences → polarized canonical coefficient | KERNEL_CHECKED | `completedNativePolarizedDslope_shiftedRadial_tendsto`, all orders with two independent step indices |
| Canonical coefficient → prime-depth geometric coefficient | KERNEL_CHECKED | Previous `primeDepthGeometricMoment_eq_canonical`, used only after scalar coefficient extraction |
| Signed finite germs → positive Gram | CONDITIONAL | Existing equivalence with chiral multiplier contractivity/Pick positivity; this condition is not proved here |
| Prime-depth normalized trace vector `X_n` → radial projective difference vector | OPEN | No natural proved transport between these two carriers was found or assumed |

`CompletedGreenForwardDifferenceGramBridge` supplies generic real-axis
**Hilbert** bridges with kernel/factor hypotheses. They are not instances of
the signed form, and those hypotheses are not assumed. The appropriate
ready-made analytic extractor is instead the **shifted radial** API in
`CompletedNativeRadialTiltSamplePositivity`.

`CompletedC3FinalReadoutKernelBridge` gives a scalar completed-ledger/kernel
readout, not a signed vector difference theorem. `GreenKernelCoefficientClosure`
already defines normalized differences and their explicit integer weights.
`PrimeDepthNormalizedResponseVectorJet` remains a source/readout lift; its
standard inner product is not used. `CompletedNativeHPGateAudit` distinguishes
the failed complex radial Taylor carrier from the real positive certificate;
no such certificate or BR2 family is an input to this construction.

## State and form

```lean
CanonicalCompletedNativeChiralCauchyCarrier :=
  MeasureTheory.Lp ℂ 2 (volume : Measure unitInterval)

CanonicalCompletedNativeProjectiveChiralCarrier :=
  CanonicalCompletedNativeChiralCauchyCarrier ×
  CanonicalCompletedNativeChiralCauchyCarrier

canonicalCompletedNativeRadialProjectiveChiralState :
  ℕ → ℕ → CanonicalCompletedNativeProjectiveChiralCarrier

canonicalCompletedNativeProjectiveChiralForm :
  CanonicalCompletedNativeProjectiveChiralCarrier →
  CanonicalCompletedNativeProjectiveChiralCarrier → ℂ
```

The first coordinate is the positive-amplitude Cauchy state, the second its
chiral-multiplier image. They remain separately explicit through finite
vector combination. The fixed signed form is

\[
\mathcal B(u,v)=\tfrac12
 (\langle u_+,v_+\rangle-\langle u_-,v_-\rangle).
\]

`projectiveChiralForm_smul` proves exactly
`B(c • u, d • v) = conj(c) * d * B(u,v)`.
No new inner product or positive carrier is selected.

## Grid and finite-difference vector

The existing grid is shifted, genuinely off-axis:

\[
 a_k=i/(k+1),\qquad z_{k,r}=(r+1)a_k.
\]

It is `canonicalCompletedC3RadialSecondStep` and
`canonicalCompletedC3RadialTiltPoint`, with the existing theorem
`canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul`.
Thus order zero samples at `a_k`, not at zero. No grid interpolation or new
one-point state is fabricated.

Define only finite combinations of the existing discrete states:

\[
 Y_{p,k}=\frac1{p!a_k^p}
   \sum_{r=0}^p(-1)^{p-r}\binom pr\,P(k,r).
\]

The exact declaration is `projectiveChiralDifferenceJet k p`. The weights
reuse `completedGreenForwardWeight`; conjugation of each weight is proved
trivial because it is real. Factorials and powers implement the existing
Taylor-coefficient normalization, not a fitted scale.

## Exact finite equality and regularity

`projectiveChiralDifferenceJet_pairing_eq_weightedSum` proves the signed
sesquilinear double-sum identity before any kernel or moment identification.
It retains `conj((p! a_k^p)⁻¹)` in the first factor and `(q! a_k^q)⁻¹` in the
second. This is the Lean conjugate-linear-first convention.

`projectiveChiralDifferenceJet_pairing_eq_dslope` proves, on a regular section
of size `p+q+1`,

```lean
B (projectiveChiralDifferenceJet k p) (projectiveChiralDifferenceJet k q) =
  completedGreenKernelTwoStepShiftedForwardDifference
    canonicalCompletedNativePolarizedDslopeKernel a_k a_k p q
```

Regularity enters **only** when replacing each state-pair form by its kernel
value. Every sample must lie in `completedNativeHeightDomain`, with nonzero
completed characteristic and positive Hermite–Biehler coordinate.
`projectiveChiralDifferenceJet_pairing_eventuallyEq_dslope` uses the existing
centered regularity theorem to discharge this automatically for every fixed
finite stencil. No globally regular source or positivity assumption is added.

The kernel is the conjugate polarization `dslope response (conj z) w`.
Accordingly the first analytic step is `conj(a_k)=-i/(k+1)`. The existing
polarized shifted-difference theorem already handles this normalization;
no extra sign or phase is dropped.

## Canaries, coefficient extraction and all orders

Finite canaries `(0,0)`, `(0,1)`, `(1,1)` are assembled in
`projectiveChiralDifferenceJet_pairing_canaries`.
The existing two-step scalar limit is restricted to the diagonal `(k,k)`;
this is a cofinal map to the product `atTop` filter.

First:
`projectiveChiralDifferenceJet_pairing_tendsto_coefficient` extracts
`polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment p q`.
Only afterwards is the existing uniqueness identification rewritten to
`primeDepthGeometricMoment`.

The low-order limit canaries in
`projectiveChiralDifferenceJet_pairing_canary_limits` are:

| Literal derivative orders | Limit |
|---|---|
| `(0,0)` | `(g0 : ℂ)` |
| `(0,1)` | `0` |
| `(1,1)` | `(g1 : ℂ)` |
| `(2,2)` | `(g2 : ℂ)`, checked separately |

The first three stencils are not consecutive geometric moment indices.
All-order capstone:
`projectiveChiralDifferenceJet_pairing_tendsto_primeDepthCoefficient`.
Its exact target is
`polarizedGreenMomentCoefficient primeDepthGeometricMoment p q`:

- `p+q` even: `g_((p+q)/2)`;
- `p+q` odd: zero.

The four public block theorems give:

| Jet orders | Complex pairing limit |
|---|---|
| `2p, 2q` | `g_(p+q)` |
| `2p+1, 2q+1` | `g_(p+q+1)` |
| `2p, 2q+1` | `0` |
| `2p+1, 2q` | `0` |

Mixed **limits** are zero; finite-step mixed orthogonality is not asserted.
No convergence of the vectors `Y_{p,k}` themselves is proved or needed.

## Separation from the earlier vector lift

`X_n` inhabits the finite structural trace-family carrier and preserves the
normalized source readout. `Y_{p,k}` inhabits the pair of infinite-dimensional
Cauchy L² channels and supplies the signed kernel pairing limit.
They share the established completed scalar coefficients, but this is not
an equality of vectors, an isometry, or a transport theorem between carriers.
No such transport is defined in this round.

BR2 is absent from the definitions and proof dependencies of this new route.
It remains a possible downstream strictness/independence transport only.

## Single next positivity gate

The remaining independent property is precisely

```lean
CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive
```

For each finite radial family it requires the norm of every combination of
multiplier vectors to be no larger than the corresponding Cauchy combination.
Existing theorems identify this with eventual Pick positivity and eventual
positive semidefiniteness of the projective/chiral sample matrices.
This round proves none of these conditions. In particular, canonical Hankel
positivity is not used to establish kernel positivity.

## Audits and publication

Every new public declaration is in the focused audit and central registry,
with `#print axioms` and the standard three-axiom check. Two proof/type-closure
checks distinguish:

1. geometric construction and finite identities: no canonical moments,
   Hankel/Jacobi/height or BR2 jet input;
2. the full coefficient/prime-depth limit route: canonical identification is
   allowed at the final stage, but BR2, Hankel and Jacobi/height inputs remain
   prohibited.

Commands:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeProjectiveChiralForwardDifference
lake build --wfail CarrySelfAdjointOperator.CompletedNativeProjectiveChiralForwardDifferenceAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

Validation completed successfully:

- New module: `--wfail` passed (9,271 jobs).
- Focused audit: `--wfail` passed (9,273 jobs).
- Root and central audit: `--wfail` passed (9,709 jobs).
- `scripts/static_audit.sh`: `static audit passed`.
- `scripts/audit.sh`, including the existing BR2/Order/recovered-C2 audits:
  `kernel audit passed`.
- New capstones print only `[propext, Classical.choice, Quot.sound]`.
- Pure geometric/finite dependency closure: 5,243 declarations checked.
- Complete signed-pairing dependency closure: 5,642 declarations checked.
- Placeholder/trust-escape scan and `git diff --check`: passed.

Publication is one coherent main commit, titled
`feat: realize prime-depth coefficients by signed chiral differences`.
Its exact hash is recorded in Git history and the delivery report.
This publication closes signed pairing, not positivity.
