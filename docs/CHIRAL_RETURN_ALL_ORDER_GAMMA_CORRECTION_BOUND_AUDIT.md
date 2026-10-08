# All-order ChiralReturn Gamma correction bound audit

## Initial checkpoint and scope

Audited source base after `git pull --ff-only`:
`65f6cdea21896ac13fc7c11135977459abe56a03`, branch `main`.
HEAD, main and origin/main agree at this checkpoint. Two pre-existing
untracked files (`C2OddTfvdTransport.lean`, `C2OddTfvdTransportAudit.lean`)
are preserved and excluded from task commits.

Request: attack the arbitrary-order bound of the pre-existing four-channel
correction by the pre-existing coisometric source energy, preserving complete
synthesis, source normalization, boundaries, completion and all crosses.
No arbitrary-order sign assumption, fitted state, metric, Gram, spectral data
or new dilation is introduced.

Statuses supported by the new kernel checks:

- `PASS_ALL_ORDER_GAMMA_CORRECTION_CANCELLATION`
- `PARTIAL_ALL_ORDER_CHIRAL_RETURN_CORRECTION_BOUND`

No all-order positivity or contractivity is claimed.

## Upstream inventory

| Object | Existing carrier/readout | Provenance and role |
|---|---|---|
| `coisometricSourceSynthesis k c r hhalf` | `CarryGammaComplexCamera` | Full original radial source weights synthesize the old intrinsic response/camera vectors |
| `canonicalCompletedC3PolarizedGammaState z hz` | `CarryGammaComplexNaimark` | Existing source-varying Gamma state of the completed six-camera source; both quadratures retained |
| `canonicalCompletedC3CoisometricThreeBoundaryCorrections` | complex polarized boundary readout | The existing port-resolved, leak-resolved and port-source channels |
| `canonicalCompletedC3RawGammaWronskianDefect` | complex polarized boundary readout | Existing full Gamma boundary minus actual completed `(F,-F')` Wronskian |
| `coisometricFourChannelBalance` | full double-sum readout | The raw channel plus all three comparison channels, with unchanged Cauchy metric and source weights |
| `sourceValue`, `sourceCompanion` | original Cauchy Hilbert carrier | Complete value and companion syntheses, not reconstructed from scalar traces |

Primary sewing uses the existing
`canonicalCompletedC3CoisometricThreeBoundaryCorrections_eq_sub_gamma`,
`canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_kernel`,
`canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel`, and
`radialCauchy_inner_mul_separation`.

The previous inter-repository audit found useful geometry but no ready
specialization proving the sign: arbitrary-camera Weyl Gram positivity,
primos prime-carry contraction, and C2 stencil energy refer to their own
sources/metrics. They are not invoked as sign premises here.

## New packaging: no new carrier or metric

`gammaSourceSynthesis` has type

```lean
(k : ℕ) → {N : ℕ} → (Fin N → ℂ) → ℝ → CarryGammaComplexNaimark
```

It is the complete sum of the already existing Gamma states at the original
radial nodes. Each coefficient is the unchanged
`c_i * r^(i+1) / completedNativePositiveHermiteBiehlerCoordinate(z_i)`.
No moment coefficient or target Gram enters this vector.

`rawGammaWronskianBalance` has type

```lean
(k : ℕ) → {N : ℕ} → (Fin N → ℂ) → (Fin N → ℂ) → ℝ → ℝ → ℂ
```

It is the double-sum polarization of the existing raw discrepancy, with the
same two independent source coefficient families and the original Cauchy
pairing. The boundary readouts inside the old discrepancy already come from
the completed source. This packaging keeps every ordered pair; it does not
replace either complete synthesis by a diagonal or a scalar source proxy.
No arbitrary complementary vector, matrix square root, or additional source
hypothesis is created.

## Exact cancellation in every finite order

Write A(c) for the old coisometric source synthesis, Gamma(c) for the new
full synthesis of the existing Gamma vectors, Q4(c,d) for the old four-channel
balance, and D(c,d) for `rawGammaWronskianBalance`.

The existing spectral separation cancels the original Cauchy factor to I.
First the three comparison channels become the difference of the two
pairwise Grams. After BOTH complete syntheses:

`Q4(c,d) = D(c,d) + I * (inner A(c) A(d) - inner Gamma(c) Gamma(d))`.

This is
`coisometricFourChannelBalance_eq_rawGamma_add_gram_difference`.
It holds for arbitrary N, independent c,d and radii r,s, with only the
existing half-plane requirements for the old coisometric state.
No channel is deleted. The norm difference and port internal crosses have
been combined exactly, not bounded separately or asserted orthogonal.

The same actual source polarized balance is therefore

`polarizedSourceBalance(c,d) = 2 * inner Gamma(c) Gamma(d) + 2*I*D(c,d)`.

On the diagonal:

`Re(storage) = 2 * norm(Gamma(c))^2 - 2 * Im(D(c,c))`.

The Mathlib inner product is conjugate-linear in the first slot.
The signs above are kernel checked. In particular the three channels cancel
against the coisometric energy, leaving **one raw signed channel**.

The exact requested bound reduces to

`Im(Q4(c,c)) ≤ norm(A(c))^2  iff  Im(D(c,c)) ≤ norm(Gamma(c))^2`.

This is
`coisometricCorrection_le_energy_iff_rawGammaCorrection_le_energy`.
It supplies neither sign as an assumption or conclusion.

## Attempted uniform sign control

The full source frontier now reads

`Im(D(c,c)) - norm(Gamma(c))^2 = -2 * Im(inner sourceValue sourceCompanion)`.

Cauchy--Schwarz proves, without a sign hypothesis,

`abs(Im(D(c,c)) - norm(Gamma(c))^2) ≤ 2 * norm(sourceValue) * norm(sourceCompanion)`.

This is a genuine arbitrary-order bound on complete vector syntheses, but
its upper endpoint lies ABOVE Gamma energy. It does not prove the needed
one-sided inequality. No sign of the mixed orientation follows from
Cauchy--Schwarz or the already positive Gamma Gram alone.

`rawGammaCorrection_comparison_eventually_complete N` packages the exact
polarization, storage identity, and size estimate with ONE eventual threshold
in k for every coefficient family and internal radius. The threshold may
depend on N. The cutoff M was arbitrary in the source comparison and is
absent from the resulting identities. Radial k, material cutoff, internal
radius, depth and height are never identified.

A fixed low-order Taylor/Green truncation also cannot provide uniform
control of all higher coefficient directions: the already proved
`radialBoundaryJetKernel_ne_bot` and
`exists_nonzero_incident_boundary_cancellation` retain nonzero complete
incident states whose first r boundary jets vanish whenever r<N. Thus the
certified six-coordinate chart is not silently used to control every larger
family. This is an observability obstruction for that fixed truncation,
not a counterexample to the full source sign.

The remaining obstacle is a signed bound of the old raw Gamma--Wronskian
channel, not a lack of full coisometric/TFVD reconstruction. No mathematical
no-go for that bound or for a future geometric realization is claimed.

## Actual-source six-node tests

Only after the arbitrary-order cancellation is established, the previous
source-certified full N=6 storage sign is reused:

- `rawGammaCorrection_six_eventually_lt_energy`:
  for one eventual threshold and every nonzero c in `Fin 6 → ℂ`,
  `Im(D(c,c)) < norm(Gamma(c))^2`;
- `coisometricCorrection_six_eventually_lt_energy`:
  the exact same strict bound in the original four-channel formulation;
- `rawGammaCorrection_six_eventually_boundary_margin`:
  there is eps>0 such that, eventually for every original input d,
  `Im(D(c_d,c_d)) + eps * sum_a normSq(h_k^a*b_a(d)) ≤ norm(Gamma(c_d))^2`,
  with `c_d = radialCompletedInputCoefficients k d` and the old six-node
  scaled Euler boundary chart.

The source, metric, raw theta coefficients, exact order-twelve remainder and
prior N=6 sign proof are unchanged. This does not promote the N=6 sign to
arbitrary N and does not assert a fixed operator-norm gap in the radial limit.

## Single remaining typed obligation

No declaration or assumption wrapper is added for this missing proof:

```lean
∀ N : ℕ, ∀ᶠ k : ℕ in Filter.atTop, ∀ c : Fin N → ℂ,
  (ChiralReturn.rawGammaWronskianBalance k c c 1 1).im ≤
    ‖ChiralReturn.gammaSourceSynthesis k c 1‖ ^ 2
```

This is exactly the all-order sign frontier after the three comparison
channels cancel. It is not supplied by a downstream HP, Stieltjes, Hankel,
Jacobi, height or BR2 result. It must be established from the actual completed
source orientation or an independently proved geometric factorization.

## Public declarations and audits

New module: `CompletedNativeChiralReturnGammaCorrectionCancellation`.
Dedicated audit: `CompletedNativeChiralReturnGammaCorrectionCancellationAudit`.
The root library and root Audit import them.

Public declarations:

1. `gammaSourceSynthesis`
2. `rawGammaWronskianBalance`
3. `radialThreeCorrections_eq_gammaGram_difference`
4. `coisometricFourChannelBalance_eq_rawGamma_add_gram_difference`
5. `polarizedSourceBalance_eq_gammaGram_add_rawGammaBalance`
6. `storage_re_eq_gammaEnergy_sub_rawGammaBalance`
7. `coisometricCorrection_le_energy_iff_rawGammaCorrection_le_energy`
8. `rawGammaCorrection_energy_gap_eq_source_cross`
9. `rawGammaCorrection_energy_gap_abs_le_sourceNorms`
10. `rawGammaCorrection_comparison_eventually_complete`
11. `rawGammaCorrection_six_eventually_lt_energy`
12. `coisometricCorrection_six_eventually_lt_energy`
13. `rawGammaCorrection_six_eventually_boundary_margin`

All declarations have `#assert_prime_depth_source_axioms`, `#print axioms`
and transitive `#assert_oriented_green_source` checks. Allowed footprint:
subsets of `[propext, Classical.choice, Quot.sound]`. The source firewall
checks 6772 reachable declarations and rejects HP certificates, canonical
moment inputs/positivity, Hankel/Jacobi/height, Stieltjes, downstream Herglotz
and BR2 proof routes.

All validation commands below passed. The abbreviated transcript and new
capstone footprints are archived under
`research/chiral-gamma-correction-cancellation-2026-10-08/`:

```text
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnGammaCorrectionCancellation CarrySelfAdjointOperator.CompletedNativeChiralReturnGammaCorrectionCancellationAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

No source object is altered. New files: the two modules, this report and
validation/axiom transcripts. Existing changes: root imports and README.
The pre-existing untracked C2 files remain untouched.
