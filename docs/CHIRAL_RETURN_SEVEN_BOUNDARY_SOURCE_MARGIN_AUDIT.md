# Seven-coordinate source margin: raw integral certificate

## Checkpoint and scope

Initial published main: `c073588076b8e6bb4710e5801cf7d9a9b66ea683`.
`git pull --ff-only` returned already up to date and HEAD/main/origin/main
agreed. The two existing untracked `C2OddTfvdTransport{,Audit}.lean` files
are preserved and excluded from this work. No previous checkpoint is rewritten.

The obligation is the sign of the ORIGINAL
`nativeSourceSevenEvenDiscriminant`, not a replacement form.
The existing complete seven-boundary sewing identity, raw thirteenth jet,
seven-node reconstruction and uniform complete remainder bound are reused.

Kernel-checked status: `PASS_SEVEN_BOUNDARY_SOURCE_MARGIN`.
This is finite source-face positivity. Full N=7 storage positivity and
arbitrary-N contractivity are separate gates and are not asserted here.

## Source-only certificate

Let `mu_j = completedNativeXiCosineMoment j` and
`tau_p = completedNativeThetaTailMoment p`. The existing integrations by
parts give

```text
mu_0 = 1/2 - tau_0/4,
mu_(j+1) = (2j+2)(2j+1) tau_(2j) - tau_(2j+2)/4.
```

`nativeSourceFourteenthMixedNumerator` is the exact 73-term polynomial
obtained by substituting the ORIGINAL source coefficient formulas into
the already-defined discriminant. It is not a moment definition or a
Gram factor. The kernel checks

```text
nativeSourceSevenEvenDiscriminant
 = nativeSourceFourteenthMixedNumerator(mu_0,...,mu_7)
     / (13153940405570764800000 * mu_0^7).
```

The divisor is positive by the existing raw integral positivity theorem.
The source recurrence, not canonical moment identification, supplies the
coefficients.

## Refined enclosures, same theta geometry

The previous enclosure route did not yield a certificate of this new sign.
Those earlier bounds are not modified and no no-go is inferred from them. New independent bounds are obtained as follows:

1. Use the same `thetaFirstMode` and its first two derivatives.
2. Expose its third and fourth derivatives, checked by differentiation.
3. Retain the full cubic Taylor polynomial in each source cell.
4. Control its remainder by the geometric fourth derivative, using the
   existing Mathlib Taylor theorem. The bound is conservative, with divisor
   `3! = 6`; no optimal quadrature constant is needed.
5. Use existing Mathlib 20-decimal pi bounds and the existing rational
   `thetaExpLower` / `thetaExpUpper` API for node certification.
6. Integrate powers 0,2,...,14 on 576 adjacent cells of size 1/512, from
   0 to 9/8. This is a quadrature cutoff, not a new material coordinate.
7. Retain the first-mode tail beyond 9/8, bounded uniformly through power
   fourteen by `2/10^13`. Retain ALL higher modes through the unchanged
   exponential majorant `p!/(100000*23^(p+1))`.

`thetaFirstMode_weighted_cubic_cell_bounds` certifies the integral bounds
before any source coefficient or discriminant readout. No state, source
amplitude, norm or metric is changed.

Every generated node and cell theorem is rational arithmetic checked by
Lean. `research/theta-fourteenth-source-certificate-generate.py` produces
the certificate files using exact fractions; Sympy is only an algebraic
certificate generator. Neither Python evaluation nor symbolic output is
trusted by the proof.

The eight new raw theta boxes feed a 1498-term exact unit-cube polynomial
expansion, organized in bounded proof chunks. The fixed denominator is
cleared with an integer homogeneous expansion (degree seven); this is
proof arithmetic only and changes no source amplitude or metric. The cube variables encode
integration bounds only. `ring` checks the expansion, and elementary
monomial bounds certify a strict lower bound `1/10^22` for the raw
polynomial throughout this enclosure. No matrix or metric is fabricated.

## Public conclusions

- `nativeSourceSevenEvenDiscriminant_integral_formula`
- `nativeSourceFourteenthMixedNumerator_thetaIntegral_box_pos`
- `nativeSourceFourteenthMixedNumerator_integral_pos`
- `nativeSourceSevenEvenDiscriminant_pos`
- `nativeSourceSevenEvenBoundaryEnergy_pos`
- `nativeSourceSevenBoundaryEnergy_pos`
- `nativeSourceSevenBoundaryEnergy_uniform_margin`

The last three conclusions apply the already-kernel-checked sewing/sign
and uniform-margin equivalences to the newly certified sign. Every even
and odd boundary cross term remains in the existing face.

## Dependency and trust firewall

The dedicated `CompletedNativeChiralReturnFourteenthSourceIntegralAudit`
checks standard axioms and the transitive source-only dependency closure.
It rejects canonical moments, HP/Stieltjes certificates, Hankel,
Jacobi/height, Herglotz positivity and BR2 dependencies. No canonical
sequence identification is used to infer a sign.

All 48 public declarations passed the dedicated axiom checks and explicit
`#print axioms`. Their footprint is at most
`[propext, Classical.choice, Quot.sound]`. The source-only transitive closure
check visited 5572 declarations and passed. The downstream modules checked
by the repository-wide audit are validation consumers, not proof premises.

## Validation

The new modules, dedicated audit, full library and umbrella audit passed
`--wfail`. Both repository audit scripts passed, as did unstaged and
staged `git diff --check`. The dedicated audit was also run directly with
`lake env lean` and passed. Generator reproduction checked all 184 generated Lean files
byte-for-byte; the remote sources match the recorded SHA-256 manifest.
The certificates comprise 181 data modules (577 nodes and 4608 weighted
cells, each with both lower and upper bounds), plus the aggregate integral
certificate, the raw polynomial identity and its enclosure.
The generator uses exact rational arithmetic. Independent kernel checking
is mandatory; generated output is not a trusted result.

Full logs are retained on llm under `/tmp/chiral-seven-margin-validation-*.log`;
the successful summary and dedicated axiom log are retained in
`research/chiral-seven-boundary-source-margin-2026-10-08/`.

## Next gate

Promote this finite boundary margin to the ACTUAL complete N=7 radial
source storage using the existing vector-prefix boundary limit and uniform
complete remainder estimate. Finite-step higher boundary coordinates and
the analytic remainder must both remain; they cannot be dropped at a
nonzero radial step. This report makes no arbitrary-order positivity claim.

## Files and publication boundary

New analytic/certificate modules:

- `CompletedNativeThetaCubicQuadrature.lean`
- `CompletedNativeThetaFourteenthTail.lean`
- `ThetaFourteenthSourceCertificateData/*.lean`
- `CompletedNativeThetaFourteenthSourceCertificate.lean`
- `CompletedNativeChiralReturnFourteenthSourcePolynomial.lean`
- `CompletedNativeThetaFourteenthPolynomialEnclosure.lean`
- `CompletedNativeChiralReturnFourteenthSourceIntegral.lean`
- `CompletedNativeChiralReturnFourteenthSourceIntegralAudit.lean`

The root library and audit import the new capstones. README appends the
closed finite source-margin checkpoint; earlier research reports are
preserved. The exact generator and validation manifest/log are retained
under `research/`. No old source definition or Hilbert metric is changed.
Tracked changes from this round are committed. The two pre-existing
untracked C2 transport probes remain untouched, so the entire local
working tree must not be described as globally clean.

## Executed validation commands

The exact new-module list and all PASS results are preserved in
`research/chiral-seven-boundary-source-margin-2026-10-08/validation-summary.txt`.

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeThetaCubicQuadrature CarrySelfAdjointOperator.CompletedNativeThetaFourteenthTail CarrySelfAdjointOperator.CompletedNativeThetaFourteenthSourceCertificate CarrySelfAdjointOperator.CompletedNativeChiralReturnFourteenthSourcePolynomial CarrySelfAdjointOperator.CompletedNativeThetaFourteenthPolynomialEnclosure CarrySelfAdjointOperator.CompletedNativeChiralReturnFourteenthSourceIntegral
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnFourteenthSourceIntegralAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
git diff --cached --check
lake env lean CarrySelfAdjointOperator/CompletedNativeChiralReturnFourteenthSourceIntegralAudit.lean
```

These commands were executed on llm, on the main checkout. Their successful
results are remote-host kernel checks, not a claim that GitHub Actions has
already finished checking the subsequently published commit.
