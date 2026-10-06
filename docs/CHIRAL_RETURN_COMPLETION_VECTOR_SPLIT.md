# Complete chiral source: vector product-rule completion and Green pairing

## Status

**PASS_CHIRAL_SOURCE_COMPLETION_VECTOR_SPLIT**.
**PASS_CHIRAL_COMPLETION_SIGNED_GREEN_PAIRING**.

The main division-free Hilbert gate remains
**PARTIAL_ORIENTED_COMPLETED_SOURCE_DIVISION_FREE_GREEN_REPRESENTATION**.
No positivity, contractivity, normalized positive kernel or strictness is
claimed. No global complex one-point Hilbert witness is constructed.

Initial published main: `4df95cc02e353a18c504e6dd5aa2c774015407e0`.
`git pull --ff-only` reported already up to date; working tree was clean.
The user authorized direct commits/push to main. All publication is after
kernel builds and audits. No experimental branch or canonical source edit.

## Attempt and geometric provenance

The previous archive consultation identified the completion derivative as a
term that cannot be omitted from the mixed form. The scalar product rule is
already present in `NativeBoundaryArchimedeanDressingSeparation`.
This round tests it on the actual vectors of `ChiralReturn`, before their
signed scalar contraction, rather than constructing another raw/Parseval
norm candidate.

Write `A = nativeXiCompletionFactor`, `Z = nativeHeightScalar`,
`C_Z = nativeHeightScalarBoundaryCompanion = -Z'`, and
`C_A = nativeXiCompletionBoundaryCompanion = -A'`.
On the existing genuine domain,

\[
F=AZ,\qquad -F'=A C_Z+C_A Z.
\]

Both normalized native TFVD traces are recovered at **every** cutoff from
the existing complete head/tail state. Their pointwise equality is exposed
by `canonicalC3BracketTfvdNormalizedTracePair_eq_native`. It is a trace
projection, not an inverse or a lossless encoder of the full Green port.
No tail, chart correction or global seed is replaced by an invented atom.

## Exact carriers and definitions

The unchanged carrier is

```lean
CanonicalCompletedNativeChiralCauchyCarrier :=
  Lp ℂ 2 (volume : Measure unitInterval)
```

It is **L²[0,1]**, not the material-edge ℓ² carrier or the raw all-bases
Green-frame coefficient carrier. Existing Cauchy vectors are
`u_i = completedNativeRadialChiralCauchyState k i`, scaled half-density
monomials. Their inner products already equal `(k+1)/(i+j+2)`.
All new channels are finite sums of these existing Hilbert vectors; no new
membership estimate, metric or norm instance is needed.

For existing radial points `z_i = canonicalCompletedC3RadialTiltPoint k i`,
set, only as notation,

\[
d_i=\frac{c_i r^{i+1}}
 {\operatorname{completedNativePositiveHermiteBiehlerCoordinate}(z_i)}.
\]

| Vector | Definition | Origin |
|---|---|---|
| `sourceValue = V` (unchanged) | `Σ_i d_i A(z_i) Z(z_i) u_i` | Full completed value trace |
| `nativeDressedCompanion = C_native` (new) | `Σ_i d_i A(z_i) C_Z(z_i) u_i` | Xi-weighted native companion from normalized, completed TFVD log/value trace |
| `completionCompanion = C_completion` (new) | `Σ_i d_i C_A(z_i) Z(z_i) u_i` | Existing completion derivative times the native completed value |
| `sourceCompanion = C` (unchanged) | `Σ_i d_i (-F'(z_i)) u_i` | Full completed companion |

Definitions use neither moments, target Grams, spectral heights nor correction
values to select amplitudes. The denominator is the existing chiral one,
not a newly chosen weight. `r` is the internal source-synthesis coordinate;
`k` is the shrinking radial grid index; neither is material time or C2 depth.

The new theorem proves the **vector** equality

\[
C=C_{\rm native}+C_{\rm completion}.
\]

`companion_channels_eq_bracketTfvd` identifies both separated vectors with
projections of the same already completed TFVD source for arbitrary cutoff M.
Their actual definitions are independent of M. This does not assert that
Cauchy trace synthesis contains every coordinate of that upstream state.

## Mixed Green transport, with all cross terms

Let `K_ij = inner ℂ u_i u_j`. Conjugate-linearity is in the first argument.
The new exact identity is

\[
\langle V,C_{\rm completion}\rangle
-\langle C_{\rm completion},V\rangle
=\sum_{i,j}\overline{d_i}d_j K_{ij}\,
 \operatorname{canonicalArchimedeanBoundaryGreenCorrection}(z_i,z_j).
\]

This is `completion_pairing_skew_eq_archimedean_sum`. The existing correction
is used literally, including its derivative signs and conjugations. In
particular the left side is not `‖C_completion‖²`.

The material term is likewise transported:

\[
\langle V,C_{\rm native}\rangle-\langle C_{\rm native},V\rangle
=\sum_{i,j}\overline{d_i}d_j K_{ij}\,
 \overline{A(z_i)}A(z_j)\mathcal G_Z(z_i,z_j).
\]

Their sum is the full product Green expression. Every ordered pair `(i,j)`
remains; no mixed terms are declared orthogonal or deleted. The two forms
are summed only after the same vector syntheses have been identified.

Consequently,

\[
4\Im\langle V,C\rangle
=4\Im\langle V,C_{\rm native}\rangle
 +4\Im\langle V,C_{\rm completion}\rangle.
\]

The new `storage_eventually_eq_native_add_completion` proves, for each N,
**eventually in k, for all c and all r**, that this sum equals `Re storage`.
The threshold comes from the existing finite-family regularity theorem,
not a new global hypothesis. The vector algebra does not need to assume that
the chiral denominators are nonzero; identification with storage uses the
existing eventual nonvanishing.

This is a signed Green-form crosswalk in the existing source carrier. It is
not a Green stencil norm defect or a positive Hilbert Gram representation.

## Canaries and what they establish

1. **Analytic center `z=0`:**
   `nativeArchimedeanCompanionChannels_zero_cancel` proves
   `A(0) C_Z(0) + C_A(0) Z(0) = 0`, from completed evenness.
   It does not assert that either factor derivative is individually nonzero.
2. **Green-form center:**
   `canonicalArchimedeanBoundaryGreenCorrection_zero_cancel` proves
   the archimedean correction is the negative of the weighted native Green
   form at `(0,0)`. The real centered division-free diagonal itself is
   vacuous (`0=0`), and is not a Hilbert norm calibration.
3. **One radial sample:** an audit example expands the completion skew
   pairing to its literal `(0,0)` summand.
4. **Two radial samples:** an audit example expands it into all four terms,
   `(0,0),(0,1),(1,0),(1,1)`, preserving both off-diagonal contributions.
5. **Arbitrary finite order:** the vector and skew-form identities hold for
   every N. Native/full product-rule identities require the existing strip
   membership; the shrinking grid supplies that eventually uniformly in c,r.

Center means spectral `z=0`, not `k=0` or an unshifted grid sample. These are
identity canaries, not positive-sign tests. No fitted numerical values were
used or numerical experiment run.

## Public declarations

- `CarrySelfAdjointOperator.canonicalC3BracketTfvdNormalizedTracePair_eq_native`
- `CarrySelfAdjointOperator.nativeArchimedeanCompanionChannels_zero_cancel`
- `CarrySelfAdjointOperator.canonicalArchimedeanBoundaryGreenCorrection_zero_cancel`
- `CarrySelfAdjointOperator.ChiralReturn.nativeDressedCompanion`
- `CarrySelfAdjointOperator.ChiralReturn.completionCompanion`
- `CarrySelfAdjointOperator.ChiralReturn.sourceValue_eq_native_product`
- `CarrySelfAdjointOperator.ChiralReturn.sourceCompanion_eq_native_add_completion`
- `CarrySelfAdjointOperator.ChiralReturn.companion_channels_eq_bracketTfvd`
- `CarrySelfAdjointOperator.ChiralReturn.completion_pairing_skew_eq_archimedean_sum`
- `CarrySelfAdjointOperator.ChiralReturn.native_pairing_skew_eq_weighted_green_sum`
- `CarrySelfAdjointOperator.ChiralReturn.source_pairing_skew_eq_product_green_sum`
- `CarrySelfAdjointOperator.ChiralReturn.completion_orientation_eq_archimedean_sum`
- `CarrySelfAdjointOperator.ChiralReturn.source_cross_eq_native_add_completion`
- `CarrySelfAdjointOperator.ChiralReturn.sourceCompanion_eventually_eq_native_add_completion`
- `CarrySelfAdjointOperator.ChiralReturn.storage_eventually_eq_native_add_completion`

There are thirteen theorems and two vector definitions. All fifteen public
declarations are registered in the root audit and theorem registry.

## Result of the division-free realization attempt

The existing Cauchy carrier now realizes each product-rule correction as a
**mixed/skew pairing**, with exact completed TFVD provenance. It does not
turn that orientation into a positive norm. A map obtained simply by placing
these channels in orthogonal slots has no proved equality to the division-free
Wronskian. Such a new candidate or assumption wrapper was not introduced.

The same single missing construction remains: a continuous source-derived
Hilbert state whose product realizes the full division-free Green identity.
The corresponding finite source sign can now be written explicitly as the
uniform nonnegativity of

\[
4\Im\langle V,C_{\rm native}\rangle
+4\Im\langle V,C_{\rm completion}\rangle.
\]

Neither summand is assumed nonnegative. No positive complementary vector,
all-order dominance bound, contractivity, Pick PSD or normalized positive
kernel was proved. The current source/normalization no-gos are preserved.

## Audits and publication

`CompletedNativeChiralReturnCompletionSplitAudit.lean` imports the existing
source dependency firewall. All fifteen roots have `#print axioms` and
allowed-footprint assertions. Their types and values have a combined closure
of **5299 declarations**; the firewall passed without HP, Stieltjes,
canonical target moments, Hankel, Jacobi/height, Herglotz or BR2 proof inputs.
Axioms are only `[propext, Classical.choice, Quot.sound]` or a subset.

Final validation before commit/push:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnCompletionSplit
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnCompletionSplitAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

Logs: `/tmp/chiral-completion-split-audit.log` and
`/tmp/chiral-completion-split-validation/` on llm. Publication occurs only
after these checks pass. All listed builds and audits passed, including
`static audit passed`, `kernel audit passed`, and `git diff --check`. The
new files passed placeholder/control scans and the registry parses as JSON.
No dependency source, Foundation, canonical metric
or archive file in `~/momentos` was modified. README and the append-only
checkpoint record only this signed vector-form result. Final commit and
HEAD/main/origin/GitHub agreement are recorded in the delivery.
