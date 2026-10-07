# Existing Pythagorean splits versus the completed chiral return

## Result

**PASS_COMPLETED_SOURCE_COISOMETRIC_DEFECT_LOCALIZATION**.
**PARTIAL_PYTHAGOREAN_RETURN_CHANNEL_IDENTIFICATION**.

Initial published main: `00aea824c29fe5da8d8ff020a68600963d933742`.
`git pull --ff-only` reported already up to date; HEAD/main/origin agreed and
the initial tree was clean. No experimental branch or archive modification.

The existing coisometric camera construction supplies a concrete positive
Gram candidate, but it is not identified with the completed chiral balance.
The exact discrepancy is now the synthesis of four **already defined**
geometric channels. The current Naimark escape contributes zero to this
boundary readout and is not automatically that discrepancy. No positivity,
contractivity, strictness or division-free Hilbert witness is claimed.

## Directed inventory: four Pythagorean families

| Family / verified declarations | Exact scope | Relation to this gate |
|---|---|---|
| `canonicalCompletedC3AmbientPortEscape_pythagoras` | Realified Naimark carrier; orthogonal port and retained escape; real-linear readout and left inverse | Supplies a conservative split, but does not identify the current chiral return as its port |
| `canonicalCompletedC3FullWronskianPolarization_norm_sq`, `inner_canonicalCompletedC3FullWronskianOperator_eq_polarizationDifference` | Complex full completed Wronskian carrier; orthogonal positive/negative chiralities; signed Wronskian difference | Already reaches the completed numerator; `canonicalCompletedC3FullWronskianChiralDifference_eq_separation_mul_dslope` keeps the spectral separation |
| `canonicalPrimosPrimeCarryProvenance_polarized_pythagoras_of_realizesOn`, `canonicalPrimosSeededTfvdBessel_polarized_pythagoras_of_realizesOn` | Real prime-carry provenance Hilbert carrier; x,y realize the SAME fixed finite readouts and common active P | Not an arbitrary complex c,d source-family kernel; no supplied realization map identifies its active readout with the chiral return |
| `canonicalC3FiniteMixedHeightStructuralChannelState_norm_sq` | Complex orthogonal direct sum of provenance/off-diagonal/readout-residual coordinates | Positive no-cancellation energy, not equality of that norm with the signed chiral orientation |

`CompletedC3CoisometricChiralEnergyBlock` and
`CompletedC3CoisometricCameraChiralTransformation` already combine the
coisometric response with negative full-Wronskian chirality in one enriched
source presentation. They retain the energy discrepancy; they do not prove
that the enlarged block is the positive chirality or remove its correction.
No second enriched carrier is constructed here.

## Full source synthesis first

The unchanged source vectors are in
`CanonicalCompletedNativeChiralCauchyCarrier = Lp ℂ 2 volume` on the unit
interval. The old completed TFVD source keeps transport, value/log-jet tails,
chart and archimedean completion before its trace is read. This round uses
that existing completed trace/Wronskian identity at every cutoff M and does
not reconstruct an upstream state from scalar traces.

Write the unchanged source balance as

\[
Q(c,d)=\langle C_c+iV_c,C_d+iV_d\rangle
       -\langle C_c-iV_c,C_d-iV_d\rangle.
\]

The existing scalar source normalization is

\[
z_i=\operatorname{canonicalCompletedC3RadialTiltPoint}(k,i),\quad
 a_i=\frac{c_i r^{i+1}}{H_+(z_i)},\quad
 b_j=\frac{d_j s^{j+1}}{H_+(z_j)}.
\]

M is the TFVD cutoff, k the radial grid index, and r,s internal synthesis
coordinates; none is identified with material time, positional depth or
operator height. Both complete syntheses occur before this pairing. The source-preserving
comparison uses independent c,d and independent internal r,s. No moment,
target Gram, eigenvalue or adjusted metric defines any vector or coefficient.

## Concrete coisometric candidate and exact cancellation

The existing complex camera view has carrier `CarryGammaComplexCamera`.
It is the type-only complex Hilbert presentation of the realified camera;
no coordinate or metric is changed. The old boundary theorem already proves

\[
B_{\rm coiso}(z_i,z_j)=(z_j-\overline{z_i})
\langle\Gamma_i,\Gamma_j\rangle,
\]

where
`Γ_i = canonicalCompletedC3GammaCameraView
(completedC3SymplecticCameraState (operatorHeightParameter z_i) hhalf_i)`.
Thus the required full complex quadratures are provided by the existing
complex view, not inferred from real norm conservation alone.

The old grid and old Cauchy scale give **exactly**

\[
K_{ij}(z_j-\overline{z_i})=i,
\qquad K_{ij}=\langle u_i,u_j\rangle.
\]

`radialCauchy_inner_mul_separation` reuses
`canonicalCompletedC3RadialTilt_I_div_separation` and the old Cauchy inner
formula. No new grid, scale, p-series or numerical approximation is used.

The new `coisometricSourceSynthesis` is the actual vector

\[
A_c=\sum_i a_i\Gamma_i
\quad\in\quad\texttt{CarryGammaComplexCamera}.
\]

It is a finite synthesis of completed geometric camera states, formed before
its inner product. It is not declared a lossless embedding of the whole
completed source or the sought complementary vector. Its ordinary response
does not silently acquire the independent completion/log-jet corrections.

## Existing four-channel defect: no fitted correction

Use literally
`canonicalCompletedC3CoisometricWronskianFourChannelDefect` from
`CompletedC3CoisometricWronskianProjectionGate`. Its four components are:

1. raw Gamma/Wronskian boundary defect;
2. port-resolved boundary correction;
3. leak-resolved boundary correction;
4. port-source boundary correction.

Its old theorem states

\[
D_{ij}=B_{\rm coiso}(z_i,z_j)-W_F(z_j,z_i).
\]

The new `coisometricFourChannelBalance` is defined by synthesizing those
existing channels with the original source weights:

\[
E(c,d)=\sum_{i,j}\overline{a_i}b_j K_{ij}D_{ij}.
\]

It is **not** defined as target minus a newly selected Gram or as a norm.
The full completed Wronskian remains the same one realized by the earlier
corrected Green/TFVD ledger. No nominal identification of the four channels
with that ledger's five corrections is required or asserted.

The new kernel-checked comparison is

\[
\boxed{Q(c,d)=2\langle A_c,A_d\rangle+2i E(c,d).}
\]

The coefficient 2 follows from the old source factor -2i and the exact
Cauchy/separation cancellation. It is not chosen to calibrate a moment.
In particular,

\[
\boxed{\Re S_k(c,r)=2\|A_c\|^2-2\Im E(c,c).}
\]

All ordered i,j terms remain. The one-sample canary retains its actual
correction; the two-sample canary has all four independent terms 00,01,10,11.
`coisometricSource_comparison_eventually` supplies half-plane admissibility
from the old shrinking-grid regularity, uniformly in all c,d,r,s for each N.
The Wronskian identity itself holds at every cutoff M.

## Why the old escape does not complete this comparison

The existing theorem
`canonicalCompletedC3CoisometricAmbientLeakBoundaryReadout_eq_zero` states
that the retained induced-source escape is orthogonal to this particular
response/source boundary readout. The new
`coisometricEscapeBoundarySynthesis_eq_zero` proves the complete weighted
sum is still zero, with independent c,d and every ordered cross term.

The leak-resolved correction inside the four-channel defect is a different
readout from `canonicalCompletedC3CoisometricAmbientLeakBoundaryReadout`. Its
vanishing is not inferred by similarity of names; it remains in E.

A second exact test, `coisometricResponse_escape_eq_zero`, shows that the
completed **response** is already in the promoted camera range and its
escape itself vanishes. This must not be confused with the **induced source**:
its leak can be nonzero, as the existing witness theorem records. No leak
vector has been erased or declared globally irrelevant.

Consequently merely appending that existing escape contribution to the
coisometric boundary readout does not change E. This is a local diagnostic,
not a proof that no other geometric complementary channel can exist.

## Single remaining candidate-specific sewing obligation

For this concrete camera candidate, the new exact theorem proves

```lean
polarizedSourceBalance k c d r s =
  2 * inner ℂ (coisometricSourceSynthesis k c r hhalf)
    (coisometricSourceSynthesis k d s hhalf)
↔ coisometricFourChannelBalance k c d r s hhalf = 0
```

The remaining equality test for this candidate is the all-coefficient,
eventual-in-k vanishing of E at r=s=1. It has **not** been supplied or assumed.
It is stronger than a bare sign assertion and is not claimed equivalent to
all possible ways to prove storage positivity. The existing Gamma/concrete
positive-state no-gos are respected; no normalization is changed to force
this candidate through them. A failure of that equality would reject only
this camera candidate, not all geometric Pythagorean realizations.

For the broader Pythagorean mission, any successful return/complement
identification must account for this explicit correction rather than hide it
in the old escape. No new assumption wrapper, positivity certificate,
source-defined sqrt or fitted matrix is introduced.

## Public declarations and trust footprint

The ten roots in `CarrySelfAdjointOperator.ChiralReturn` are:

- `radialCauchy_inner_mul_separation`;
- `coisometricSourceSynthesis`;
- `coisometricFourChannelBalance`;
- `radialBracketWronskian_eq_coisometricGram_sub_defect`;
- `polarizedSourceBalance_eq_coisometricGram_add_fourChannelBalance`;
- `polarizedSourceBalance_eq_coisometricGram_iff_fourChannelBalance_zero`;
- `coisometricEscapeBoundarySynthesis_eq_zero`;
- `storage_re_eq_coisometricEnergy_sub_fourChannelBalance`;
- `coisometricSource_comparison_eventually`;
- `coisometricResponse_escape_eq_zero`.

Two definitions and eight theorems; no new carrier, metric or canonical
operator. The dedicated audit prints/asserts the permitted foundational
footprint and rejects downstream positive certificates, canonical moments,
Hankel, Stieltjes, Jacobi/height, Herglotz and BR2 proof dependencies.
The dedicated audit passed for **6713 reachable declarations**, with only
`[propext, Classical.choice, Quot.sound]`. The one-/two-sample canaries also
passed; the complete final validation result is recorded below.

## Validation and publication

All listed builds, static/kernel audits, placeholder/control scans and
`git diff --check` passed before publication. The final SHA and
HEAD/main/origin/GitHub agreement are recorded in the delivery. Logs are retained on llm under
`/tmp/chiral-coisometric-audit.log` and
`/tmp/chiral-coisometric-validation/`.

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnCoisometricSewing
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnCoisometricSewingAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

No dependency source, Foundation, canonical metric, or file in ~/momentos was
modified. Main remains the normative checkpoint.
