# Complete-source polarized Green / Pythagorean audit

## Status and scope

**PASS_COMPLETED_SOURCE_POLARIZED_GREEN_BALANCE**.

**PARTIAL_POLARIZED_GREEN_PYTHAGOREAN_SEWING**.

Initial `main`, `HEAD`, `origin/main`:
`96c1d10a332cfc8c5d01e565cb00b2b837b2b9ef`.
`git pull --ff-only` reported already up to date; initial tree was clean.
The user authorized main publication after complete formal validation.

The request is to test a geometric polarized Pythagorean identity, not to
obtain sign by assuming a positive downstream certificate. The successful
result is the exact **signed** polarized Green balance. No orthogonal
complement, positivity, contractivity, division-free Hilbert representation,
PSD or strictness is claimed. The absence of a witness in the audited maps
is not a mathematical impossibility theorem.

## Complete synthesis before scalar contraction

All new definitions use the unchanged completed `ChiralReturn.sourceValue`
and `sourceCompanion`, in

```lean
CanonicalCompletedNativeChiralCauchyCarrier :=
  Lp ℂ 2 (volume : Measure unitInterval)
```

Let `V_c = sourceValue k c r` and `C_c = sourceCompanion k c r`, and likewise
`V_d,C_d` at the independent internal coordinate `s`. These are the existing
finite Cauchy syntheses of the completed value and companion `-F'`.
The upstream completion state retains TFVD transport and both exact tails;
its completed trace is read only after that synthesis. This round neither
inverts that trace projection nor claims it determines the entire Green port.

`source_pair_eq_bracketTfvd` and the completed Wronskian readout identify the
same traces at **every cutoff M**. No bracket-only scalarization replaces
them. The existing geometric completion, chart and source denominators are
unchanged. No target moments select a vector or a coefficient.

The new definition is made **after both complete vector syntheses**:

\[
I_c=C_c+iV_c,\qquad R_c=C_c-iV_c,
\]
\[
Q(c,d)=\langle I_c,I_d\rangle-\langle R_c,R_d\rangle.
\]

With the conjugate-linear-first Mathlib convention, the exact identity is

\[
Q(c,d)=-2i\bigl(\langle V_c,C_d\rangle-
                         \langle C_c,V_d\rangle\bigr)
       =2i\,\operatorname{greenForm}((V_c,C_c),(V_d,C_d)).
\]

The existing `greenForm` uses `inner C_c V_d - inner V_c C_d`, so the last
factor is **+2i**, not -2i. The sign has been kernel checked. The diagonal is

\[
Q(c,c)=\operatorname{Re} S_k(c,r)
      =4\Im\langle V_c,C_c\rangle.
\]

`Q` is Hermitian. The conservative sum also polarizes exactly:

\[
\langle I_c,I_d\rangle+\langle R_c,R_d\rangle
=2\bigl(\langle C_c,C_d\rangle+\langle V_c,V_d\rangle\bigr).
\]

This sum identity does not order the two energies.

## Exact all-order Green ledger, including cross terms

For the existing shifted radial points `z_i`, write

\[
a_i=\frac{c_i r^{i+1}}{H_+(z_i)},\qquad
b_j=\frac{d_j s^{j+1}}{H_+(z_j)},\qquad
K_{ij}=\langle u_i,u_j\rangle.
\]

For every finite N and every cutoff M, on the existing genuine strip,

\[
Q(c,d)=-2i\sum_{i,j}\overline{a_i}b_j K_{ij}
 \operatorname{canonicalC3BracketTfvdCompletedWronskianReadout}
 (M,z_j,z_i).
\]

The right point occurs first in the Wronskian. The exact existing ledger
substitutes for each Wronskian; none of its components are dropped:

- radial Green term with its Xi weight;
- Green provenance;
- off-diagonal channel;
- readout residual;
- tail completion;
- archimedean/chart completion;
- original chart denominator.

This is `polarizedSourceBalance_eq_corrected_green_ledger`. No positivity of
individual terms, diagonal projection, temporal averaging or synthetic
orthogonality is used. The one-sample audit checks its literal Wronskian
specialization. The two-sample audit has independent c,d and expands all
four ordered terms `00,01,10,11`.

`polarizedSourceBalance_eventually_complete` uses the old finite-family
regularity theorem. For each N, one eventual threshold in k works for
**all M, all c,d and all r,s**. It gives both the unchanged storage diagonal
and the full polarized Wronskian sum. This is not a new global regularity
assumption. k, M, material time, depth, height and r/s remain distinct.

## Native / completion channels are not orthogonal slots

The old product-rule vector identity is used on both sides:

\[
C_c=C_{{\rm native},c}+C_{{\rm completion},c}.
\]

The new theorem `polarizedSourceBalance_eq_native_add_completion` separates
Q into the two actual mixed orientations. Each term still uses the full V
and both coefficient families. Neither is replaced by its squared norm.
In particular, the completion companion is not identified as the sought
Pythagorean defect vector. No new orthogonality is asserted.

## Directed audit of geometric complements

| Existing construction | Conservation / form actually supplied | First unmatched property |
|---|---|---|
| `CarrySelfAdjointOperator.C2GreenPreStencilCanary.preStencilLinearIsometry omega` | Complex isometry from material `State` to `WithLp 2 (SeedResidualSpace × ℓ²(GreenEvent,ℂ))`; seed/return plus direct Green norm split | No map from the current Cauchy source identifies its actual chiral return as either component |
| `CarrySelfAdjointOperator.ReturnMetric.polarizedCovariance_eq_direct` / `_eq_factorization` | Finite endpoint/bulk cancellation, under the explicit endpoint/Poisson compatibility and conservation equations | No specialization identifies those probes with the full completed chiral value/companion family |
| `finiteC3SymplecticNaimarkRealization` / `_complexReadout_eq_greenForm` | Preserves the mixed symplectic Green readout, including reflected and quarter-turned legs | Symplectic form preservation is not a positive complementary norm identity |
| `CanonicalCompletedC3AllCutoffOnePointHilbert` | Existing Hilbert packaging retaining direct/reflected/quarter-turned ports, four head/tail coordinates, and a mixed readout | Its standard norm is not identified with the current incident-minus-return balance |
| Bounded oriented Green synthesis / weighted TFVD reconstruction | Recovers original vertical states and both boundary coordinates | Algebraic reconstruction does not identify return as an orthogonal energy component |

These constructions were inspected as geometric candidates; no old C2
positivity, artificial resolvent, Gram-fitted transport or normalization is
imported into a new sign proof. The new proof roots use the completed-source
Wronskian chain only. The old literal C3 candidate and one-center no-gos
remain intact.

A new general theorem, `chiral_pairing_balance_isometry`, verifies that a
**common complex linear isometry** applied to the already complete vectors
preserves Q unchanged. It does not refute a correctly identified geometric
return/complement split. It shows precisely why isometric repackaging alone
is not that identification.

## Single remaining typed obligation

For each finite N, find a Hilbert carrier H and a **source-derived** linear
channel (notation only; no declaration or assumption wrapper is added)

```lean
D_k : (Fin N → ℂ) →ₗ[ℂ] H
```

whose existing geometric provenance proves, eventually in k,

```lean
∀ c d : Fin N → ℂ,
  ChiralReturn.polarizedSourceBalance k c d 1 1 =
    inner ℂ (D_k c) (D_k d)
```

This is the exact polarized Pythagorean sewing obligation. D must come from
actual complete boundary/return/complement channels, not from square roots
of storage, a target matrix factorization, moments or a chosen metric.
An identified conservative colligation whose first component is the actual
return would be one way to supply it, but none is postulated here.

Its diagonal would give `Re storage = ‖D_k c‖²`. Until that geometric channel
and equality are constructed, neither storage positivity nor the global
continuous division-free Hilbert witness is closed. This round makes the
all-cross-term equality available for that test without circular sign input.

## Public declarations

All declarations are in `CarrySelfAdjointOperator.ChiralReturn`:

- `chiral_pairing_balance`;
- `chiral_pairing_total`;
- `polarizedSourceBalance`;
- `polarizedSourceBalance_eq_greenForm`;
- `polarizedSourceBalance_self_eq_storage`;
- `polarizedSourceBalance_conj_symm`;
- `chiral_pairing_balance_isometry`;
- `polarized_mixed_synthesis_eq_wronskian_sum`;
- `polarizedSourceBalance_eq_bracketTfvd_sum`;
- `polarizedSourceBalance_eq_corrected_green_ledger`;
- `polarizedSourceBalance_eq_native_add_completion`;
- `polarizedSourceBalance_eventually_complete`.

One scalar form definition and eleven theorems; no new vector carrier,
metric, canonical state, assumption wrapper or dependency source change.
All twelve roots are registered and have dedicated footprint assertions,
`#print axioms` and the source dependency firewall. The firewall checked
**6183 reachable declarations**, rejecting positive downstream certificates,
canonical target moments, Hankel, Stieltjes, Jacobi/height, Herglotz and BR2
proof dependencies. The footprint is only
`[propext, Classical.choice, Quot.sound]`.

## Validation / publication

The dedicated module and audit builds passed with `--wfail`, including the
one/two-sample identity canaries. The full root build, root audit, static audit, repository kernel audit,
placeholder/control scan and diff whitespace check also passed:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnPolarizedGreen
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnPolarizedGreenAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

Logs on llm: `/tmp/chiral-polarized-build.log`,
`/tmp/chiral-polarized-audit.log`, `/tmp/chiral-polarized-validation/`.
All listed checks passed. Final main/origin/GitHub agreement and the publication
SHA are recorded in the delivery. No dependency source or archive file was
modified; Foundation and canonical metrics are unchanged.
