# Source-first chiral return storage audit

## Main checkpoint

Initial main: `e6d82dc0bf70db0b3c080e09f4015a1d3404507b`.
`git pull --ff-only` was up to date; HEAD/main/origin/main/GitHub agreed and
working tree was clean. Only canonical main is used.

STATUS: `PARTIAL_SOURCE_FIRST_CHIRAL_RETURN_STORAGE_POSITIVITY`.

The new kernel result is a complete-source **identity**, not nonnegativity.
No all-order sign theorem or counterexample to actual storage is claimed.

## Inventory of candidate energies

| Existing declaration / object | Type or identity | Layer / signal | Moment or HP input? | Cross terms |
|---|---|---|---|---|
| `ChiralReturn.storage_re_eq_norm_balance` | Re storage = incident norm² − returned norm² in the Cauchy L² carrier | Exact source-defined balance, no sign | No moment/HP input to the identity | All preserved |
| `hasDerivAt_storage`, `integral_flux_eq_storage` | Signed flux derivative and accumulated integral | Exact source identities, no sign | No moment/HP input to these identities | All preserved |
| `degree_mul_defect_entry` | Cauchy denominator cancels degree weight, leaving `1−conj(q_i)q_j` | Source coefficient identity, no signal bound | No moment/HP premise | All preserved |
| `completedNativeNormalizedChiralTraceTotalEnergy_eq`, `_ge_half` | Total diagonal energy = 1/2 + normalized derivative norm² | Positive **sum**, not chiral difference | Source F/derivative, no HP premise | A single point; no uniform finite-family sign |
| `completedNativeChiralTraceDifference_eq_defectGram_of_quotient_contraction` | Difference equals norm of `sqrt(1−norm(q)²) • P+` | Conditional diagonal factorization | Assumes `norm(q) ≤ 1`; unusable as an independent sign proof | Does not supply the all-family storage cross terms |
| `canonicalCompletedC3FullWronskianCentralState_chiralEnergies_eq`, `_pos` | Equal positive central chiral energies; each half the total | Upstream geometric norms, difference zero at center | No HP premise; central comparison only | Central vector; not arbitrary radial syntheses |
| `canonicalCompletedNativePolarizedDslopeKernel_eq_chiralDifference_div` | Separation-regularized signed full-Wronskian difference | Source kernel equality, no sign | No positivity/HP premise | Both parameters retained |
| `canonicalCentralInfiniteGreenBulkFirstVariation_eq_atlasChannelSum` | Positive carry/TFVD Green-bulk norm channels | Genuine positive geometry | Independent bulk energy | Its own channels retained |
| `deriv_completedNativeCentralChiralEnergyDifference_zero_eq_greenBulk_iff` | Matching the two slopes requires `h0 = log(3) * reflectedGreenEnergy` | Comparison gate, not supplied equality | References h0 in comparison; not used in new proof | Does not give uniform radial storage dominance |
| `canonicalNativeGreenFrameReturnMetric_isometry`, `_ReturnKernel_eq_state_inner` | Endpoint + Poisson return is the original Green-state Gram | Concrete positive return geometry | No HP premise in isometry | Endpoint, bulk and cross terms retained |
| `canonicalNativeReturnMetricCentralDefect_pos` | Literal return graph has a positive central discrepancy from the native zeroth moment | Existing diagnostic excludes simply substituting that graph kernel | Uses moment comparison; not used in new proof | No required Cauchy-multiplier defect identity supplied |
| Ambient/Gamma correction ledgers | Positive raw ambient Gram plus exact signed correction | Positive ambient object, **unknown correction sign** | Regularized native comparison invokes h0; not used in new proof | Complete ledger retains corrections; not zero by construction |
| `canonicalCompletedNativeChiralTwoPoint_contractive_eventually` | Two-point finite synthesis estimate | Existing low-order diagnostic | Certified low-order theta/moment bounds; not used in new proof | Both off-diagonal terms included |
| Cayley/Herglotz equivalences | Pick ↔ Herglotz ↔ multiplier ↔ dslope | Existing equivalences, not a positive Gram source | No all-order sign furnished | Full finite matrices |
| `CompletedNativeSignedGeneratorHerglotzGram` | Positive resolvent Gram from signed height generator | **Downstream / forbidden here** | `CompletedNativeRealHPCarrierCertificate` | Not used |

The relevant native source is the completed TFVD value/companion trace.
Prime-depth/material log slope, exact head/tails, chart and archimedean
completion produce that trace upstream. The multiplication/Cayley identities
transport its readout; they do not assert nonnegative orientation of every
finite combination. No independent all-order positive return decomposition
was located in the audited upstream declarations.

## Audit of the multiplier as an operator

The existing state family is literally `w_i = q_i • v_i`, with
`v_i = completedNativeRadialChiralCauchyState k i` and
`q_i = completedNativeHermiteBiehlerChiralQuotient z_i`.

There is an existing **parameter-dependent** projective graph transform at
one point `z`. It is linear in its Cauchy input and uses that single `q(z)`.
It does not provide one operator whose action on all samples is `q_i v_i`.
A diagonal map on a chosen coefficient ledger is not automatically bounded
or contractive in the Cauchy synthesis norm: those vectors are not orthogonal.
No interpolation of q_i, functional calculus, new global operator, or fitted
unitary dilation is constructed here.

The Green frame has a genuine endpoint/Poisson Parseval return and positive
return metric. Its domain and readout are different from this chiral Cauchy
synthesis. No existing equality supplies a complementary `D(k,c)` satisfying
`norm(incident)² = norm(returned)² + norm(D)²` for this storage. The known
central discrepancy also prevents simply calling its positive kernel the
native signed kernel. This does **not** refute a future proved transport.

## New geometric source vectors

For `z_i = canonicalCompletedC3RadialTiltPoint k i`, set

\[
 F_i=F(z_i),\quad C_i=-F'(z_i),\quad P_i=C_i+iF_i,
 \quad a_i=c_i r^{i+1}.
\]

Here F is the **existing completed source characteristic**. Define in the
unchanged `CanonicalCompletedNativeChiralCauchyCarrier`:

\[
 V_{k,c,r}=\sum_i \frac{a_iF_i}{P_i}v_i,
 \qquad C_{k,c,r}=\sum_i \frac{a_iC_i}{P_i}v_i.
\]

Exact declarations:

```lean
ChiralReturn.sourceValue     (k : ℕ) (c : Fin N → ℂ) (r : ℝ)
ChiralReturn.sourceCompanion (k : ℕ) (c : Fin N → ℂ) (r : ℝ)
```

Both are finite L² vectors, linear in the coefficients. Division by P_i is
forced by undoing the existing chiral quotient, not a new metric or a weight
chosen to fit moments. The constructions mention no moments, sign certificate
or target Gram.

`source_pair_eq_bracketTfvd` identifies both syntheses, at **every** cutoff M,
with the exact `canonicalC3BracketTfvdCompletedTracePair M` readouts. These
are the already synthesized head-plus-exact-tail traces with their existing
chart/completion. This is a trace projection after complete source synthesis,
not a claimed lossless embedding of every Green-port coordinate.

The internal r is the Cauchy storage radius. It is neither height nor the
material logarithmic clock.

## What the kernel closed

With only `P_i ≠ 0`,

\[
 A_{k,c,r}=\sum_i a_i v_i=C_{k,c,r}+iV_{k,c,r},
 \quad
 B_{k,c,r}=\sum_i a_i w_i=C_{k,c,r}-iV_{k,c,r}.
\]

The theorems `incident_synthesis_eq_source` and
`returned_synthesis_eq_source` preserve the same c_i and **all cross terms**.
The existing completed chiral fields supply both orientations.

`source_total_energy` proves:

\[
 \|A\|^2+\|B\|^2=2(\|C\|^2+\|V\|^2).
\]

This is the total chiral energy identity. It is not the inequality
`norm(B) ≤ norm(A)` and supplies no independent nonnegative defect vector.

With Mathlib's conjugate-linear-first convention,
`norm_chiral_balance_eq_source_cross` and `storage_re_eq_source_cross` give

\[
 \boxed{\Re S_k(c,r)=4\Im\langle V_{k,c,r},C_{k,c,r}\rangle.}
\]

`integral_flux_re_eq_source_cross` identifies the same mixed orientation
with the **accumulated** flux. No local integrand sign is asserted.

`storage_eventually_eq_source_cross` discharges P_i nonvanishing from the
existing radial regularity germ, uniformly over every c and r on each finite
family. Endpoint capstone:

```lean
ChiralReturn.storage_one_eventually_eq_source_cross (N : ℕ) :
  ∀ᶠ k : ℕ in atTop, ∀ c : Fin N → ℂ,
    (ChiralReturn.storage k c 1).re =
      4 * (inner ℂ (ChiralReturn.sourceValue k c 1)
                    (ChiralReturn.sourceCompanion k c 1)).im
```

## Single remaining obligation

Literally:

```lean
∀ N : ℕ, ∀ᶠ k : ℕ in Filter.atTop, ∀ c : Fin N → ℂ,
  0 ≤ (inner ℂ (ChiralReturn.sourceValue k c 1)
               (ChiralReturn.sourceCompanion k c 1)).im
```

The eventual threshold for each N must work simultaneously for **all** c.
A limit or sign estimate for each fixed c, with a c-dependent threshold, does
not establish this quantifier order.

The constant four is positive, so this is the exact sign of the already
existing accumulated-storage gate, now exposed before chiral compression in
complete source vectors. **It is still unproved.** No new assumption wrapper
is introduced, and this restatement is not used to claim contractivity.
The audit did not find a uniform positive factorization or a concrete
negative witness for the actual source, so neither PASS positivity nor a
no-go for the canonical storage is declared.

N=1 and N=2 obey the same source identity. Their known signs come from
separate low-order curvature/theta bounds, including the two-point cross
margin. They do not yield an all-order source complement or a justified
induction. No uniform pattern was found to justify a new N=3 construction.
The existing example with accumulated nonnegative storage and negative local
endpoint flux remains intact and is not reproved.

All-order contractivity and its Pick/Herglotz/dslope PSD corollaries are not
closed by this round. Strictness remains a later independent step. BR2 is not
used. Norm positivity of each source vector and positivity of their **sum**
do not establish the required imaginary mixed-pairing sign.

## Trust and publication

All new public declarations are registered and printed in the focused audit.
A transitive type/body audit prohibits HP/Stieltjes certificates, canonical
moment/sign dependencies, any Hankel/Jacobi/height-operator declaration and
BR2. Importing a module containing downstream theorems is not counted as using
them: the check follows actual declaration dependencies.

Commands:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnSourceTrace
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnSourceTraceAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

Validation completed:

- New source module: `--wfail` passed (9,190 jobs).
- Focused audit: `--wfail` passed (9,282 jobs).
- Root and central audit: `--wfail` passed (9,711 jobs).
- `scripts/static_audit.sh`: `static audit passed`.
- `scripts/audit.sh`, including existing BR2/Order/recovered-C2 audits:
  `kernel audit passed`.
- All new capstones print only `[propext, Classical.choice, Quot.sound]`.
- Source dependency closure: 5,312 declarations checked without forbidden
  moment, positive certificate or operator inputs.
- Placeholder/trust-escape scan and `git diff --check`: passed.

Publication is a single main commit titled
`feat: expose complete-source chiral return balance`.
This records the source identity and explicit sign frontier, not a positivity
theorem. The exact hash is recorded in Git history and delivery.
