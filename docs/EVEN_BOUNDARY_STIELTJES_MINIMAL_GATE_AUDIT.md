# Minimal raw even-boundary gate for the existing height construction

## Checkpoint and exact status

Initial published main: `3b6243691e5da87be25e5909b1ebfa33aa4217fa`.
`git pull --ff-only`: already up to date; HEAD, main, origin/main agreed.
The only initial untracked files were `C2OddTfvdTransport.lean` and
`C2OddTfvdTransportAudit.lean`. They remain untouched and are not staged.

Kernel-checked in this round:

- `PASS_EVEN_BOUNDARY_STIELTJES_EQUIVALENCE`;
- exact **conditional** handoff to the existing height capstone.

Still open: `OPEN_EVEN_BOUNDARY_STRICT_SIGN_ALL_ORDER`.
No unconditional height/positivity result is claimed. No N=8 certificate is
built. The source, carriers, metrics, TFVD synthesis, Jacobi construction,
whitening, and self-adjointness infrastructure are not redefined.

## 1. Original source, factor and full limiting face

The already-proved completed source is `Q = -F'/F`, with existing companion
`C = -F'`. Its raw coefficients are

\[
c_j=\frac{\Re(\partial^{2j+1}Q(0))}{(2j+1)!}
    =2g_j,
\qquad g_j=\operatorname{primeDepthGeometricMoment}(j).
\]

The equality is the existing
`nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment`.
Its proof uses the completed normalized response `C/(2F)` and does not use
canonical recursive moments. `nativeSourceOddGreenTower_eq_primeDepth` already
identifies the entire tower with all ordered crosses.

The new `nativeSourceFiniteBoundaryEnergy N x` merely names the raw expression
from that tower, on zero-extended **limiting boundary** coordinates:

\[
b_a=\begin{cases}x_a&a<N,\\0&a\ge N,\end{cases}
\qquad
E_N(x)=2\sum_{j<N}(-1)^jc_j
       \sum_{a\le2j}(-1)^a\Re(\overline{b_a}b_{2j-a}).
\]

This is exactly the expression already audited in
`CHIRAL_STORAGE_ALL_ORDER_REVERSE_SOURCE_AUDIT.md`. It agrees with the right
side of the existing `nativeSourceSevenBoundaryEnergy_eq_alternating_green`
when `N=7`, by unfolding the two identical zero extensions. No new proof of
that seven-coordinate sign or storage certificate is performed.

The double finite sum is reindexed by the arithmetic bijection
`(j,a) -> (a,2j-a)`. Terms outside the original support vanish. The theorem
`nativeSourceFiniteBoundaryEnergy_eq_coefficient_sum` retains **every** ordered
source cross, with coefficient

\[
\mathbf1_{a+b\text{ even}}
  2(-1)^{(a+b)/2+a}c_{(a+b)/2}.
\]

Consequently, for `N=2n`:

\[
y_i=(-1)^ix_{2i},\quad z_i=(-1)^ix_{2i+1},\qquad
E_{2n}(x)=4\left[
 \sum_{i,j<n}g_{i+j}\Re(\overline{y_i}y_j)+
 \sum_{i,j<n}g_{i+j+1}\Re(\overline{z_i}z_j)\right].
\]

This is `nativeSourceFiniteBoundaryEnergy_even_split`. The factor four is the
raw outer factor two times `c_j=2g_j`. In the odd block the additional two
sign powers cancel. The forced phases are real unit signs, not selected
weights. The inverse signed interleaving is explicit; the two phases cannot
both vanish for a nonzero source input.

## 2. Exact equivalence, including complex inputs and the empty section

`nativeSourceEvenBoundary_positive_iff_stieltjes` proves:

```lean
(∀ n : ℕ, 1 ≤ n → ∀ x : Fin (2*n) → ℂ, x ≠ 0 →
  0 < nativeSourceFiniteBoundaryEnergy (2*n) x) ↔
  CanonicalCompletedNativeStieltjesPositivity
```

There is no coercivity premise, numerical margin, radial parameter or
uniform-in-dimension threshold in this equivalence.

For a real symmetric matrix M, the ordinary complex quadratic expression
used here is exactly the sum of its real and imaginary quadratic expressions:

\[
\sum_{i,j}M_{ij}\Re(\overline{u_i}u_j)
=(\Re u)^TM(\Re u)+(\Im u)^TM(\Im u).
\]

Local algebraic lemmas establish this identity; existing Mathlib
`Matrix.PosDef.dotProduct_mulVec_pos` and the corresponding PSD nonnegative
lemma do the sign algebra. Conversely, even-only and odd-only inputs produced
by the inverse interleaving test each **same-source** real block. Their
Hermitian symmetry is supplied by existing `hankelGram_isSymm` and
`shiftedHankel_isSymm`. The N=0 section in the Stieltjes predicate is handled
vacuously; it introduces no extra sign obligation.

Only at the final target identification is
`primeDepthGeometricMoment_eq_canonical` used. The raw energy, its phase maps
and the whole parity split do not depend on canonical moments or downstream
positivity. This is an equivalence, not an assumed positivity certificate
renamed as a theorem.

## 3. Route A versus route B

**Choose A in the current formal library.** The exact source inequality and
standard quadratic positivity API already give the gate above.

Route B (positive determinants of BOTH towers at every positive size) is
mathematically equivalent by Sylvester: the leading principal minors of a
Hankel/shifted-Hankel prefix are the smaller prefixes of the same tower.
The existing `hankelGram_succ_principal` and shifted principal-section lemma
record that indexing. This round does not claim a new formal Sylvester
criterion or formal determinant-only all-order equivalence.

The directly available `Matrix.PosSemidef.posDef_iff_det_ne_zero` cannot be
used to supply an upstream strict sign: it requires PSD **first**. Existing
`Matrix.PosDef.det_pos` gives route-B determinants after the raw route-A sign,
not before it. No all-order determinant lower bound was found. Thus adding
a general Sylvester development would not discharge the source inequality;
it would only add algebraic infrastructure to a gate already spelled out.

## 4. Reused results, concrete correspondences, genuine sign

| Existing result | Reusable conclusion | Remaining input / limit |
|---|---|---|
| `ChiralReturn.radialEulerPower_green_boundary` | Exact original-Cauchy polarized boundary identity at every degree | Alternating form is signed; the identity alone gives no strict sign |
| `ChiralReturn.storage_one_eq_odd_green_tower_and_remainder` | Full synthesized storage = tower + exact analytic vector remainder | Finite-step crosses and remainder remain |
| `primeDepthGeometricMoment_isLogDerivativeMomentSequence` and uniqueness | Source coefficient identification at all orders | Recurrence is not quadratic positivity |
| `fixedFiniteQuadratic_relative_control` | Complete continuous homogeneous correction is small in a fixed dimension once that face has a margin | Margin is a premise; no arbitrary-N boundary sign follows |
| `storage_one_sevenSample_eventually_relative_control` | Certified complete N=7 relative control, including the full remainder | No claim in other dimensions |
| `canonicalCompletedNativeHankel_two_det_pos_iff_schur` | Exact low-order determinant/Schur sign reduction | Fixed-size scalar reduction, not an all-order sign law |
| `canonicalCompletedNativeShiftedHankel_two_det_pos` | Unconditional specific 2x2 shifted determinant from certified raw integral boxes | Does not prove all prefixes |
| `canonicalCompletedC3ExpandedStructuralStrictChiralDominance_iff_stieltjesPositivity` | Exact alternative spelling of the same strict sign | It is an equivalence, not a proof of dominance |
| `canonicalC2Geometry_native_source_valve_green_operator_forced` | Existing source/valve/Green and finite height chain | Takes `hdominance` explicitly |
| `canonicalC2Geometry_native_strictChiralDominance_of_radialLedger` | Existing radial sewing-to-sign consumer | Takes no-leak and determinant-lower-bound hypotheses |
| `_of_radialJetFlatness`, `_of_radialQuadraticEnergy` | Existing energy/flatness consumers | Take flatness plus nondegeneracy |
| `nativeGeometry_to_finiteHeight_chain` | Camera moments, canonical Jacobi section, symmetric native finite height matrix | Takes precisely `CanonicalCompletedNativeStieltjesPositivity` |

The September-era operator machine really is already chained. The audit
confirms its consumers are reusable. It does not turn any of their explicit
sign/sewing inputs into an unconditional source theorem.

A different positive TFVD/Bessel/Gamma/expanded Gram is insufficient: it still
needs its exact same-source, same-normalization mixed-kernel identification.
The signed chiral difference of two positive Grams has no automatic sign.
Neither the multiplicative valve nor the scalar Green coefficient shift law
supplies that missing lower bound. The previous reverse source audit's
concrete-correspondence frontier remains intact.

## 5. The ONE elementary remaining obligation

The pending mathematical assertion, **not a Lean declaration or assumption
added by this round**, is exactly:

```lean
∀ n : ℕ, 1 ≤ n → ∀ x : Fin (2*n) → ℂ, x ≠ 0 →
  0 < nativeSourceFiniteBoundaryEnergy (2*n) x
```

Its definition depends only on the already-defined raw logarithmic source
coefficients and finite sums/conjugation. Those coefficients come from the
completed source after full synthesis. Their identification with the
prime-depth normalized response is already proved. There is no HP,
Hankel-positivity, Jacobi, height or BR2 premise in this elementary assertion.

This is sufficient to feed the existing height construction. It is **not**
the entire arbitrary-N storage reconstruction/control problem. A positive
limiting face alone does not remove finite radial correction terms. The
existing fixed-dimension analytic mechanism can consume a certified face
when the complete corresponding boundary chart and remainder control are
available; no dimension-uniform threshold is required or asserted.

## 6. Minimal existing-operator handoff

`nativeGeometry_to_finiteHeight_chain_of_evenBoundary` takes the raw assertion
above, applies the proved equivalence, then invokes
`nativeGeometry_to_finiteHeight_chain` unchanged. It returns the old completed
camera characteristic/moment identities, the old finite canonical Jacobi
section identity, and the old symmetric finite native height operator.
Its proof is two lines. It does not assert that its boundary premise has
been established, and it does not rebuild an operator.

## 7. Declarations, dependency firewall and validation

New source algebra is in:

- `CompletedNativeChiralEvenBoundaryEnergy.lean`: raw expression and complete
  antidiagonal coefficient sum;
- `CompletedNativeChiralEvenBoundarySplit.lean`: original even/odd indices,
  forced phases and exact whole-source split;
- `CompletedNativeChiralBoundaryParityCoordinates.lean`: inverse signed
  interleaving, its two phase identities and nonzero preservation;
- `CompletedNativeChiralEvenBoundaryStieltjesGate.lean`: minimal exact iff;
- `CompletedNativeChiralEvenBoundaryHeightHandoff.lean`: existing consumer only.

The two dedicated audits are imported by `CarrySelfAdjointOperator.Audit`.
Raw algebra passes the existing transitive `#assert_oriented_green_source`:
5228 reachable declarations, no canonical moment target or downstream sign
consumer. The iff passes a separate transitive firewall: 5082 reachable
declarations. That firewall permits the canonical target predicate and its
scalar definition, but rejects HP, BR2, Jacobi/height, Herglotz and positive
Stieltjes-carrier consumers. It does not mistake an import graph for a
proof-dependency graph. The downstream handoff is checked separately, because
using the existing height consumer there is intentional.

Capstone `#print axioms` and the enforcing trust assertions allow only
`[propext, Classical.choice, Quot.sound]` (or a subset). No open-sign assertion
is installed via `#check`, postulate or trust escape.

Validation commands and their actual results are recorded below after execution.
Logs: `research/chiral-even-boundary-stieltjes-2026-10-08/`.


### Executed validation

All commands below exited successfully on the authoritative `llm` checkout:

| Command | Result |
|---|---|
| `lake build --wfail` for all seven new modules/audits | PASS |
| `lake env lean CarrySelfAdjointOperator/CompletedNativeChiralEvenBoundaryAudit.lean` | PASS: direct capstone printing and both dependency firewalls |
| `lake env lean CarrySelfAdjointOperator/CompletedNativeChiralEvenBoundaryHeightHandoffAudit.lean` | PASS: downstream handoff footprint |
| `lake build --wfail CarrySelfAdjointOperator` | PASS |
| `lake build --wfail CarrySelfAdjointOperator.Audit` | PASS |
| `bash scripts/static_audit.sh` | PASS |
| `bash scripts/audit.sh` | PASS, ending in `kernel audit passed` |
| `git diff --check` | PASS |

The pending universal raw inequality is not proved, and no validation command
is presented as a proof of it. GitHub Actions status is recorded separately
from these completed Lean/kernel runs.

Publication consists of two semantic increments: original-source parity algebra,
then exact Stieltjes equivalence/old-height handoff with audits and documentation.
The final tracked working tree is clean; the two original user untracked files
remain, with their SHA-256 recorded in the validation directory.
