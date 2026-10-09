# Reverse source-first audit of all-order chiral storage positivity

## Published checkpoint and scope

Initial main: `d0671e8127b93a178405aae3b4b7cf031d9a437d`.
`git pull --ff-only` returned already up to date. HEAD, main and origin/main
agreed. The two pre-existing untracked `C2OddTfvdTransport.lean` files are
preserved and excluded from publication. No N=8 certificate, new source,
carrier, metric, Gram factor or positive hypothesis is introduced.

Statuses:

- `PASS_SOURCE_BOUNDARY_COEFFICIENT_PROVENANCE_ALL_ORDER`
- `OPEN_SOURCE_BOUNDARY_POSITIVITY_ALL_ORDER`

The directed audit did not find an existing unconditional all-order source
boundary sign theorem. This is an audit conclusion, not a theorem asserting
nonexistence of a proof or a no-go of the theory.

## 1. Reusable kernel-checked lemmas

| Declaration / module | What it proves | Sign / correspondence still required |
|---|---|---|
| `ChiralReturn.radialEulerPower_green_boundary` | Exact polarized Green identity on the original Cauchy carrier, every N and degree, both families | Alternating boundary form is signed; no general nonnegative assertion |
| `ChiralReturn.storage_one_eq_odd_green_tower_and_remainder` | Complete storage = finite odd Green tower + exact higher-source vector pairing | Neither the tower nor remainder receives a sign from this equality |
| `fixedFiniteQuadratic_relative_control` | For a fixed dimension, complete continuous homogeneous correction is small relative to a certified boundary margin | Source coercivity is an explicit premise, not proved by compactness |
| `storage_one_sevenSample_eventually_relative_control` | Complete N=7 correction, all crosses and entire analytic remainder, is bounded by eta E7 for every direction | Uses the existing raw-integral seven-face certificate; does not certify other N |
| `ChiralReturn.coisometricFourChannelBalance_eq_rawGamma_add_gram_difference` | All three coisometric comparison channels reduce to the exact difference of two fully synthesized Grams | Raw Gamma--Wronskian correction remains signed |
| `ChiralReturn.rawGammaCorrection_comparison_eventually_complete` | The Gamma comparison identities hold for each N, eventually k, uniformly in all coefficient families and radii | The result supplies a two-sided absolute estimate, not the one-sided sign |
| `primeDepthGeometricMoment_isLogDerivativeMomentSequence` | Independent source-first recurrence of the completed normalized response | A recurrence and uniqueness provide coefficients, not quadratic positivity |
| `canonicalC2Geometry_nativeWronskianResponse_coefficientEquation_before_gram` | Scalar response array obeys first-column and index-shift coefficient identities | This array is not asserted to be a Hilbert-vector Gram |
| `polarizedGreenMomentCoefficient_even_even`, `_odd_odd`, `_even_odd`, `_odd_even` | Exact coefficient indices and limiting mixed-parity zeros | Does not say that two vector families are orthogonal at finite radial step |
| `projectiveChiralDifferenceJet_pairing_tendsto_primeDepthCoefficient` | All-order signed projective/chiral pairing limit realizes the source coefficients | Signed form, not a positive Hilbert Gram |

No statement above is used as a positivity premise when it only proves an
identity, limit, reconstruction or size bound.

The pre-Gram scalar/vector distinction was checked explicitly in
`NaturalNativeOperatorShiftCapstone`. The unconditional native Wronskian
response theorem uses the SCALAR array `responseTaylorCoefficient(M,p+q+1)`.
By contrast, `polarizedCoefficientVectorEquation_realMomentKernel` takes
`HasPolarizedCoefficientVectorEquation moments rawJet` as an input on the
inner products of a Hilbert-valued jet. The concrete seeded-clock route
receives `HasCorrectedNativeSeededClockBoundaryTransport M block`. The
source-to-height capstones additionally receive a strict chiral dominance,
center-leg readout, or realized Green moment-jet premise. These conditional
consumers do not promote the scalar shift identity to a positive vector Gram.

## 2. Exact source and normalization

Write F for `completedNativeOperatorCharacteristic`, C for its existing
companion -F', Q for `completedNativeOperatorLogDerivative`, and

```text
c_j = nativeSourceOddBoundaryCoefficient j
    = Re(iteratedDeriv(2j+1,Q,0)) / (2j+1)!,
g_j = primeDepthGeometricMoment j.
```

The independent geometric response is the completed prime-depth response,
whose germ equals `completedGreenNormalizedResponse F C = -F'/(2F)`.
The raw odd source is `Q = -F'/F`. Thus the normalization is fixed, rather
than a choice made to fit a target Gram.

The new module proves, without using the canonical recursive moment sequence:

```text
Q = 2 * completedGreenNormalizedResponse F C,
c_j = 2 * g_j                         for EVERY j,
2 * (-1)^j * c_j * (-1)^a = 4 * (-1)^(j+a) * g_j.
```

The function identity is global for the existing total division convention;
no unproved neighborhood or differentiability premise is introduced. Iterated
constant multiplication and the already-proved prime-depth coefficient germ
identity give the coefficient equality.

`nativeSourceOddGreenTower_eq_primeDepth` also proves the ENTIRE finite tower
identity, for arbitrary order r and arbitrary boundary sequence b:

\[
2\sum_{j<r}(-1)^jc_j\sum_{a\le2j}(-1)^a
\Re(\overline{b_a}b_{2j-a})
=
4\sum_{j<r}(-1)^jg_j\sum_{a\le2j}(-1)^a
\Re(\overline{b_a}b_{2j-a}).
\]

Every ordered cross on both sides is the same cross. For the actual storage,
this rewrites only its finite prefix after the existing full synthesis;
the exact remainder pairing is left in place. No finite polynomial is
substituted for the completed source.

The existing `primeDepthGeometricMoment_eq_canonical` can identify the
canonical sequence afterward. It is NOT an ingredient of any new proof.

## 3. Limiting E_N and the parity audit

For x in `Fin N -> Complex`, let b be its zero-extension. The limiting
source boundary face is the existing alternating Green expression

\[
E_N(x)=2\sum_{j<N}(-1)^jc_j\sum_{a\le2j}(-1)^a
\Re(\overline{b_a}b_{2j-a}).
\]

This expression is the raw tower evaluated on the LIMIT boundary coordinates.
It is not the finite-step tower with higher reconstructed jets suppressed.
The N=7 specialization agrees with the already-proved
`nativeSourceSevenBoundaryEnergy_eq_alternating_green`.

The entry for two even indices 2i and 2j is
`2*(-1)^(i+j)*c_(i+j) = 4*(-1)^(i+j)*g_(i+j)`.
The entry for two odd indices 2i+1 and 2j+1 is
`2*(-1)^(i+j)*c_(i+j+1) = 4*(-1)^(i+j)*g_(i+j+1)`.
These two all-order entry identities are new kernel-checked theorems.
Mixed limiting entries vanish because the response is odd, as the existing
polarized coefficient parity API records.

Consequently, algebraic reindexing of the limiting face gives its two
index-sum blocks, with signs removed by the FORCED real phases
`y_(2i)=(-1)^i*x_(2i)`, `y_(2i+1)=(-1)^i*x_(2i+1)`:

\[
E_N(x)=4\sum_{i,j<(N+1)/2}g_{i+j}\Re(\overline{y_{2i}}y_{2j})
+4\sum_{i,j<N/2}g_{i+j+1}\Re(\overline{y_{2i+1}}y_{2j+1}).
\]

The phases come from the original alternating Green identity, not a selected
weight or metric. The displayed finite block reindexing is an audit derivation
from the proved tower/entry identities; no additional general-N matrix
reindexing theorem is claimed in this checkpoint.

Important distinction: the source coefficients have been identified with
geometric response coefficients, but NOT with the inner products of a known
positive feature family. Calling the blocks Hankel describes index-sum
algebra; it does not assert a sign. Mixed FINITE-STEP crosses still exist,
including the previously proved N=7 first correction and the analytic
remainder. The limiting mixed zeros cannot be used to delete them.

## 4. Positive Gram candidates and the missing concrete correspondences

| Candidate | Positivity actually proved | Why it does not currently certify E_N |
|---|---|---|
| `greenJetOddPrefixGram jet N` | Unconditional PSD of its own Hilbert Gram | `greenJetOddPrefixGram_eq_shiftedHankel_of_greenRepresentation` requires `IsGreenWronskianMomentKernelGramRepresentation`; the realized source jet is not supplied |
| `MomentGramPositivity` generic consumers | A correct Gram representation gives PSD; independence of the SAME family gives PD | `IsMomentGramRepresentation` / shifted realization and independence are premises |
| Corrected oriented Green-frame source | Injective channel transport, bounded synthesis, retained residual; exact scalar readout equals dslope | `canonicalCompletedC3AllCutoffOrientedRealKernelReadout_eq_parsevalInner` takes `HasCompletedNativeRealAxisNormalizedGreenKernel state` |
| Division-free Hilbert Green route | `hasCanonicalCompletedNativeRealAxisNormalizedGreenKernel_of_divisionFreeGreen` derives the normalized Hilbert kernel from `hgreen` and continuity | A source-correct Hilbert state satisfying `HasDivisionFreeGreenRepresentation F C state` remains unconstructed; positivity alone would still not prove same-family nondegeneracy |
| Projective/chiral state | Exact dslope signed pairing and all-order coefficient limit | Its form is one half of a DIFFERENCE of Grams; PSD is equivalent to the still-open multiplier contractivity |
| Expanded eight-channel structural/chiral block | `canonicalCompletedC3ExpandedStructuralChiralBlockKernel_posSemidef` is unconditional; both fixed-chirality compressions are nonnegative | Complete structural synthesis recovers the positive AND negative chiral Grams; the Wronskian reads their signed difference, not their positive sum |
| TFVD/Bessel provenance Pitagoras | Positive active energy and orthogonal residual, including polarization, with realization of those prime-atlas readouts | The active readout is not identified with this completed normalized Green coefficient kernel |
| Gamma / coisometric source | Positive norm squared of the actual Gamma vector | Exact full storage subtracts the raw Gamma--Wronskian channel, whose one-sided bound is not proved all-order |
| Xi theta integral moments | Positive raw integral masses, strict low-order inequalities and certified finite boxes | c_j are nonlinear log-derivative combinations of these integrals; integral positivity does not provide their alternating quadratic sign |
| Six-frame upper bound | `6I-H` and its shifted complement are PSD unconditionally | An upper bound gives no lower positivity of H; blind/loss-channel realization remains a distinct seam |
| Signed-generator Herglotz Gram | Exact positive resolvent Gram once a real HP certificate is supplied | The certificate already contains the required moment realization; using it upstream would be circular |

The eight-channel result is especially important: no structural cross is
missing from that positive block. Yet
`canonicalCompletedC3ExpandedStructuralChiralCompression_positive_eq` and
`canonicalCompletedC3ExpandedStructuralChiralCompression_negative_eq` recover
both Gram channels, and
`canonicalCompletedC3NormalizedFullWronskianOperatorKernel_eq_polarizationDifference`
reads `I * (positiveGram - negativeGram)`. The positive block does not order
its two nonnegative compressions. Its PSD cannot be used as positivity of
that signed observable. The same distinction holds for the existing chiral
Pythagorean norm identity, which adds the two energies.

The chart-replacement positivity split also receives raw PosDef and correction
PSD hypotheses. The six-source material radial PSD theorem is an equivalence
with chiral contractivity; it does not discharge that contractivity. Camera
Parseval transport consumers receive a visible-coefficient realization
hypothesis. None is a source-first all-order sign proof.

The existing concrete C3 positive-state no-go is respected:
`not_hasCompletedNativeRealAxisNormalizedGreenKernel_concreteC3_of_defect`.
No rescaling or extra coordinate is introduced to evade it. Linear/projective
incidence, injectivity or TFVD recovery are not treated as metric realization.

## 5. Coisometric cancellation: exact frontier, all crosses retained

The named four-channel theorem is important and reusable. It gives

```text
fourChannelBalance = rawGammaBalance
                  + I*(coisometricGram - GammaGram).
```

After COMPLETE synthesis, the three comparison channels cancel exactly:

\[
\Re S_k(c,r)=2\|\Gamma_{k,c,r}\|^2
-2\Im\operatorname{rawGammaWronskianBalance}(k,c,c,r,r).
\]

This is `storage_re_eq_gammaEnergy_sub_rawGammaBalance`. It has geometric
strip/nonvanishing premises, supplied eventually for every finite N by the
existing radial regularity theorem. It has NO all-order sign premise hidden
inside that identity.

The still-needed PSD inequality is precisely

```lean
∀ N : ℕ, ∀ᶠ k : ℕ in Filter.atTop,
  ∀ c : Fin N → ℂ,
    (ChiralReturn.rawGammaWronskianBalance k c c 1 1).im ≤
      ‖ChiralReturn.gammaSourceSynthesis k c 1‖^2
```

The strict version excludes c=0 and uses `<`. The existing six-node strict
comparison is proved FROM the already-certified six-node storage, rather
than proving that storage. It cannot be generalized by dropping its N=6
restriction. Absolute Cauchy--Schwarz control of the energy gap has no
one-sided sign and cannot replace this inequality.

The equivalent source orientation is the mixed pairing
`4*Im(inner sourceValue sourceCompanion)`. Its exact TFVD/Green ledger
crosswalk retains tails, chart/completion, provenance and off-diagonal terms,
but remains a signed readout. No pointwise flux sign is required or asserted.

## 6. First mathematical obligation still unproved

For the proposed route through boundary margins and relative continuity, the
first missing SIGN obligation is arbitrary-N source boundary coercivity:

```lean
∀ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin N → ℂ,
  let b : ℕ → ℂ := fun a => if ha : a < N then x ⟨a,ha⟩ else 0
  ε * ‖x‖^2 ≤ 2 * (∑ j ∈ Finset.range N,
    (-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j *
      (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
        (conj (b a)*b (2*j-a)).re))
```

The exact Lean syntax is TYPE-CHECKED by a `#check` in the dedicated audit.
This is deliberately not a theorem, hypothesis wrapper, axiom or new
canonical object. It states the needed sign directly on the source tower.
Its directly named source dependency is `nativeSourceOddBoundaryCoefficient`,
which is defined from iterated derivatives of the existing -F'/F. The remaining
symbols are finite sums, zero extension, complex conjugation, real parts and
the existing finite coordinate norm. No HP/Hankel/Jacobi/height premise enters.
That Pi norm is the already-used maximum coordinate norm, solely a finite
compactness/coercivity tool; it does not replace the physical Cauchy metric.

The source-specific certificates currently discharge this obligation in
low finite dimensions, including N=7. The algebraic coefficient and parity
correspondence does NOT discharge it in arbitrary dimension. A positive
Gram realization would discharge semidefiniteness only after the concrete
source/carrier/normalization/cross equality is proved; strict coercivity also
requires nondegeneracy of that same family.

A source-facing N-generic reconstruction/continuity implementation would
still be needed to instantiate the fixed-dimension analytic lemma for all N.
It is a separate API task; it does not create the missing source sign. Strict
boundary coercivity is sufficient for this perturbative route, not asserted
necessary for every possible proof of eventual storage positivity.

The required quantifier order remains `forall N, exists epsilon_N` and then
`exists h_N`. A single dimension-uniform margin or radial radius is not needed
for positivity in each fixed finite dimension, and is not assumed.

## 7. New declarations and dependency audit

No new definitions or carriers are added. The six new theorems are:

- `completedNativeOperatorLogDerivative_eq_twice_greenResponse`
- `nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment`
- `nativeSourceOddBoundaryCoefficient_weighted_eq_primeDepth`
- `nativeSourceEvenBoundaryCoefficient_eq_polarizedPrimeDepth`
- `nativeSourceOddBoundaryCoefficient_eq_polarizedPrimeDepth`
- `nativeSourceOddGreenTower_eq_primeDepth`

They live in `CompletedNativeChiralReturnBoundaryCoefficientProvenance.lean`.
The dedicated audit checks axioms and transitive declaration dependencies.
The source closure rejects canonical moments, HP/Stieltjes, Hankel,
Jacobi/height, Herglotz and BR2 declarations. Modules containing downstream
material may be READ during the audit; none of that material is a proof input.
Allowed footprint is `[propext, Classical.choice, Quot.sound]` or a subset.

The audit is registered in the repository umbrella. README receives an
appended checkpoint, preserving earlier research reports. Validation commands,
exit statuses and direct Lean outputs are retained under
`research/chiral-storage-reverse-source-audit-2026-10-08/`.
The natural jet cutoff `r : Nat`, the internal Cauchy radius `r : Real`,
radial index k and TFVD cutoff M are not identified. No source amplitude,
Cauchy metric, completion, readout or sampling parameter is modified. Neither all-order positivity nor its negation is claimed.
