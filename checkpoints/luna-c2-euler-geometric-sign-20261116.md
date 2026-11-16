# Luna checkpoint — C2 geometric Schur Euler balances

Date: 2026-11-16

Repository: `thiagomassensini/carry-self-adjoint-operator`

Branch: `luna/c2-euler-geometric-sign-20261116`

Base: `origin/main` at `f1df607ee46dc9a7127fc9b3cd1aa3bcdc574aa4`
Implementation commit: `f806bb2deafd9f15b1e64993a226121cfb2056ae`

PR: [#125](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/125) (draft).

## Provenance and scope

The tested sequence is the existing canonical sequence
`canonicalCompletedNativeLogDerivativeMoment`, whose prime-depth geometric
readout is identified by `primeDepthGeometricMoment_eq_bracketTfvdReadoutTaylor`
and `primeDepthGeometricMoment_eq_canonical`. No heights or zeros were
recomputed, and no alternative moment sequence was introduced.

This checkpoint does not prove all-order positivity. It uses the already
proved critical direction and Euler/Green identities without assuming a sign
for a pivot, a Schur remainder, or either source matrix.

## New Lean results

`CarrySelfAdjointOperator/NativeSourceSchurEulerGeometricSignProbe.lean`
adds:

- `nativeSchurCriticalReadout_even_eq_zero`: for `n > 0`, the even critical
  readout is exactly zero whenever the old even prefix is invertible. This is
  the existing critical orthogonality applied to the zeroth row. It explains
  why no nonzero square readout can appear in the even Euler balance.
- `nativeSchurEulerPolynomial_green_integral`: the Euler derivative
  `X * P'` has zero value and first derivative at the center, so its exact
  Green transport has no boundary correction.
- `nativeSchurEuler_odd_green_balance` and
  `nativeSchurEuler_even_green_balance`: the balances after both source
  remainders and Euler integrals are transported through Green:

  ```text
  (4n+4) ∫ G(P₁,n) θ = 2 c₀ ρₙ² + ∫ G(X P₁,n') θ
  (4n+2) ∫ G(P₀,n) θ =                 ∫ G(X P₀,n') θ
  G(Q) = Q'' - Q/4
  ```

  Here `Pₛ,ₙ = nativeSchurThetaPolynomial s n`, `ρₙ` is the existing odd
  critical readout, and `θ = thetaTail`. The odd identity leaves the full
  signed Green integral next to the source-derived square. The even identity
  has no square; for every nonempty invertible even prefix its corresponding
  readout is zero.

`NativeSourceSchurEulerGeometricSignProbeAudit.lean` audits the four public
results. It reports only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, or new axiom was added.

## Pole-atom convolution and critical evaluation

The follow-up comparison used the merged [geometry-of-numbers PR #70](https://github.com/thiagomassensini/geometry-of-numbers/pull/70)
and its generic [Bézout product rule](https://github.com/thiagomassensini/geometry-of-numbers/blob/main/research/c3-tilt-prime/BezoutSourceProduct.lean),
alongside the C2 pole factorization and Hankel atom already present in
`CompletedNativePoleAtomHankelPerturbation.lean`.

`CarrySelfAdjointOperator/NativePoleAtomCriticalEvaluation.lean` now proves:

- `nativePoleFactorProduct_geometricConvolution`: if the coefficients of
  `C_pre` are `a`, multiplication by `Φ(u)=1+4u` gives coefficients
  `aₙ + 4aₙ₋₁`; convolution with `(-4)^j` recovers `aₙ` at every order.
- `nativePoleFactorConvolutionMatrix_mul_atom`:
  `T_N(Φ C_pre) * v_N = a[0:N]`, with `v_N[j]=(-4)^j`.
- `nativePoleCriticalPairing_eq_polynomialEvaluation`: under the explicit
  transport hypothesis `T_N(Φ C_pre)ᵀ y = c₀ x`, the source coefficient
  pairing is exactly `c₀ * Σ_j xⱼ(-4)^j = c₀ Pₓ(-4)`.
- `nativePoleCritical_evenCorrection_eq` and
  `nativePoleCritical_oddCorrection_eq`: the product-rule corrections
  contract respectively to `-4 c₀² Pₓ(-4)²` and
  `+16 c₀² Pₓ(-4)²`.

These lemmas are algebraic and make no pivot or kernel sign assumption. The
normalization is `ξ(u)=Φ(u) C_pre(u)` with `C_pre=-Λ/8`, from the existing
`completedNativeOperatorCharacteristic_eq_poleFactor_mul_raw`; if the
coefficient vector is instead taken from unscaled `Λ`, the Bézout kernel
correction carries the additional factor `1/64`.

Scope limit: the new module proves the finite identities for a generic
pre-factor coefficient sequence and states critical transport as a hypothesis.
It does not yet extract the Taylor coefficients of the actual raw `Λ`
characteristic into this sequence, nor import the separate GoN source-kernel
and TFVD implementation into this C2 repository. The exact function
factorization and moment atom are proved locally, but that coefficient/physical
transport crosswalk remains the next formal obligation. The numeric CSV gives
`Pₓ(-4) ≈ -4.00160885567459714` for the first nontrivial even critical vector,
while its Euler readout is zero; this is a diagnostic confirming the two
functionals differ, not a certified sign input.

The CSV calculation is reproducible with
`scripts/probe_c2_schur_csv_excerpt.py` (SHA-256
`508d99ca0726a6950aeca82b066c5d0bf4bd0b17569cdd5410efc6a2a7b823fd`).

## What the sign attempt found

- Odd sector: the open estimate is precisely
  `∫ G(X P₁,ₙ') θ > -2 c₀ ρₙ²`. No uniform bound for this signed integral was
  obtained. Existing `nativeSchurThetaPolynomial_odd_negativeMass_pos` still
  rules out deleting the negative mass or replacing the source polynomial by
  a pointwise square.
- Even sector: for `n > 0`, orthogonality kills `ρ₀,ₙ`. Thus the task is to
  prove positivity of the signed Green integral itself. Existing
  `nativeSchurThetaGreenPolynomial_even_coeff_top_neg` and
  `nativeSchurThetaGreenPolynomial_even_tendsto_atBot` show why pointwise
  nonnegativity of the original Green polynomial is not a viable route; at
  `(s,n)=(0,0)` it even evaluates to `-1/8` at `u=3`.
- The positive/negative theta-mass equivalences remain reductions, not mass
  domination estimates. The new identities expose an additional signed
  Euler-transformed Green integral but do not control it.

## CSV experiment (diagnostic only)

Input: `momentos/investigations/jacobi_polynomial_moments_20261024/c2_momentos_16_excerpt.csv`

SHA-256: `2485addf2d0d470869db3ff393979624e60c16455ee4ec880feece3edfa7fcb8`
Used `h₀,…,h₁₅` as supplied; no height computation was run.

For each `s,n`, `p = h₂ₙ₊ₛ - bᵀA⁻¹b` was computed from the CSV. The Euler integral
was evaluated independently from the source recurrence

```text
eₖ = (2k+2)hₖ - 2 Σ_{j<k} hⱼ hₖ₋₁₋ⱼ
Iₛ,ₙ/c₀ = Σᵢⱼ vᵢ vⱼ eᵢ₊ⱼ₊ₛ
```

and `ρₙ = Σᵢ vᵢ hᵢ`. Since `Rₛ,ₙ = c₀ pₛ,ₙ`, `c₀` cancels from
`qₙ = -I₁,ₙ/(2c₀ρₙ²)`. All displayed pivots are for the decimal excerpt,
not certified signs for the underlying exact moments.

| n | `p₀,n = R₀,n/c₀` | `I₀,n/c₀` | `p₁,n = R₁,n/c₀` | `I₁,n/c₀` | `qₙ` |
|---:|---:|---:|---:|---:|---:|
| 0 | 2.310499311542e-2 | 4.620998623084e-2 | 3.717259928527e-5 | -9.189910165860e-4 | 0.860735238781 |
| 1 | 8.436858410134e-8 | 5.062115046080e-7 | 1.038530676385e-10 | -4.669107760080e-9 | 0.848939133137 |
| 2 | 1.114641604497e-13 | 1.114641604497e-12 | 8.081775961675e-17 | -5.365807796070e-15 | 0.846926902832 |
| 3 | 5.419624538382e-20 | 7.587474353734e-19 | 2.962261727718e-23 | -2.375179307720e-21 | 0.833647458725 |
| 4 | 1.666281011782e-26 | 2.999305821208e-25 | 8.511283277988e-30 | -7.312699233269e-28 | 0.811174155860 |
| 5 | 4.127241644034e-33 | 9.079931616876e-32 | 1.572947964218e-36 | -1.742284784505e-34 | 0.821912971314 |
| 6 | 5.136864276584e-40 | 1.335584711912e-38 | 1.397873288606e-43 | -1.869388378528e-41 | 0.826872898918 |
| 7 | 3.807653956938e-47 | 1.142296187081e-45 | 1.050518157413e-50 | -1.341247608438e-48 | 0.799592750003 |

For this excerpt, all tested decimal pivots are positive, the odd `I₁,n` are
negative, and all eight `qₙ` lie below one. `qₙ` is not monotone: it rises
from `n=4` to `n=6`. The identity itself gives
`qₙ = 1 - (4n+4)p₁,ₙ/(2ρₙ²)`, so `qₙ < 1` is equivalent to the odd pivot sign;
this observation is not an independent proof of that sign.

Command:
`python3 scripts/probe_c2_schur_csv_excerpt.py /home/thlinux/momentos/investigations/jacobi_polynomial_moments_20261024/c2_momentos_16_excerpt.csv`

Arithmetic at 70/90/110/120 decimal digits changed the computed nonzero
quantities by at most `6.2e-58`, `1.1e-77`, and `2.7e-98` across successive
precision pairs. The largest infinity-norm condition estimate was about
`4.5e37` (even) and `2.7e38` (odd). The final stored moment has 87 significant
decimal digits and the CSV supplies no rigorous rounding intervals; these
facts prevent treating the signs as certified. The largest normalized Euler
balance residual for the supplied decimals was about `5.4e-108`.

## Validation

- `lake build --wfail CarrySelfAdjointOperator.NativeSourceSchurEulerGeometricSignProbeAudit` — passed (9,839 jobs including replayed dependencies).
- Direct `lake env lean -DwarningAsError=true` compilation of the probe and audit — passed.
- Direct `lake env lean -DwarningAsError=true CarrySelfAdjointOperator/NativePoleAtomCriticalEvaluation.lean` — passed.
- `lake build --wfail CarrySelfAdjointOperator.NativeSourceSchurEulerGeometricSignProbeAudit` — passed after the extension (9,841 jobs).
- Axiom checker: nine reports, all with only standard Lean axioms.
- `python3 scripts/scan_lean_trust_escapes.py` — passed.
- `git diff --check` — passed.
- `python3 scripts/probe_c2_schur_csv_excerpt.py <provided CSV>` — passed; it does not recalculate heights.

## First remaining gap and next lemma

No all-order geometric estimate was found. The first odd obligation is a
noncircular lower bound on the signed integral of `G(X P₁,ₙ') θ` strong enough
to keep it above `-2 c₀ρₙ²`. In the even sector there is no square term and
`ρ₀,ₙ=0` for every nonempty invertible prefix; one must control the signed
integral of `G(X P₀,ₙ') θ` directly. The negative leading coefficient blocks
a proof by pointwise positivity of the existing even Green density. A useful
next source lemma would have to bound these signed integrals from the C2
depth/bracket decomposition while retaining their cross-cancellation; no such
bound is included here.

## Follow-up — exact pivot change under the pole atom

The subsequent analysis formalizes the correction to the Schur pivot itself,
including the fact that the prefix inverse changes. For a symmetric invertible
prefix `A`, old coupling `b`, atom prefix `w`, last atom coefficient `t`, and
`δ = 1 + α wᵀA⁻¹w ≠ 0`, the new pivot satisfies

```text
p_updated = p_old + α (t - wᵀA⁻¹b)^2 / δ.
```

The denominator condition also proves the updated prefix is invertible by an
explicit Sherman–Morrison inverse and determinant argument. No positivity or
pivot-sign hypothesis is used. The numerator is the evaluation at `-4` of the
old monic critical direction `(-A⁻¹b,1)`.

New module: `CarrySelfAdjointOperator/NativePoleAtomSchurUpdate.lean`.
Important declarations:

- `nativePoleRankOneUpdate_isUnit` — nonzero denominator implies the updated
  symmetric rank-one prefix is invertible.
- `nativePoleSchurRankOneUpdate` — generic fractional-square pivot identity.
- `sourceMomentSchur_add_nativePoleAtom` — source Hankel specialization for
  every shift `s`, with atom mass `4(-4)^s` and the updated coupling.
- `nativePoleCriticalPolynomialEvaluation` — identifies the numerator with the
  polynomial evaluation of the old critical direction at `-4`.
- `canonicalRawSourceMomentSchur_update_criticalPolynomial` — specializes to
  the existing canonical completed moments and the existing raw `Lambda`
  moments. The `s=0` and `s=1` corollaries expose the masses `+4` and `-16`.

The conditions are explicit for this matrix argument: the old prefix is a
unit, it is symmetric, and `δ` is nonzero. For Hankel prefixes symmetry is
definitional. No all-order positivity, positive definiteness, positive pivot,
Green-integral sign, or positive Gram premise is used. This identity accounts
for the prefix correction that is missed by contracting the atom against a
fixed vector. It does not estimate the canonical Euler–Green integral and does
not close the remaining source-sign question.

### Numerical check of the pivot update

The CSV diagnostic now also computes the raw pivot directly and from the
fractional formula, plus the atom denominator and the old critical polynomial
evaluation. At `n=1`, using only the supplied decimal moments at 120-digit
mpmath precision:

| sector | canonical pivot | raw pivot, direct | correction | denominator | `P(-4)` | relative formula residual |
|---|---:|---:|---:|---:|---:|---:|
| even (`s=0`) | `8.4368584101341518e-8` | `0.36785260731239055` | `0.36785252294380645` | `174.1227522993991` | `-4.00160885567459714` | `2.11e-120` |
| odd (`s=1`) | `1.0385306763847226e-10` | `0.00059591702753351622` | `0.00059591692368044858` | `-430423.56830131567` | `-4.00387850013647296` | `4.04e-116` |

The odd sector illustrates why the sign of `α=-16` alone does not determine
the correction: its denominator is also negative here, so this decimal
correction is positive. Both old prefix condition estimates are `1` at this
one-dimensional order. The tiny algebraic residual measures agreement of two
calculations on the same finite decimal input; it is not a rounding interval
or a certificate about the exact moments. These values do not imply a
general-order pivot sign.

Reproducible command:

```sh
python3 scripts/probe_c2_schur_csv_excerpt.py \
  /home/thlinux/momentos/investigations/jacobi_polynomial_moments_20261024/c2_momentos_16_excerpt.csv \
  --dps 70 90 110 120
```

For the updated script, the reported maximum relative changes across those
precision pairs are `9.06e-21`, `3.53e-40`, and `6.22e-62` for the tracked
pivots and formula calculations. The input file SHA-256 remains
`2485addf2d0d470869db3ff393979624e60c16455ee4ec880feece3edfa7fcb8`.

### Follow-up validation and publication

- `lake env lean -DwarningAsError=true CarrySelfAdjointOperator/NativePoleAtomSchurUpdate.lean` — passed.
- `lake build --wfail CarrySelfAdjointOperator.NativeSourceSchurEulerGeometricSignProbeAudit` — passed (9,842 jobs).
- The audit now prints the axioms for the new matrix and C2 pivot theorems; each reports only `propext`, `Classical.choice`, and `Quot.sound`.
- `python3 scripts/scan_lean_trust_escapes.py` — passed; no `sorry`, `admit`, or new axiom.
- `git diff --check` — passed.

Follow-up implementation commit: `ae5ef0cfec157d2d5ca8a5f0343d34da8455456b`.
It is pushed to `luna/c2-euler-geometric-sign-20261116` and updates draft PR
[#125](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/125).
The checkpoint publication update is committed immediately after this feature
commit. The remaining mathematical gap is unchanged: a noncircular geometric
estimate for the signed canonical Euler–Green integral, especially direct
positivity control in the even sector.
