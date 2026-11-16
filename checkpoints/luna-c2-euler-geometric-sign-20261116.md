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
- Axiom checker: four reports, all with only standard Lean axioms.
- `python3 scripts/scan_lean_trust_escapes.py` — passed.
- `git diff --check` — passed.
- Numerical script was an inline `mpmath` diagnostic over the provided CSV; it did not write to the repository or recalculate heights.

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
