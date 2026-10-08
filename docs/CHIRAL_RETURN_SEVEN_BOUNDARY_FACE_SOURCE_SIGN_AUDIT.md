# Complete seven-coordinate boundary face: exact source sign gate

## Checkpoint and result

Initial published main: `2c99dca09181e82368ba035eef6b8267e6d3416a`.
`git pull --ff-only` returned already up to date; HEAD/main/origin/main agreed.
The two pre-existing untracked files `C2OddTfvdTransport.lean` and
`C2OddTfvdTransportAudit.lean` are preserved and excluded from task commits.

Status: `PASS_SEVEN_BOUNDARY_EXACT_SOURCE_SIGN_REDUCTION`.
The requested sign remains `PARTIAL_SEVEN_BOUNDARY_SOURCE_MARGIN`.
The kernel proves an exact equivalence and raw source formulas, **not** the
new positive sign, N=7 storage positivity or arbitrary-N contractivity.

The previously closed uniform order-fourteen remainder bound and full
N=6 result are reused. They are not redefined or presented as new results.

## Same source, same complete boundary coordinates

Write `c_j = nativeSourceOddBoundaryCoefficient j`. These are derivatives
of the unchanged completed source `Q = -F'/F` at the center, divided by
`(2*j+1)!`, before any canonical-moment identification. The original
radial nodes remain 1,...,7 and the exact Euler boundary chart is unchanged.

The complete boundary face is

```text
E7(x) = 2 * (Q4(x0,x2,x4,x6) + Qodd3(x1,x3,x5)),
Q4(u,v,w,t) =
 c0 |u|² - 2c1 Re(conj(u)v) + 2c2 Re(conj(u)w) - 2c3 Re(conj(u)t)
 + c2 |v|² - 2c3 Re(conj(v)w) + 2c4 Re(conj(v)t)
 + c4 |w|² - 2c5 Re(conj(w)t) + c6 |t|².
```

`Qodd3` is exactly the already certified three-coordinate odd face from
N=6, not an altered form. All six even pairwise crosses and all odd crosses
remain. `nativeSourceSevenBoundaryEnergy_eq_alternating_green` identifies
this face with the original alternating Green boundary tower, with no
index relabeling or target Gram.

This is the limiting boundary face only. No finite-step source remainder
is dropped: its complete estimate was proved in the preceding increment.
No scalar is used to reconstruct a lost state, and no metric on the original
Cauchy carrier is changed. The finite Pi maximum norm is used only to
express a uniform coordinate bound, as in the preceding remainder theorem.

## Complete vector prefix and its boundary limit

`CompletedNativeChiralReturnSevenBoundaryRegularization` extends the
existing six-coordinate regularization to the already constructed exact
seven-node Euler inverse. It introduces no new carrier or source.
For every order m, define the reconstructed boundary coordinate by

```text
B_h(x,m) = x_m,                                           m<7,
B_h(x,m) = sum_{a<7} h^(m-a) * [sum_{i<7} (i+1)^m W_ia] x_a,  m>=7.
```

For h nonzero, `radialSevenRegularizedBoundary_eq` proves this is exactly
`h^m * radialEulerBoundaryJet(d(h,x),m)`. No higher boundary coordinate is
zeroed at a finite step. Only at h=0 does it become the limiting extension
used by E7. These statements are algebraic source reconstruction, not metric
identifications.

Let A_k be the original `radialIncidentSynthesis k 7` in the unchanged
Cauchy Hilbert carrier. The full prefix VECTOR is

```text
P(k,h,x) = sum_{j<7} (-1)^j c_j h^(2j+1)
                         * radialEulerPowerSynthesis k 7 (2j+1) d(h,x).
```

For `(k+1)*h=1`, the existing general odd Euler Green energy identity gives

```text
4 Re(inner A_k(d(h,x)) P(k,h,x))
 = 2 sum_{j<7} (-1)^j c_j
       sum_{a<2j+1} (-1)^a Re(conj(B_h(x,a)) B_h(x,2j-a)).
```

`radialSevenSourcePrefix_energy` checks this AFTER the whole vector sum,
with all original seven-by-seven Cauchy crosses. The right side is jointly
continuous in `(h,x)` and equals E7(x) at h=0. Consequently
`radialSevenSourcePrefix_energy_tendsto` proves the ACTUAL vector prefix's
mixed readout tends to E7(x) for every fixed x along the original radial
step `1/(k+1)`. No positivity premise is used. This is not a claimed uniform
convergence in x; the separate uniform margin criterion follows below.
The complete analytic source remainder is still retained and bounded by
the already published seven-sample remainder theorem.

## Exact polarized sewing and the only new sign

Let `D = nativeSourceFiveEvenDiscriminant`, already proved positive directly
from source integral bounds. In the formulas below use
`a=c0,b=c1,c=c2,d=c3,e=c4,f=c5,g=c6`.

```text
D  = a*c*e + 2*b*c*d - a*d² - b²*e - c³
n0 = b*e² - 2*c*d*e + d³ - b*d*f + c²*f
n1 = a*e² - b*d*e + c*d² - c²*e - a*d*f + b*c*f
n2 = a*d*e - b*c*e - b*d² + c²*d - a*c*f + b²*f
D7 = D*g + d*n0 - e*n1 + f*n2.
```

The kernel proves

```text
Q4(u,v,w,t)
 = Q3(u + (n0/D)t, v + (n1/D)t, w + (n2/D)t)
   + (D7/D)|t|².
```

This identity expands the SAME actual form; it does not assign a new inner
product, change weights or construct a factor from a desired target.
`nativeSourceSevenEvenBoundaryEnergy_sewing` checks every cross term.

The exact nonzero diagnostic chart

```text
x* = (-n0/D, 0, -n1/D, 0, -n2/D, 0, 1)
```

has complete energy `2*D7/D`. It is a test direction in the existing source
chart, not a fitted source or replacement state. Thus the new sign cannot
be bypassed by checking just the new diagonal or the pure cancellation
vector. `nativeSourceSevenBoundaryPivot_ne_zero` and
`nativeSourceSevenBoundaryPivot_energy` formalize this test.

## Uniform margin, with the correct quantifiers

Continuity, quadratic homogeneity and compactness of the existing finite
unit sphere prove

```text
(exists epsilon>0, forall x : Fin 7 -> Complex,
 epsilon * norm(x)^2 <= E7(x))
   iff 0 < nativeSourceSevenEvenDiscriminant.
```

This is `nativeSourceSevenBoundaryEnergy_uniform_margin_iff`.
The whole odd sector is retained in both implications. It is an equivalence,
not a theorem asserting either side and not a new assumption structure.

The equivalent single raw coefficient inequality is

```text
(-c3*n0 + c4*n1 - c5*n2)/D < c6.
```

The kernel does NOT prove this inequality in this increment.

## Raw thirteenth source jet, before moments

The original cosine integral representation of F is differentiated twice
beyond the already checked twelfth derivative. Dominated differentiation
uses the existing integrability of all polynomial powers of the SAME raw
cosine kernel. It proves

```text
iteratedDeriv 14 F 0 = - completedNativeXiCosineMoment 7.
```

No sign of a connected/logarithmic coefficient follows merely from the
positivity of this raw integral. Let `mu_j = completedNativeXiCosineMoment j`.
The division-free source recurrence at order 13, together with parity and
raw even derivatives, proves

```text
c6 = P13(mu0,...,mu7)/(13! * mu0^7),
13! = 6227020800.
```

The exact connected numerator is

```text
P13(a,b,c,d,e,f,g,h) =
 a^6*h - 91*a^5*b*g - 1001*a^5*c*f - 3003*a^5*d*e
 + 6006*a^4*b²*f + 90090*a^4*b*c*e + 84084*a^4*b*d²
 + 210210*a^4*c²*d - 270270*a^3*b³*e - 3783780*a^3*b²*c*d
 - 3153150*a^3*b*c³ + 7567560*a²*b^4*d + 37837800*a²*b³*c²
 - 113513400*a*b^5*c + 97297200*b^7.
```

The raw fourteenth characteristic derivative is retained explicitly in
`nativeSourceLogSlope_thirteenth_derivative_eq_rawCharacteristicJet` before
being identified with its actual integral. The final integral formula uses
that source equality, never canonical moments. Reality and factorial
normalization are then proved. The even twelfth source jet vanishes by the
original source recurrence. Together these prove the exact expansion

```text
-I Q(I*y) = sum_{j<7} (-1)^j c_j y^(2j+1) + y^14 R(y),
```

with R analytic at zero and the ENTIRE analytic remainder retained.

`nativeSourceSevenBoundaryEnergy_uniform_margin_iff_integral_gap` combines
these identities. The remaining inequality now has a complete source-only
right side, not an unspecified Taylor coefficient.

## Attempt to close the remaining source sign

The source certificates currently used for the N=6 sign enclose the theta
integrals through degree 12. They give no corresponding certified upper
bound at degree 14. A finite numerical diagnostic also found that varying
the old independent interval endpoints changes the apparent sign of the
new connected expression, even with the new integral held fixed near its
numerically evaluated value. This is **uncertified numerical evidence**
about the adequacy of those boxes, not a Lean refutation or a counterexample
to the actual source sign.

Accordingly this increment asserts neither that D7 is negative nor that it
is positive. Closing the gate requires a source integral enclosure strong
enough to control the complete expression, possibly retaining correlations
between the integrals. Positivity of the individual integrals, the old
three-coordinate faces, and the remainder bound do not prove it.

The ONE remaining typed obligation is

```lean
0 < nativeSourceSevenEvenDiscriminant
```

or equivalently the explicit raw integral gap in the public theorem above.
No positivity hypothesis, desired-sign wrapper or target-defined carrier
is introduced to fill it.

## Public surface, provenance and audit

39 public declarations are checked individually in
`CompletedNativeChiralReturnSevenBoundaryFaceAudit`, with
`#assert_prime_depth_source_axioms`, `#print axioms`, and the transitive
`#assert_oriented_green_source` closure check.

New formulas live in `CompletedNativeChiralReturnThirteenthSourceJet`,
`CompletedNativeChiralReturnSevenBoundaryFace`, and the exact finite-prefix
bridge `CompletedNativeChiralReturnSevenBoundaryRegularization`. The raw integral derivative
extension is appended to `CompletedNativeXiCosineMoments`, reusing its
existing dominated-derivative APIs. The root library and audit import the
new surface. Existing source/state definitions are not changed.

The proof dependency closure rejects canonical moments, HP/Stieltjes,
Hankel, Jacobi/height, Herglotz and BR2 declarations. Historical imports can
contain such declarations; the audited new proofs do not use them.
Allowed footprint: `[propext, Classical.choice, Quot.sound]` or a subset.

## Validation and publication

Commands required before publication:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeXiCosineMoments
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnThirteenthSourceJet
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenBoundaryFace
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenBoundaryRegularization
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenBoundaryFaceAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

All listed checks passed on `llm` before publication. The final source-only
closure check traversed 5,756 declarations for the 39 public additions.
Results and source/axiom outputs are retained in
`research/chiral-seven-boundary-face-2026-10-08/validation-summary.txt`
and its adjacent audit log. The two pre-existing untracked files remain
outside the commits. Main remains the normative formal checkpoint.

## Limit of this result

This closes an exact source reduction of the seven-coordinate margin.
It does NOT close N=7 storage positivity, the arbitrary-N Gamma inequality,
radial eventual contractivity, positive moment Grams or spectral conclusions.
The previous signed pairing and scalar source genealogy remain unchanged.
