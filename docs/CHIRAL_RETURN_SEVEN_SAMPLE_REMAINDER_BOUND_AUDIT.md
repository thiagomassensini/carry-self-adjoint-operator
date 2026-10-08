# Complete seven-sample analytic remainder bound

## Checkpoint and scope

Initial published `main`: `47ec4f54ee5a9d58da2d20254f86347ac4275261`.
`git pull --ff-only` returned already up to date; HEAD/main/origin/main agreed.
The two pre-existing untracked files `C2OddTfvdTransport.lean` and
`C2OddTfvdTransportAudit.lean` are preserved and excluded from task commits.

Status: `PASS_SEVEN_SAMPLE_COMPLETE_SOURCE_REMAINDER_BOUND`.
The all-order Gamma inequality remains
`PARTIAL_ALL_ORDER_CHIRAL_RETURN_CORRECTION_BOUND`.
This increment proves a **uniform remainder estimate for N=7**, not the sign
of the complete seven-coordinate boundary face, seven-sample storage
positivity, or arbitrary-N contractivity.

## Source and complete geometric coordinates

The existing radial grid is unchanged: node multipliers 1,...,7 and
`h_k = radialFourSourceStep k = 1/(k+1)`. The historical name of the step
does not change its meaning. Let

```text
b_a(d) = sum_i d_i (i+1)^a,
x_a = h^a b_a(d),   a=0,...,6.
```

`radialSevenBoundaryInverseCoefficients` is the rational inverse of the
Euler evaluation matrix at those seven nodes. Its coefficients come ONLY
from that matrix; both inverse identities are proved in Lean. It neither
uses moment values nor calibrates a metric. The geometric input is

```text
d_i(h,x) = sum_a W_ia h^(-a) x_a.
U_i(h,x) = sum_a W_ia h^(6-a) x_a = h^6 d_i(h,x).
```

All seven source coefficients and boundary coordinates are retained. The
change of coordinates is invertible for nonzero h. The finite Pi norm
`norm(x)` (the existing maximum norm on `Fin 7 -> Complex`) is used only
for a compact coordinate sphere and the bound. No Hilbert metric on the
original Cauchy source is changed.

## Actual completed source expansion

The source is the existing transverse completed logarithmic response

```text
f(y) = -I * completedNativeOperatorLogDerivative (I*y).
```

`nativeSourceLogSlope_analyticAt` and the analytic Taylor theorem give an
analytic R at zero such that locally

```text
f(y) = sum_{m<14} y^m/m! * iteratedDeriv m f 0 + y^14 R(y).
```

All degrees 0,...,13 are kept, including coefficients that may later be
shown zero by parity. No parity simplification or coefficient sign is
needed here. The same source-derived R works eventually at ALL seven
original radial nodes. The statement is
`radialSevenSourceTaylorTemplate_eventually_eq_slopes`.

The construction uses the actual completed response, so it does not
replace its tail, chart or completion by a finite proxy. It adds no new
source, radial grid, metric, or positivity premise.

## Synthesis before the mixed readout

Let `A_k(d) = radialIncidentSynthesis k 7 d`. The entire remainder vector is

```text
E_k(h,x) = A_k(d_i(h,x) * radialCompletedSlope k i)
         - A_k(d_i(h,x) * TaylorPrefix((i+1)*h)).
```

It lives in the unchanged `CanonicalCompletedNativeChiralCauchyCarrier`.
`radialSevenSourceTaylorTemplate_synthesis` proves the full vector
prefix-plus-remainder identity. No scalar projection is used to reconstruct
this vector. At the actual source nodes it equals

```text
A_k(d_i(h,x) * h^14 * (i+1)^14 * R((i+1)*h)).
```

For `(k+1)*h=1`, `radialSevenSourceRemainder_energy` proves exactly

```text
4 Re(inner A_k(d(h,x)) E_k(h,x))
 = 4h Re(sum_{i,j<7}
     conjugate(U_i(h,x)) U_j(h,x) (j+1)^14
       R((j+1)*h)/(i+j+2)).
```

All 49 ordered i/j pairings are present. Mathlib's first argument is
conjugate-linear. The factor h follows from `h^14 * h^(-12) * h^(-1)`:
source remainder order, two input factors, and the original Cauchy metric.
It is not a new weight or a fitted constant.

## Uniform bound and quantifiers

The double sum's real part, `radialSevenRemainderQuadraticReadout R h x`,
is jointly continuous at each `(0,x)` and homogeneous of degree two.
Compactness of the finite unit sphere gives ONE neighborhood of h=0 and
ONE positive finite constant for ALL x. Homogeneity extends the bound
from the sphere to every coefficient vector, including cancellation
vectors. No sign of the quadratic readout is assumed.

The generic energy estimate is

```text
exists C>0, eventually h near 0, forall x,
  abs(radialSevenRegularizedRemainderEnergy R h x)
    <= C * abs(h) * norm(x)^2.
```

The actual source supplies R, and the existing step tends to zero, yielding

```text
radialSevenSourceTaylorRemainder_eventually_abs_bound:
exists C>0, eventually k, forall x : Fin 7 -> Complex,
  abs(4 Re(inner A_k(d(h_k,x)) E_k(h_k,x)))
    <= C * h_k * norm(x)^2.
```

`radialSevenOriginalSourceRemainder_eventually_abs_bound` rewrites the same
estimate for EVERY original d, with right side
`C*h_k*norm(radialSevenScaledBoundary h_k d)^2`. The quantifier order is
`exists C, eventually k, forall d`; neither threshold nor constant depends
on the chosen direction. The constant is existential, not numerically
optimized, and no dependence uniform in N is claimed.

## Public surface and audits

26 public definitions/theorems in:

- `CompletedNativeChiralReturnSevenBoundaryReconstruction`
- `CompletedNativeChiralReturnFourteenthSourceRemainder`
- `CompletedNativeChiralReturnSevenRemainderBound`

All are listed individually in
`CompletedNativeChiralReturnSevenRemainderBoundAudit`, with both axiom
assertions and `#print axioms`, followed by the source-only transitive
closure audit. They are integrated into the root library/audit.

Allowed footprint: `[propext, Classical.choice, Quot.sound]` or a subset.
The dependency closure rejects canonical moments, HP/Stieltjes,
Hankel, Jacobi/height, Herglotz and BR2 declarations. Imported historical
modules may contain downstream theorems, but none is used by the new
proofs. This is a proof dependency audit, not a claim that the entire import
hierarchy contains no downstream material.

## Validation and publication

Required successful commands before commit/push:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenBoundaryReconstruction
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnFourteenthSourceRemainder
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenRemainderBound
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenRemainderBoundAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

Final result and log locations are recorded in the validation artifact
`research/chiral-seven-sample-remainder-2026-10-08/validation-summary.txt`.
Source closure and new axiom outputs are retained in that folder.

## Next gate

The remainder's size/rate is now controlled, including near cancellation
directions. The next source-first obligation is to identify and prove a
positive uniform margin for the COMPLETE seven-coordinate boundary face
of the original degree-thirteen source prefix. Its new fourth even
coordinate and the old odd coordinates must be kept together. That face
has not been declared positive here. The lower-order source sign facts do
not automatically imply positivity of its entire polarized form.

The analytic remainder above is distinct from the raw Gamma--Wronskian
sewing correction. This estimate alone does not prove the arbitrary-N
one-sided Gamma bound or chiral eventual contractivity. No all-order
positivity, moment Gram, spectral conclusion or strictness is asserted.
