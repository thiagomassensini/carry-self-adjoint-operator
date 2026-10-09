# Complete seven-source storage and the signed finite-step margin loss

## Checkpoint and scope

Initial published main: `84dce314e98251fbb2ceaddd33a6262f5dff80fc`.
`git pull --ff-only` returned already up to date. HEAD, main and origin/main
agreed before changes. The two pre-existing untracked files
`C2OddTfvdTransport.lean` and `C2OddTfvdTransportAudit.lean` are preserved
and excluded from staging. Previous research checkpoints are unchanged.

The previous raw-integral certificate of the complete seven-boundary
margin is reused. It is not reproved. The present gate is its transport
to the ACTUAL complete seven-node radial storage, and identification of
which correction prevents carrying the limiting energy unchanged.

Statuses:

- `PASS_SEVEN_SAMPLE_SOURCE_STORAGE_POSITIVITY`
- `PASS_SEVEN_SAMPLE_SIGNED_MARGIN_LOSS_DIAGNOSTIC`

These conclusions concern N=7, with one radial threshold for ALL coefficient
vectors. They do not assert arbitrary-N eventual contractivity or all-order
kernel positivity.

## Same completed source and complete vector synthesis

The source is still `completedNativeOperatorLogDerivative = -F'/F` with
the existing completion. Its raw odd coefficients are
`c_j = nativeSourceOddBoundaryCoefficient j`. No canonical moment sequence
is used to define the source or infer a sign.

`radialSevenOddSourceTemplate` repackages the ALREADY-proved seven-term
odd expansion at the original node multipliers 1,...,7, retaining the
entire analytic order-fourteen remainder R. The incident source and its
companion are synthesized in the original Cauchy carrier before taking
the mixed readout. The source grid, amplitudes, Cauchy inner product and
completed characteristic are unchanged.

`radialSevenOddSourceTemplate_synthesis` splits the completed vector into
its full odd prefix and remainder vector. Only afterward does
`radialSevenOddSourceTemplate_energy` identify their mixed readout with
`radialSevenRegularizedStorage`. All 49 ordered i/j terms in the remainder
remain present. No pointwise flux sign is assumed.

## Exact two-term correction

Let h=1/(k+1) and let x be the existing seven scaled Euler boundary
coordinates. Denote the certified boundary energy by E7(x), the full
finite-prefix energy by Eprefix(h,x), and the complete analytic remainder
readout by Erem(R,h,x). Then the kernel proves

```text
storage(k, normalized completed input(h,x),1).re
  = Eprefix(h,x) + Erem(R,h,x)                 eventually in k,
Eprefix(0,x) = E7(x),
Erem(R,h,x) = 4h Q_R(h,x),
full storage = E7(x) + [Eprefix(h,x)-E7(x)] + Erem(R,h,x).
```

The finite-prefix correction is `radialSevenBoundaryMarginLoss`. It is
distinct from the analytic source remainder. Substituting E7 at finite h
would prematurely discard higher reconstructed boundary coordinates.

## Uniform transport of the margin

The existing certificate supplies epsilon0>0 with
`epsilon0 * ||x||^2 <= E7(x)` in the unchanged finite Pi norm.
The complete regularized storage is jointly continuous at every (0,x).
Compactness of the unit sphere gives ONE neighborhood of h=0 on which

```text
forall x, ||x||=1 -> epsilon0/2 < full regularized storage(h,x).
```

This uses the entire completed storage, including the source remainder.
Homogeneity and the existing inverse boundary chart transfer the result
to every original coefficient vector. In sum-of-squares coordinates the
proof supplies the constant epsilon0/14 (no optimal value is claimed).
The Pi norm is a compactness/coordinate tool; the Cauchy Hilbert metric
has not been replaced.

Public capstones:

- `storage_one_sevenSample_eventually_boundary_coercive`
- `storage_one_sevenSample_eventually_pos`
- `storage_one_original_sevenSample_eventually_pos`
- `radialReturnTransfer_seven_eventually_norm_le_one`
- `chiralMultiplier_seven_eventually_contractive`

The order of quantifiers is `eventually k, forall coefficients`. It is
not a separate cutoff chosen for each vector.

## Which term changes the margin?

The original seven-node inverse fixes

```text
radialSevenHigherBoundaryCoefficient 7 6 = 28.
```

Here 28=1+...+7 is determined by the sampling geometry. The first higher
coordinate satisfies B7(0,x)=0 and B7'(0,x)=28*x6. Every Bm with m>7 has
zero first derivative. Differentiating the SAME complete signed prefix
therefore gives exactly

```text
L(x) = 112 * (
  -c4 * Re(conj(x1)*x6)
  +c5 * Re(conj(x3)*x6)
  -c6 * Re(conj(x5)*x6)).
```

This is an even/odd cross coupling, not a discarded positive diagonal.
The derivative of `radialSevenBoundaryMarginLoss` at zero is L(x).
For x1=x6=1 and all other coordinates zero, L(x)=-112*c4<0.
Changing x1 to -1 gives +112*c4>0. The sign c4>0 comes from the already
certified raw five-coordinate source face, not moment positivity.

The source's division-free derivative recurrence also kills its
fourteenth even derivative. Its own Taylor order-fifteen expansion
supplies the order-fourteen remainder R with R(0)=0. Consequently the
analytic remainder energy has zero first derivative at h=0. This is not
an assumption about its sign.

Hence the FULL completed storage has the same first correction L(x):
`storage_one_sevenSample_first_correction_tendsto` proves that its
boundary-energy difference divided by h converges to L(x). In the first
direction actual storage is eventually strictly BELOW E7(x); in the
opposite direction it is strictly ABOVE it. The kernel proves both
witnesses. Thus the limiting energy cannot simply be copied unchanged
at nonzero step. This does not prove that every possible coercive lower
bound is optimally diminished: it identifies the signed change in the
energy and proves that a reduced uniform margin still survives.

No uniform O(h^2) remainder theorem is claimed here. The zero derivative
and first-correction limits are fixed-direction statements; uniform
positivity is supplied separately by compactness of the complete energy.

## Provenance and trust

All new objects are scalar/algebraic packaging of existing source
expansions, boundary reconstruction, Cauchy synthesis and complete
storage. No new carrier, metric, fitted coefficient, spectral operator,
Hankel factor or positivity premise is introduced. BR2 is not used.

Dedicated audits check all 37 new public declarations with
`#assert_prime_depth_source_axioms`, explicit `#print axioms` and a
transitive source-only dependency traversal. The closure rejects canonical
moments, HP/Stieltjes certificates, Hankel, Jacobi/height, Herglotz and BR2
inputs. Allowed axioms are at most
`[propext, Classical.choice, Quot.sound]`. The storage audit traversed
5848 declarations and the margin-loss audit traversed 5591 declarations;
both source-only checks passed.

## Validation and changed files

Validation commands and outcomes are recorded in
`research/chiral-seven-storage-margin-2026-10-08/validation-summary.txt`.
Dedicated axiom/dependency outputs are preserved beside it. Validation
includes all new modules and audits under `--wfail`, the full library and
umbrella audit, both repository audit scripts, placeholder scans and
unstaged/staged `git diff --check`.

New modules:

- `CompletedNativeChiralReturnSevenSampleStorage.lean`
- `CompletedNativeChiralReturnSevenSourceRemainderParity.lean`
- `CompletedNativeChiralReturnSevenMarginLoss.lean`
- the two dedicated audit modules for storage and margin loss.

Integration changes: root imports, umbrella audit imports, README and this
append-only report. Existing source certificates and prior checkpoints
remain unchanged. Tracked work must be clean after publication; the two
pre-existing untracked files remain present by design.

## Next gate

For N=7 the boundary margin-to-complete-storage seam is closed. The next
source-only gate is the next boundary face (N=8), or a uniform-in-dimension
geometric argument that avoids proving a fresh raw source sign at every
new face. The present theorem supplies neither that arbitrary-N sign
nor all-order positive kernel closure.
