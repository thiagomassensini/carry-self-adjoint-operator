# Source-only order-twelve integral sign / six-coordinate boundary face

Initial audited main: `7205c30ff900be815d29a603f7c36d183e0a6002`.

## Scope and external reference

This round keeps the existing source polynomial, cosine integrals, signed
Green tower and six-coordinate face. It changes neither a carrier nor a
metric. The Liu–Mao coefficient enclosure motivated testing a sharper local
certificate; none of its numerical enclosures or its analytic error claims
is assumed by the Lean proof.

Reference: Yanxin Liu and Jianxi Mao, *Infinite log-concavity of the Taylor
coefficients of the Riemann xi-function*,
[arXiv:2610.04972v1](https://arxiv.org/abs/2610.04972).
The reference and the distinction between motivation and proof input are
recorded adjacent to the code in `CompletedNativeChiralReturnTwelfthSourceIntegral.lean`
and the generator. There is no literal port of their quadrature algorithm.

## Source provenance

Let `theta_p = completedNativeThetaTailMoment p`. The existing exact
integrations by parts give

```text
mu0 = 1/2 - theta0/4
mu1 = 2 theta0 - theta2/4
mu2 = 12 theta2 - theta4/4
mu3 = 30 theta4 - theta6/4
mu4 = 56 theta6 - theta8/4
mu5 = 90 theta8 - theta10/4
mu6 = 132 theta10 - theta12/4.
```

All seven integrals therefore retain their common source. They are not
replaced by independently fitted canonical moment values.

The refinement uses:

1. The second derivative of the existing first theta mode is decreasing for
   `u >= 0`; a right-endpoint curvature bound is therefore valid on every cell.
2. Integrate the same curvature-corrected source tangent at an already certified
   rational node, retaining its first-moment term when the node is not the
   weighted mean. Integrate the corrected chord for the upper bound.
3. Use 512 cells on `[0,1]`, reusing the earlier 1537 certified source nodes.
4. Retain the first-mode tail on both sides. For every natural power,
   its integral beyond 1 is at least `2/10^12`. Through power 12 it is at most
   `9/10^12`. The lower bound uses a source rectangle on `[1,65/64]`.
5. Retain every higher theta mode with the existing decaying majorant, adding
   `p!/(100000 * 23^(p+1))` to the upper bound.
6. Substitute these source enclosures into the unchanged twelfth mixed
   numerator. Its exact unit-cube polynomial identity is verified by `ring`;
   each monomial bound and the rational positive margin are kernel checked.

No HP/Stieltjes certificate, canonical moment sign, Hankel/Jacobi/height,
BR2, zero table or supplied spectrum is a proof premise. The dedicated
`#assert_oriented_green_source` traversal verifies the declaration dependency
closure with the preexisting classical-theta source exceptions unchanged.

## Certified theta box

These integers all have common denominator `10^15`:

| Power | Lower numerator | Upper numerator |
|---:|---:|---:|
| 0 | 11516617599405 | 11517069318739 |
| 2 | 247319838208 | 247322074809 |
| 4 | 20000462238 | 20000577037 |
| 6 | 2877024151 | 2877047408 |
| 8 | 589742473 | 589753563 |
| 10 | 155202273 | 155210624 |
| 12 | 49402687 | 49410222 |

Every bound refers to the original `completedNativeThetaTailMoment`.
The older independent-box obstruction remains valid for its older box;
this proof uses a sharper source enclosure and exact integrations by parts.

## New capstones

```lean
nativeSourceTwelfthMixedNumerator_gt_rational
nativeSourceTwelfthMixedNumerator_pos
nativeSourceSixOddDiscriminant_pos
nativeSourceSixOddBoundaryEnergy_pos
nativeSourceSixBoundaryEnergy_pos
```

The rational margin is `P12(mu0,...,mu6) > 1/10^19`. It yields strict
positivity for every nonzero `x : Fin 6 -> Complex` on the limiting boundary
face through the previously proved equivalence. All even, odd and mixed
source terms remain in that face.

## Boundary face versus finite-step storage

Closing the limiting face does not by itself close `ChiralReturn.storage`
at a nonzero radial step. The next obligation is uniform transport of the
existing exact remainder `nativeSourceTransverseSlope_six_exact_remainder`
through full six-coordinate synthesis. The threshold must be independent
of the coefficient vector. No N=6 storage contractivity or all-order
positivity is claimed here.

## Reproduction and validation

The generator `research/theta-twelfth-source-certificate-generate.py` reads
the existing source node certificates and the existing numerator declaration.
It requires SymPy only to emit exact rational algebra; Lean checks the output.
It reads no external coefficient archive. Regeneration into a temporary
output directory is compared byte for byte against the committed certificates.

Required builds and audits:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnTwelfthSourceIntegral
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnTwelfthSourceIntegralAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

All listed builds passed with `--wfail`; both audit scripts passed, and
`git diff --check` passed. The dedicated declaration audit checked 5314
reachable declarations with the source firewall unchanged. All new printed
capstones have footprint `[propext, Classical.choice, Quot.sound]`.
The generator reproduces every data file and both enclosure modules byte
for byte in a temporary directory. The server Python environment has no
SymPy; regeneration was checked locally against the source files copied
from this same main checkout. No dependency was installed or altered.

The initial monolithic polynomial elaboration was deliberately interrupted
and replaced by an equivalent 15-chunk proof, which compiled successfully.
The final checked arithmetic and the public theorem statement are unchanged.

Status: `PASS_SOURCE_FIRST_SIX_BOUNDARY_ENERGY_POSITIVITY`.
The finite-step N=6 storage/remainder gate remains open.

## Worktree preservation

Two unrelated files were already untracked at the start:
`CarrySelfAdjointOperator/C2OddTfvdTransport.lean` and
`CarrySelfAdjointOperator/C2OddTfvdTransportAudit.lean`.
They are preserved and excluded from this round's commits. All changes of this round are committed separately from those two files.
The working tree still has those two preexisting untracked files; it is
therefore not globally clean.
