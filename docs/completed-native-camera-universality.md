# Exact camera-to-moment universality

This module joins the all-order camera bridge to the canonical moment and
operator construction. It applies to every integer camera `b >= 2`, every
cutoff, and every derivative order.

## Normalized characteristic

Let `C_{b,M}(t)` denote `completedNativeCharacteristic b M (nativeLine t)`.
It includes both the finite head and the exact analytic tail. Define

```text
F_{b,M}(t) = A(t) C_{b,M}(t) / kappa_b(t),
```

where `A` is `nativeXiCompletionFactor` and `kappa_b` is the existing camera
`factor`. The all-order bridge already supplies

```text
A(t) C_{b,M}(t) = kappa_b(t) F(t).
```

The camera factor is nonzero on the entire real height axis for every
supported base. The new normalization theorem therefore proves equality of
functions `F_{b,M} = F|_R`. The existing real/complex derivative theorem then
identifies every real derivative of `F_{b,M}` with the corresponding complex
derivative of `F` on that axis.

## Coefficients and moments

The camera coefficients are extracted from this normalized function:

```text
phi_{b,M,n} = Re(F_{b,M}^{(2n)}(0) / (2n)!).
```

The module constructs its own camera moment sequence recursively from these
coefficients:

```text
h_{b,M,n} = (-(n+1) phi_{b,M,n+1}
             - sum_{k<n} h_{b,M,k} phi_{b,M,n-k}) / phi_{b,M,0}.
```

It proves the denominator is nonzero, the recurrence holds, and the sequence
is the unique real solution of the division-free coefficient identity.
Every such sequence equals `canonicalCompletedNativeLogDerivativeMoment`.
The equivalence `completedNativeCamera_momentSequence_iff` also lets a
downstream construction supply its own sequence and prove the camera
recurrence to enter the existing completed-native moment interface.

## Exported results and hypotheses

| Declaration | Conclusion | Inputs beyond natural-number indices |
| --- | --- | --- |
| `normalizedCompletedNativeCameraCharacteristic_eq` | Exact equality with the common characteristic on the real axis | Camera at least 2 |
| `completedNativeCameraUniversality` | Equal jets, equal entire moment sequences, equal `G_N` and `K_N` for all orders | Both cameras at least 2 |
| `existsUnique_completedNativeCameraLogDerivativeMoment` | Unique real moment sequence from a camera's coefficients | Camera at least 2 |
| `completedNativeCamera_momentSequence_iff` | Camera recurrence iff the existing completed-native moment interface | Camera at least 2 |
| `completedNativeCamera_finiteJacobi_independent` | Equal canonical `J_N` matrices | Supported cameras and positive definite `G_N` |
| `completedNativeCamera_jacobiTower_independent` | Equal infinite coefficient matrices of the principal towers | Supported cameras and positive definite `G_N` at every order |
| `completedNativeCamera_finiteHeight_independent` | Equal finite height matrices `J_N^(-1/2)` | Supported cameras, positive definite `G_N` and `J_N` |

The scalar, coefficient, moment, and Hankel identities require no positivity
certificate. The operator statements retain the positivity needed by their
existing definitions. The infinite-tower statement concerns the coefficient
matrix selected by exact principal sections.

Cutoff independence concerns head plus exact tail. Estimates for truncated
tails, numerical zero convergence, and a uniform positive realization of
the logarithmic moments remain separate statements. This module adds no
dependency updates.

## Validation

The dedicated audit prints the dependencies of the new synthesis theorems
and is included in `scripts/audit.sh`.

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeCameraUniversalityAudit
bash scripts/audit.sh
```

Validated on the server on 2026-09-04 with the pinned Lean 4.32.0 toolchain:
the dedicated audit completed 4,039 jobs and the complete `scripts/audit.sh`
finished with `kernel audit passed`, including `BoundaryTraceAudit`.
The coefficient proof explicitly normalizes the real zero coerced into the
complex Taylor center with `Complex.ofReal_zero`. No theorem statement,
positivity hypothesis, or dependency pin was changed by that correction.
