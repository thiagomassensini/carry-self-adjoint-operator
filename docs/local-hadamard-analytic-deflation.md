# Analytic deflation at a simple completed-native zero

This file complements the [formal logarithmic derivative](local-hadamard-formal-series-bridge.md). The characteristic is the completed native function `F`, with its native/archimedean separation preserved upstream.

At any analytic function `f` with `f(0)=0` and `f'(0)≠0`, the theorem
`analyticSimpleZero_normalizedDeflatedGerm` builds an analytic `g` at zero satisfying:

```text
g(0)=1,
g(v)=f(v)/(v*f'(0))  for v≠0.
```

The construction uses Mathlib's analytic Taylor factorization at degree one; it does not assume a zero list or a Hadamard product.

The specialization
`completedNative_simpleZero_normalizedDeflatedGerm` applies this result to
`f(v)=F(gamma+v)` under the explicit hypotheses:

- `gamma` belongs to `completedNativeHeightDomain`;
- `F(gamma)=0`;
- `F'(gamma)≠0`.

Therefore the local normalized quotient genuinely has an analytic extension; its apparent pole at `v=0` is removable. This is kernel-checked, without RH or positivity.

**Remaining seam:** identification of the individual Taylor coefficients of the constructed extension with `F^(n+1)(gamma)/((n+1)! F'(gamma))`. The *formal* series defined by those expressions is already proved to obey `A'/A` in `LocalHadamardFormalSeriesBridge`, but the full analytic coefficient correspondence is not yet a Lean theorem. This also does not certify spectral remainder bounds or gaps.

Validation:

```sh
lake build --wfail CarrySelfAdjointOperator.LocalHadamardAnalyticDeflationAudit
lake env lean CarrySelfAdjointOperator/LocalHadamardAnalyticDeflationAudit.lean
```

## Follow-up: coefficient bridge closed

The analytic-to-formal Taylor coefficient identification left open in this
file is now proved in `LocalHadamardAnalyticCoefficient.lean`, including
universality of the camera readout of every `S_m`. See
[local-hadamard-analytic-coefficients.md](local-hadamard-analytic-coefficients.md).
Certified spectral gap tails remain a separate obligation.
