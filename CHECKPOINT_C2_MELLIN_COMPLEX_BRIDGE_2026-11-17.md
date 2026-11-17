# Checkpoint — complex Mellin bridge for the C2 source

## Repository state

- Repository: `thiagomassensini/carry-self-adjoint-operator`
- Worktree: `/home/thlinux/worktrees/luna-c2-mellin-complex-bridge-20261117`
- Branch: `luna/c2-mellin-complex-bridge-20261117`
- Base: `origin/main` at `f1df607ee46dc9a7127fc9b3cd1aa3bcdc574aa4`
- Main checkout: left untouched; it already had user changes on another branch.
- Existing code commit: `09a6603`; current branch includes the DCT continuation below.
- Draft PR: https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/127

## Results proved

`CarrySelfAdjointOperator/C2MellinComplexBridge.lean` formalizes the Mellin transform at the level of the original C2 bracket cells.

For every complex `s` with `0 < s.re` and every positive real rate `r`,

```lean
nativeC2MellinComplexRateIntegral
```

proves that the integral of `x^(s-1) * exp(-r*x)` is `Gamma(s) * r^(-s)`. The proof uses Mathlib's complex Euler Gamma integral and separately establishes integrability of each scaled exponential leg.

For every real center `c` with `1 < c`,

```lean
nativeC2MellinComplexBracketIntegral
```

proves the exact three-leg identity

```text
∫ x^(s-1) (exp(-(c-1)x) - 2 exp(-cx) + exp(-(c+1)x)) dx
  = Gamma(s) ((c-1)^(-s) - 2 c^(-s) + (c+1)^(-s)).
```

No positivity hypothesis is used.

The pointwise identity

```lean
nativeC2MellinCellKernel_eq_centered_exponentials
```

shows that `exp(-c*x) * 4*sinh(x/2)^2` is exactly the positive hyperbolic form of the same centered second difference. Specializing to the repository's aligned centers gives

```lean
nativeC2MellinComplexPositiveCellIntegral
```

with right side `Complex.Gamma s * centerBracketTerm 2 s index`.

Two finite-head results are now proved:

- `nativeC2MellinFinitePositiveCellSum_eq_geometric`: the first `M` positive hyperbolic cells sum to the closed geometric factor `(1-exp(-4Mx))*exp(-4x)*K/(1-exp(-4x))`, where `K=4*sinh(x/2)^2`.
- `nativeC2MellinComplexFiniteHeadIntegrand_eq_closed_form`: pointwise identification of the seed plus those cells with the closed finite-head expression.
- `nativeC2MellinComplexFiniteHeadIntegral`: for every natural cutoff `M` and `0 < s.re`, the Mellin integral of the finite positive-cell head equals `Complex.Gamma s * finiteBracketCharacteristic 2 M s`.

The closed expression for the cell mass is the hyperbolic form already identified with `nativeC2MellinOmega0` by the existing `nativeC2MellinOmega0_eq_exp_sinh` theorem. This module imports the original bracket definitions directly and deliberately keeps the proof independent of the large completion/Green import tree.

`CarrySelfAdjointOperator/C2MellinInfiniteLimit.lean` closes the next obligation for the geometric hyperbolic density without importing the large completion/Green dependency tree. It proves an explicit algebraic form and bound for

```text
omega₀(x) = exp(-4x) * 4*sinh(x/2)^2 / (1-exp(-4x)),
0 < omega₀(x) ≤ exp(-x)  for x > 0.
```

It then applies dominated convergence to the finite-head integrands with majorant `2 * exp(-x) * x^(Re(s)-1)`, integrable by Euler's Gamma integral whenever `Re(s)>0`:

- `nativeC2MellinComplexFiniteHeadIntegral_tendsto_source` proves convergence of the integrals to the integral of the infinite positive geometric source.
- `nativeC2MellinComplexGeometricSourceIntegral_eq_gamma_bracketCharacteristic` identifies that infinite source integral exactly with `Complex.Gamma s * bracketCharacteristic 2 s`, using the existing convergence of the finite bracket characteristics.

The limiting density is kept in the original seed-plus-hyperbolic-cell form. The pre-existing `nativeC2MellinOmega0_eq_exp_sinh` is the exact bridge to the repository's rational density spelling; it was not imported into this focused module because that import pulled in the broad completion/Green and theta-certificate dependency tree. No moments, camera, seed, or completion factor were redefined.

## Axiom audit

`CarrySelfAdjointOperator/C2MellinComplexBridgeAudit.lean` prints axioms for the rate, bracket, aligned-cell, finite geometric-sum, closed-head, and finite-head integral theorems. Each reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; no project axiom, `sorry`, or `admit` was added.

`CarrySelfAdjointOperator/C2MellinInfiniteLimitAudit.lean` audits the two new convergence and source-identification theorems; both report only the same standard Lean axioms.

## Independent numerical probe in `~/temporario`

Read and ran `/home/thlinux/temporario/c2_mellin_cumulantes_probe.py` at its configured 55 decimal digits. It reconstructs the proposed source density from the seed and positive C2 cells, computes the log-Mellin cumulants, and only then adds the completion/camera term. The independent completed-characteristic check is used as a comparison, not as input to the construction.

The reproduced values are:

| order | source contribution | completion/camera | canonical sum |
|---|---:|---:|---:|
| `h0` | `2.41902789340156408442` | `-2.395922900286145113631` | `0.02310499311541897078893` |
| `h1` | `-8.100613329306168605299` | `8.100650501905453874985` | `0.00003717259928526968616487` |
| `h2` | `32.04427963450730340067` | `-32.04427949033337199969` | `1.441739314009732796954e-7` |

The script reports `kappa₂ = 4.83805578680312816884`, `kappa₄ = 97.20735995167402326358`, `kappa₆ = 7690.62711228175281616`, and the canonical `2 × 2` Hankel determinant `1.94933555481914221474e-9`. Its independent reference differences are about `5.2e-55`, `6.7e-51`, and `2.5e-47` for `h0`–`h2` respectively. These are reproducible high-precision quadrature diagnostics, not interval certificates. The exact toy transform `(3 + cos t)/4` also gives `h1 = -1/192`, demonstrating that positivity of a measure alone does not force positivity of the associated logarithmic-derivative coefficients.

These numerical results do not prove differentiation under the Mellin integral or any all-order canonical Hankel sign. The infinite source identification is now a separate Lean theorem for the hyperbolic geometric density.

## Validation run

- `lake env lean -DwarningAsError=true CarrySelfAdjointOperator/C2MellinComplexBridge.lean` — passed without warnings.
- `lake build CarrySelfAdjointOperator.C2MellinComplexBridgeAudit` — passed; rebuilt the bridge and audit module and printed the axiom results above.
- `lake build CarrySelfAdjointOperator.C2MellinComplexBridge` — passed (`3416 jobs`).
- `lake env lean -DwarningAsError=true CarrySelfAdjointOperator/C2MellinInfiniteLimit.lean` — passed without warnings.
- `lake build CarrySelfAdjointOperator.C2MellinInfiniteLimit` — passed.
- `lake build CarrySelfAdjointOperator.C2MellinInfiniteLimitAudit` — passed; the new limit and source-identification declarations have only standard axioms.
- `python3 ~/temporario/c2_mellin_cumulantes_probe.py` — completed at the script's configured 55 decimal digits and reproduced the table above.
- `git diff --check` — to rerun before the continuation commit.

An initial attempt to import `C2MellinPositiveDensity` directly started a 9,641-target dependency build with large theta-certificate modules; it was stopped at 9,162 targets. The focal proof instead imports the pinned native bracket module and derives the required hyperbolic-density majorant locally, avoiding that broad dependency. This is a focal build, not the repository's full default target.

## First remaining gap

The limit `M → ∞` under the integral is now proved for every fixed complex `s` with `Re(s)>0`. The next concrete obligation is differentiation under that integral for logarithmic Mellin moments. For each fixed logarithmic order `r`, establish compact-parameter domination for

```text
x^(sigma-1) * |log x|^r * (exp(-x) + omega0(x)),
```

uniformly for `sigma` in compact subintervals of `(0,∞)`. Then identify derivatives of the source Mellin transform with the source log-moments/cumulants. The camera and completion derivatives still need to be combined with those source derivatives to recover the canonical moments. No cumulant identity with the completed moments and no canonical moment sign are claimed here.

## Publication

- Code commit SHA: `09a6603` (`Prove finite C2 complex Mellin head identity`).
- DCT continuation commit SHA: pending.
- Draft PR URL: https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/127
- Published branch: `luna/c2-mellin-complex-bridge-20261117`.
