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

`CarrySelfAdjointOperator/C2MellinLogMomentDerivative.lean` proves local analytic differentiation results for the same positive geometric density. The first differentiation-under-the-integral theorem now holds throughout `3/8 < s < 5/8`, not only at the midpoint:

```lean
nativeC2MellinGeometricSourceIntegral_hasDerivAt
nativeC2MellinGeometricSourceIntegral_hasDerivAt_half
nativeC2MellinGeometricLogMoment_one_hasDerivAt_half
nativeC2MellinGeometricSourceIntegral_iteratedDeriv_one_half
nativeC2MellinGeometricSourceIntegral_iteratedDeriv_two_half
```

The first theorem gives `deriv Z(s) = m₁(s)` throughout that open interval. The log-moment theorem differentiates `m₁` at `1/2` and gives `m₁'(1/2) = m₂(1/2)`. The two iterated-derivative theorems then establish the actual equalities `iteratedDeriv 1 Z (1/2) = m₁(1/2)` and `iteratedDeriv 2 Z (1/2) = m₂(1/2)`. The neighborhood identity is essential for the second equality: derivative facts only at the midpoint would not suffice. The first bound uses `|log x| ≤ 8 * (x^(1/8) + x^(-1/8))`, the density bound `density x ≤ 2 * exp(-x)`, and a four-term Gamma-integrable envelope uniformly for `3/8 < s < 5/8`. The second differentiation uses the two-term majorant `512 * exp(-x) * (x^(-7/8) + x^(-1/8))`. Each pointwise derivative is established before applying Mathlib's local dominated differentiation theorem. These are source-only results; they do not identify derivatives with those of the completed characteristic or canonical completed moments.

`CarrySelfAdjointOperator/C2MellinDensityCrosswalk.lean` closes the rational/geometric spelling gap against the legacy definitions in `C2MellinPositiveDensity.lean`:

```lean
nativeC2MellinDensity_eq_geometricDensity
nativeC2MellinSourceIntegral_eq_geometricSourceIntegral
nativeC2MellinLogMoment_eq_geometricLogMoment
nativeC2MellinIteratedDerivative_one_half
nativeC2MellinIteratedDerivative_two_half
```

The density equality follows pointwise for `x > 0` from `nativeC2MellinOmega0_eq_exp_sinh`; integral and every fixed log-moment equality follow by almost-everywhere integral congruence on `Ioi 0`. The last two results instantiate orders one and two of the legacy `nativeC2MellinIteratedDerivativeObligation` at `s = 1/2`. They do not prove that universal-in-order predicate.

## Axiom audit

`CarrySelfAdjointOperator/C2MellinComplexBridgeAudit.lean` prints axioms for the rate, bracket, aligned-cell, finite geometric-sum, closed-head, and finite-head integral theorems. Each reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; no project axiom, `sorry`, or `admit` was added.

`CarrySelfAdjointOperator/C2MellinInfiniteLimitAudit.lean` audits the two new convergence and source-identification theorems; both report only the same standard Lean axioms.

`CarrySelfAdjointOperator/C2MellinLogMomentDerivativeAudit.lean` audits the neighborhood derivative, actual first and second iterated derivatives, and first log-moment derivative. `CarrySelfAdjointOperator/C2MellinDensityCrosswalkAudit.lean` audits the density, integral, log-moment, and transferred derivative equalities. Every audited new theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Independent numerical probe in `~/temporario`

Read and ran `/home/thlinux/temporario/c2_mellin_cumulantes_probe.py` at its configured 55 decimal digits. It reconstructs the proposed source density from the seed and positive C2 cells, computes the log-Mellin cumulants, and only then adds the completion/camera term. The independent completed-characteristic check is used as a comparison, not as input to the construction.

The reproduced values are:

| order | source contribution | completion/camera | canonical sum |
|---|---:|---:|---:|
| `h0` | `2.41902789340156408442` | `-2.395922900286145113631` | `0.02310499311541897078893` |
| `h1` | `-8.100613329306168605299` | `8.100650501905453874985` | `0.00003717259928526968616487` |
| `h2` | `32.04427963450730340067` | `-32.04427949033337199969` | `1.441739314009732796954e-7` |

The script reports `kappa₂ = 4.83805578680312816884`, `kappa₄ = 97.20735995167402326358`, `kappa₆ = 7690.62711228175281616`, and the canonical `2 × 2` Hankel determinant `1.94933555481914221474e-9`. Its independent reference differences are about `5.2e-55`, `6.7e-51`, and `2.5e-47` for `h0`–`h2` respectively. These are reproducible high-precision quadrature diagnostics, not interval certificates. The exact toy transform `(3 + cos t)/4` also gives `h1 = -1/192`, demonstrating that positivity of a measure alone does not force positivity of the associated logarithmic-derivative coefficients.

These numerical results do not prove higher-order differentiation under the Mellin integral or any all-order canonical Hankel sign. The source identity and its first two iterated derivatives at `s=1/2` are Lean theorems for the hyperbolic geometric density, now transferred exactly to the legacy rational-density definitions.

## Validation run

- `lake env lean -DwarningAsError=true CarrySelfAdjointOperator/C2MellinComplexBridge.lean` — passed without warnings.
- `lake build CarrySelfAdjointOperator.C2MellinComplexBridgeAudit` — passed; rebuilt the bridge and audit module and printed the axiom results above.
- `lake build CarrySelfAdjointOperator.C2MellinComplexBridge` — passed (`3416 jobs`).
- `lake env lean -DwarningAsError=true CarrySelfAdjointOperator/C2MellinInfiniteLimit.lean` — passed without warnings.
- `lake build CarrySelfAdjointOperator.C2MellinInfiniteLimit` — passed.
- `lake build CarrySelfAdjointOperator.C2MellinInfiniteLimitAudit` — passed; the new limit and source-identification declarations have only standard axioms.
- `lake build --wfail CarrySelfAdjointOperator.C2MellinLogMomentDerivative` — passed (3,419 jobs), including the neighborhood derivative and iterated derivatives of order one and two.
- `lake build --wfail CarrySelfAdjointOperator.C2MellinLogMomentDerivativeAudit` — passed (3,420 jobs); audited declarations have only standard Lean axioms.
- `lake build --wfail CarrySelfAdjointOperator.C2MellinPositiveDensity` — passed after building its 9,639-target dependency tree.
- `lake env lean -DwarningAsError=true CarrySelfAdjointOperator/C2MellinDensityCrosswalk.lean` — passed without warnings.
- `lake build --wfail CarrySelfAdjointOperator.C2MellinDensityCrosswalkAudit` — passed (9,644 jobs); crosswalk and transferred derivative declarations have only standard Lean axioms.
- `python3 ~/temporario/c2_mellin_cumulantes_probe.py` — completed at the script's configured 55 decimal digits and reproduced the table above.
- `git diff --check` — to rerun before the continuation commit.

An earlier attempt to import `C2MellinPositiveDensity` stopped partway through its broad completion/Green and theta-certificate dependency tree. The continuation completed that tree through all 9,639 targets, allowing the crosswalk to be checked against the actual legacy declarations. This validates the Mellin-density and derivative modules, not the repository's full default target.

## First remaining gap

The limit `M → ∞` under the integral is proved for every fixed complex `s` with `Re(s)>0`, and the actual first and second iterated derivatives of the real source integral at `s=1/2` are identified with its logarithmic moments. The next concrete obligation is third and higher differentiation under that integral. For each fixed logarithmic order `r`, establish compact-parameter domination for

```text
x^(sigma-1) * |log x|^r * (exp(-x) + omega0(x)),
```

uniformly for `sigma` in compact subintervals of `(0,∞)`. Then formally express the source cumulants from these derivatives and combine them with the camera and completion derivatives to recover canonical moments. The current results supply source log-moments through order two, but do not yet formalize the cumulant conversion or the completion/camera combination. No cumulant identity with the completed moments and no canonical moment sign are claimed here.

## Publication

- Code commit SHA: `09a6603` (`Prove finite C2 complex Mellin head identity`).
- DCT continuation commit SHA: `9b69656` (`Prove infinite C2 Mellin source limit by dominated convergence`).
- First-derivative continuation commit SHA: `c260098f780e8847513acb0e7488bc15a38cee41` (`Prove first C2 Mellin source derivative at half`).
- Second-derivative continuation commit SHA: `43338936be2d91b83ea2d24a085f8611e49c47df` (`Prove second C2 Mellin source derivative at half`).
- Draft PR URL: https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/127
- Published branch: `luna/c2-mellin-complex-bridge-20261117`.
