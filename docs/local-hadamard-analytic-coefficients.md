# Analytic → formal Hadamard coefficient bridge (2026-11-20)

**Formalized and kernel-checked:** the Taylor coefficients of the analytic simple-zero quotient are exactly those supplied by the native completed characteristic, in every order, and this readout is camera/cutoff-independent.

## Statement and provenance

The source is the completed characteristic `F=completedNativeOperatorCharacteristic`, itself assembled from the native bracket/Genuine pipeline and the separate archimedean completion. The bracket operator, Genuine and `F` are not conflated.

Let `gamma : ℝ` satisfy the explicit assumptions:
- `gamma` is in `completedNativeHeightDomain`;
- `F(gamma)=0`;
- `F'(gamma) ≠ 0` (a simple real zero).

There exists `g : ℂ → ℂ` analytic at `0` with

```text
g(0) = 1
g(v) = F(gamma+v)/(v*F'(gamma))   for v ≠ 0
iteratedDeriv n g 0 / n!
  = (iteratedDeriv (n+1) F gamma / (n+1)!)/F'(gamma)
  = nativeLocalDeflatedCoefficient gamma n.
```

This is a **full all-order coefficient equality**. It follows from the analytic Taylor factorization `F(gamma+v)=v*u(v)`, the iterated derivative identity
`(v*u(v))^(n+1)(0)=(n+1)*u^(n)(0)`, and the factorial shift.

Theorem `completedNative_simpleZero_deflatedGerm_coefficients` proves this, building on the general lemma `analyticSimpleZero_normalizedDeflatedGerm_coefficients`.

The theorem `cameraLocalHadamard_analyticReadout` further states that for every supported camera `2 ≤ camera` and cutoff:
1. the camera deflated coefficient agrees with the analytic Taylor coefficient of this same `g` for every `n`;
2. the local Hadamard moments `S_m` computed from those Taylor coefficients agree exactly with the camera readout for every `m`.

Combining with `LocalHadamardFormalSeriesBridge.lean`, the formal series of `g` has logarithmic derivative `A'/A` and yields `S6 = -[X^5] A'/A`, `S7=[X^6] A'/A`. These are now linked to an **actual analytic function**, not an independently stipulated coefficient list.

## What is *not* claimed

- The proof **assumes** the anchor zero exists and is simple. It does not construct zeros from an operator or prove RH.
- An analytic representation by a sum over all zeros (a global Hadamard product) is not used or established here.
- Certification of gap estimators still requires rigorous tail bounds on the *other zeros'* contributions.
- No infinite-dimensional positivity or completed Green sign closure follows.

## Check

```sh
lake build --wfail CarrySelfAdjointOperator.LocalHadamardAnalyticCoefficientAudit
lake env lean CarrySelfAdjointOperator/LocalHadamardAnalyticCoefficientAudit.lean
bash scripts/static_audit.sh
lake build --wfail CarrySelfAdjointOperator
```

This module closes the specific analytic ↔ formal coefficient seam left open in the previous two modules.
