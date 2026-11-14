# Radial first correction checkpoint — 2026-11-14

## Completed and compiled

- **C1, arbitrary dimension:** `CarrySelfAdjointOperator/RadialVandermondeJetRecurrence.lean` proves the nodal-polynomial moment recurrence, exact divisibility of every high coordinate by its required power of the radial parameter, and the coefficient `e₁ x_(N−1)` in the first high coordinate.
- **C2, arbitrary dimension:** `CarrySelfAdjointOperator/CompletedNativeRadialFirstCorrectionAllOrder.lean` defines a finite response prefix, proves its boundary value is `nativeSourceFiniteBoundaryEnergy`, and identifies its first derivative with
  `4 e₁ Σ_{0≤j<N, 0≤2j−N<N} (-1)^(j+N) β_j Re(conj(x_(2j−N)) x_(N−1))`.
- The correction is represented by a real symmetric matrix `u e_lastᵀ + e_last uᵀ`; its quadratic form is proved equal to the coefficient formula and its rank is at most two.
- The coefficient vanishes on both pure parity sectors; the `N=1` case is proved separately.
- For nodes `1,…,7`, the explicit source inverse is proved to be the Vandermonde inverse. The full finite response prefix is identified pointwise in the radial parameter with the existing `radialSevenRegularizedBoundaryEnergy`, and the general derivative recovers `radialSevenBoundaryFirstCorrection`.
- The source normalization is explicit: `nativeSourceOddBoundaryCoefficient j = 2 * primeDepthGeometricMoment j`; the response itself carries its existing outer factor `2`.

## Validation

Both Lean modules compile with Lean `4.32.0` and `-DwarningAsError=true` against the pinned dependency snapshot rooted at commit `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. `#print axioms` on the recurrence, coefficient, matrix, parity, `N=1`, seven-sample and chart-identification theorems reports only Lean's standard `propext`, `Classical.choice` and `Quot.sound`. The two new Lean files contain no `sorry`, `admit` or new axioms.

The accompanying `verificar_sinal_all_order.py --exact-only` regression completed: 36 exact rational radial checks through second order for `2≤N≤10`, plus its other exact checks. These finite checks supplement, and do not replace, the arbitrary-`N` Lean proofs.

## Scope boundary / next step

C3 was **not started**. No infinite-series convergence or analytic remainder estimate for arbitrary `β` is claimed: C2 differentiates the finite prefix that contains every summand able to affect the boundary value or first derivative. The quadratic coefficient `Q_N`, its rank-four representation and its last-coordinate sign control are the next isolated task.

This checkpoint is based on `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`, in branch `codex/radial-first-correction-all-order-20261114`. It does not modify the shared checkout, its toolchain or the root aggregator.
