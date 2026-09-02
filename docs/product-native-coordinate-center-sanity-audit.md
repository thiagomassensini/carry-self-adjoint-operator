# Product native-coordinate center sanity audit

## Scope

This audit performs the center test requested before any construction of a
coupled xi/native Green kernel.  It uses no theta representation, zero data,
confinement statement, `h1`, or all-order promotion.

Write

```text
g0 = normalizedCompletedGreenState
       nativeHeightScalar
       canonicalCompletedOperatorC3HilbertState
       0.
```

If a positive Hilbert product state has

```text
Psi_product(0) = xi0 ⊕ g0
```

and center Gram `h0`, positivity forces the necessary inequality

```text
||g0||^2 <= h0.
```

The Lean theorem
`norm_sq_normalizedCompletedNativeC3State_zero_le_h0_of_productGram`
formalizes this implication for every xi Hilbert carrier and every xi state.

## Exact center Gram

At `operatorHeightParameter 0 = 1/2`, the radial phase coefficient of the
first finite C3 leg is exactly one.  Hence the two legs of
`finiteC3GenuineBracketGreenBoundaryPair 3` coincide.  Lean proves

```text
||canonicalCompletedOperatorC3HilbertState 0||^2
  = 2 * ||finiteC3Port(1/2).snd||^2.
```

The factor `2` is cancelled exactly by the `sqrt 2` in
`normalizedCompletedGreenState`.  Therefore

```text
||g0||^2
  = ||finiteC3Port(1/2).snd||^2 / ||nativeHeightScalar 0||^2

  = [sum n : Fin 3,
       ||positiveDirichletGradient (1/2) n||^2]
      / ||riemannZeta (1/2)||^2.
```

These are theorems
`norm_sq_normalizedCompletedNativeC3State_zero_eq_finiteLeg`,
`norm_sq_normalizedCompletedNativeC3State_zero_eq_finThreeSum`, and
`norm_sq_normalizedCompletedNativeC3State_zero_eq_zeta_finThreeSum`.
They contain no still-abstract xi state and no Green-representation
hypothesis.

## Numerical comparison

An 80-decimal evaluation of the literal finite sum and the classical central
zeta value gives

```text
zeta(1/2)                         ~= -1.4603545088095868128894991525152980
sum of the three gradient squares ~=  0.1086062541762198206234011370530473
||g0||^2                          ~=  0.0509258449459957619006901269636560
```

Independently, evaluating the exact completed-characteristic curvature

```text
h0 = xi''(1/2) / (2 * xi(1/2))
```

gives

```text
h0                                ~= 0.0231049931154189707889338104303390
||g0||^2 - h0                     ~= 0.0278208518305767911117563165333170
||g0||^2 / h0                     ~= 2.2041056100558074559007116060610931.
```

The decimal evaluation is diagnostic and is not claimed as a kernel theorem
inside Lean.  The formula being evaluated, the cancellation of the two C3
legs against the normalization, and the necessary inequality are formal.

## Conclusion

The necessary center inequality fails decisively:

```text
||g0||^2 > h0.
```

Thus `canonicalCompletedOperatorC3HilbertState` cannot be the positive native
coordinate of the requested product carrier with the current normalization,
regardless of how the xi Hilbert space or `xiState` is chosen.  In particular,
no positive xi coordinate can repair the center, because it can only add a
nonnegative squared norm.

Following the requested stop condition, this audit does not define
`Delta_G`, `Delta_A`, or `K_xi_required`, and does not test hermiticity or
two-point positivity of that kernel.  Those questions become relevant only
after replacing or transporting the native coordinate so that the center
energy budget is satisfied.
