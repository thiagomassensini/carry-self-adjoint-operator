# Six-camera intrinsic Weyl high-energy return

This crosswalk starts at `11228f8841bb80599b0fa0a722384c970e7d7841` and adds the
imaginary-axis, realified, finite-dimensional algebra needed for the intrinsic
six-camera Weyl block. The result is deliberately a reduction: the current
pin proves the exact coefficient decomposition and the scalar high-energy
remainder, but it does not yet prove that the finite operator remainder tends
to zero.

## Carriers and the imaginary axis

For a finite index type `ι`, the existing carriers are

```lean
FiniteCameraCoordinates ι := EuclideanSpace ℝ ι
FiniteCameraRealification ι :=
  WithLp 2 (FiniteCameraCoordinates ι × FiniteCameraCoordinates ι)
```

The six-camera carrier is `SixCameraRealification`, an abbreviation for the
case `ι = Fin 6`. The new parameterization is

```lean
imaginarySpectralParameter eta := Complex.I * (eta : ℂ)
imaginarySpectralParameterNat n :=
  imaginarySpectralParameter ((n + 1 : ℕ) : ℝ)
```

The proved simplifiers give real part zero, imaginary part `eta` (or `n+1`),
and a nonzero imaginary part on the positive axis. The realified complex
structure is the existing block map

```text
J (x,y) = (-y,x)
```

called `finiteCameraComplexStructure`. The theorem
`finiteCameraComplexStructure_sq` proves `J (J z) = -z`. This is the real
carrier representation of multiplication by `i`; no complex camera carrier
is introduced.

The real matrices `sixCameraLogOperator`, `sixCameraWhitenedSecondMoment`, and
`sixCameraVariance` are lifted diagonally by
`finiteCameraRealifiedMatrixOperator`. The resulting blocks commute with `J`.
This keeps the two real quadratures separate and makes the coefficient in the
scaled imaginary-axis limit appear as `J` applied to the real variance block.

The older `sixCameraRealifiedCauchyCompression` remains a component-style
embedding from `EuclideanSpace ℝ (Fin 6)` into the first coordinate of the
ambient realification. The new `sixCameraImaginaryAxisCauchy` uses the full
`SixCameraRealification` block supplied by
`FiniteCameraRealifiedCauchyInvertibility`; the two objects are not silently
identified.

## Exact normalized Cauchy/Weyl algebra

For `eta = n+1`, the new definitions are

```lean
sixCameraImaginaryAxisCauchy n
sixCameraImaginaryAxisNormalizedCauchy n
sixCameraImaginaryAxisNormalizedWeyl n
```

The normalized Cauchy map is `eta • J ∘L C_n`. The normalized Weyl map is the
intrinsic inverse composed with `-eta⁻¹ • J`. The following identities are
proved pointwise and as continuous-linear-map equalities:

```lean
sixCameraImaginaryAxisNormalizedWeyl_comp_cauchy
sixCameraImaginaryAxisNormalizedCauchy_comp_weyl
sixCameraImaginaryAxisNormalizedWeyl_comp_cauchy_clm
sixCameraImaginaryAxisNormalizedCauchy_comp_weyl_clm
```

Thus the normalization is an exact two-sided inverse construction; it is not a
formal asymptotic inverse. The theorem
`sixCameraIntrinsicWeylBlock_eq_normalizedWeyl_comp_scale` restores the
intrinsic Weyl from the normalized inverse at `lambda = i (n+1)`.

The exact scalar identity

```text
(λ-y)⁻¹ = λ⁻¹ + λ⁻² y + λ⁻² y² (λ-y)⁻¹
```

is recorded by `scalar_imaginary_axis_resolvent_third_order` and its scaled
version `scalar_imaginary_axis_resolvent_scaled_remainder`. The ratio

```text
(i eta)/(i eta-y)
```

has a proved limit `1` and, for `eta > 0`, norm at most `1`:

```lean
imaginary_resolvent_ratio_tendsto
imaginary_resolvent_ratio_norm_le
imaginary_resolvent_ratio_tendsto_nat
imaginary_resolvent_ratio_norm_le_nat
```

These are scalar statements. They provide the correct second-moment
majorant, but the current module does not claim that dominated convergence has
already been transported through the Naimark integral and finite compression.

## Exact second-order decompositions

The named Cauchy remainder is
`finiteCameraNormalizedSecondOrderRemainder`. Its decomposition theorem is
pure finite-dimensional algebra:

```text
N = I - eta⁻¹ A - eta⁻² B + eta⁻² R_N(eta).
```

Specializing `A = J L₆` and `B = M₂` gives
`sixCameraImaginaryAxisNormalizedCauchy_second_order_decomposition`.

The inverse remainder
`sixCameraImaginaryAxisNormalizedInverseSecondOrderRemainder` is defined from
the already everywhere-defined intrinsic inverse. The theorem
`sixCameraImaginaryAxisNormalizedWeyl_second_order_decomposition` proves the
exact identity

```text
W_norm,n = I + eta⁻¹ F + eta⁻² (M₂ + F²)
           + eta⁻² R_W,n,
```

where `F = J L₆`. No convergence of `R_W,n` is built into this definition.

The matrix identity

```lean
sixCameraRealifiedSecondMoment_sub_logSquare
```

proves `M₂ - L₆² = V₆` on the realified carrier. Together with
`finiteCameraComplexStructure_sq` and the commutation lemmas, this gives

```lean
sixCameraRealifiedSecondOrderCoefficient_apply_complexStructure
```

which identifies the quadrature-tested second-order coefficient with
`J (V₆ z)`.

## First-return reduction

The exact scaled first-return residual is
`sixCameraIntrinsicWeylFirstReturnResidual`. Its two key identities are

```lean
sixCameraIntrinsicWeylFirstReturnResidual_eq_coefficient_add_remainder
sixCameraIntrinsicWeylFirstReturnResidual_eq_variance_add_remainder
```

The second one says, for every finite realified vector `z`,

```text
Residual_n(z) = J (V₆ z) + R_W,n (J z).
```

The intrinsic expression itself is related to this residual by

```lean
sixCameraIntrinsicWeyl_first_return_eq_residual
```

namely

```text
eta • ( W₆(i eta) z - eta • J z + L₆ z ) = Residual_n(z).
```

Consequently the conditional theorem
`sixCameraIntrinsicWeyl_first_return_tendsto_of_inverse_remainder` proves

```text
R_W,n (J z) → 0
  ⟹ eta • (W₆(i eta)z - eta • Jz + L₆z) → J (V₆ z).
```

In the usual complex convention this is exactly the statement that the
coefficient of `1/λ` in

```text
W₆(λ) = λ I - L₆ - V₆ / λ + ...
```

is `-V₆`. On the positive imaginary axis, multiplying the centered expression
by `eta` produces the realified limit `+ J (V₆ z)`. The sign difference is the
factor `1/(i eta) = -i/eta`, represented by `J` in the realification.

What is still missing is the analytic premise

```text
sixCameraImaginaryAxisNormalizedInverseSecondOrderRemainder n (J z) → 0.
```

The repository currently has no theorem proving that limit (in pairing,
application, or operator norm) for this finite compressed Cauchy family. The
new exact residual identities isolate that one seam without changing the
upstream definitions.

## Scope and non-identifications

No cutoff limit, camera-growth limit, `Dom(Y²)` argument, `Big-O` notation,
determinant calculation, `allBasesWeylInverse`, or equality between an inverse
of a compression and a compression of an inverse is used. No Jacobi, Hankel,
TFVD, Green, halo, Gpre, Genuine/zero, or spectral conclusion is used. Existing
halo and global-escape variance decompositions remain available upstream, but
they are not used to prove the high-energy remainder limit here.

## Answers to the required audit questions

1. **Parameterization.** The proved sequence is
   `lambda_n = imaginarySpectralParameterNat n = i * (n+1)`, with the general
   real parameter `imaginarySpectralParameter eta = i * eta`.
2. **Multiplication by `i`.** It is `finiteCameraComplexStructure`, the block
   `(x,y) ↦ (-y,x)`, with square `-I`.
3. **Realified log operator.** It is the diagonal block
   `finiteCameraRealifiedMatrixOperator sixCameraLogOperator`.
4. **Realified variance.** It is the diagonal block
   `finiteCameraRealifiedMatrixOperator sixCameraVariance`.
5. **Second-moment control.** The scalar remainder is reduced to `y²` times a
   ratio with norm at most one. A finite compressed/operator dominated-
   convergence theorem is not yet present, so the full remainder control is
   still open.
6. **`Dom(Y²)`.** It is not used.
7. **Cauchy expansion.** The exact second-order decomposition is closed; the
   high-energy `Tendsto` for the finite Cauchy remainder is not.
8. **Convergence notion.** Scalar ratio convergence is `Tendsto` at `atTop`;
   the first-return result is conditional pointwise `Tendsto` in the finite
   realification. No operator-norm high-energy limit is claimed.
9. **`lambda * M(lambda) → I`.** Not proved.
10. **Inverse identity.** `inverse_one_add_exact` and
    `finiteCameraIntrinsicWeyl_inverse_second_order_exact` provide an exact
    finite algebraic identity.
11. **Uniform inverse bound.** Not needed for the exact identities and not
    proved uniformly in `n`.
12. **Inverse expansion.** It is an exact expansion with the named remainder
    `R_W,n`; it is not yet an asymptotic expansion with a vanishing error.
13. **Formula for `W(i eta)`.** Exactly, the first-return identity gives
    `W(i eta)z = eta • Jz - L₆ z + eta⁻¹ • J(V₆ z)
    + eta⁻¹ • R_W,n(Jz)`.
14. **Coefficient sign.** Algebraically the `1/lambda` coefficient is
    `-sixCameraVariance`; the unconditional limit certificate is the remaining
    inverse-remainder seam.
15. **Scaled-axis sign.** The conditional positive-axis limit is
    `+ J (sixCameraRealifiedVariance z)`.
16. **Halo plus escape.** The prior theorem
    `sixCameraVariance_eq_globalHaloGram_add_globalNaimarkEscapeGram` is still
    available, but no new transport of that decomposition into a high-energy
    limit is asserted here.
17. **Halo nontriviality.** The imported prior module already has a centered
    six-camera halo witness; it is not used in the remainder derivation.
18. **Jacobi/Hankel.** None was used.
19. **`allBasesWeylInverse`.** It was not used.
20. **Inverse/compression interchange.** It was not assumed.
21. **Cutoff.** No camera or TFVD cutoff is used.
22. **Genuine/zero hypotheses.** None is used.
23. **Next minimum theorem.** Prove
    `sixCameraImaginaryAxisNormalizedInverseSecondOrderRemainder n (J z) → 0`.
    The shortest route is first to prove the corresponding normalized Cauchy
    second-order limit from the scalar ratio using the existing finite Naimark
    synthesis, then use finite-dimensional inverse continuity (or an exact
    algebraic bound) to transfer it to `R_W,n`.
24. **Next direction.** The immediate next step is this six-camera finite
    analytic remainder theorem, followed by an arbitrary finite-atlas version.
    Mixed-mode scalarization is a later gate.

## Axioms and validation boundary

The audit file prints axioms for the axis, exact inverse, scalar remainder,
realified coefficient, and conditional first-return declarations. They use
only the project's accepted standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). No new axiom or proof placeholder is introduced.
