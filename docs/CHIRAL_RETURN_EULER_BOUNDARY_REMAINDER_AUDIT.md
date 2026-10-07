# Completed chiral return: positive Euler boundary and exact nonlinear remainder

## Main checkpoint and status

Initial published main: `ad4255a13223467720b07746484a1796b9d350d1`.
`git pull --ff-only`: already up to date. HEAD, main and origin/main agreed;
initial working tree clean. Work remains on main.

Local result: `PASS_SOURCE_EULER_BOUNDARY_ENERGY`.
Overall frontier: `PARTIAL_COMPLETED_SOURCE_ENERGY_POSITIVITY`.
The requested all-order bound `norm(radialReturnTransfer k N) <= 1`
**is not proved**. No native-source counterexample is proved either.

This round attacks the bound using the exact completed source and the
UNCHANGED Cauchy norm. It separates a positive boundary contribution from
a signed nonlinear remainder. The source is not replaced by its tangent.

## Audit and provenance

The original finite transfer, sourceValue/sourceCompanion and source/storage
identities are reused. Existing scalar Cayley factorization was audited in
`CompletedNativeChiralCayleyHerglotz`; its names and positivity consumers are
not inputs to the new proof. Its coordinate is definitionally the already
existing `completedNativeOperatorLogDerivative = -F'/F`.

The upstream raw analytic ingredient comes from
`CompletedNativeXiCosineMoments`, using:

- `XiThetaCosine.completedNative_eq_xiCosineKernel`;
- `completedNativeXiCosineTransformReal_zero`;
- `iteratedDeriv_two_completedNativeOperatorCharacteristic_zero`;
- `completedNativeXiCosineMoment_pos`.

These identify the actual completed characteristic with the existing theta
cosine source and its raw curvature with positive source integrals. The
integrals named `completedNativeXiCosineMoment` are polynomial integrals of
the positive theta kernel. They are **not** the canonical logarithmic moment
sequence and are not Hankel, HP or Herglotz positivity hypotheses.
The existing low-order Herglotz/Pick consumers were inspected but not used
to prove any new sign, and no low-order result is extrapolated to all N.

No metric, source, scalar completion or sampling grid is changed. No Gram
factor, alternative operator, new positive state or complementary norm is
constructed. The moment-independent source firewall checks both types and
values of every new declaration.

## Exact types and geometry

All new names are in `CarrySelfAdjointOperator.ChiralReturn`.

```lean
radialEulerSynthesis (k N : ℕ) (d : Fin N → ℂ) :
  CanonicalCompletedNativeChiralCauchyCarrier
radialCompletedSlope (k n : ℕ) : ℂ
radialCompletedValueCoefficients (k : ℕ) {N : ℕ}
  (c : Fin N → ℂ) : Fin N → ℂ
radialCompletedEulerScale (k : ℕ) : ℝ
radialCompletedEulerRemainder (k n : ℕ) : ℂ
radialCompletedRemainderSynthesis (k N : ℕ) (d : Fin N → ℂ) :
  CanonicalCompletedNativeChiralCauchyCarrier
```

The carrier stays `Lp ℂ 2 (volume : Measure unitInterval)`.
Write κ=k+1, zᵢ=`canonicalCompletedC3RadialTiltPoint k i`,
A(d)=`radialIncidentSynthesis k N d`, and uᵢ for its original half-density
features. Their pairing is κ/(i+j+2). The degree action is

```text
E(d) = A((i+1) dᵢ).
```

This degree belongs to the existing monomial/Cauchy feature basis. It is not
identified with material-edge number, C2 depth, camera label or height.

The exact normalized source coefficients and slope are

```text
dᵢ = cᵢ F(zᵢ) / P(zᵢ),
P = −F′ + I F,
bᵢ = −I (-F′(zᵢ)/F(zᵢ)).
```

F is the unchanged `completedNativeOperatorCharacteristic`. Thus the full
companion is `I • A(dᵢ bᵢ)` and the full value is A(d). These equalities are
proved at vector level from the complete source before taking the pairing.
All tails/Xi/chart completion remain those of the original completed F.
This does not recover a structured TFVD state from scalar traces.

## Polarized Green boundary identity

For arbitrary independent d,e, the kernel proves

```text
inner A(d) E(e) + inner E(d) A(e)
  = κ conj(sum dᵢ) (sum eᵢ).
```

The sum of the two native degrees cancels the Cauchy denominator exactly.
Mathlib conjugates the first argument; both ordered pairings and independent
coefficient families are retained. On the diagonal:

```text
Re inner A(d) E(d) = κ/2 * normSq(sum dᵢ).
```

This is endpoint energy. It is nonnegative but has rank at most one, not a
positive definite bulk bound. Every coefficient family with sum zero lies
in its nullspace. The first such nonzero family is d=(1,−1); its incident
vector is nonzero by the previously proved finite source injectivity.

## Source-derived scale, not a fitted coefficient

The degree scale is defined from the raw source curvature:

```text
αₖ = Re(-F″(0)/F(0)) / κ.
```

The raw theta source gives F(0)=μ₀ and F″(0)=−μ₂, with μ₀,μ₂ strictly
positive integrals of that source. Hence the kernel proves

```text
αₖ = (μ₂/μ₀)/κ > 0.
```

Here μ₀=`completedNativeXiCosineMoment 0` and
μ₂=`completedNativeXiCosineMoment 1`.
The scale is the existing source's first radial slope divided by its native
sample-degree scale. It is not selected to fit a target entry or moment.

The full nonlinear remainder is retained by the exact definition

```text
ρᵢ = bᵢ − αₖ(i+1),
R(d) = A(dᵢ ρᵢ).
```

No Taylor truncation replaces b. Vectorially:

```text
A(dᵢ bᵢ) = αₖ E(d) + R(d).
```

## Exact accumulated-storage decomposition

On the original nonzero F/P denominators, the kernel proves for every c:

```text
Re storage k c 1
  = 2 κ αₖ normSq(sum dᵢ) + 4 Re inner A(d) R(d).
```

The first term is unconditionally nonnegative on every finite source
family. The second is still signed. This is NOT a positive complementary
channel or a sum-of-squared-norms theorem. It is not a pointwise sign of the
internal flux either.

The amplitude coordinate change is invertible on the same regular source:
`radialCompletedInputCoefficients k d = dᵢ P(zᵢ)/F(zᵢ)` returns d under
`radialCompletedValueCoefficients`. No coordinate is made from a target
kernel; this is only the original complete source-amplitude normalization.
Nonzero F and P hold eventually on every finite radial family by the existing
regularity theorem, uniformly in coefficients.

## Quantitative remaining gate and cancellation canary

The exact original norm bound is equivalent to

```lean
∀ d : Fin N → ℂ,
  -(((k : ℝ) + 1) / 2 * radialCompletedEulerScale k *
      Complex.normSq (∑ i, d i)) ≤
    (inner ℂ (radialIncidentSynthesis k N d)
      (radialCompletedRemainderSynthesis k N d)).re
```

This equivalence is also proved with the original all-order quantifiers:
for every N, eventually k, for ALL d. Nonnegative remainder on every d is
not imposed: it would be a stronger unproved condition. The finite norm
bound is not inferred from a small remainder estimate because the positive
boundary contribution has cancellation directions.

For d=(1,−1), both legs use the native completed source, and the scale
cancels exactly:

```text
inner A(d) R(d) = κ/12 * (2 b₀ − b₁),
Re storage k (inputCoefficients d) 1
  = κ/3 * (2 Re b₀ − Re b₁).
```

The corresponding necessary slope inequality for a contractive two-vector
transfer is proved. Its sign is not claimed here, and it is not an affine
probe: b is the actual completed logarithmic derivative. This canary
exhibits where the nonlinear response matters even with a strictly positive
boundary coefficient. The prior affine-probe no-go remains unchanged.

**One remaining obligation** is the eventual all-N quantitative lower bound
on the exact R pairing displayed above. Proving it would close the original
norm/storage gate using the already established equivalence. No new
assumption wrapper is introduced. No source-derived positive complement or
ambient contraction supplying it was found in this round.

## Public declarations

- `radialEulerSynthesis`
- `radialEuler_boundary_polarized`, `radialEuler_boundary_energy`
- `radialCompletedSlope`, `radialCompletedValueCoefficients`
- `radialCompletedEulerScale`, `radialCompletedEulerRemainder`
- `radialCompletedRemainderSynthesis`
- `radialCompletedEulerScale_eq_sourceIntegralRatio`, `radialCompletedEulerScale_pos`
- `sourceValue_eq_completedCoefficients`, `sourceCompanion_eq_completedSlope`
- `radialCompletedSlopeSynthesis_eq_euler_add_remainder`
- `storage_one_eq_euler_boundary_add_remainder`
- `radialCompletedEuler_boundary_nonnegative`
- `radialCompletedInputCoefficients`, `radialCompletedValueCoefficients_input`
- `radialReturnTransfer_norm_le_one_iff_euler_remainder`
- `radialReturnTransfer_eventually_norm_le_one_iff_euler_remainder`
- `radialEuler_boundary_energy_zero_of_sum_zero`
- `radialCompletedRemainder_opposite_pairing`
- `storage_one_completed_opposite_eq_two_slopes`
- `radialReturnTransfer_two_norm_le_one_implies_slope_inequality`

## Audit, validation and publication

All 23 public definitions/theorems have dedicated source and foundation
checks plus `#print axioms`. The combined source dependency closure traverses
5547 declarations and contains no canonical moment, HP, Stieltjes, Hankel,
Jacobi/height, Herglotz or BR2 proof input. Maximum footprint:
`[propext, Classical.choice, Quot.sound]`. Positivity of raw theta integrals
passes that same firewall; it is not a downstream certificate.

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnEulerBoundary
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnEulerBoundaryAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

All seven validation steps passed: focused module, dedicated source/axiom
audit, full root, full root Audit, static scan, complete kernel suite, and
`git diff --check`. Logs stay on llm under
`/tmp/chiral-euler-boundary-validation/{module,focused-audit,root,root-audit,static,kernel-suite,diff}.log`.
The dedicated audit prints all footprints and the 5547-declaration source
closure. No placeholder or trust escape was found in the new modules.

Modified files: new Euler-boundary module and dedicated audit, root/Audit
imports, theorem registry, README, append-only research checkpoint and this
report. Audited changes are committed directly to main; delivery records
the final publication SHA and clean/synchronized state.
