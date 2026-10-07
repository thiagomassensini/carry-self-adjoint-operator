# Completed chiral return: Green boundary tower and retained higher defect

## Checkpoint and scope

Initial published main: `5399220e988ca2bf5028abf64f39e7fd9c9ce837`.
`git pull --ff-only` reported up to date; HEAD/main/origin-main agreed and
the working tree was clean. Work stays exclusively on main.

Stable local result: `PASS_COMPLETED_SOURCE_GREEN_BOUNDARY_TOWER`.
The requested all-order return contraction remains
`PARTIAL_COMPLETED_SOURCE_ENERGY_POSITIVITY`.
No native-source nonpositivity or global impossibility is claimed.

The test extends the existing Euler boundary identity in the original Cauchy
geometry. It finds a second nonnegative source-derived boundary energy and
an exact square decomposition, but the full higher defect still has no sign.
There is no new Hilbert metric, Gram factor, operator realization or source.

## Existing facts reused and source provenance

The original finite transfer and Euler/storage crosswalk are reused from
`CompletedNativeChiralReturnFiniteTransfer` and
`CompletedNativeChiralReturnEulerBoundary`.

The raw source facts are reused from `CompletedNativeXiCosineMoments` and
`CompletedNativeXiThetaMomentBounds`:

- `XiThetaCosine.completedNative_eq_xiCosineKernel`;
- `completedNativeXiCosineTransformReal_zero`;
- `iteratedDeriv_two_completedNativeOperatorCharacteristic_zero`;
- `iteratedDeriv_four_completedNativeOperatorCharacteristic_zero`;
- `completedNativeXiCosineMoment_pos`;
- `completedNativeXiCosineMoment_strict_kurtosis`.

The last theorem is the already certified source-integral inequality
μ₀ μ₄ < 3 μ₂². Here μ₂ and μ₄ are raw integrals of the positive theta cosine
source, NOT the canonical logarithmic moment sequence. No moment/HP/Herglotz
positivity certificate or spectral data is used. The generic geometric-sum
identity in Mathlib supplies the finite algebra for repeated degree transport.

The full F and −F′ response remains unchanged, with its existing TFVD exact
tails and Xi/chart completion. We do not invert scalar traces into a structured
TFVD state. The source is never replaced by a polynomial truncation.

## Types and boundary roles

All new declarations are in `CarrySelfAdjointOperator.ChiralReturn`.

```lean
radialEulerPowerSynthesis (k N m : ℕ) (d : Fin N → ℂ) :
  CanonicalCompletedNativeChiralCauchyCarrier
radialEulerBoundaryJet {N : ℕ} (d : Fin N → ℂ) (m : ℕ) : ℂ
radialCompletedCubicScale (k : ℕ) : ℝ
radialCompletedCubicRemainder (k n : ℕ) : ℂ
radialCompletedCubicRemainderSynthesis (k N : ℕ) (d : Fin N → ℂ) :
  CanonicalCompletedNativeChiralCauchyCarrier
```

The carrier is the existing complex `Lp` on the unit interval, with the SAME
Cauchy norm. Let κ=k+1, nᵢ=i+1, A(d)=∑dᵢuᵢ, and

```text
Eᵐ(d) = A(dᵢ nᵢ^m),
Jₘ(d) = ∑ dᵢ nᵢ^m.
```

J₀ is the endpoint value of the synthesized polynomial; J₁ is its degree
slope; J₂ is the next degree jet. These are Cauchy polynomial boundary roles.
They are not identified with C2 positional depth, material edge numbers or
TFVD discrete boundary coordinates without a morphism. Nor is m identified
with a canonical moment order or an analytic response-derivative order.

## All-order polarized Green identity

For arbitrary independent d,e and every finite k,N,m, the kernel proves:

```text
inner A(d) Eᵐ(e) − (−1)^m inner Eᵐ(d) A(e)
  = κ ∑_{a<m} (−1)^a conj(Jₐ(d)) J_{m−1−a}(e).
```

This is repeated degree transport in the original Cauchy pairing. The
Cauchy denominator nᵢ+nⱼ cancels against the exact finite difference of the
two degree powers. No orthogonality or cross-term deletion is assumed.
The first Hilbert argument is conjugate-linear. The identity includes both
even and odd degree orders; it does not assert a positive form at each order.

The cubic case keeps all three ordered boundary channels:

```text
inner A(d) E³(e) + inner E³(d) A(e)
 = κ (conj(J₀(d)) J₂(e) − conj(J₁(d)) J₁(e) + conj(J₂(d)) J₀(e)).
```

On the diagonal:

```text
Re inner A(d) E³(d)
  = κ (Re(conj(J₀) J₂) − |J₁|²/2).
```

Thus cubic transport has a value/curvature cross and a signed slope energy.
One cannot retain the slope and silently drop the cross.

## Second source scale and exact higher correction

The previous positive scale is a=αₖ. The new raw cubic scale is fixed by the
actual characteristic derivatives and radial grid:

```text
b=βₖ = Re((F''''(0) F(0) − 3 F''(0)²)/(6 F(0)²)) / κ³.
```

The kernel identifies it exactly with

```text
βₖ = (μ₄ μ₀ − 3 μ₂²)/(6 μ₀² κ³) < 0.
```

This is a raw source-curvature formula and sign, not an identification with
a canonical moment. No theorem about analytic Taylor remainder estimates is
claimed. The retained remainder is an EXACT subtraction from the full source:

```text
ρ³ᵢ = radialCompletedEulerRemainder(k,i) − βₖ nᵢ³,
R³(d) = A(dᵢ ρ³ᵢ),
R(d) = βₖ E³(d) + R³(d).
```

This vector identity precedes scalar contraction. R³ contains every remaining
source order; it is not set to zero, approximated or assumed nonnegative.

## Exact storage and nonnegative boundary terms

For the original completed value amplitudes
`d = radialCompletedValueCoefficients k c`, on existing regular F/P
denominators, the full storage is exactly

```text
Re S = 2κa |J₀|² + 4κb Re(conj(J₀) J₂) − 2κb |J₁|²
       + 4 Re inner A(d) R³(d).
```

Because a>0 and b<0, the value and slope energies are nonnegative. The
value/curvature cross is signed. Both signs come from upstream source
integrals; no canonical logarithmic moments supply them.

The standard scalar complex norm allows an exact completion of the boundary
square, using only the fixed ratio b/a:

```text
Re S = 2κa |J₀+(b/a)J₂|² − 2κb |J₁|² + D(d),
D(d) = 4 Re inner A(d) R³(d) − 2κ(b²/a)|J₂|².
```

The first two terms are nonnegative. D is still signed. This is an algebraic
identity in the existing norm, NOT whitening, a fitted metric, a new positive
state or a proof that a full Pythagorean positive complement exists.
In particular the curvature cost is not discarded. No assertion `D >= 0`
is made. The two scalar squares are not proved to be orthogonal components
of the complete source. No lossless identity of the form whole energy =
returned energy + complementary squared norm is derived here.

## Cancellation canaries

On J₀=0, the original value energy and value/curvature cross vanish:

```text
Re S = −2κb |J₁|² + 4 Re inner A(d) R³(d).
```

On J₀=J₁=0, both degree and cubic contributions vanish:

```text
Re S = 4 Re inner A(d) R³(d).
```

In the square presentation the shifted value square may still be nonzero;
it is exactly offset by its retained negative curvature cost. It is incorrect
to claim that this cancellation leaves a free positive square.

The smallest fixed coefficient family with both cancellations is
`d=(1,−2,1)`. Both boundary identities are kernel checked. The actual completed
source, at the unchanged three radial samples, has exact storage

```text
κ/15 * (5 Re b₀ − 4 Re b₁ + Re b₂),
```

where here bᵢ denotes `radialCompletedSlope k i` (not the scalar βₖ).
No target values are used to choose this family. Its incident vector is
nonzero by the existing incident-synthesis injectivity. The sign of this
native three-sample expression is NOT claimed. A single canary sign would
also not establish the all-coefficient norm bound.

## One remaining quantitative obligation

The kernel proves that the original norm <=1 gate is EXACTLY

```text
Re inner A(d) R³(d)
 >= −κa |J₀|²/2 − κb Re(conj(J₀)J₂) + κb |J₁|²/2,
```

for every finite coefficient family, with the original all-order quantifiers:

```text
forall N, eventually k, forall d : Fin N -> complex.
```

This is `radialReturnTransfer_eventually_norm_le_one_iff_green_boundary_tower`.
The right hand side retains the cross and both boundary-energy allowances.
Demanding a nonnegative higher defect everywhere would be a stronger
unproved condition and is not introduced as a wrapper.

**Frontier:** prove this joint bound for the exact native higher correction.
Existing source curvature signs and Green boundary transport do not yet
supply it. The two positive boundary channels support the geometric route,
but do not close all-order storage positivity or contractivity.

## Public declarations and audit

- `radialEulerPowerSynthesis`, `radialEulerBoundaryJet`
- `radialEulerPowerSynthesis_zero`, `radialEulerBoundaryJet_zero`
- `radialEulerPower_inner`, `radialEulerPower_green_boundary`
- `radialEuler_cubic_boundary_polarized`, `radialEuler_cubic_boundary_energy`
- `radialCompletedCubicScale`, `radialCompletedCubicScale_eq_sourceIntegrals`
- `radialCompletedCubicScale_neg`
- `radialCompletedCubicRemainder`, `radialCompletedCubicRemainderSynthesis`
- `radialCompletedRemainder_eq_cubic_add_higher`
- `radialCompletedRemainder_pairing_eq_green_boundary`
- `radialCompletedCubic_slope_energy_nonnegative`
- `storage_one_eq_green_boundary_tower`
- `radialReturnTransfer_norm_le_one_iff_green_boundary_tower`
- `radialReturnTransfer_eventually_norm_le_one_iff_green_boundary_tower`
- `storage_one_zero_value_eq_slope_add_higher`
- `storage_one_zero_value_slope_eq_higher`
- `radialEulerBoundaryJet_secondDifference_zero`
- `storage_one_completed_secondDifference_eq_three_slopes`
- `radialCompleted_boundary_square`
- `storage_one_eq_green_squares_plus_signed_defect`

All 25 public definitions/theorems pass dedicated source/axiom checks and
`#print axioms`. The source firewall traverses types and values of 5555
reachable declarations: no canonical logarithmic moment, HP, Stieltjes,
Hankel, Jacobi/height, Herglotz or BR2 proof input. Maximum foundation footprint:
`[propext, Classical.choice, Quot.sound]`.

## Validation and publication

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnGreenBoundaryTower
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnGreenBoundaryTowerAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

All seven validation steps passed: focused module, focused source/foundation
audit, root build, root Audit, static audit, complete kernel suite and
`git diff --check`. Logs remain on llm under
`/tmp/chiral-green-boundary-tower-validation/{module,focused-audit,root,root-audit,static,kernel-suite,diff}.log`.
The dedicated audit prints every permitted footprint and the 5555-declaration
source closure. No placeholder or trust escape was found in the new modules.

Files changed: new module/audit, root and Audit imports, theorem registry,
README, append-only checkpoint and this report. Audited progress is published
directly to main; delivery records the final SHA and clean synchronized tree.
