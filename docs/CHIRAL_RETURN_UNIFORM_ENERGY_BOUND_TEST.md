# Chiral return: testing uniform energy dominance without moment premises

## Checkpoint and result

Audited initial `HEAD = main = origin/main`:
`f9aa8107c4648a4a799cd699dfd40db1eb6e4a30`.
`git pull --ff-only` was up to date. The initial working tree was clean.
Work uses `llm:/home/thlinux/carry-self-adjoint-operator`, exclusively `main`.

```text
PARTIAL_COMPLETED_SOURCE_ENERGY_POSITIVITY
NO_GO_AFFINE_RADIAL_SAMPLE_CONTROL_AS_ENERGY_PROOF
```

The main energy inequality has NOT been proved or refuted. The local no-go
concerns an affine diagnostic and the inference from small sample error and
individual sample contractivity to complete synthesis contractivity. It is
not a no-go for the completed native source, its exact nonlinear quotient,
or the theory. No new positive carrier, complementary channel or metric is
constructed.

## Original obligation retained

The existing complete source identity remains:

```text
Re storage = 2 ||coisometricSourceSynthesis||²
               - 2 Im(coisometricFourChannelBalance).
```

The ONE remaining obligation is unchanged:

```lean
∀ N : ℕ, ∀ᶠ k : ℕ in Filter.atTop,
  ∀ c : Fin N → ℂ, 0 ≤ (ChiralReturn.storage k c 1).re
```

On the already proved eventually regular samples, this is equivalent to
the imaginary full four-channel correction being bounded by the geometric
camera-source energy, for ALL coefficient vectors at one common cutoff.
This report supplies neither side of that inequality.

## Directed source audit

The current coisometric boundary projection and ChiralReturn sewing modules
were inspected before defining the diagnostic. The three coisometric
corrections equal the compressed boundary minus the Gamma boundary. Adding
the independent raw Gamma/Wronskian correction gives the literal complete
four-channel defect. On the diagonal the projection balance retains:

```text
2 Re <projected Gamma port, ambient port difference>
 + ||ambient port difference||² - ||Gamma escape||².
```

Orthogonality of port and escape does not sign the internal port/difference
cross term. The independent raw Gamma/Wronskian defect also remains. No
estimate of these complete terms by the camera energy was found upstream
of moment/HP inputs in the inspected source identities.
The existing escape boundary readout vanishes; it cannot be repurposed as
a complementary vector realizing the nonzero complete correction.

The independently completed adjacent clock channels and the corrected
ledger are preserved. Absolute convergence, trace completion and norm
conservation are not used to infer dominance. No pointwise nonnegative
flux integrand is required or claimed.

## Finite test before any approximation argument

The diagnostic is defined on the SAME canonical radial Cauchy carrier:

```lean
CanonicalCompletedNativeChiralCauchyCarrier
  = Lp ℂ 2 (volume : Measure unitInterval)
```

The unchanged vectors `u_(k,n)` satisfy:

```text
<u_(k,i),u_(k,j)> = (k+1)/(i+j+2).
```

For a free real analytic-test parameter `a`, independently of every moment,
define ONLY the diagnostic sample multiplier:

```text
q_aff(k,n) = -1 + a(n+1)/(k+1).
```

This is not the canonical quotient and is never substituted for it in an
existing declaration. It is the simplest first-order candidate to test
whether central approximation can prove the energy bound. Its return
vector is a legitimate finite synthesis in the existing carrier:

```text
Σ_i c_i q_aff(k,i) u_(k,i).
```

Both syntheses precede the norm observation; no cross term is removed.
For `c=(1,-1)`, Lean proves exactly:

```text
||u_(k,0)-u_(k,1)||²
 - ||q_aff(k,0) u_(k,0)-q_aff(k,1) u_(k,1)||²
 = -a²/[6(k+1)].
```

Thus for every `a ≠ 0` and every radial index k the balance is negative.
The coefficient 6 is derived from the unchanged Cauchy denominators 2,3,4;
it is not fitted or the six-source frame constant.

For `a>0`, the SAME diagnostic has, eventually in k:

- `||q_aff(k,i)|| ≤ 1` for BOTH samples;
- `||q_aff(k,i)+1|| < ε` for BOTH samples, for ANY prescribed ε>0;
- the strictly negative complete balance above.

The theorem has the simultaneous quantifiers:

```text
∀ a>0, ∀ ε>0, eventually k,
  (all two samples within ε of -1)
  AND (all two samples individually contractive)
  AND (opposite-coefficient synthesis has negative balance).
```

This refutes these scalar controls as a sufficient general proof strategy.
It does not assert that the native quotient has this affine form.

The cancellation direction annihilates the leading constant quadratic
term. Therefore shrinking absolute errors cannot simply be compared with
a uniformly strictly positive leading energy. The exact negative witness
can tend to zero and remain negative at every cutoff.

## Genuine completed-source tangent, independently checked

The actual source centered value is proved from the unchanged complete
characteristic and its complete companion:

```text
q_native(0) = -1.
```

The new source coefficient is spelled using curvature BEFORE any moment:

```lean
nativeRadialSourceCurvature : ℂ :=
  -2 * iteratedDeriv 2 completedNativeOperatorCharacteristic 0 /
    completedNativeOperatorCharacteristic 0
```

Reusing `hasDerivAt_completedNativeHermiteBiehlerChiralQuotient_zero_raw`,
the kernel proves, for each fixed sample n:

```text
I * [q_native(z_(k,n))+1]/z_(k,n) → nativeRadialSourceCurvature.
```

For every finite N and ε>0 this convergence is uniform over `i : Fin N`
with one eventual cutoff. It concerns finitely many samples, not dominance
of quadratic forms for all coefficient vectors. No reality, positivity or
nonzero value of this curvature is assumed or derived here. In particular,
the positive real `a` in the diagnostic is not claimed to equal this
complex source coefficient.

## An exact source constraint lost by truncation

The completed source's even characteristic and odd derivative yield the
source-first reciprocal germ:

```text
eventually z near 0, q_native(-z) q_native(z) = 1.
```

Nonzero chiral denominators follow from their original centered values
and continuity. No positivity or moment premise is involved.

For the affine diagnostic the corresponding product is instead:

```text
q_aff(-a,k,n) q_aff(a,k,n)
 = 1 - [a(n+1)/(k+1)]².
```

This explicitly distinguishes the diagnostic from the exact source. It
also shows why throwing away nonlinear terms can destroy a constraint of
the complete source, even when the first-order centered behavior agrees.
Reciprocity itself is NOT asserted to imply the energy inequality. A
future proof must preserve the exact source structure and control the
complete interference, rather than use this affine replacement.

## Provenance and scope

- Diagnostic definitions use only a free real slope, the original radial
  index and existing Cauchy vectors; no moments, height data or Gram fitting.
- The exact source theorems use the full completed characteristic, its raw
  derivative theorem, evenness, original radial grid and continuity.
- Norm observations occur after both complete finite vector syntheses.
- The original native sources, complete ledger, metrics, TFVD tails, Xi,
  chart, off-diagonal and residual coordinates are unchanged.
- Source Taylor convergence is not promoted to operator-norm dominance.
- No strictness, PSD, contractivity or complementary norm is claimed for
  the actual all-order source.
- BR2 is absent from the new proof/type dependency closures.
- The parameter a is not a material time, height, camera label or C2 depth;
  radial k remains the original shrinking-grid index.

## Public declarations

All are in `CarrySelfAdjointOperator.ChiralReturn`:

1. `affineRadialMultiplierProbe`
2. `affineRadialReturnedProbe`
3. `affineRadialProbe_opposite_energy`
4. `affineRadialProbe_opposite_energy_neg`
5. `affineRadialProbe_sample_norm_le_one`
6. `affineRadialProbe_tendsto_center`
7. `affineRadialProbe_uniform_control_not_energy_dominance`
8. `nativeChiralQuotient_center_eq_neg_one`
9. `nativeChiralQuotient_reflection_reciprocal`
10. `affineRadialProbe_reflection_product`
11. `nativeRadialSourceCurvature`
12. `nativeRadialSource_tangent`
13. `nativeRadialSource_tangent_uniform`

## Validation

Dedicated audit checks every declaration with `#print axioms`,
`#assert_prime_depth_source_axioms` and `#assert_oriented_green_source`.
The type/value dependency closure contains 5475 declarations and rejects
canonical moments, HP/Stieltjes, Hankel, Jacobi/height, Herglotz and BR2
inputs. Imports replay older historical information; those imported
modules are not treated as proof dependencies of every new declaration.
Axiom footprint is at most `[propext, Classical.choice, Quot.sound]`.

Commands executed on llm:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnLinearizationObstruction
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnLinearizationObstructionAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

All commands passed. The root build completed 9536 jobs and the main Audit
completed 9736 jobs. The full script ended with `kernel audit passed`.
No warning was accepted under `--wfail`. The final clean/synchronized SHA
is recorded in the handoff. Logs:
`llm:/tmp/chiral-uniform-control-validation/`.

Modified files: the new module and dedicated audit, root imports, public
registry, this report, README frontier note and append-only checkpoint.
Foundation, dependencies and existing mathematical declarations are intact.
