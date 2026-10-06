# Affine six-source role interface audit

STATUS: `PARTIAL_AFFINE_SIX_SOURCE_ROLE_LIFT`.

Initial main: `4e609bbe0095ebdbcc83d6362a29519c9df7d26a`.
No historical checkout is imported by this increment.

## 1. Is the existing linear interface honest?

Yes, as a variation/gradient-analysis interface. The definition
`BR2IncidenceToCanonicalC3SixSourceAnalysis S` targets
`CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S`, consisting of six
TFVD analyses of ordinary or logarithmic gradient prefixes. It has no field
for the global unit atom. `nativeC3SeededClockTfvdSixSourceAnalysis_zero_cutoff`
proves that this entire analysis datum is zero at cutoff zero.

The zero-input argument therefore does **not** refute that existing interface.
It refutes only a homogeneous ledger map into the complete seeded carrier
whose ordinary seed is required to be one at every input.
`no_homogeneous_incidence_map_realizes_fixed_ordinary_seed` states exactly
that scoped obstruction. No global six-source impossibility is claimed.

## 2. Where does the fixed ordinary seed live?

`canonicalOrdinaryBoundarySeed s = positiveDirichletValue s 0 = 1`.
It is retained outside the analysis carrier in the existing
`CameraResolvedSeededClockOrdinaryRoleAnalysis.boundarySeed` and
`CameraResolvedAffineSixSourceRoleAnalysis.boundarySeed`.
The canonical affine camera ledger has seed one at ordinary roles and zero
at logJet roles. It is a global atom, not an external-camera contribution,
and is not the TFVD trace of a gradient state.

## 3. What is linear?

The role view of the six analysis data, insertion of a zero seed alongside
an arbitrary analysis variation, and a supplied incidence variation map
are real-linear. Adding the fixed ordinary boundary is affine.
No linearity in the analytic parameters z, w or reflected z is asserted.

The new standard product carrier is

```lean
CanonicalC3SixSourceRole → (ℂ × NativeGpreFiniteTfvdAnalysisCarrier S)
```

The six canonical roles remain distinct from camera slots. No metric is
introduced. The exact canonical source decomposes as fixed seed plus its
unchanged role analyses; a comparison theorem identifies this packaging
with the boundary and synthesized analysis of the existing camera ledger.
This comparison does not define a pre-compression transport by synthesis.

## 4. Minimal correct interface

Retain the existing homogeneous variation type. Use the standard affine
assembly after its role view:

```lean
canonicalC3SixSourceAffineIncidenceLiftOfVariation
  (S : Finset NativeGpreBoundaryContext)
  (variation : BR2IncidenceToCanonicalC3SixSourceAnalysis S) :
  (ℕ →₀ ℝ) →ᵃ[ℝ] CanonicalC3AffineSixRoleAnalysisCarrier S
```

The constructor does not choose `variation`. It does not repeat the BR2
analysis in six roles, map source roles to cameras, or relabel native value
as ordinary or native numberFlux as logJet. Every native field of a given
variation datum is retained by the affine assembly.

## 5. Enriched correlation

The established BR2 canary `−a²/128 ≠ 0` is preserved unchanged upstream.
The new analysis projection identity and native value-pairing identity
show that insertion of the fixed seed changes no coordinates or pairings
of a **given** role variation. They do not establish that the BR2 value
canary has become an ordinary/logJet role coefficient. That requires the
actual geometric variation map, which remains absent.

Thus the Gate D transport is not closed. There is no new claim about h₁,
visible camera Gram, total isometry or blind energy excess.

## 6. Single typed obligation remaining at this stage

Geometrically construct the existing arrow

```lean
variation : BR2IncidenceToCanonicalC3SixSourceAnalysis S
-- (ℕ →₀ ℝ) →ₗ[ℝ] CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S
```

with actual ordinary/logJet parameter-role provenance and a proved
connection to the enriched BR2 datum. The standard affine seed assembly
is available once that arrow is supplied; it is not a substitute for it.
If that provenance cannot be supplied, BR2 has not been established as
the appropriate source. The scoped zero-input theorem does not settle
this question either way. No target-fitted map is defined.

## Provenance and clock note

All constructions use current local role selectors, canonical gradient
analyses, the existing global unit seed, and Mathlib standard products,
linear maps and affine maps. They depend on neither target moments nor
heights. No positivity, spectral calibration or metric is an input.
Boundedness is not claimed for this algebraic interface.

The user note `DO_CLOCK_LOGN_AO_OPERADOR_DE_ALTURAS.md` was read as a
conceptual blueprint only. Its distinction between the material clock,
Jacobi and height is compatible with this audit. It does not prove the
missing role transport. On the infinite raw critical sequence, the orbit
notation also needs a valid carrier/domain: n^(-1/2) alone is not a
material ℓ² vector. Neither that formal notation nor the downstream
J^(-1/2) construction is used as a premise here.

## Directed follow-up: moment/Jacobi/height modules

The three user-mentioned local modules were read directly. In
`LogarithmicMomentHankel`, `IsLogDerivativeMomentSequence.unique` offers an
independent future identification route: a geometric sequence must first
be proved to satisfy the same division-free recurrence and nonzero phi(0).
Uniqueness then identifies it; it cannot supply that recurrence by itself.
`FiniteJacobiTransport` consumes Gram representation/positivity and exact
whitening, and `FiniteHeightOperator` consumes a positive definite Jacobi
section to apply inverse-square-root functional calculus. Neither module
constructs the missing source-role map or decides BR2 source suitability.
No new moment/Jacobi/height theorem is asserted in this increment.

## Public declarations

- `CanonicalC3AffineSixRoleAnalysisCarrier`
- `canonicalC3SixSourceRoleAnalysisLinearMap`
- `canonicalC3SixSourceFixedRoleSeed`
- `canonicalC3SixSourceRoleVariationEmbedding`
- `canonicalC3SixSourceRoleAffineAssembly`
- `canonicalC3SixSourceRoleAffineAssembly_seed`
- `canonicalC3SixSourceRoleAffineAssembly_analysis`
- `canonicalC3SixSourceRoleAffineAssembly_sub`
- `canonicalC3SixSourceAffineRoleState`
- `canonicalC3SixSourceAffineRoleState_eq_fixedSeed_add_variation`
- `canonicalC3SixSourceAffineRoleState_eq_existing_cameraLedger`
- `nativeC3SeededClockTfvdSixSourceAnalysis_zero_cutoff`
- `canonicalC3SixSourceAffineRoleState_zero_cutoff`
- `no_homogeneous_incidence_map_realizes_fixed_ordinary_seed`
- `canonicalC3SixSourceAffineIncidenceLiftOfVariation`
- `canonicalC3SixSourceAffineIncidenceLiftOfVariation_analysis`
- `canonicalC3SixSourceAffineIncidenceLiftOfVariation_valuePairing`

## Validation and publication ledger

All public declarations are registered and checked by the focused
`CanonicalC3SixSourceAffineRoleInterfaceAudit` with explicit `#print axioms`.
The allowed set is `[propext, Classical.choice, Quot.sound]` or a subset.
No new foundational dependency, placeholder or trust escape is accepted.

Commands required for publication:

- `lake build --wfail CarrySelfAdjointOperator.CanonicalC3SixSourceAffineRoleInterface`
- `lake build --wfail CarrySelfAdjointOperator.CanonicalC3SixSourceAffineRoleInterfaceAudit`
- `lake build --wfail CarrySelfAdjointOperator`
- `lake build --wfail CarrySelfAdjointOperator.Audit`
- `bash scripts/static_audit.sh`
- `bash scripts/audit.sh`
- `git diff --check`

All seven commands above completed with exit status 0. The full script
reported `kernel audit passed`; the static script reported `static audit
passed`. The focused guards checked all 17 public declarations. Every
printed footprint was `[propext, Classical.choice, Quot.sound]` or a subset.
No new local trust escape was found. The root build and central audit also
passed `--wfail`. The commit containing
this report is identifiable with
`git log --format=%H -- docs/AFFINE_SIX_SOURCE_ROLE_INTERFACE_AUDIT.md`.
