# Source-first mixed boundary jets — audited finite frontier

## Checkpoint and scope

Initial main: `7a8451dc1fae805a87a0302b7ff6bf4d0fc48c29`.
`git pull --ff-only` was already up to date; HEAD/main/origin-main matched
and the initial working tree was clean. Work is on llm, exclusively on main.

Status: `PASS_SOURCE_FIRST_MIXED_BOUNDARY_JET_CONTROL`.
The overall gate remains `PARTIAL_SOURCE_FIRST_CHIRAL_RETURN_STORAGE_POSITIVITY`.

The preceding four-sample cancellation-sector sign is reused. This increment
controls the two mixed blocks of the **four-coordinate boundary jet face**;
it does not yet prove full Fin 4 storage positivity or arbitrary-N return
contractivity. No new metric, Hilbert state, fitted Gram or source is introduced.

## Provenance and exact coefficients

Let `q = completedNativeOperatorLogDerivative = -F'/F`, with the existing
completed characteristic. Define only its own real source coefficients

```text
c_j = Re(D^(2j+1) q(0)) / (2j+1)!.
```

These definitions contain no canonical moment or moment Gram. The previous
source-first division-free derivative recurrence gives their literal values.
For raw cosine integrals `a,b,c,d,e = mu_0,mu_2,mu_4,mu_6,mu_8`, write

```text
A = 3 b^2 - a c
B = 30 b^3 - 15 a b c + a^2 d
C = 630 b^4 - 420 a b^2 c + 35 a^2 c^2 + 28 a^2 b d - a^3 e.
```

Then `(c_0,c_1,c_2,c_3) = (b/a, A/(6a^2), B/(120a^3), C/(5040a^4))`.
The cast theorem verifies the corresponding complex derivatives and factorials.

Exact transverse Taylor sewing on the original imaginary radial line:

```text
-I q(I h) = sum_{j<4} (-1)^j c_j h^(2j+1) + h^8 R(h),
```

with R analytic at zero and the equality on a neighborhood germ. The higher
analytic source is retained, not replaced by a seventh-degree polynomial.

## Mixed boundary form and strict control

For a four-coordinate complex jet x, the finite alternating Green face is

```text
E(x) = 2 [
 c_0 |x_0|^2 - 2 c_1 Re(conj(x_0) x_2) + c_2 |x_2|^2
 + c_1 |x_1|^2 - 2 c_2 Re(conj(x_1) x_3) + c_3 |x_3|^2
].
```

`nativeSourceFourBoundaryEnergy_eq_alternating_green` proves this is exactly
the order-through-seven alternating Green boundary expression restricted to
four coordinates. The finite zero extension used to state this identity is
**not** a reconstruction of a full source. Actual four-sample higher boundary
jets are not asserted to vanish.

The discriminants are certified independently:

```text
c_0 c_2 - c_1^2 = (15 b^2 c + 3 a b d - 10 a c^2)/(360 a^3) > 0
c_1 c_3 - c_2^2 = xiEighthMomentNumerator(a,b,c,d,e)/(302400 a^4) > 0.
```

The first uses the existing pure real polynomial lower-bound theorem with
margin `4861191/50000000000000`, instantiated from the refined integral box.
The second uses the existing refined eighth-order integral certificate.
Only that pure polynomial declaration is selected from the historically
Hankel-named module; no Hankel/moment positivity consumer enters the proof.
The dependency firewall checks this distinction transitively.

For arbitrary complex u,v, the exact existing-norm identity is

```text
a |u|^2 - 2 b Re(conj(u) v) + c |v|^2
 = a |u - (b/a) v|^2 + ((a c - b^2)/a) |v|^2.
```

Thus each block is strictly positive on every nonzero pair and E(x)>0 for
all nonzero x. The cross terms are bounded by a strict source margin; they
are neither deleted nor assumed orthogonal. This scalar square completion
is a diagnostic inequality, not construction of a target-fitted carrier.

## Full vector synthesis and exact remainder

The new all-order odd Green readout is derived directly from
`radialEulerPower_green_boundary` and conjugate symmetry. It retains every
ordered boundary cross.

The full storage theorem is valid for arbitrary k,N,r,d under only the
original nonzero sample denominators F/P. It proves

```text
Re storage(sourceInput d,1)
 = 2(k+1) sum_{j<r} sourceScale(k,j)
     sum_{a<2j+1} (-1)^a Re(conj(J_a(d)) J_(2j-a)(d))
   + 4 Re <incident(d), exactOddSourceRemainder(k,N,r,d)>.
```

The exact remainder is the already defined fully synthesized completed
source minus its own odd jets. Its tails and completion are unchanged.
Synthesis precedes pairing. No source state is reconstructed from a scalar.

## Remaining finite seam — one uniform source estimate

The strict finite-face sign is NOT a sign for arbitrary full radial storage.
To promote it, the four-sample boundary reconstruction must retain the
higher boundary coordinates and the analytic remainder and control them
uniformly in the coefficient vector as h_k tends to zero.

A precise sufficient next target, with one epsilon and one radial threshold,
is the following (statement of an open obligation, not an assumption added
to Lean):

```text
exists epsilon > 0, eventually k, forall d : Fin 4 -> C,
 epsilon * sum_{a : Fin 4} normSq(h_k^a * J_a(d))
 <= Re(storage k (radialCompletedInputCoefficients k d) 1).
```

Here `h_k = canonicalGreenJetStep k` and J is the existing Euler boundary jet.
This asks for control of the complete same-source form, including all mixed
sectors. A pointwise limit for a fixed d or the previous one-dimensional
cancellation theorem does not supply the uniform quantifier. No assumption
wrapper for this obligation was created. The arbitrary-N analogue remains
separate after the Fin 4 gate.

## Public declarations

- `nativeSourceOddBoundaryCoefficient`
- `nativeSourceOddBoundaryCoefficient_integral_formulas`
- `nativeSourceSixthMixedNumerator_pos`
- `nativeSourceMixedDiscriminants_integral_formulas`
- `nativeSourceMixedDiscriminants_pos`
- `nativeSourceMixedLeadingCoefficients_pos`
- `nativeSourceMixedBoundary_square`
- `nativeSourceEvenBoundaryEnergy`
- `nativeSourceOddBoundaryEnergy`
- `nativeSourceEvenBoundaryEnergy_pos`
- `nativeSourceOddBoundaryEnergy_pos`
- `nativeSourceFourBoundaryEnergy`
- `nativeSourceFourBoundaryEnergy_pos`
- `nativeSourceFourBoundaryExtension`
- `nativeSourceFourBoundaryEnergy_eq_alternating_green`
- `nativeSourceOddBoundaryCoefficient_cast_jets`
- `nativeSourceTransverseSlope_exact_remainder`
- `radialEulerPower_odd_green_energy`
- `storage_one_eq_odd_green_tower_and_remainder`

## Validation and trust

Dedicated audit: `CompletedNativeChiralReturnMixedSourceJetsAudit`.
Every public declaration has `#print axioms`,
`#assert_prime_depth_source_axioms` and transitive `#assert_oriented_green_source`.
The firewall rejects canonical moments, HP/Stieltjes, Hankel positivity,
Jacobi/height, Herglotz consumers and BR2 in types and proof dependencies.
Allowed axioms: subsets of `[propext, Classical.choice, Quot.sound]`.

Validation logs: `llm:/tmp/chiral-mixed-source-validation/`.
Server Lean builds and GitHub Actions are reported separately.

All checks completed successfully on the llm main checkout:

```text
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnMixedSourceJets
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnMixedSourceJetsAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

The focused source firewall traversed 5,508 reachable declarations. All 19
public declarations passed the axiom assertions; their printed footprints
are subsets of `[propext, Classical.choice, Quot.sound]`. The new-module
trust-escape/placeholder scan returned no matches. The broad root audits
also passed; their unrelated downstream declarations are not proof premises
of the new source capstones. No external repository was modified.

Files: new source module, dedicated audit and this report; root imports,
root Audit and README updated. Publication follows validation; final Git
refs and working-tree cleanliness are verified afterward.
