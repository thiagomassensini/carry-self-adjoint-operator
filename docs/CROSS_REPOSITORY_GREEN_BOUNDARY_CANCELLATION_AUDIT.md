# Cross-repository Green audit and completed-source boundary cancellation

## Checkpoint and outcome

Date: 2026-10-07. Initial normative main:
`101768b75d367fe6f6fd655560a7b994ff2c3cc2`.
`git pull --ff-only` was up to date; HEAD/main/origin-main agreed and the
working tree was clean. All research checkouts below were read only.

New local status: `PASS_SOURCE_BOUNDARY_CANCELLATION_HIERARCHY`.
Overall status remains `PARTIAL_COMPLETED_SOURCE_ENERGY_POSITIVITY`.
Neither native storage positivity nor return contractivity is claimed.

## Directed audit of other repositories on llm

These are inspected checkout snapshots, not claims that every repository was
fetched or rebuilt. The audit examined definitions and theorem signatures of
the listed routes; it does not assert a global absence of other constructions.

| Repository / HEAD | Inspected construction | Exact role and limitation for this gate |
| --- | --- | --- |
| native-carry-spectral-weyl / `2236bc5d881b7945ff1737e4b6d158ab733ea532` | `Infinite.Cauchy`, `Infinite.ComplexifiedCauchy`, `Boundary.SourceRelation`, `Boundary.GammaField`, `Boundary.GreenHaarCameraForm` | Bounded logarithmic resolvent on the all-bases Naimark space and its camera compression. `carryGammaField` is a real linear partial map from `RealifiedCameraComplexification` to `RealifiedNaimarkComplexification`. This is not the native `Lp` half-density source quotient. No intertwiner identifying its resolvent with the completed F/-F' source was found in the inspected route. The form-first Green/Haar extension module explicitly does not assert the research-specific source formula. |
| primos / `8c4b7fdf65a49d1d0febe8193d56e2cfb2191260` | `CpTfvdSeededFiniteBesselConservation`, `CpTfvdSeededNativeMomentContraction`, `CpCarryVerticalBoundaryGreenDefect` | Exact seeded TFVD/Bessel Pythagoras uses `IsCanonicalEnrichedPrimeCarryDefectReadoutRealizationOn`. The `11/12` bound on the reconstructed ledger uses `IsNativeGprePrimeMomentRealizationAt`; these are prime-tower readouts, not canonical logarithmic moments. Neither predicate is provided for the current chiral source by these theorems. The vertical boundary Green defect is an initial Wronskian in `CarryVerticalL2`, with isotropy required for symmetry. |
| native-carry-c3-crosswalk / `d9e9e3a7469cb2a95ad3a07d08d0c1a860377ec0` | `ReflectedPairCommutatorGreenIdentity` | `finiteC3ReflectedPairCommutatorTrace_eq_neg_log_mul_greenForm` keeps all three residues and identifies a phase-normalized reflected commutator with the C3 boundary Green form. Its parameters, reflection and form are not the completed radial Cauchy mixed pairing. It supplies no contractivity morphism to that pairing. |
| geometry-of-numbers / `e1084b43533255b399b82dc307b536d7dfdca07f` | `C2GreenPreStencilCanary`, `C2GreenTemporalMeanCanary` | Conservative pre-stencil split, exact stencil norm defect and event diagonal + cross decomposition. Crosses remain present; temporal averaging is a material-time operation on the authorized C2 source. It cannot replace the radial all-coefficient statement. |
| momentos / `206b06bcc61f5450fb15d3a13f974b50e4968394` | README and saved Green/TFVD snapshots | Research archive distinguishes compiled sources, snapshots and numerical experiments. It is not a single additional formal package, and its snapshots are not imported as new premises. |

The usable principle is to retain the boundary and every unobserved source
channel. A positive unrelated resolvent, a conditional Bessel realization or
a positive temporal mean cannot supply the missing native-source sign.
No external repository was added to the dependency graph.

## Construction in the existing Cauchy geometry

The new module is `CompletedNativeChiralReturnBoundaryCancellation`.
All declarations belong to `CarrySelfAdjointOperator.ChiralReturn`.

Let κ=k+1, n_i=i+1 and

```text
A(d) = radialIncidentSynthesis k N d,
E^m(d) = radialEulerPowerSynthesis k N m d,
J_m(d) = radialEulerBoundaryJet d m.
```

The new map and sector are

```lean
radialBoundaryJetAnalysis (N r : Nat) :
  (Fin N -> Complex) ->ₗ[Complex] (Fin r -> Complex)
radialBoundaryJetKernel (N r : Nat) : Submodule Complex (Fin N -> Complex)
```

They retain exactly the first r existing endpoint degree jets. The kernels
are nested as r increases. The coefficient norm and original Cauchy Hilbert
norm are unchanged; no quotient reconstructs a state from its scalar jets.

Rank-nullity proves `radialBoundaryJetKernel_ne_bot` when r<N. Injectivity of
the original monomial synthesis then proves that this kernel contains genuine
nonzero incident states. In particular, for every real C and r<N, the kernel
refutes the estimate

```text
forall d, ||A(d)||^2 <= C * sum_{j<r} |J_j(d)|^2.
```

This is a LOCAL finite-boundary observability obstruction. It is not a
counterexample to storage positivity or to a complete Green realization.

## All-order polarized cancellation

The existing repeated Green identity is reused without changing its form:

```text
<A(d), E^m(e)> - (-1)^m <E^m(d), A(e)>
  = κ sum_{a<m} (-1)^a conj(J_a(d)) J_{m-1-a}(e).
```

For d,e in the r-jet cancellation sector and m<=2r, every ordered product
on the right vanishes: at least one of its jet orders is below r.
Consequently the polarized boundary form is zero. For odd m, conjugate
symmetry then gives

```text
Re <A(d), E^m(d)> = 0.
```

No even-degree diagonal energy is declared zero from this argument. No cross
is omitted. Mathlib's first argument is conjugate-linear.

## Exact source-jet remainder before scalar readout

Define the transverse completed source function, in the definition of the
new scale, by

```text
b(y) = -I * completedNativeOperatorLogDerivative(I*y).
```

The raw real odd derivative scales are

```text
a_(k,j) = Re(D^(2j+1) b(0)) / ((2j+1)! κ^(2j+1)).
```

Their public name is `radialCompletedOddSourceJetScale`. They are extracted
from the actual source, not from canonical moments, a target Gram or spectral
data. No general sign, analytic remainder rate, or identification with a
canonical moment is proved here. Real parts are explicit in the definition;
no unproved reality theorem is silently used.

The finite vector jet part and the EXACT remainder are

```text
P_r(d) = sum_{j<r} a_(k,j) E^(2j+1)(d),
R_r(d) = A(d_i * radialCompletedSlope(k,i)) - P_r(d).
```

The reconstruction `full slope synthesis = P_r + R_r` is a vector identity
before any inner product. It retains the complete original source; defining
the subtraction requires no Taylor error estimate and never replaces the
full F/-F' response by a polynomial.

The kernel proves, on the existing F/P regularity conditions,

```text
Re storage(k, sourceInput(d), 1)
  = 4 Re <A(d), A(d_i * radialCompletedSlope(k,i))>.
```

If d belongs to the r-jet cancellation sector, all r odd degree contributions
vanish in the real pairing, giving the all-order EXACT identity

```text
Re storage(k, sourceInput(d), 1) = 4 Re <A(d), R_r(d)>.
```

Tails, chart/Xi completion and all sample crosses remain in the full source
used by `radialCompletedSlope`. None receives a sign by this subtraction.
The sector index r is an endpoint degree-jet count, not material time, C2
address depth or an automatically identified moment order.

## Low-order source-independent witnesses

The existing `(1,-2,1)` direction is proved to belong to the second sector.
The new `(1,-3,3,-1)` direction belongs to the third sector and has nonzero
incident synthesis. It therefore kills the degree 1,3,5 boundary energies.
Its FULL native source storage is exactly

```text
κ/70 * (14 Re b_0 - 14 Re b_1 + 6 Re b_2 - Re b_3),
b_i = radialCompletedSlope(k,i).
```

This uses the actual four radial source samples, not a Taylor approximation.
Its sign is not proved, and a positive value on this one direction would not
prove the all-coefficient gate.

## Remaining obligation

The original all-order statement remains

```text
forall N, eventually k, forall coefficients c,
  0 <= Re(storage k c 1).
```

Equivalently, the existing
`radialReturnTransfer_eventually_norm_le_one_iff_green_boundary_tower`
requires the joint lower bound for the cubic higher-source pairing, including
both boundary allowances AND their value/curvature cross. Positivity of R_r
on the cancellation sectors is a necessary diagnostic, not a sufficient
replacement for that joint estimate.

Next concrete diagnostic: bound the actual four-sample expression above
from upstream source estimates. The full proof must additionally retain and
control the interactions between cancellation sectors. No finite family of
already positive boundary terms can supply coercivity on every order.

## Trust and validation

Twenty public declarations are registered in the dedicated audit and imported
by `CarrySelfAdjointOperator.Audit`. Each has `#print axioms` and
`#assert_prime_depth_source_axioms`. The oriented source dependency firewall
checks their transitive declaration closure and rejects canonical moments,
HP/Stieltjes certificates, Hankel/Jacobi/height and BR2 declarations.
The allowed axiom footprint is at most
`[propext, Classical.choice, Quot.sound]`.

Validation logs: `/tmp/chiral-boundary-cancellation-validation/` on llm.
The final validation record includes module/audit --wfail builds, root/root
Audit --wfail builds, static audit, full kernel audit, placeholder scan and
`git diff --check`. No other repository is changed. The working tree is made
clean by the audited main commit; remote equality is verified after push.

Files added: module, dedicated audit and this report.
Files updated: root import, root Audit import and README frontier paragraph.

### Executed validation results

All of the following completed successfully on the llm main checkout:

```text
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnBoundaryCancellation
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnBoundaryCancellationAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

The focused source firewall checked 5,453 reachable declarations across the
20 public declarations. Every printed axiom list is a subset of
`[propext, Classical.choice, Quot.sound]`. The placeholder scan returned no
matches. These are executed server-side Lean/kernel checks; GitHub Actions
status is checked separately after publication, not inferred from them.
