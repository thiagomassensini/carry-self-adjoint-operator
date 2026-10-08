# First surviving Green boundary and the seven-source Gamma test

## Checkpoint and scope

Initial `git pull --ff-only` returned already up to date on `main` at
`355769eca51c0848aed1248976e88d5377c80baa`; HEAD/main/origin/main agreed.
The pre-existing untracked `C2OddTfvdTransport.lean` and
`C2OddTfvdTransportAudit.lean` are preserved and excluded from task commits.

Request: attack the unsigned raw Gamma--Wronskian comparison remaining after
three-channel cancellation. Previously certified N=6 storage positivity and
all-order cancellation are reused, not reproved. No positivity, moment,
HP, Hankel, Jacobi, height, BR2, new source, metric, or fitted coefficient is
an input to the new proofs.

Kernel status of this increment:

- `PASS_ALL_ORDER_FIRST_SURVIVING_GREEN_BOUNDARY`
- `PARTIAL_ALL_ORDER_CHIRAL_RETURN_CORRECTION_BOUND`

**The arbitrary-N one-sided bound is still open.** No all-order positivity
or contractivity, and no full seven-sample positivity, is claimed.

## Existing source and boundary filtration

All vectors remain in `CanonicalCompletedNativeChiralCauchyCarrier` until
complete synthesis is performed. `radialIncidentSynthesis k N d` synthesizes
the original finite source coefficients. Its degree-transported version is
`radialEulerPowerSynthesis k N m d`.

The existing boundary jet is

```text
b_m(d) = radialEulerBoundaryJet d m = sum_i d_i (i+1)^m.
```

The existing subspace `radialBoundaryJetKernel N r` consists of source
coefficients with b_0,...,b_(r-1) zero. Membership is not a compression or a
replacement source. In particular complete incident states need not vanish
on this subspace.

`radialCompletedOddSourceJetScale k r` is the existing real, factorial-
normalized derivative of `y -> -I * completedNativeOperatorLogDerivative(I*y)`
at order 2r+1, including the original radial scale (k+1)^(-(2r+1)). No canonical
moment enters its definition. Let this real coefficient be lambda_(k,r).

The existing vector remainder `radialCompletedOddSourceRemainderSynthesis`
is the ENTIRE completed slope synthesis minus its own finite source jet sum.
Its definition retains tails/completion and makes an exact reconstruction.
It does not by itself prove any analytic remainder rate or sign.

## Arbitrary-order polarized first survivor

For d in the r-jet cancellation sector and e in the s-jet cancellation sector,
the existing all-order Green boundary identity now specializes exactly to

```text
inner A(d) E^(r+s+1)(e)
  - (-1)^(r+s+1) inner E^(r+s+1)(d) A(e)
= (k+1) (-1)^r conjugate(b_r(d)) b_s(e).
```

This is `radialEulerPower_firstSurviving_boundary`. Every other ordered
boundary term contains a boundary coordinate PROVED zero by the relevant
membership. No cross is deleted by an unproved orthogonality claim.
The surviving r/s cross remains polarized for independent coefficient
families. Mathlib is conjugate-linear in the first argument.

With e=d and s=r:

```text
Re(inner A(d) E^(2r+1)(d))
= (k+1)/2 * (-1)^r * normSq(b_r(d)).
```

This is `radialEulerPower_firstSurviving_energy`. The alternating sign is
explicit; a squared boundary norm alone is not a storage sign proof.

## Full source synthesis and Gamma gap

Incrementing the OLD source jet tower gives an exact VECTOR identity

```text
remainder_r = lambda_(k,r) E^(2r+1)(d) + remainder_(r+1).
```

The full reconstructed source, not the isolated boundary jet, is consumed
by the readout. On the cancellation sector:

```text
Re(storage k (radialCompletedInputCoefficients k d) 1)
 = 2(k+1)(-1)^r lambda_(k,r) normSq(b_r(d))
   + 4 Re(inner A(d) remainder_(r+1)).
```

Using the already closed Gamma cancellation ONLY after this source identity:

```text
norm(Gamma(c))^2 - Im(D(c,c))
 = (k+1)(-1)^r lambda_(k,r) normSq(b_r(d))
   + 2 Re(inner A(d) remainder_(r+1)),
c = radialCompletedInputCoefficients k d.
```

All higher source terms and ordered Cauchy crosses remain. A source-only
Cauchy--Schwarz estimate bounds the absolute difference from the first
boundary term by

```text
2 norm(A(d)) norm(remainder_(r+1)).
```

This is not a relative smallness estimate or a one-sided sign.
`rawGammaCorrection_cancellation_eventually_complete N` supplies one
radial threshold for ALL cancellation depths r and coefficient vectors d.
The threshold depends on N, not on r or d. It uses only the existing
regularity of the source denominators and strip.

## Exact next canary: seven original nodes

Define the source-independent sixth finite difference

```text
d = [1,-6,15,-20,15,-6,1] : Fin 7 -> complex.
```

Kernel checks prove:

- d lies in `radialBoundaryJetKernel 7 6`;
- b_6(d)=720;
- `radialIncidentSynthesis k 7 d` is nonzero for every k.

Thus this is an actual unobserved direction for the six lower boundary
coordinates, with a nonzero complete incident vector. It is NOT an assertion
that the previous full N=6 storage theorem fails. The coefficient families
have different sizes.

The exact completed storage is

```text
1036800 (k+1) lambda_(k,6)
  + 4 Re(inner A(d) remainder_7).
```

The first source degree that can contribute through this boundary channel is
THIRTEEN. The same nonlinear source storage has an independent exact reading:

```text
(k+1)/6006 * (
  429 Re(slope_0) - 572 Re(slope_1) + 429 Re(slope_2)
  - 208 Re(slope_3) + 65 Re(slope_4) - 12 Re(slope_5)
  + Re(slope_6)).
```

These seven rational coefficients are calculated in Lean from the original
Cauchy pairing and the six-step difference. They are not fitted, sampled
numerically, or selected from moments. The diagnostic vector itself is a
fixed binomial finite difference independent of every source value.

`storage_one_sixthDifference_eq_seven_slopes` keeps the FULL nonlinear slopes,
not a truncation. `sixthDifference_gammaGap_eventually_eq_seven_slopes` proves
that the same slope combination, with factor (k+1)/12012, is exactly the raw
Gamma gap on this original input. No sign is assigned to this combination.

## Attempt at the sign and its exact limitation

The algebraic cancellation now identifies the first observable source term
for EVERY cancellation depth. It does not control the signed higher
remainder or the mixed terms between distinct cancellation sectors. Neither
Cauchy--Schwarz nor positivity of the already available Gamma Gram supplies
this one-sided bound. The prior six-node source certificate cannot be used
on d above: it is a seven-node family with six lower jets zero.

In particular no source-first theorem certifying the thirteenth coefficient
or a uniform relative remainder estimate was established in this increment.
Even closing this one-direction canary would not establish every seven-node
cross, much less arbitrary N. No counterexample to the all-order bound is
proved or claimed.

## Single remaining global obligation

The all-order frontier is unchanged but has a more explicit source diagnostic:

```lean
forall N : Nat, eventually k : Nat in Filter.atTop, forall c : Fin N -> Complex,
  (ChiralReturn.rawGammaWronskianBalance k c c 1 1).im <=
    norm (ChiralReturn.gammaSourceSynthesis k c 1) ^ 2
```

No assumption wrapper or hypothetical encoder is added. On each boundary
cancellation sector this is now a concrete bound on the full retained
higher-source mixed readout relative to its first boundary square. The seven-
slope formula is a necessary canary of that single global obligation.

## Public declarations and provenance audit

New module: `CompletedNativeChiralReturnFirstSurvivingBoundary`.
Audit: `CompletedNativeChiralReturnFirstSurvivingBoundaryAudit`.

1. `radialEulerPower_firstSurviving_boundary`
2. `radialEulerPower_firstSurviving_energy`
3. `radialCompletedOddSourceRemainder_step`
4. `storage_one_cancellation_eq_firstBoundary_add_higher`
5. `rawGammaCorrection_cancellation_gap_eq_firstBoundary_add_higher`
6. `rawGammaCorrection_cancellation_higher_abs_bound`
7. `rawGammaCorrection_cancellation_eventually_complete`
8. `sixthDifference`
9. `sixthDifference_mem_radialBoundaryJetKernel`
10. `sixthDifference_first_boundary`
11. `radialIncidentSynthesis_sixthDifference_ne_zero`
12. `storage_one_sixthDifference_eq_thirteenth_add_higher`
13. `storage_one_sixthDifference_eq_seven_slopes`
14. `sixthDifference_gammaGap_eventually_eq_seven_slopes`

Each public declaration passed `#assert_prime_depth_source_axioms`,
`#print axioms`, and `#assert_oriented_green_source`. The transitive source
firewall checked **6388 declarations** and rejects moment/HP/Hankel,
Stieltjes/downstream Herglotz, Jacobi/height and BR2 routes.
Axiom footprints are subsets of `[propext, Classical.choice, Quot.sound]`.
No new carriers, metrics, source definitions, boundary reconstruction,
or all-order positivity hypotheses are introduced. The only vector definition
is the seven-node diagnostic in the existing source coefficient space.

## Validation and publication

Validation records are archived in
`research/chiral-first-surviving-boundary-2026-10-08/`.
All validation commands passed. Commands:

```text
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnFirstSurvivingBoundary
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnFirstSurvivingBoundaryAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

Changed files: new source/audit/report/validation records, root imports, and
an appended README checkpoint. The two pre-existing untracked C2 files are
left untouched. Publication occurs only after complete validation.
