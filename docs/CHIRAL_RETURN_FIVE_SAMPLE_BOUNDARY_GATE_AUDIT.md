# Five-sample chiral return — exact next source sign

## Checkpoint and scope

Audited initial main: `a6bb7ac4d2ed84fe614c3a0600ad1548fe1b82e6`.
`git pull --ff-only` was already up to date; HEAD/main/origin-main matched,
and the initial working tree was clean. Work is exclusively in the llm main
checkout. The published full N=4 result is preserved and not reproved.

Status: `PARTIAL_SOURCE_FIRST_FIVE_SAMPLE_STORAGE_POSITIVITY`.

This round closes the ninth source jet, exact tenth-order remainder, full
vector synthesis of that prefix AND remainder at every fixed finite cutoff,
and the complete five-coordinate limiting Green boundary face. It does NOT
prove full N=5 storage positivity, N=5 return contractivity, arbitrary-N
positivity, a completed positive Green carrier, or strictness all-order.

## Source and vector provenance

Write F for `completedNativeOperatorCharacteristic`, q for the EXISTING
`completedNativeOperatorLogDerivative = -F'/F`, and
mu_(2j) for `completedNativeXiCosineMoment j`. These are raw source integrals,
not canonical logarithmic moments or inputs from any moment positivity
certificate. The existing completed source already retains TFVD tails and
archimedean/chart completion.

The source division-free identity q F = -F' and its differentiated Leibniz
recurrence determine the new jets. The raw cosine kernel gives
F^(10)(0) = -mu_10. We reuse that integral identity directly, without using
any canonical tenth-order logarithmic-moment formula.

For a=mu_0, b=mu_2, c=mu_4, d=mu_6, e=mu_8, f=mu_10, define the raw polynomial

```text
D9 = 22680 b^5 - 18900 a b^3 c + 3150 a^2 b c^2
   + 1260 a^2 b^2 d - 210 a^3 c d - 45 a^3 b e + a^4 f.
```

The kernel proves q^(8)(0)=0 and q^(9)(0)=D9/a^5, as an exact real integral
ratio. No sign of D9 for the actual source is asserted in this round.

The same source analyticity supplies an R analytic at zero with

```text
-I q(I h) = sum_{j<5} (-1)^j c_j h^(2j+1) + h^10 R(h),
c_j = Re(q^(2j+1)(0))/(2j+1)!.
```

R has the correct sign from I^10=-1: it is I times the source Taylor
remainder evaluated at I h. It is not removed or assumed positive.

`radialFifthOddSourceTemplate_synthesis` is an equality of vectors in the
UNCHANGED `CanonicalCompletedNativeChiralCauchyCarrier`, before the mixed
readout. It retains every finite coordinate and the entire analytic
remainder. `radialFifthOddSourceTemplate_eventually_eq_slopes N` identifies
the template with the actual source at all original radial nodes for each
fixed finite N, with a threshold uniform over those nodes. This is not one
threshold uniform over arbitrary N.

## Complete five-coordinate boundary face

The zero-step boundary face is obtained from the existing alternating
polarized Green tower. The source coefficients c_0,...,c_4 are factorial
normalized derivatives, independent of canonical moment targets.

Its even sector uses u=x_0, v=x_2, w=x_4:

```text
Eeven = c0 |u|^2 - 2 c1 Re(conj(u)v) + 2 c2 Re(conj(u)w)
      + c2 |v|^2 - 2 c3 Re(conj(v)w) + c4 |w|^2.
```

Its odd sector is exactly the previously certified two-coordinate source
energy on x_1,x_3. The total is twice the sum of these two sectors.
`nativeSourceFiveBoundaryEnergy_eq_alternating_green` includes all crosses.
Its zero extension defines only the limiting jet FACE; no higher jet of the
actual source is set to zero at a nonzero radial step.

Put delta=c0*c2-c1^2, already strictly positive by the earlier raw integral
certificate, and

```text
D = c0 c2 c4 + 2 c1 c2 c3 - c0 c3^2 - c1^2 c4 - c2^3.
```

The kernel checks, in the existing complex norm,

```text
Eeven = c0 |u - (c1/c0)v + (c2/c0)w|^2
      + (delta/c0) |v + ((c1 c2-c0 c3)/delta)w|^2
      + (D/delta) |w|^2.
```

This is exact scalar algebra in the original Green face, not a constructed
Gram factor, new state, fitted metric or whitening. It implies and is
accompanied by kernel-checked equivalences:

```text
Eeven is strictly positive on every nonzero triple iff D>0;
the whole five-coordinate face is strictly positive on nonzero x iff D>0.
```

These are diagnosis theorems, not a positivity assumption wrapper or a
claim that the new sign has been proved.

## One remaining raw integral inequality

`nativeSourceFiveEvenDiscriminant_integral_formula` gives

```text
D = P10(a,b,c,d,e,f)/(4572288000 a^5),

P10 = 105 a^2 b d f - 180 a^2 b e^2 - 350 a^2 c^2 f
    + 2520 a^2 c d e - 2646 a^2 d^3 + 525 a b^2 c f
    - 2205 a b^2 d e - 9450 a b c^2 e + 26460 a b c d^2
    - 14700 a c^3 d + 14175 b^3 c e - 35280 b^3 d^2
    + 22050 b^2 c^2 d.
```

Let S6=15 b^2 c+3 a b d-10 a c^2, whose positivity is already certified
source-first. Exact algebra gives

```text
P10(a,b,c,d,e,f) = 35 a S6 f + P10(a,b,c,d,e,0).
```

Since a>0 and S6>0, the NEW obligation is EXACTLY

```lean
-nativeSourceTenthMixedNumerator
  (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
  (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
  (completedNativeXiCosineMoment 4) 0 /
  (35 * completedNativeXiCosineMoment 0 *
    (15 * completedNativeXiCosineMoment 1 ^ 2 * completedNativeXiCosineMoment 2 +
      3 * completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 1 *
        completedNativeXiCosineMoment 3 -
      10 * completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 2 ^ 2)) <
  completedNativeXiCosineMoment 5
```

Equivalently P10(mu_0,...,mu_10)>0. This is the only new sign obligation
isolated here. After it is actually certified, the exact source remainder
still must be sewn into a uniform full N=5 storage argument, using the
boundary reconstruction/regularization mechanism already successful at N=4.
That subsequent transport has NOT been claimed in this round.

## Exact obstruction to reusing the old box alone

The refined tail upper theorem currently has a p<=8 hypothesis; the refined
first-mode integral certificate exposes orders 0,2,4,6,8. No new joint
order-ten sign certificate is supplied by those statements.

More strongly, `nativeSourceRefinedBox_does_not_force_fiveEvenSign` proves an
exact rational counterexample to the INFERENCE from the existing box and
previous mixed signs (even supplemented by positivity of the ninth jet):

```text
a = 19884837/40000000; b = 574269/25000000;
c = 740861/250000000; d = 299619/500000000;
e = 161051/1000000000; f = 53/1000000.
```

This point satisfies every existing five-integral box bound, f>0, S6>0,
P8>0 and D9>0, but P10<0. All comparisons are exact rational kernel checks.
It is NOT the tuple of actual source integrals. It is not a no-go for N=5,
contractivity or the theory. It proves the old bounds and individual jet
signs alone do not certify this mixed block. A sharper JOINT integral
certificate or a source identity supplying the displayed lower bound is
needed. No constants from this witness define a source or realization.

## Public declarations and dependencies

New modules:

- `CompletedNativeChiralReturnNinthSourceJet.lean`;
- `CompletedNativeChiralReturnFiveBoundaryFace.lean`;
- `CompletedNativeChiralReturnFiveBoundaryFaceAudit.lean`.

The dedicated audit checks all 23 new public declarations with
`#assert_prime_depth_source_axioms`, `#print axioms`, and the transitive
`#assert_oriented_green_source` firewall. The actual types and proof values
are traversed, including the raw tenth source derivative. Canonical moment
positivity, HP/Stieltjes, Hankel, Jacobi/height, Herglotz certificates and BR2
cannot supply this new result. No Foundation changes or trust escapes.

Validation results and final dependency count are recorded below after the
commands complete.

## Validation result

PASS on llm, with the repository's current Lean toolchain:

```text
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnNinthSourceJet
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnFiveBoundaryFace
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnFiveBoundaryFaceAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

The leaf audit checks a transitive closure of **5,506 declarations**. All 23
public declarations have an axiom footprint no larger than
`[propext, Classical.choice, Quot.sound]`. The new Lean files pass the trust
escape/placeholder scan. The root module, root audit and full kernel audit
pass. An initial script invocation lacked lake on PATH; rerunning the whole
script with the elan bin directory on PATH passed. This was an environment
invocation error, not a kernel proof failure.

Logs: `llm:/tmp/chiral-five-boundary-validation/` (leaf/source audit, root
build, root audit, static audit and full script audit). GitHub Actions status
is distinct from these completed server kernel checks; no CI success is
inferred from them.

Files modified: the two new source modules, their dedicated audit, root
module and root audit imports, README, and this report. No existing source,
metric, source-to-TFVD encoding, completion channel or Foundation definition
is changed. Publication uses small semantic commits directly on main; the
final SHA and remote-ref/clean-tree confirmation are reported in the final
response after push.
