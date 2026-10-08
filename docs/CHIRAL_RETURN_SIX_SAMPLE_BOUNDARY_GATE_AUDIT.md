# Six-sample chiral source boundary gate

## Verified checkpoint and scope

- Repository: `thiagomassensini/carry-self-adjoint-operator`, exclusively `main`.
- Initial `HEAD = main = origin/main`: `fbc9636836be11a42e10109abb2d9a406cb29c8d`.
- `git pull --ff-only` was already up to date; the initial working tree was clean.
- Status: **PARTIAL_SOURCE_FIRST_SIX_SAMPLE_STORAGE_POSITIVITY**.

The full N=5 source storage positivity and return contractivity remain
established. This round derives the next exact source jet and localizes
the new N=6 boundary sign. It does not prove or refute full N=6 storage
positivity, and does not claim arbitrary-N contractivity.

## Unchanged source and exact derivative provenance

The source remains `completedNativeOperatorLogDerivative = -F'/F`, with
`F = completedNativeOperatorCharacteristic`. Write

```text
mu_j = completedNativeXiCosineMoment j,
c_j = nativeSourceOddBoundaryCoefficient j
    = Re(iteratedDeriv (2*j+1) (-F'/F) 0)/(2*j+1)!.
```

The new `iteratedDeriv_twelve_completedNativeOperatorCharacteristic_zero`
extends the existing cosine integral derivative chain in its original
module. It proves `F^(12)(0) = mu_6`, with positive sign. It uses the same
integrability and differentiation-under-the-integral lemmas; no new source,
completion factor or target moment is introduced.

`nativeSourceLogSlope_eleventh_derivative_eq_integralRatio` follows from
the existing division-free source product recurrence at order 11 and the
previous source derivatives. For `(a,b,c,d,e,f,g)=(mu_0,...,mu_6)`:

```text
q^(11)(0) = E11/a^6,
c_5 = E11/(39916800*a^6),

E11 = -a^5*g + 66*a^4*b*f + 495*a^4*c*e + 462*a^4*d^2
      -2970*a^3*b^2*e -27720*a^3*b*c*d -11550*a^3*c^3
      +83160*a^2*b^3*d +311850*a^2*b^2*c^2
      -1247400*a*b^4*c +1247400*b^6.
```

This is a raw source identity, not a transported canonical moment formula.
The tenth source derivative vanishes by the same recurrence and parity.

## Complete synthesis before mixed readout

`nativeSourceTransverseSlope_six_exact_remainder` proves existence of one
analytic R at zero with the exact germ identity

```text
-I q(I h) = sum_{j<6} (-1)^j c_j h^(2*j+1) + h^12 R(h).
```

`radialSixthOddSourceTemplate_synthesis` then proves an equality of vectors
in the EXISTING Cauchy carrier, for every finite node family, retaining all
six odd prefix terms and the entire analytic remainder. Only after this
synthesis can a mixed source pairing be read. The same original radial
nodes and `canonicalGreenJetStep` are used.

`radialSixthOddSourceTemplate_eventually_eq_slopes` supplies ONE eventual
threshold for all nodes of each FIXED finite cutoff N. It does not supply
one common threshold for arbitrary N, and asserts no remainder sign.
Zero extension used below describes only the limiting boundary face;
it does not truncate the finite-step vector or erase the remainder.

## Exact six-coordinate boundary face

The even coordinates 0,2,4 reuse the already certified
`nativeSourceFiveEvenBoundaryEnergy`. The new odd coordinates 1,3,5 have

```text
Eodd(u,v,w) = c_1 |u|^2 - 2 c_2 Re(conj(u)*v)
           + 2 c_3 Re(conj(u)*w) + c_3 |v|^2
           - 2 c_4 Re(conj(v)*w) + c_5 |w|^2.

Dodd = c_1*c_3*c_5 + 2*c_2*c_3*c_4
       - c_1*c_4^2 - c_2^2*c_5 - c_3^3.

E6(x) = 2*(Eeven(x_0,x_2,x_4) + Eodd(x_1,x_3,x_5)).
```

All three odd-sector crosses remain. The complete E6 agrees exactly with
the existing alternating polarized Green boundary sum through j=5;
`nativeSourceSixBoundaryEnergy_eq_alternating_green` checks the signs and
indices, rather than assuming a target kernel.

Let `delta = c_1*c_3-c_2^2`. The earlier source certificates already prove
`c_1 > 0` and `delta > 0`. An exact identity in the unchanged complex norm is

```text
Eodd = c_1 |u-(c_2/c_1)v+(c_3/c_1)w|^2
     + (delta/c_1) |v+((c_2*c_3-c_1*c_4)/delta)w|^2
     + (Dodd/delta) |w|^2.
```

It is elementary algebra of the original form, not a new metric,
whitening, square-root operator or Gram realization. Testing the direction
that kills the first two squares also proves necessity of `Dodd > 0`.
Consequently, strict positivity of the whole six-coordinate face is
EQUIVALENT to this single new sign.

## The one raw-integral sign

The polynomial `nativeSourceTwelfthMixedNumerator` is defined explicitly
in `CompletedNativeChiralReturnSixBoundaryFace.lean` from the displayed
raw source coefficients. The kernel proves

```text
Dodd = nativeSourceTwelfthMixedNumerator(mu_0,...,mu_6)
       / (1520925880320000 * mu_0^6).
```

The denominator is positive by the existing source integral theorem.
The capstone is

```lean
nativeSourceSixBoundaryEnergy_pos_iff_rawIntegral :
  (forall x : Fin 6 -> C, x != 0 -> 0 < nativeSourceSixBoundaryEnergy x)
  <-> 0 < nativeSourceTwelfthMixedNumerator(mu_0,...,mu_6)
```

The remaining boundary obligation is exactly the RIGHT-HAND inequality.
No assumption wrapper, target-defined vector or unproved sign is added.
After this sign closes, a separate transfer must still control the full
N=6 remainder uniformly, as was done at N=5.

## Exact obstruction to reusing the previous independent box

`nativeSourcePreviousThetaBox_does_not_force_sixOddSign` gives an exact
rational tuple inside all six theta intervals from
`CompletedNativeThetaTenthSourceCertificate`, with positive new theta entry,
positive induced raw Xi entries and positive previous mixed numerator,
but NEGATIVE new mixed numerator. The witness is

```text
(t0,t2,t4,t6,t8,t10,t12) =
(23033696541651/2000000000000000,
 30915154979/125000000000000,
 20000578953/1000000000000000,
 5754128737/2000000000000000,
 1179540429/2000000000000000,
 31050931/200000000000000,
 1/100000000000000).
```

The induced entries use the existing integration-by-parts expressions:

```text
mu_0 = 1/2-t0/4;
mu_1 = 2*t0-t2/4;      mu_2 = 12*t2-t4/4;
mu_3 = 30*t4-t6/4;     mu_4 = 56*t6-t8/4;
mu_5 = 90*t8-t10/4;    mu_6 = 132*t10-t12/4.
```

All inequalities are proved by exact rational arithmetic in Lean.
The witness is NOT claimed to be the actual theta source or to satisfy
all correlations obeyed by its integrals. It refutes only sufficiency of
the independent old box plus the listed positive quantities. It is NOT a
counterexample to canonical storage positivity. Better source integral
bounds or correlated source identities are needed to certify the new sign.

## Files, source firewall and validation

New modules:

- `CompletedNativeChiralReturnEleventhSourceJet.lean`;
- `CompletedNativeChiralReturnSixBoundaryFace.lean`;
- `CompletedNativeChiralReturnSixBoundaryBoxObstruction.lean`;
- `CompletedNativeChiralReturnSixBoundaryFaceAudit.lean`.

The existing `CompletedNativeXiCosineMoments.lean` gains the integral
derivative chain through order 12. Root and root Audit import the new gate.
README records this partial checkpoint without removing the closed N=5 result.
No source definition, carrier, readout, metric or audit firewall changes.

The dedicated audit checks all 23 new public declarations with
`#assert_prime_depth_source_axioms`, `#print axioms`, and the transitive
`#assert_oriented_green_source`; its source dependency traversal checks
5,536 declarations. The narrow existing classical-theta
exceptions remain unchanged. Canonical targets, HP/Stieltjes positivity,
Hankel, spectral Jacobi/height and BR2 are excluded as proof dependencies.
The allowed footprint remains `[propext, Classical.choice, Quot.sound]`.

Validation commands on llm, Lean v4.32.0:

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnEleventhSourceJet
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnSixBoundaryBoxObstruction
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralReturnSixBoundaryFaceAudit
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
```

All listed builds and audit scripts passed, including the dedicated source
firewall and the placeholder/whitespace scans. Validation outcomes are recorded in
`research/chiral-six-source-gate-2026-10-08/validation.txt`.
Detailed logs are preserved on llm in `/tmp/chiral-six-boundary-validation/`.
Final ref equality and clean working tree are checked after commit/push.

## Boundary between proved and open

PROVED: F12 and q11 raw integral formulas; exact twelfth-order vector
remainder synthesis; both parity faces and all crosses; exact positivity
criterion for the N=6 boundary face; insufficiency of the old independent box.

OPEN: the actual source polynomial sign, full N=6 storage transfer,
arbitrary-N source positivity and all-order contractivity.
