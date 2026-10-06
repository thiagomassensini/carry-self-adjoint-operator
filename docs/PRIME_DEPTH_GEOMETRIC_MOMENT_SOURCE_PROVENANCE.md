# Prime-depth geometric moment source provenance

STATUS: `PASS_PRIME_DEPTH_GEOMETRIC_MOMENT_RECURRENCE`.

Initial main: `247448fa1a51f42163d7106315f22f05237e55d1`.
Pinned CPFormal: `65d50f6db1208708e109982ba97e1d51d3039956`.

## Scope and result

BR2 is not a source premise. The new sequence is the real part of the odd
Taylor coefficients of the existing completed prime-depth response. That
response is defined by actual prime-depth log brackets, a finite head and
exact tail, chart correction, ordinary material readout, and the separate
archimedean completion channel. No target moment or matrix is used to define
it. The source equation is proved first and uniqueness identifies it last.

This closes scalar response-to-moment recurrence and identification. It does
not derive the archimedean factor from C2, equate the finite odd-core extraction
with the universal completed response, or construct a positive Hilbert pairing
of response jets. No new Gram, Hankel, Jacobi or operator is constructed.

## Gate 0: exact genealogy and types

| Arrow/object | Type or endpoint | Classification / actual evidence |
|---|---|---|
| C2 center -> current depth and positive odd core | natural indices with literal center `4*(j+1)` | KERNEL_CHECKED: `c2AlignedCenter_log_eq_currentDepth_add_primeCoreLedger` |
| prime positional depth -> ledger | `primeDepthLogLedger : ℕ → ℝ` | DEFINITIONAL finite sum of `positionalDepth p n * log p`; KERNEL_CHECKED `primeDepthLogLedger_eq_log` for nonzero n |
| ledger -> ordinary/log material atoms and consecutive slopes | `positiveLogDirichletValue s n` and `positiveLogDirichletGradient s n` in ℂ | KERNEL_CHECKED `positiveLogDirichletValue_eq_primeDepthLogLedger_mul`, `positiveLogDirichletGradient_eq_primeDepthSlope`; positive indexing is material integer n+1 |
| native material slopes -> finite prime-depth Hilbert prefix | `finitePrimeDepthGeneratedLogSlopePrefixState M t : CarryVerticalL2` | DEFINITIONAL packaging; KERNEL_CHECKED equality with native and completed TFVD logJet prefixes |
| ordinary + log slope prefix -> two-channel TFVD prefix | `finitePrimeDepthGeneratedC3HilbertPrefixState M t : CanonicalCompletedC3HilbertState` | KERNEL_CHECKED `finitePrimeDepthGeneratedC3HilbertPrefixState_eq_completedTfvd` |
| finite prefix -> complete two-channel difference state | `canonicalCompletedC3HilbertState s hs : CarryVerticalL2 × CarryVerticalL2`, hs: 0 < Re(s) | KERNEL_CHECKED `canonicalCompletedC3HilbertPrefixState_tendsto`; this pair alone does not include every scalar boundary/completion channel |
| TFVD head + exact value/log tails -> structured source | `canonicalC3BracketTfvdCompletionState M s : CanonicalC3BracketTfvdCompletionState M` | DEFINITIONAL retained transport plus two separate tails; KERNEL_CHECKED transport components, tail completion and Green port identities |
| prime-depth completed log head/tail -> normalized material response | `primeDepthNativeHeightScalarNormalizedResponse : ℂ → ℂ` | DEFINITIONAL normalized value/companion response; chart derivative correction retained |
| independent archimedean channel + material response | `primeDepthCompletedNativeNormalizedResponse : ℂ → ℂ` | DEFINITIONAL sum; KERNEL_CHECKED equality of germs with the completed normalized response |
| completed response -> all-order coefficients | `primeDepthCompletedNativeResponseTaylorCoefficient : ℕ → ℂ` | DEFINITIONAL normalized iterated derivatives; no moment sequence in its definition |
| odd coefficients -> real source sequence | `primeDepthGeometricMoment : ℕ → ℝ` | DEFINITIONAL real part; KERNEL_CHECKED reality and recurrence independently of the target |
| independent recurrence -> canonical identification | equality of sequences ℕ → ℝ | KERNEL_CHECKED `primeDepthGeometricMoment_eq_canonical`, by `IsLogDerivativeMomentSequence.unique` only |
| local tower/finite C2 logarithmic extraction -> this universal completed response | no direct source intertwiner identified in this audit | OPEN; do not infer it from equality of arithmetic logarithms |

The earliest all-order material jet data are the two-index slope Taylor
coefficients `nativeLogDirichletSlopeTaylorCoefficient order n`. The first
object carrying the entire completed moment readout is the analytic germ
`primeDepthCompletedNativeNormalizedResponse`; its normalized derivative
sequence exposes that data explicitly. The last such object before the old
module mentions canonical moments is `primeDepthCompletedNativeResponseTaylorCoefficient`.

The preexisting `canonicalCompletedNativeLogDerivativeMoment_eq_primeDepthResponse`
is an exact comparison of germs and coefficients. It does not define prime
coefficients using the target, but its final proof invokes the preexisting
canonical coefficient identification. It is not used in the new independent
recurrence, reality, canaries or TFVD readout proof.

### Two prior bridges that cannot supply the independent proof

`canonicalC2Geometry_nativeWronskianResponse_coefficientEquation_before_gram`
rewrites its coefficient array to the polarized canonical moment array and
then applies the generic equation. Its boundary/shift corollary follows from
that rewrite. It is pre-Gram, but already depends on moment identification.

`canonicalCompletedNativeProjectiveValve_curvature_eq_moments` likewise
uses `projectiveValveMass_nativeMoments_eq_reciprocal`; the underlying
`derivative_completedNativeEvenFormalSeries` was proved from the canonical
moment recurrence. It is a valid scalar normalization theorem, not an
independent source-first proof. Neither theorem is used here.

## Gates 1 and 2: historical hybrid crosswalk and finite defects

No unique declaration named C2 hybrid has been identified. The historical
label can be compared component by component, not equated to one new operator:

| Historical component | Actual current object | Exact scope |
|---|---|---|
| geometric tower / local Mangoldt | `MultiplicativeValve.geometric_isTowerChannel` and `isTowerChannel_iff_isLogDerivChannel` | geometric powers c^k give b(0)=0, b(k)=c^k; restoring log p gives the local prime-tower weight |
| finite C2 mass / logarithmic extraction | `CPFormal.Carry.C2.oddCoreTruncatedMass`, `c2OddCoreNormalizedMassArithmetic`, `c2OddCoreLogCoefficientArithmetic` | actual truncated odd-core branches; normalized unit; Dirichlet inverse of the mass |
| exact finite convolution | `c2OddCoreLogCoefficientArithmetic_mul_mass` | b_T * a_T = a_T log under Dirichlet convolution, not an equality b_T=Λ |
| arithmetic Möbius/log roundtrip | `integerLog_mul_moebius_eq_primePowerSignal`, `primePowerSignal_mul_zeta_eq_integerLog` | exact arithmetic function identities, distinct from the finite carry/cutoff mass |
| depth log clock | `primeDepthLogLedger`, `nativeLogGenerator_basisVector_primeDepthLedger` | prime valuation synthesis equals log(n+1), with an actual native clock crosswalk |
| connected finite dressing | `c2OddCoreConnectedCumulant`, `c2OddCoreDirichletLogSpectralGap`, `c2OddCoreCofinalMassScale` | local mass square, dressed log spectral gap and connected support normalization |
| Green/multiplicative valve | `greenChannelSeries`, `greenMassSeries`, `projectiveGreenMass` | algebraic curvature/Green/integral/exponential construction, with `derivative_projectiveGreenMass` |
| native completed scalar response | `primeDepthCompletedNativeNormalizedResponse` | material TFVD head/tail and chart correction plus independent archimedean factor response |
| moment readout | `primeDepthGeometricMoment` | odd Taylor response coefficients, with independent recurrence now exposed |

The tower convolution is Cauchy convolution in the prime-power exponent.
The finite C2 extraction uses arithmetic Dirichlet convolution in material
integers. They are not conflated by this crosswalk.

Actual finite/cutoff results exist in the pinned source:

- `oddCoreTruncatedMass_lt_one`: finite a_T is below one.
- `oddCoreTruncatedMass_richardson_exact`: for 0 < m ≤ M,
  `2*a_(8M)(m) - a_(4M)(m) = 1`, proved from actual cutoff depths.
- `c2OddCoreLogCoefficient_prime`: b_T(p)=a_T(p)*log p for odd primes.
- `c2OddCoreLogCoefficient_distinct_primes`: at distinct odd primes,
  b_T(pq)=log(pq)*connectedCumulant_T(p,q), rather than automatically Λ(pq)=0.
- `c2OddCoreLogCoefficient_distinct_primes_richardson_exact`: the corresponding
  Richardson expression is log(pq) times the explicit marginal-defect product.
- `c2OddCoreDirichletLogTfvdReadout_eq_logCoefficient_mul`: the local enriched
  TFVD readout equals that finite coefficient dressed by (pq)^(-s).
- `c2OddCoreNormalizedCofinalGpreReadout_eq_natLogDirichletTerm` and its tendsto
  theorem: a normalized local semiprime G-pre cell recovers the log Dirichlet
  vertex under its specified prime/cutoff hypotheses.

These are KERNEL_CHECKED local identities and limits with their exact support.
A universal finite-channel formula `b_T = Λ - carryDefect_T` together with
its completed all-order response intertwiner was not identified in the
inspected APIs. For that stronger historical claim the classification remains
`HISTORICAL_DEFECT_IDENTITY_NOT_YET_PORTED`. In particular, the odd-support
normalization is not silently changed to an all-integer channel.
Three-color/connected-tail notes are not used as formal premises.

## Gates 3 through 5: independent sequence, canaries and uniqueness

Definition:

```lean
def primeDepthGeometricMoment (n : ℕ) : ℝ :=
  (primeDepthCompletedNativeResponseTaylorCoefficient (2*n+1)).re
```

Its proof starts with
`completedNativeGreenNormalizedResponse_mul_characteristic_eventually`:
R(z)F(z)=−F'(z)/2 near zero. The existing
`completedNativeGreenResponse_rawDerivativeRecurrence` uses analytic Leibniz;
factorial normalization and even-characteristic parity give
`completedNativeGreenResponse_oddCoefficient_recurrence`.
Equality of response germs then gives the new prime-depth convolution.
Neither this proof nor taking its real part uses the canonical sequence.

Writing phi_n for `completedNativeRealEvenCharacteristicCoefficient n`,
the source canaries proved are:

- g₀ = −phi₁ / phi₀;
- g₁ = (−2 phi₂ − g₀ phi₁) / phi₀;
- g₂ = (−3 phi₃ − g₀ phi₂ − g₁ phi₁) / phi₀.

The all-order theorem is
`primeDepthGeometricMoment_isLogDerivativeMomentSequence`.
The complex imaginary part is zero by a separate induction on the same
source recurrence, using real phi and phi₀ ≠ 0, not target comparison.
Only the final `primeDepthGeometricMoment_eq_canonical` introduces the
canonical target and applies the real recurrence uniqueness theorem.
No constants have been fitted or moments supplied as data.

## Gate 6: concrete predecessor carrier, without Gram

There are two concrete levels already present:

1. `CanonicalCompletedC3HilbertState = CarryVerticalL2 × CarryVerticalL2`
   retains complete ordinary and log difference channels on Re(s)>0.
2. `CanonicalC3BracketTfvdCompletionState M` additionally retains finite
   enriched transport and exact value/log tails before scalar boundary
   pairing. Its Green port and completed trace are readouts of the same
   structured source. The trace becomes (F,−F') after chart and archimedean
   product-rule dressing, which occurs downstream of joined head/tail.

The new `primeDepthGeometricMoment_eq_bracketTfvdReadoutTaylor M n` proves
that the normalized Wronskian readout of that existing structured carrier
has exactly the geometric moment coefficient, at every cutoff and order,
without referencing canonical moments. This identifies a concrete precursor
and its scalar readout, not a positive metric or moment Gram.

No standalone all-order Hilbert vector-jet family X_n and fixed continuous
linear ell with ell(X_n)=g_n has been constructed. The response uses a
normalized quotient after completed synthesis. Taking a derivative of that
scalar quotient is not automatically a linear readout of a vector derivative.
Raw radial-normalized complex state Taylor jets are not reintroduced.

There is no remaining obligation for the scalar recurrence or its canonical
identification. The single next *vector-source* obligation is to realize
these normalized readout coefficients by provenance-preserving jets of the
completed TFVD source, retaining boundary/tails and the independent
completion channel. The current theorem proves exactly the scalar side:

```lean
(primeDepthGeometricMoment n : ℂ) =
  canonicalC3BracketTfvdResponseTaylorCoefficient M (2*n+1)
```

It does not assert the further linear vector-readout lift, nor any pairing.
The older universal finite-C2/Mangoldt defect identity is a separate historical
claim, not a new hypothesis inserted into this closed prime-depth recurrence.

## POSSIBLE_DOWNSTREAM_STRICTNESS

BR2 is unnecessary in every new definition, recurrence and identification.
If an independent future same-family Gram realization needs linear
independence, BR2 may be tested there as a strictness/transport tool. No such
application is asserted here.

## Declaration and audit ledger

- `primeDepthGeometricMoment`
- `primeDepthResponse_oddCoefficient_recurrence`
- `primeDepthGeometricMoment_zero`
- `primeDepthGeometricMoment_one`
- `primeDepthGeometricMoment_two`
- `primeDepthGeometricMoment_isLogDerivativeMomentSequence`
- `primeDepthResponse_oddCoefficient_im_zero`
- `primeDepthGeometricMoment_coe`
- `primeDepthGeometricMoment_eq_bracketTfvdReadoutTaylor`
- `primeDepthGeometricMoment_eq_canonical`

The focused audit prints all ten public footprints and checks that each is a
subset of `[propext, Classical.choice, Quot.sound]`. All printed footprints
are exactly that set. An additional source-first command walks types and
proof/definition bodies transitively for the nine pre-identification roots.
It checked 5,243 declarations, rejecting reachability of the canonical
recursive sequence and its prefixed lemmas, Hankel matrices, finite Jacobi,
finite height, and the literal BR2 projective Hilbert family. This concerns
actual proof dependencies, not unrelated modules present in the import graph.

The independent response-recurrence declarations were also read explicitly:
their product identity, Leibniz, factorial/parity reduction precede the old
canonical identification and do not use that theorem.

Validation commands:

- `lake build --wfail CarrySelfAdjointOperator.PrimeDepthGeometricMomentRecurrence`
- `lake build --wfail CarrySelfAdjointOperator.PrimeDepthGeometricMomentRecurrenceAudit`
- `lake build --wfail CarrySelfAdjointOperator`
- `lake build --wfail CarrySelfAdjointOperator.Audit`
- `bash scripts/static_audit.sh`
- `bash scripts/audit.sh`
- `git diff --check`

All seven commands passed with exit status 0 before publication. The
static script reported `static audit passed`; the full script reported
`kernel audit passed`. Root and central audit passed `--wfail`. No new
placeholder or trust escape was found, and `git diff --check` was clean. The commit containing this
report is recoverable with
`git log --format=%H -- docs/PRIME_DEPTH_GEOMETRIC_MOMENT_SOURCE_PROVENANCE.md`.
