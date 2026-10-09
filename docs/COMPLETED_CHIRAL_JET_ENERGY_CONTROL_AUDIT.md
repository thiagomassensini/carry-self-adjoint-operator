# Completed chiral jet energy control

Date: 2026-10-09.

## Checkpoint

Repository: `thiagomassensini/carry-self-adjoint-operator`, published `main`.
Initial HEAD = main = origin/main:
`d45c1aa51647ec8cf6ab1b0847c960a3fe1392eb`.
`git pull --ff-only`: already up to date. Tracked working tree initially clean.
The two user-owned untracked `C2OddTfvdTransport*.lean` files are preserved.

Statuses:

- `PASS_FIXED_DIMENSION_COMPLETE_CHIRAL_ENERGY_CONTROL`.
- `PASS_CERTIFIED_SIX_JET_CHIRAL_DOMINANCE`.
- `PASS_GEOMETRIC_CHIRAL_JET_STORAGE_TRANSPORT`.
- General completed storage positivity remains open.

The previous material-clock injectivity and log-gap decomposition are not
reproved. Injectivity alone does not imply a sign for a signed form. The useful
existing input for this increment is the ALL-ORDER signed coefficient limit
of the completed projective/chiral difference jets.

## Same existing vectors, not a fitted state

Let

```lean
J n k x := nativeSourceProjectiveBoundaryJetSynthesis n k x
```

with its existing type `CanonicalCompletedNativeProjectiveChiralCarrier`.
Its even/odd phases, normalization, radial sampling and complete F/-F' source
remain unchanged. No public vector definition, new carrier, operator or metric
is added. Neither canonical moments nor a positive target Gram defines J.

Set, as explanatory notation only,

$$
D_{n,k}(x)=2\bigl(\|J_{n,k}(x)_+\|^2-\|J_{n,k}(x)_-\|^2\bigr).
$$

The old theorem already identifies its pointwise limit with the RAW source
energy `nativeSourceFiniteBoundaryEnergy (2*n) x`. Denote this existing
expression by E_(2n)(x). Its factors are not adjusted:

$$
D_{n,k}(x)=4\Re\mathcal B(J_{n,k}(x),J_{n,k}(x)).
$$

## Unconditional control, arbitrary fixed dimension

New capstone:

```lean
nativeSourceProjectiveBoundaryJetSynthesis_eventually_energy_control
    (n : ℕ) (η : ℝ) (hη : 0 < η) :
  ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
    |2 * (‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).1‖^2 -
      ‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).2‖^2) -
        nativeSourceFiniteBoundaryEnergy (2*n) x| ≤ η * ‖x‖^2
```

Quantifiers are:

$$
\forall n\;\forall\eta>0\;\exists K_{n,\eta}\;
\forall k\ge K_{n,\eta}\;\forall x.
$$

No positive boundary hypothesis is present. No threshold uniform in dimension
is claimed. The coefficient norm is the EXISTING finite Pi norm (supremum of
coordinate norms), used solely for an error estimate, not as a new metric on
any source or chiral carrier. n=0 is included without a sign premise.

### Why the complete error is controlled

The finite index set is `Fin n ⊕ Fin n`, of cardinality 2n. The old vector
synthesis is expanded sesquilinearly, after its two channels are retained.
Mathlib conjugates the first argument. The inherited phases have modulus one,
so each coefficient has norm at most the original coefficient norm.

For each ordered pair of jet orders the existing completed signed pairing
converges to its already-proved polarized source coefficient. Choose

$$
\delta=\frac{\eta}{4(2n)^2+1}.
$$

Finiteness supplies ONE eventual threshold at which all ordered-pair errors
have norm at most delta. Summing their absolute values bounds their aggregate
by `(2n)^2 * delta * norm(x)^2`; the final signed diagonal has the factor 4.

This includes even/even, odd/odd and BOTH mixed sectors at finite k. Mixed
terms are not deleted by using their limiting parity zero early. The private
limit recombination is identified with E through the old energy-limit theorem
and uniqueness of limits, not through a positive Gram.

No Taylor truncation replaces the finite vectors. The exact completed source
inside each pairing retains its higher analytic terms and completion. The
estimate controls their aggregate signed finite-step error as it actually
occurs in J; it is not asserted as a bound on a different TFVD/Gamma carrier.

## Reuse of the old six-source margin

The existing
`radialSixRegularizedStorage_eventually_unit_margin` already has its source
integral proof. Evaluating its neighborhood assertion at radial step zero
recovers the old six-coordinate boundary margin. The zero auxiliary remainder
function is used ONLY to read this already-proved boundary assertion at zero;
it never replaces the actual remainder of any finite-step source.

The new exact identity

```lean
nativeSourceFiniteBoundaryEnergy_six (x : Fin 6 → ℂ) :
  nativeSourceFiniteBoundaryEnergy 6 x = nativeSourceSixBoundaryEnergy x
```

checks the SAME zero extension, source coefficients, ordered crosses and
factor 2 of the old raw expression. No normalization is fitted.
`nativeSourceFiniteBoundaryEnergy_smul` exposes its existing complex quadratic
homogeneity. Scaling the old unit-sphere bound gives its margin in the existing
coordinate norm, without a new source sign certificate.

Consequently, for every eta>0, eventually uniformly over ALL x in `Fin 6 → ℂ`:

$$
|D_{3,k}(x)-E_6(x)|\le\eta E_6(x).
$$

This is
`nativeSourceProjectiveBoundaryJetSynthesis_six_eventually_relative_control`.
Taking eta=1/2 proves the actual chiral-channel inequality

```lean
nativeSourceProjectiveBoundaryJetSynthesis_six_eventually_dominant :
  ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop, ∀ x : Fin 6 → ℂ,
    ε * ‖x‖^2 ≤
      ‖(nativeSourceProjectiveBoundaryJetSynthesis 3 k x).1‖^2 -
        ‖(nativeSourceProjectiveBoundaryJetSynthesis 3 k x).2‖^2
```

In the proof epsilon is one quarter of the recovered source boundary margin.
It gives strict dominance for every nonzero x in this certified sector.
This transports an EXISTING six-source sign to the actual completed chiral
jet vectors. It does not start another dimension-by-dimension certificate
program, nor certify N=8. The current even-jet API naturally uses n=3 here.

## Exact whole-source transport to ORIGINAL storage

A subsequent inspection found the vector sewing directly in the existing
projective/chiral graph definitions. It is now formalized in
`CompletedNativeChiralJetStorageTransport`, before any scalar readout.

```lean
nativeSourceChiralJetInput (n k : ℕ) :
  (Fin (2*n) → ℂ) →ₗ[ℂ] (Fin (2*n) → ℂ)
```

Its source-coordinate matrix is fixed by the old finite-difference geometry:

$$
U_{r,a}(k)=A_{k,r}\,\sigma_a\,(a!H_k^a)^{-1}
  (-1)^{a-r}\binom ar,
$$

where `A` is the EXISTING
`completedNativeNormalizedPositiveChiralAmplitude` at the radial node,
`H` is the EXISTING `canonicalCompletedC3RadialSecondStep`, and
`sigma_a=(-1)^(floor(a/2))` is the inherited raw boundary phase.
The coefficient vanishes for r>a. No moment, sign assumption, matrix square
root, spectral data or adjustable weight defines this matrix. It is a
coordinate transform, not a moment Gram or a new operator of heights.

`nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource` proves EXACTLY:

```lean
nativeSourceProjectiveBoundaryJetSynthesis n k x =
  (radialIncidentSynthesis k (2*n) (nativeSourceChiralJetInput n k x),
   radialReturnedSynthesis k (2*n) (nativeSourceChiralJetInput n k x))
```

The same coefficient map is used on BOTH completed Cauchy channels. Forward
weights vanish outside their original finite support, which is proved before
regrouping the two vector sums. Both vector equalities precede any inner
product. This does not invert a scalar TFVD trace into an infinite source
state; it regroups the already-existing complete finite graph vectors.

The unchanged old norm-balance identity then gives the exact factor:

$$
D_{n,k}(x)=2\Re S_k(U_{n,k}x,1).
$$

`nativeSourceChiralJetInput_injective` proves invertibility algebraically,
using the triangular matrix with diagonal
`A_(k,r)*sigma_r/(r!*H_k^r)`. All diagonal factors are nonzero wherever the
completed characteristic and positive chiral coordinate are regular.
`nativeSourceChiralJetInput_eventually_bijective` proves eventual bijectivity
for each fixed n. No conditioning uniform in k or n, or isometry, is claimed.

Therefore the absolute error control now applies directly to ORIGINAL storage:

```lean
storage_one_chiralJetInput_eventually_energy_control (n : ℕ)
    (η : ℝ) (hη : 0 < η) :
  ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
    |2 * (storage k (nativeSourceChiralJetInput n k x) 1).re -
      nativeSourceFiniteBoundaryEnergy (2*n) x| ≤ η * ‖x‖^2
```

`storage_one_chiralJetInput_allCoefficients_control` includes the quantifier
over EVERY original source input c, with its geometric coordinate x such that
`U x=c`. Bijectivity makes x unique; a fitted inverse is not constructed.
This covers every even finite family used by the boundary/parity route.
The estimate is in geometric jet coordinates, not a uniform bound for the
inverse chart in the original coefficient norm.

The certified six-source margin also transports to
`storage_one_chiralJetInput_six_eventually_relative_control` and
`storage_one_chiralJetInput_six_eventually_coercive`. This uses only the old
source sign and the proved whole-vector equality.

### The actual raw Gamma correction is also controlled

Reuse the old, fully synthesized identity, without deleting the three
coisometric comparison channels manually:

$$
\Re S_k(c,1)=2\|\Gamma_{k,c}\|^2-
  2\Im(\mathrm{rawGammaWronskianBalance}_{k,c,c,1,1}).
$$

The NEW `rawGamma_chiralJetInput_eventually_energy_control` proves

$$
\left|4\bigl(\|\Gamma_{k,Ux}\|^2-\Im R_{k,Ux,Ux}\bigr)
  -E_{2n}(x)\right|\le\eta\|x\|^2
$$

in every fixed even finite order, uniformly over coefficients. This is the
actual completed correction gap, not a proxy or an unrelated positive Gram.
`rawGamma_chiralJetInput_six_eventually_coercive` gives its positive uniform
margin in the already-certified six-coordinate sector.

## Exact remaining all-order sign

Status added: `PASS_GEOMETRIC_CHIRAL_JET_STORAGE_TRANSPORT`.
The all-order correction is controlled in this geometric chart. The old
seven-source regularization/control is not reconstructed; N=8 is not certified.

The unproved source inequality needed to turn this control into strict
positivity at EVERY order remains exactly:

```lean
∀ n : ℕ, 1 ≤ n →
  ∀ x : Fin (2*n) → ℂ, x ≠ 0 →
    0 < nativeSourceFiniteBoundaryEnergy (2*n) x
```

In each fixed dimension a strict continuous quadratic boundary has a positive
unit-sphere margin, so the new uniform error estimate can retain it. This
explains sufficiency; it is not a proof of the missing all-order boundary sign.
The existing raw boundary/Stieltjes equivalence diagnoses this gate only and
is not used to provide any sign here. No new hypothesis wrapper is added.

Material log-clock jets, spectral finite differences and the internal Cauchy
radius remain distinct. The newly proved finite source transport is precisely
U above; it does not identify material node indices with radial order/depth,
or provide a new Green Hilbert kernel, positive moment certificate, or height
closure. All completed channels, analytic terms and crosses in original
storage and its corrected ledger remain unchanged.

## Public declarations and dependency audit

The first module adds five public theorems:

1. `nativeSourceProjectiveBoundaryJetSynthesis_eventually_energy_control`;
2. `nativeSourceFiniteBoundaryEnergy_smul`;
3. `nativeSourceFiniteBoundaryEnergy_six`;
4. `nativeSourceProjectiveBoundaryJetSynthesis_six_eventually_relative_control`;
5. `nativeSourceProjectiveBoundaryJetSynthesis_six_eventually_dominant`.

The source transport module adds ten public theorems:

1. `nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource`;
2. `nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage`;
3. `storage_one_chiralJetInput_eventually_energy_control`;
4. `storage_one_chiralJetInput_six_eventually_relative_control`;
5. `storage_one_chiralJetInput_six_eventually_coercive`;
6. `nativeSourceChiralJetInput_injective`;
7. `nativeSourceChiralJetInput_eventually_bijective`;
8. `storage_one_chiralJetInput_allCoefficients_control`;
9. `rawGamma_chiralJetInput_eventually_energy_control`;
10. `rawGamma_chiralJetInput_six_eventually_coercive`.

Its three public definitions are `nativeSourceJetOrderPhase`,
`nativeSourceChiralJetInputMatrix`, and `nativeSourceChiralJetInput`.

Every theorem receives `#assert_prime_depth_source_axioms` and `#print axioms`
in the dedicated audit. Footprint: only
`[propext, Classical.choice, Quot.sound]` or a subset.

Raw algebra passes `#assert_oriented_green_source`. The completed-limit proof
reuses the old final scalar uniqueness identification, without a moment-sign
premise. Its closure passes `#assert_even_boundary_no_downstream`. An additional
stricter check rejects EVERY Hankel/Stieltjes declaration, even a target
predicate, on the complete type/proof closures: 5673 declarations checked for
the energy module, and 6631 for the whole-source/Gamma transport.
HP certificates, spectral Jacobi/height, moment-Gram positivity, Herglotz and
BR2 consumers are also rejected by the existing checker. No BR2 is used.

## Validation and publication

Executed on the authoritative remote checkout, with full logs and readable
tails in `research/completed-chiral-jet-energy-2026-10-09/`:

```text
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralJetEnergyControl
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralJetEnergyControlAudit
lake env lean CarrySelfAdjointOperator/CompletedNativeChiralJetEnergyControlAudit.lean
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransport
lake build --wfail CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransportAudit
lake env lean CarrySelfAdjointOperator/CompletedNativeChiralJetStorageTransportAudit.lean
lake build --wfail CarrySelfAdjointOperator
lake build --wfail CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
git diff --cached --check
```

All passed before publication. README and root audit imports are updated.
The existing canonical vectors and metrics are unchanged. User untracked files
retain their initial hashes and are excluded from staging. At handoff tracked
files are clean; the two user untracked files intentionally remain. Remote main
identity is verified after commit/push; CI status is reported separately from
the executed Lean kernel validation.

Proof declarations commit: `449e042df9ee378c43d5ffc6cd47701663d90066`.
The following documentation commit publishes this report and its validation logs.
