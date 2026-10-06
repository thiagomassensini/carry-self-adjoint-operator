# Canonical six-frame upper bound

Date: 2026-10-06 (America/Sao_Paulo).
Initial HEAD = main = origin/main:
`62b1c0d6b18e70b4c156c3bdf0253893fdb27a35`.
Repository: `thiagomassensini/carry-self-adjoint-operator`.

## Scope and status

**PASS_CANONICAL_SIX_FRAME_UPPER_BOUND**.

The exact necessary test is closed unconditionally:

```text
for every N:
  6 I_N - Hankel(h,N) is positive semidefinite;
  6 I_N - shiftedHankel(h,N) is positive semidefinite;
where h = canonicalCompletedNativeLogDerivativeMoment.
```

No `CanonicalCompletedNativeTfvdGreenLosslessCorrection`, `hloss`, moment
positivity, Gram representation or spectral certificate is a hypothesis.
The literal BR2 no-go and its order-zero excess `6-h_0` remain unchanged.
The proof does not attempt to identify the uncorrected BR2 jet with moments.

## Existing-theorem audit

The directed source audit found only the conditional
`CanonicalCompletedNativeTfvdGreenLosslessCorrection.six_sub_nativeHankelBlocks_posSemidef`
for this all-order numeric bound. Existing scalar `h_0 < 1/16` does not control
both towers. Existing
`canonicalCompletedNativeLogDerivativeMoment_geometricBound` has existential
positive constants and no certified decay ratio below one or numeric frame
bound six. Neither was promoted to the requested unconditional theorem.

## Proof from the actual canonical source

Write `phi_n = completedNativeRealEvenCharacteristicCoefficient n`.
The new `completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder`
proves, for every n,

```text
phi_n = (-1)^n * completedNativeXiCosineMoment n / (2n)!.
```

The fixed cosine kernel already represents the actual completed native
characteristic on the real height axis. Polynomially weighted integrability
is already local. Dominated differentiation gives cos-channel derivative
minus sin-channel and sin-channel derivative next cos-channel. Induction
therefore closes every even derivative, with its sign and factorial intact;
the existing real/complex derivative crosswalk transfers it to the canonical
coefficients. No finite-order extrapolation is used.

The existing explicit majorant
`calibration_thetaTail_le_exp` gives

```text
A(u) <= (1/7) exp(-5u), u >= 0;
ThetaTailMoment(p) <= p! / (7 * 5^(p+1)).
```

This uses the ordinary Gamma integral of a polynomial times an exponential,
not a supplied moment table. The already proved all-order integration by
parts identity for the fixed cosine kernel gives

```text
mu_(n+1) = (2n+2)(2n+1) ThetaTailMoment(2n)
           - (1/4) ThetaTailMoment(2n+2).
```

Its positive cosine moments and nonnegative theta moments are properties of
that preexisting kernel, not assumptions about the logarithmic moment Hankel.
Dropping the subtracted nonnegative term only in an upper bound and cancelling
the factorial yields

```text
phi_0 >= 1/3;
|phi_(n+1)| <= 1 / (35 * 25^n);
|phi_(n+1)| <= phi_0 * (1/4)^(n+1).
```

The unchanged canonical logarithmic recurrence, by strong induction, then gives

```text
|h_n| <= (1/2) * (3/4)^n.
```

The constants are coarse analytic estimates, not adjustments to the sequence,
carrier, metric or literal BR2 energy.

## Uniform quadratic estimate and PSD

For every cutoff N, every shift s, and every complex vector x:

```text
|x* H_(N,s) x| <= 2 * sum_i |x_i|^2,
H_(N,s)(i,j) = h_(i+j+s).
```

Entrywise absolute decay bounds this quadratic form by
`(1/2) (sum_i (3/4)^i |x_i|)^2`. Finite Cauchy-Schwarz and the elementary
geometric prefix bound `sum_i (3/4)^i <= 4` give the stated estimate.
The matrix is Hermitian because h is real and i+j is symmetric. Consequently
`x* (6I-H_(N,s)) x >= 0`. The requested two towers are exactly s=0 and s=1.
This proves an upper bound, independently of whether H itself is PSD.

## Public theorems

`CompletedNativeAllOrderMomentUpperBound.lean`:

- `completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder`
- `completedNativeThetaTailMoment_factorial_upper`
- `completedNativeRealEvenCharacteristicCoefficient_zero_ge_third`
- `completedNativeRealEvenCharacteristicCoefficient_succ_abs_upper`
- `completedNativeRealEvenCharacteristicCoefficient_succ_relative_bound`
- `canonicalCompletedNativeLogDerivativeMoment_explicit_decay`

`CompletedNativeSixFrameUpperBound.lean`:

- `canonicalCompletedNativeHankel_quadratic_norm_le_two`
- `canonicalCompletedNative_six_sub_hankel_posSemidef`
- `canonicalCompletedNative_six_sub_hankelPair_posSemidef`
- `nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_blocks_posSemidef_unconditional`

The last theorem uses the existing exact C3 even/odd excess-block identities.
It accepts the existing six-source parameters but no correction or loss map.

## Provenance and open geometric construction

The new proof reuses the current local canonical theta/cosine representation,
all-order theta integration-by-parts identities, the fixed characteristic,
and its unchanged logarithmic recurrence. Dominated-differentiation techniques
come from the local finite-order cosine-moment module and are reconstructed
at every order in the new module.

**This is not a new zeta-free source derivation.** The existing
`CompletedNativeXiThetaCosineRepresentation` derives its native theta bridge
through Mathlib's Mellin `completedRiemannZeta₀` construction. That existing
upstream identification is inherited and recorded explicitly. No RH,
zero locations, externally supplied heights/moments, new measure, fitted
operator, Hankel Cholesky or correction hypothesis enters the new argument.

The next gate remains exactly a geometrically constructed loss channel with

```lean
correction.RealizesSixSourceEnergyExcess M q hqpos.le hq1 S 3 1
```

namely, for the same literal BR2 parity family,

```text
inner(lossMap B_i, lossMap B_j)
  = nativeC3SeededClockTfvdSixSourceBr2EnergyExcess(...,i,j),
```

together with the correction's lossless polarized split and corrected-map
injectivity. Passing the necessary PSD test does not supply that channel,
its provenance or those operator properties. No target-defined square root
or vector fabrication is substituted for the geometric construction.
No HP/Stieltjes conclusion is added by this round.

## Validation

All ten public theorems are registered in `audit/theorem-registry.json` and in
the scoped audit imported by the central audit. The scoped command rejects any
dependency outside `[propext, Classical.choice, Quot.sound]` and also executes
`#print axioms` for every theorem.

```bash
lake build --wfail CarrySelfAdjointOperator.CompletedNativeAllOrderMomentUpperBound
lake build --wfail CarrySelfAdjointOperator.CompletedNativeSixFrameUpperBound
lake build --wfail CarrySelfAdjointOperator.CompletedNativeSixFrameUpperBoundAudit
lake build --wfail CarrySelfAdjointOperator CarrySelfAdjointOperator.Audit
bash scripts/static_audit.sh
bash scripts/audit.sh
git diff --check
git diff --cached --check
```

Validation completed: both proof modules, the scoped audit, the root library
and central audit passed `lake build --wfail` (exit 0). The direct scoped
`lake env lean` kernel check passed (exit 0). All ten printed footprints were
exactly `[propext, Classical.choice, Quot.sound]`, and their explicit guards
passed. Both `scripts/static_audit.sh` and the complete `scripts/audit.sh`
pipeline passed (exit 0). Working and staged whitespace checks passed.

This coherent increment is published under message
`feat: prove unconditional six-frame bounds for canonical Hankel towers`.
The delivery records the resulting SHA and verified remote references. The
commit does not insert its own self-referential SHA into its content.
