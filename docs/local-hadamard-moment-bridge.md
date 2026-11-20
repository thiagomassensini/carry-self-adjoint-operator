# Completed C2 / Genuine to local Hadamard moments — Lean bridge

**Status:** analytical pole removal, coefficient recurrence and all-camera universality are kernel-checked; numeric root/gap recovery is a separate experiment in `momentos`. This does **not** prove RH, all-order Gram positivity, a certified next gap, or a completed positive Green closure.

## Provenance

The original geometric second difference acts on the C2 legs, and the camera head-plus-exact-tail presentation gives a normalized native characteristic. After the independent archimedean factor, this is `completedNativeOperatorCharacteristic`, denoted `F`. Do not identify bracket, Genuine and `F` as the same object.

In `CompletedNativeCameraUniversality.lean`, `normalizedCompletedNativeCameraCharacteristic_eq` already identifies every supported normalized camera (and every cutoff) with `F`, and `completedNativeCameraLogDerivativeMoment_eq_canonical` identifies the **central** moments `h_n`. The new `LocalHadamardMomentBridge.lean` uses that exact equality rather than inserting a zeta zero table.

## Local jet at a simple zero

Suppose `F(gamma)=0` and `F'(gamma) ≠ 0`, with real `gamma`. The deflated local germ is

```text
G_gamma(v) = F(gamma+v) / (v * F'(gamma))
a_n = F^(n+1)(gamma) / ((n+1)! F'(gamma)),    a_0 = 1.
```

The file defines `nativeLocalDeflatedCoefficient gamma n` by these derivatives, and `cameraLocalDeflatedCoefficient` by derivatives of the corresponding normalized camera. The theorem `cameraLocalDeflatedCoefficient_eq_native` proves their equality for every index, without assuming a simple zero; the zero hypothesis is only required for the analytic interpretation as the deflated germ.

The recurrence for local logarithmic coefficients `c_n` is

```text
a_0 c_n + Σ_{k=0}^{n-1} c_k a_(n-k) = (n+1) a_(n+1)
S_m = (-1)^(m-1) c_(m-1)  (m >= 1).
```

The Lean implementation sums over `(Finset.range n).attach` to make structural decrease explicit. This is extensionally the ordinary range sum. The normalization `a_0 ≠ 0` appears explicitly in the recurrence theorem.

`cameraLocalHadamardMoment_eq_native` proves equality in every order. `cameraLocalS6_eq_native` and `cameraLocalS7_eq_native` specialize it to the historical gap estimators. `cameraGlobalAndLocalMoments_eq_native` packages the central `h_n` and local `S_m` universality together, without asserting they are the same sequence.

## Exact logarithmic pole removal

If `Phi(u) = (u-a) B(u)` and `B(u) ≠ 0`, then

```text
- Phi'(u)/Phi(u) + 1/(u-a) = -B'(u)/B(u).
```

`localLogDerivative_pole_removal_of_factor` formalizes this analytic derivative identity; its algebraic core is `localLogDerivative_pole_removal`.

For `a=gamma²`, `u=(gamma+v)²` and `q=-Phi'/Phi`, the variable-change formula reads

```text
-2(gamma+v) q(u) - 1/v
  = 1/(2 gamma+v) - 2(gamma+v) [q(u)+1/(u-a)].
```

`localHeightResponse_pole_removal` proves that algebraic identity, with nonzero denominators explicit. The term `1/(2gamma+v)` is the local contribution of the reflected anchor.

**Formal boundary:** the code proves the algebraic identities, the derivative factorization, the jet recurrence and universal camera readout. A single Lean theorem combining the analytic Taylor quotient `G_gamma` with the coefficient recurrence has not yet been supplied; it must not be presented as completed. Likewise the real-distance root-sum formula requires additional spectral assumptions.

## Validation

```sh
lake build --wfail CarrySelfAdjointOperator.LocalHadamardMomentBridge
lake build --wfail CarrySelfAdjointOperator.LocalHadamardMomentBridgeAudit
lake env lean CarrySelfAdjointOperator/LocalHadamardMomentBridgeAudit.lean
bash scripts/static_audit.sh
```

Numerical companion: `thiagomassensini/momentos/investigations/c2_local_hadamard_20261120`.

The numerical regression uses C2 seed and brackets plus the exact Hurwitz tail, removes the camera factor, then completes to `F`. It computes central moments without a zero table, recovers real roots numerically and evaluates `S6, S7` using the jets. Those results are **not** certified interval enclosures.
