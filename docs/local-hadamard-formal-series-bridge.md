# Formal Hadamard logarithmic-derivative bridge — follow-up (2026-11-20)

This module extends [the local jet bridge](local-hadamard-moment-bridge.md) with a checked identity in the **formal power series ring** over `ℂ`. The characteristic is still `F=completedNativeOperatorCharacteristic`, not the bracket or Genuine themselves.

For any coefficient sequence `a_n` with `a_0 ≠ 0`, let

```text
A(X) = Σ a_n X^n
C(X) = Σ c_n X^n
c_n = ((n+1)a_(n+1) - Σ_{k<n}c_k a_(n-k))/a_0.
```

Lean now proves:

```text
C(X) * A(X) = dA(X)/dX
C(X) = (dA(X)/dX) * A(X)^(-1).
```

The nonzero constant term provides the formal-series inverse. For the completed native characteristic at a **simple** real height zero `gamma`, the previously defined jet
`a_n=F^(n+1)(gamma)/((n+1)! F'(gamma))` has `a_0=1`. This is source-first: no zero list is an input, and the real zero is a separate anchor hypothesis, not derived from the moment sequence.

The historical local Hadamard coefficients satisfy, for `m≥1`:

```text
S_m(gamma) = (-1)^(m-1) * [X^(m-1)] ((dA/dX)/A).
S_6(gamma) = -[X^5] ((dA/dX)/A)
S_7(gamma) =  [X^6] ((dA/dX)/A).
```

Formal Lean declarations:
- `localLogResponseFormalSeries_mul_deflated`
- `localLogResponseFormalSeries_eq_formal_log_derivative`
- `nativeLocalHadamardMoment_eq_formal_log_derivative_coeff`
- `nativeLocalS6_eq_formal_log_derivative_coeff`
- `nativeLocalS7_eq_formal_log_derivative_coeff`.

**Scope:** This establishes equality of formal Taylor coefficient systems and exact algebraic pole removal in the previous module. An analytic deflated quotient with removable zero is now proved in
`LocalHadamardAnalyticDeflation.lean`; the remaining seam is the
coefficient-by-coefficient identification of that analytic germ with
the formal series `localDeflatedFormalSeries`. Neither is an all-order positivity theorem, interval enclosure for gaps, or a Green sign closure.

## Numerical precision note

The separate 2026-11-20 test in `momentos` reported Cholesky failure for `N=16` at **80-digit** working precision, but passed at 125 digits. The previously completed high-precision campaign in `momentos/native_jet_exploration/vm_campaign/relatorio_vm.md` reported 2,048 moments and 1,024 positive Jacobi eigenvalues at up to 36,000 working digits. These are different algorithms/precision regimes and do not imply a sign reversal at dimension 16. Numerical positive checks at large finite dimensions still do not prove positivity in every dimension.

## Focused audit

```sh
lake build --wfail CarrySelfAdjointOperator.LocalHadamardFormalSeriesBridgeAudit
lake env lean CarrySelfAdjointOperator/LocalHadamardFormalSeriesBridgeAudit.lean
bash scripts/static_audit.sh
```
