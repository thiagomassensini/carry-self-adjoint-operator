# Symplectic crossing tangent audit

## Scope and answer

This audit starts from the full raw-plus-archimedean carrier identified in
`CompletedC3ExistingRawSymplecticCarrierAudit.lean`.  It does not reconstruct
the raw carrier, provenance channels, a boundary pencil, or a new symplectic
operator.  It also makes no Gram, norm, metric, or positivity claim.

The exact object represented by `B_total'(0) = h0` is:

> the value of one fixed continuous linear crossing functional on the real
> tangent of the existing full source curve, divided by the old nonzero
> central ledger normalization.

Equivalently, it is the first real crossing variation of the sesquilinear
form

```text
beta(x,y) = <x, J_full y>
```

with the response leg fixed at the central state.  Only the source leg is
differentiated.  The Lean implementation is
`CarrySelfAdjointOperator/CompletedC3SymplecticCrossingTangentAudit.lean`.

## 1. Numerator before normalization

For fixed cutoff `M`, define

```text
N_M(t) =
  <X_full,M(0), J_full (X_full,M(t))>

D(t) = canonicalCompletedC3FixedCenterLedgerNormalization(t)

B_M(t) = N_M(t) / D(t).
```

All three definitions use the old full state and old fixed operator.  Lean
proves directly

```text
N_M(0) = 0
B_M(t) = canonicalCompletedC3FullOperatorFixedCenterRealBranch M t.
```

The first equality is the complete raw/completion versus
archimedean/chart collision cancellation before division.

## 2. Why the denominator derivative disappears

Both `N_M` and `D` are differentiable at zero, and `D(0)` is nonzero.  The
ordinary quotient rule therefore gives

```text
B_M'(0)
  = (N_M'(0) D(0) - N_M(0) D'(0)) / D(0)^2
  = N_M'(0) / D(0).
```

This is formalized as

```text
deriv_canonicalCompletedC3FullOperatorRealCollisionQuotient_zero.
```

No cancellation is hidden after scalarization: the reason the `D'` term
vanishes is exactly the previously proved operatorial identity `N_M(0)=0`.

## 3. The real tangent and its block expansion

The permanent enriched carrier is realified, so the proof does not assert a
complex-linear source map on that carrier.  Instead it first uses the exact
strip-local equality between the old full state and its analytic boundary
trace spelling.  Restricting that equality to the real line proves that the
actual curve

```text
t |-> X_full,M(t)
```

is real differentiable.  Its derivative is named

```text
canonicalCompletedC3FullWronskianOperatorRealSourceTangent M.
```

Fixing `X_full,M(0)` defines the already forced continuous complex-linear
functional

```text
L_M(v) = <X_full,M(0), J_full v>.
```

After restricting the curve to the real axis, Lean proves

```text
N_M'(0) = L_M(X_full,M'(0)).
```

The full direct sum then expands this without losing either block:

```text
N_M'(0)
  = <X_raw,M(0), J_boundary X_raw,M'(0)>
    + <X_arch(0), J_arch X_arch'(0)>.
```

Here the displayed derivatives mean the corresponding projections of the
one full real tangent; they are not separately invented source curves.

## 4. Structural identity for `h0`

Combining the preceding identity with the old theorem `B_total'(0)=h0`
produces

```text
h0
  = L_M(X_full,M'(0)) / D(0)

  = ( <X_raw,M(0), J_boundary X_raw,M'(0)>
      + <X_arch(0), J_arch X_arch'(0)> ) / D(0).
```

The two Lean theorems are

```text
canonicalCompletedNativeLogDerivativeMoment_zero_eq_normalized_symplectic_crossing
canonicalCompletedNativeLogDerivativeMoment_zero_eq_normalized_raw_add_archimedean_crossing.
```

This is the requested operator-level meaning of the first collision
variation.  It is deliberately called a normalized symplectic crossing,
not an energy.

## 5. Classification of the object

The strongest interpretation supplied by the current Lean types is:

- `beta(x,y) = <x,J_full y>` is a complex sesquilinear pairing;
- after fixing `x = X_full,M(0)`, `L_M` is a bounded complex-linear
  functional of the second leg;
- the physical collision curve supplies one distinguished real tangent;
- `h0` is one complex scalar obtained by evaluating that functional on that
  tangent and normalizing.

Thus the current result is **not** a quadratic form on a tangent space, does
not polarize a positive metric, and is not a norm square.  A tangent
bilinear form would require varying or differentiating another independent
leg; no such second variation is present in this gate.

Lean records additivity and complex homogeneity of `L_M`.  It also gives the
exact kernel test for the one canonical tangent:

```text
X_full,M'(0) in ker(L_M)  <->  h0 = 0.
```

The audit does not decide this equivalence by importing a positivity theorem
for `h0`.

## 6. Clock quotients stop at a carrier mismatch

The old clock quotients do not yet act on this crossing tangent:

- `Q3` acts on `CarryVerticalL2`;
- `Qport` acts on `CanonicalCompletedC3HilbertCarrier`;
- `L_M` acts on `CanonicalCompletedC3FullWronskianOperatorCarrier`.

The full tangent contains the product/completion derivative in its raw
boundary-trace block and the independent archimedean/chart derivative.  No
existing theorem identifies it with the finite native clock tangent, and no
existing bounded map sends the `Q3` or `Qport` clock line to a line in the
full carrier while intertwining `L_M`.

This is the first precise obstruction to applying `Q3` or `Qport` before the
crossing variation.  Projecting either old clock carrier at this stage would
compare different types and would discard completion/chart tangent terms
without a sewing theorem.  A later quotient comparison must first construct
or locate that intertwiner; this audit does not invent one.

## Conclusion

`B_total'(0)=h0` is exactly a normalized, fixed-response symplectic crossing
functional evaluated on the real full-source tangent.  It is more structured
than an unexplained scalar derivative, but strictly weaker than a tangent
metric or positive Gram realization.  The existing clock quotients cannot
be moved in front of it with the maps currently formalized.
