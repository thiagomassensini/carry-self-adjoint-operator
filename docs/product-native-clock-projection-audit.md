# Product native clock-projection audit

## Question

The preceding center sanity check showed that the native coordinate

```text
g0 = normalizedCompletedGreenState
       nativeHeightScalar
       canonicalCompletedOperatorC3HilbertState
       0
```

has squared norm approximately `0.050925844946`, already larger than `h0`.
This audit asks whether `g0` is still a pre-quotient state and whether the
existing central clock Schur construction acts canonically on the same
information.

No xi state, compensating kernel, theta representation, zero data,
confinement statement, `h1`, or all-order promotion is used.

## Exact carriers and normalization

The objects do not initially live in the same carrier.

```text
canonicalCompletedOperatorC3HilbertState 0
  : WithLp 2
      (FiniteC3GreenBoundarySpace 3 × FiniteC3GreenBoundarySpace 3)

canonicalCompletedC3CentralOrdinaryState
canonicalCompletedC3CentralLogJetState
  : CarryVerticalL2 = ell^2(N, C).
```

At the center, the two finite port legs coincide.  If their common value is
`v3`, then

```text
g0 = (sqrt 2 * G(0))^-1 • (v3, v3),
G   = nativeHeightScalar.
```

The already existing map `finiteC3LegL2Extension` extends one finite leg by
zero into `CarryVerticalL2`, and Lean had already proved

```text
finiteC3LegL2Extension 3 v3
  = canonicalCompletedC3DirichletGradientPrefixState (1/2) 3.
```

The new module packages the symmetric diagonal collapse

```text
(x1,x2) |-> (x1_extended + x2_extended) / sqrt 2.
```

The factor `1/sqrt 2` is forced by the Hilbert norm of a diagonal pair.  It is
not a fitted coefficient.  The resulting exact vector identity is

```text
diagonalCollapse(g0)
  = G(0)^-1 • O3,

O3 = canonicalCompletedC3DirichletGradientPrefixState (1/2) 3.
```

Lean also proves that this readout preserves the center Gram of `g0`.

## First incompatibility with the old Schur clock

The old state is

```text
Oinf = canonicalCompletedC3CentralOrdinaryState,
```

the complete all-cutoff gradient in `ell^2(N,C)`.  The product-ledger state
contains only `O3`.  Lean proves

```text
O3 != Oinf.
```

The proof evaluates coordinate `3`: it is zero in `O3` and strictly nonzero
in `Oinf`.  Thus the old Schur energy is not directly the energy of `g0`
after a change of carrier.  Passing from `O3` to `Oinf` adds genuine tail
information; it is not a quotient or readout of `g0`.

There is also a normalization mismatch:

```text
g0 uses                     |G(0)|^2,
old normalized Schur gate   |F(0)|^2,
F(0) = A(0) G(0).
```

Numerically, the all-cutoff Schur energy is approximately

```text
Schur(Oinf,Linf)                  ~= 0.0108915838158084
Schur(Oinf,Linf) / |G(0)|^2       ~= 0.00510710099365182
Schur(Oinf,Linf) / |F(0)|^2       ~= 0.0440724512873259.
```

The last expression is the normalization used by the existing old Schur
gate, and it is still larger than `h0`.  These all-cutoff decimals are a
diagnostic evaluation, not a formal identification theorem.

## Schur quotient induced on the actual finite native prefix

Although the old all-cutoff Schur state is not `g0`, its clock direction has
a canonical finite restriction:

```text
L3 = canonicalCompletedC3LogJetPrefixState (1/2) 3.
```

The existing derivative theorem gives, coordinatewise,

```text
d/dt O3(1/2 + i t)|t=0 = -i L3.
```

Thus `L3` is forced by the product-ledger prefix itself.  The finite
projective coefficient is the Hilbert coefficient

```text
c3 = <L3,O3> / ||L3||^2,
```

and the residual is

```text
R3 = O3 - c3 L3.
```

Lean proves

```text
<L3,R3> = 0

||R3||^2
  = ||O3||^2 - |<L3,O3>|^2 / ||L3||^2.
```

The native-normalized projected energy is therefore

```text
E3_projected = ||R3||^2 / |G(0)|^2.
```

Its literal three-coordinate evaluation gives

```text
||O3||^2                    ~=  0.1086062541762198206234011371
||L3||^2                    ~=  0.2644720414883344939648095588
<L3,O3>                     ~= -0.1668136102668377445489955933
c3                           ~= -0.6307419465894494883066215648
||R3||^2                    ~=  0.0033899129189008051459490621
E3_projected                 ~=  0.0015895417901832940457559535.
```

Consequently

```text
E3_projected < h0 ~= 0.0231049931154189707889338104,
h0 - E3_projected ~= 0.0215154513252356767431778569.
```

The strict decimal comparison is numerical.  Lean formally proves the exact
Schur formula, nonnegativity, and

```text
E3_projected <= ||g0||^2.
```

This is a successful center-energy compatibility test, not a proof that
`R3/G(0)` is already the physical native coordinate.

## Other existing projections

The audit also checked the nearby constructions.

- The Naimark ambient-port projection does not remove energy from `g0`.
  After the existing finite symplectic Naimark promotion, Lean proves that
  the projection fixes the promoted state pointwise.  The state already lies
  in the port range.

- Port-plus-escape is lossless by construction and therefore cannot perform
  this quotient.

- The compressed Gamma/correction states and their coisometric compression
  live in the ambient Naimark response carrier, not in the finite native C3
  Hilbert carrier.  No existing map identifies their correction direction
  with `L3` before the Gram.

- The generic kernel-support orthogonal projections require a specified
  operator and closed kernel.  No such operator is attached canonically to
  `g0` in the current ledger.

- The projective chiral carrier acts on a different ambient Cauchy pair and
  signed form.  It is not a same-carrier quotient of this finite native port.

## Conclusion

The old all-cutoff Schur energy is not directly the missing quotient of
`g0`: its ordinary state contains a nonzero tail absent from the product
ledger, and its normalized gate uses the completed characteristic rather
than the native factor.

However, the same geometry induces a canonical quotient on the actual
native prefix.  The component removed is precisely the complex line spanned
by the finite logarithmic clock jet `L3`; its coefficient is forced by the
inner product.  This projection reduces the center energy from
`0.050925844946` to `0.00158954179018`, which fits inside the `h0` budget.

The next mathematical question is not how to tune this coefficient—it is
already canonical—but whether the coupled product Green identity selects
this finite clock quotient, or instead a different transported clock/tail
combination.  That identification is deliberately not assumed here.
