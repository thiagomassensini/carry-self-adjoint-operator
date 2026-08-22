# Canonical finite Green-jet/signed-height intertwiner

## Outcome

The finite intertwiner is not an additional fitted operator.  It is forced by
the two parity Gram sections and the same inverse-square-root height already
constructed from them.

For one order `N`, write

```text
G_N[i,j] = h_(i+j),
K_N[i,j] = h_(i+j+1).
```

The reflected Green kernel realizes these as the mutually orthogonal even and
odd jet Grams.  Linear independence of both finite jet prefixes makes both
sections positive definite.

## Double whitening

Canonical LDL whitening gives a lower-triangular matrix `B_N^G` with

```text
B_N^G G_N (B_N^G)^T = I.
```

Transporting the odd Gram through the same coordinates gives

```text
J_N = B_N^G K_N (B_N^G)^T.
```

The height operator is the positive inverse square root

```text
T_N = J_N^(-1/2),
```

so it satisfies the exact normalization law

```text
T_N J_N T_N = I.
```

Consequently

```text
W_N = diag(B_N^G, T_N B_N^G)
```

whitens the complete parity Gram:

```text
W_N diag(G_N,K_N) W_N^T = I.
```

## From parity grading to signed reflection

On the Green-jet coordinates the reflection is the grading

```text
Gamma = diag(I,-I).
```

On the signed-height realization the relevant reflection is the sector swap

```text
S = [0 I]
    [I 0].
```

The normalized Hadamard matrix

```text
U_N = (1/sqrt(2)) [I  I]
                    [I -I]
```

is symmetric, orthogonal, and satisfies

```text
U_N Gamma = S U_N.
```

Because `W_N` is block diagonal, it commutes with `Gamma`.  Therefore

```text
B_N = U_N W_N
```

satisfies

```text
B_N Gamma = S B_N,
Gamma B_N^T = B_N^T S,
B_N diag(G_N,K_N) B_N^T = I.
```

The first identity is the analysis/readout intertwining law, the second is
its adjoint/synthesis form, and the third says that the map retains the entire
finite Green parity metric.

## Exact status

`GreenJetSignedHeightIntertwiner.lean` proves all matrix identities above and
also proves that the existing functional-calculus definition of `T_N` equals
the positive inverse square root used by the whitening package.

The construction assumes one reflected Green moment-kernel representation and
linear independence of the two order-`N` jet prefixes.  It does not assume a
list of heights, a fitted matrix, or an order-dependent calibration.

The remaining passage is not another finite formula.  One must construct the
bounded completed-state realization whose finite sections are these `B_N`,
and prove compatibility with the projective cutoff maps.  Once that ambient
realization is known, the existing Naimark adjoint fixes its camera readout
canonically.
