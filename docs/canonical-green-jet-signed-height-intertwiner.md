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

## Exact transported cutoff law

The finite inverse square roots need not be principal submatrices of one
another.  Functional calculus does not generally commute with principal
compression, so that would be the wrong compatibility condition to impose.

Write

```text
P_N = diag(G_N,K_N),
A_N = B_N,
S_N = P_N A_N^T.
```

Since `A_N P_N A_N^T = I`, finite-dimensionality proves both

```text
A_N S_N = I,
S_N A_N = I.
```

For `N <= M`, let `R_NM` be raw prefix restriction in both parity sectors and
define the transported cutoff

```text
C_NM = A_N R_NM S_M.
```

`CompletedGreenJetSignedHeightIntertwiner.lean` proves exactly

```text
C_NM C_NM^T = I,
C_NM C_ML = C_NL,
C_NM S = S C_NM,
S C_NM^T = C_NM^T S.
```

Thus `C_NM^T` is the canonical isometric inclusion from the signed section of
order `N` into the section of order `M`.  It also proves that these inclusions
preserve the Euclidean inner product, constructs their metric inductive limit,
and takes its complete metric completion.  Every finite section maps
isometrically into this completed carrier, and consecutive inclusions become
literally equal in the inductive limit.

No asymptotic estimate enters this construction: cutoff compatibility is an
exact cocycle identity.

## Hilbert promotion

`GreenJetSignedHeightHilbertSpace.lean` now supplies the compatible linear
inner-product structure without adding an unrelated carrier.  It takes the
closed real span of the Green jets, realizes the order-`N` signed vectors as
the rows of `A_N` synthesized against the raw prefix, and proves that they are
orthonormal.  Hence every finite signed-coordinate space enters by a linear
isometry.  These isometries commute exactly with every `C_NM^T`, their ranges
are nested, and the closure of the supremum of all finite ranges is the whole
closed Green span.

If the original ambient inner-product space is not assumed complete, the
module first embeds it canonically in its uniform completion.  The exact Gram
representation and the two global independence hypotheses survive that
embedding, so the resulting closed span is a genuine complete real Hilbert
space.

The remaining operator-theoretic layer is narrower: the finite signed
reflections and finite height operators must be shown to descend or close on
this Hilbert carrier, and the resulting realization must be identified with
the concrete completed Green/camera state.  The repository does not yet claim
those operator closures or that final state identification.
