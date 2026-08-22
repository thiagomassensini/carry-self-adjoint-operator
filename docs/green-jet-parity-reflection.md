# Global Green-jet parity reflection

This note records the operator-theoretic promotion of the exact finite
Green-jet/signed-height tower.  It is a construction ledger.  No external
spectral list and no multiplicative input enters the construction.

## 1. The two closed sectors

Let

```text
H = closure(span_R(range jet))
```

be the canonical Green-jet Hilbert carrier.  Inside `H`, define

```text
H_even = closure(span_R { jet(inl n) | n in N }),
H_odd  = closure(span_R { jet(inr n) | n in N }).
```

The coefficient-level Green identity already says

```text
<jet(inl i), jet(inr j)> = 0
```

for every `i,j`.  Linear extension and continuity therefore give

```text
H_even orthogonal H_odd.
```

Orthogonality alone would allow an unused third sector.  The definition of
`H` rules it out: all raw jets have dense algebraic span in `H`.  Projecting
that dense span onto `H_even^perp` kills every even generator and fixes every
odd generator.  Since `H_odd` is closed, this proves the stronger identity

```text
H_odd = H_even^perp,
H_even + H_odd = H.
```

Thus completion preserves the parity split and adds no unrelated direction.

## 2. The canonical global operator

Let `P_even` be orthogonal projection onto `H_even`.  Define

```text
R = 2 P_even - I.
```

Equivalently, `R` is the orthogonal reflection in `H_even`.  It is forced by
the preceding decomposition:

```text
R x =  x   for x in H_even,
R x = -x   for x in H_odd.
```

Mathlib packages this reflection as a linear isometric equivalence.  Lean
then proves

```text
R^2 = I,
<R x, R y> = <x,y>,
||R x|| = ||x||,
<R x,y> = <x,R y>.
```

The associated everywhere-defined bounded operator is therefore
self-adjoint.  For an ambient realization not initially known complete, the
same construction is performed after the canonical uniform-space
completion; no additional hypothesis is required.

## 3. Exact finite restriction

At order `N`, write

```text
v_N = raw even/odd jet prefix,
A_N = canonical Green-jet/signed-height section,
q_N = A_N v_N,
V_N x = sum_a x(a) q_N(a).
```

On raw coordinates, `R` is the diagonal parity grading `G_N`.  The already
proved finite crosswalk is

```text
A_N G_N = S_N A_N,
```

where `S_N` is the signed-sector swap.  Hence

```text
R q_N = S_N q_N
```

and, for every finite coordinate vector,

```text
R (V_N x) = V_N (S_N x).
```

This is an exact identity, not convergence in a numerical tolerance.  It
shows that every finite range is invariant under the single global operator.

## 4. Compatibility with cutoff enlargement

For `N <= M`, let `C_NM^T` be the exact isometric coordinate inclusion.  The
previous Hilbert construction proved

```text
V_M(C_NM^T x) = V_N x,
```

and the cutoff crosswalk proved that the inclusions intertwine the sector
swaps.  The global result now closes the square:

```text
R V_M(C_NM^T x)
  = V_M(C_NM^T S_N x)
  = V_N(S_N x).
```

Thus increasing the cutoff changes only the chosen finite coordinates.  The
represented vector and the action of `R` are unchanged.

## 5. What has and has not been constructed

The formal object constructed here is the canonical bounded parity
reflection associated with the Green-jet geometry.  Its spectrum is the
two-point set contained in `{+1,-1}`; it is not itself the unbounded height
operator.  Its role is to give the global Hilbert symmetry to which every
finite signed-height reflection restricts exactly.  Transporting or closing
the height operator is a separate next layer.

