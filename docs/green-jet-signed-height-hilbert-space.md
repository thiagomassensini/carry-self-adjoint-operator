# Canonical Green-jet signed-height Hilbert space

This note records the Hilbert promotion of the exact finite cutoff tower.  It
is a construction ledger, not an independent input to the theory.

## 1. Input already available

Let `jet : (ℕ ⊕ ℕ) → E` be the even/odd Green-jet family and let

```text
P_N = diag(G_N, K_N)
```

be its finite parity Gram.  The coefficient identity gives exactly

```text
Gram(jet restricted to N) = P_N.
```

Global linear independence of the two parity families makes every `P_N`
positive definite.  The previously constructed canonical section `A_N`
satisfies

```text
A_N P_N A_N^T = I.
```

No target spectral values or fitted matrices enter these statements.

## 2. The carrier comes from the jets

The real carrier is

```text
H_jet = closure(span_ℝ(range jet)).
```

Thus no unrelated Hilbert space is attached afterward.  If `E` is complete,
this closed subspace is complete.  If `E` was not assumed complete, the module
uses the canonical embedding

```text
E → UniformSpace.Completion E
```

first.  Lean proves that this embedding preserves the Green Gram identity and
global independence of both parity families.  The resulting closed span is
therefore a complete real inner-product space without an extra completeness
hypothesis on the original `E`.

## 3. Signed vectors are actual Green-jet combinations

Writing `v_N` for the raw parity prefix, define the signed family

```text
q_N(a) = sum_i A_N(a,i) v_N(i).
```

The exact Gram calculation is

```text
<q_N(a), q_N(b)>
  = (A_N P_N A_N^T)(a,b)
  = delta(a,b).
```

Lean therefore proves `Orthonormal ℝ q_N`.  Linear synthesis gives a
canonical map

```text
V_N : EuclideanSpace ℝ (Fin N ⊕ Fin N) →ₗᵢ[ℝ] H_jet,
V_N(x) = sum_a x(a) q_N(a).
```

This is a genuine `LinearIsometry`, not only a distance-preserving function.

## 4. Exact cutoff compatibility

Put

```text
S_N = P_N A_N^T,
C_NM = A_N R_NM S_M       (N ≤ M).
```

The inverse identity already proved for the whitening gives

```text
S_N A_N = I.
```

At vector level Lean now proves both

```text
S_N q_N = v_N,
q_N = C_NM q_M.
```

Consequently the coordinate inclusion `C_NM^T` obeys

```text
V_M(C_NM^T x) = V_N(x)
```

for every finite vector `x`.  Hence the ranges of the `V_N` are nested.  A
larger cutoff changes the coordinates but not the represented Hilbert vector.

## 5. No directions are left unused

The inverse synthesis shows that every raw jet belongs to one finite signed
range: a jet of order `n` already occurs in the range at cutoff `n+1`.
Since the original jets generate `H_jet`, Lean obtains

```text
closure (⨆ N, range V_N) = ⊤.
```

Thus the compatible finite signed tower is dense in the canonical carrier.
Together with completeness of the automatically completed carrier, this is
the Hilbert completion statement supplied by the geometry.

## 6. Global operator layer

The Hilbert space, finite linear isometries, exact cutoff commutation, nested
ranges, inverse synthesis, and density are formalized here.  The canonical
bounded parity reflection on this carrier has since been constructed and is
recorded in [`green-jet-parity-reflection.md`](green-jet-parity-reflection.md).
The subsequent Green-factor construction now supplies the global reciprocal
signed-height operator on the completed even/odd sectors.  Under the exact
head-in-shifted-tail, equivalently vanishing moment-defect, gate, this operator
is densely defined, closed, and maximal real self-adjoint.  Its two-step action
identifies its square with the natural inverse of `J=B*B` on the range of `J`.
See
[`global-reciprocal-signed-height-operator.md`](global-reciprocal-signed-height-operator.md).
