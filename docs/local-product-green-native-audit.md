# Local product-Green and native-factor audit

## Scope

This audit is center/local only.  It does not use theta, zeros, confinement,
`h1`, an all-order coefficient argument, or the old real-axis carrier `P`.

The repository was first rebuilt with

```text
lake build --wfail
```

and all 9175 jobs passed.  The emitted `ring_nf` suggestions are Lean `info`
messages, not warnings; `--wfail` reported no warning failure.

The formal results are in
`CompletedNativeLocalProductGreenAudit.lean`.

## The center theorem is genuinely local

The exact product rule has now been localized:

```text
HasDivisionFreeGreenRepresentationOn D A PsiA a
HasDivisionFreeGreenRepresentationOn D G PsiG g
------------------------------------------------
HasDivisionFreeGreenRepresentationOn D (A * G)
  (productBoundaryCompanion A PsiA G PsiG)
  (weightedProductGreenState A G a g).
```

The proof is pointwise and reuses the existing Wronskian product identity and
weighted direct-sum Gram formula.

Specializing to `completedNativeHeightDomain` gives the completed product
ledger without global factor hypotheses.  Combining this local identity with
the existing center collision-removal theorem proves

```text
<Psi_dressed(0), Psi_dressed(0)> = h0
```

provided only that:

1. the xi factor has a Green representation on the centered domain;
2. the native factor has a Green representation on that domain; and
3. the xi state is continuous at zero.

Thus global Green identities are not needed for the center gate.

## Native trace reconstructed by the existing C3 tails

Write

```text
G = nativeHeightScalar,
PsiG = nativeHeightScalarBoundaryCompanion = -G'.
```

The existing value and log-jet tail theorems prove, throughout the centered
strip,

```text
canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout = G,
canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout = -G'.
```

Consequently Lean now proves the polarized identity

```text
W_G(z,w)
  = W_(tail-completed value, tail-completed log jet)(z,w).
```

So there is no missing scalar tail in the native Wronskian.  Completing the
tails leaves exactly the same `(G,-G')` trace which the proposed factor Green
representation must realize.

## What the proposed C3 state actually realizes

The proposed state is

```text
g(z) = canonicalCompletedOperatorC3HilbertState(z).
```

It is the `L2` wrapper of the minimal finite C3 port.  Its Hilbert Gram is the
positive same-coordinate sum

```text
<g(w),g(z)>
  = <port(w).fst, port(z).fst>
      + <port(w).snd, port(z).snd>.
```

By contrast, the existing C3/Green identities use:

- the skew boundary `greenForm` between opposite port legs;
- a reflected spectral parameter;
- a radial C3 coefficient; and
- in the scalar sewing, the explicit provenance, cross-edge, readout, and
  tail channels.

Faithful Naimark packing is already proved not to be an intrinsic Green
intertwiner.  None of these theorems converts the skew/reflected C3 form into
the positive same-coordinate Gram above.

Lean reduces the desired native representation to the exact concrete
equality

```text
W_(tail-completed value, tail-completed log jet)(z,w)
  = (z - conjugate(w)) *
      ( <finitePort(w).fst, finitePort(z).fst>
      + <finitePort(w).snd, finitePort(z).snd> ).
```

No existing theorem supplies this equality.

## The first obstruction occurs at zeroth diagonal order

The obstruction appears before differentiating the kernel or forming the
`h0` Gram.  Setting `z = w = 0` in the requested representation makes its
right-hand side zero, hence it requires

```text
W_G(0,0) = 0.
```

Native Schwarz reflection gives

```text
conjugate(G(0))  = G(0),
conjugate(G'(0)) = -G'(0),
G(0) != 0.
```

Lean therefore proves the implication

```text
HasDivisionFreeGreenRepresentationOn
  completedNativeHeightDomain G (-G') g
    -> G'(0) = 0.
```

This is the first genuinely new equality forced by the proposed native
factor route.  It is stronger and earlier than a mismatch in the central
norm.

A direct high-precision evaluation of the literal functions gives

```text
G(0)       ~= -1.4603545088095868,
G'(0)      ~= -3.9226461392091517 i,
W_G(0,0)   ~= -11.456907951717206 i.
```

This numerical calculation is not used by Lean, but it decisively diagnoses
the proposed representation as incorrectly normalized/oriented at zeroth
diagonal order.  For comparison, its next diagonal quantities also disagree:

```text
finite-C3 normalized center Gram ~= 0.05092584494599576,
native response coefficient 1    ~= 1.8734388488020301.
```

The formal module exposes the exact remaining refutation fact as
`deriv nativeHeightScalar 0 != 0`; once that fact is supplied, the negation of
the proposed local representation follows immediately.

## Why the completed product can still be centered

The failure is factorwise, not a contradiction in the completed scalar.
Lean proves the exact unconditional cancellation

```text
|G(0)|^2 W_A(0,0) + |A(0)|^2 W_G(0,0) = 0.
```

Centered evenness kills this weighted sum.  It does not kill `W_A(0,0)` and
`W_G(0,0)` separately.  The two raw factor responses have opposite imaginary
constant terms, which cancel only after the product is formed.

Requiring separate positive Green representations with the raw companions
`-A'` and `-G'` would incorrectly force both factor Wronskians to vanish at
the center.  Therefore the conditional two-factor direct-sum theorem from the
previous audit is mathematically too strong for these raw companions, even
though its algebra is correct.

## Conclusion

This audit reaches outcome 2:

```text
the native factor representation fails first at
W_G(0,0) = 0, equivalently G'(0) = 0.
```

The failure is not caused by a missing C3 tail.  The tails reconstruct the
correct scalar trace, while the chosen finite C3 Hilbert state realizes a
different positive pairing from the skew/reflected Green form present in the
geometry.

Following the requested order, the xi factor was not opened: doing so cannot
repair a native factor representation which already fails before the product
rule applies.  A future route would have to retain the weighted cancellation
between the two factor Wronskians—possibly through a coupled/gauged product
state—rather than demand two separately positive raw-factor Green states.
No such new carrier is constructed here.
