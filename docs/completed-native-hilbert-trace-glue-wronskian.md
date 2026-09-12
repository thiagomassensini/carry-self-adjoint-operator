# Completed native Hilbert trace glue and the mixed Wronskian

This branch starts at `0e04b256f459da4b87b80ad8ddbbc316f7c4ad04` and records the
trace-level result that is available in the current pinned APIs.  It does not
turn the scalar C3 residual into zero.  The purpose is to keep the TFVD,
provenance, and completion ledgers separate until a canonical map into one
Hilbert boundary has been proved.

## Status

Primary outcome: **Outcome C**.

The native finite and full Hilbert trace Green defects close exactly to the
vertical Wronskian.  The C3 ordinary/logarithmic edge cores can be extracted
from the seeded TFVD/`G_pre` ledger, and their vertical realizations are
literally the existing C3 finite prefix states.  What remains open is the
lossless crosswalk from the scalar C3 mixed readout, including its completion
channel, to a single glued Hilbert boundary state and then to a defect/source
relation.  The present result is therefore a trace-glue theorem, not a
positive moment-kernel theorem.

## Exact objects and orientation

For an edge core `x y : NativeGpreComplexEdgeCore`, a finite boundary context
set `S`, and `q : ℝ`, the new definition is

```lean
canonicalNativeFiniteGluedHilbertTraceGreenDefect q S x y :=
  inner ℂ (finitePencil q S).fluxTrace y (finitePencil q S).valueTrace x
    - inner ℂ (finitePencil q S).valueTrace y (finitePencil q S).fluxTrace x
```

The exact proved identity is

```lean
canonicalNativeFiniteGluedHilbertTraceGreenDefect_eq_verticalWronskian
```

and its coordinate form is

```lean
(q : ℂ)⁻¹ * (star (y 1) * x 0 - star (y 0) * x 1)
```

with the actual coordinate expansion supplied by
`carryWeightedVerticalBoundaryWronskian`.  The full `CarryVerticalL2`
version is `canonicalNativeHilbertGluedTraceGreenDefect`, with theorem
`canonicalNativeHilbertGluedTraceGreenDefect_eq_verticalWronskian`.

The scalar C3 wedge has the opposite order.  The definition
`canonicalNativeVerticalTraceBoundaryWedge` inserts the explicit leading
minus sign, and
`canonicalNativeVerticalTraceBoundaryWedge_eq_verticalWronskian` proves that
this convention is exactly the native vertical Wronskian.  The opposite
orientation is recorded by
`mixedScalarBoundaryWedge_nativeTrace_eq_neg_verticalWronskian`.

## The two concrete edge cores

The natural C3 cores are the cores already present in
`seededCompletedTfvdGreenLedger`:

```lean
canonicalCompletedC3OrdinaryEdgeCore M s :=
  (seededCompletedTfvdGreenLedger M s).1.1.2

canonicalCompletedC3LogJetEdgeCore M s :=
  (seededCompletedTfvdGreenLedger M s).1.2.2
```

They are built from the finite TFVD/`G_pre` ledger, not from moments, Hankel
matrices, or a fitted Gram.  The theorems
`canonicalCompletedC3OrdinaryEdgeCore_eq_prefixCore` and
`canonicalCompletedC3LogJetEdgeCore_eq_prefixCore` identify them with
`c2DirichletGradientPrefixCore` and `c2LogJetPrefixCore`.  Applying
`nativeGpreCanonicalVerticalRealization` gives exactly
`canonicalCompletedC3DirichletGradientPrefixState` and
`canonicalCompletedC3LogJetPrefixState`, respectively.

The product states
`canonicalCompletedC3OrdinaryEdgeState` and
`canonicalCompletedC3LogJetEdgeState` retain both the vertical state and its
original provenance core.  Their simplification theorems show the exact
pairs `(prefix, core)`.

For the ordinary state at `w` and log-jet state at `z`,
`canonicalCompletedC3OrdinaryLogJetTraceGlue` proves that the finite glued
Hilbert defect is the vertical Wronskian of those two C3 prefix states.
Thus the provenance coordinates are retained in the traces and cancel inside
the Green defect by the existing CPFormal Green-symmetry theorem; they are not
silently thrown away.

## What is and is not identified with the C3 scalar ledger

The scalar finite C3 identity already in the repository is

```lean
canonicalC3FiniteMixedHeadWronskian_eq_green_add_structuralDefect
```

and the new wrapper
`canonicalC3FiniteMixedStructuralDefect_eq_headScalarizationResidual` makes
its exact residual explicit:

```text
scalar C3 mixed head wedge
  - finite reflected Green form.
```

The definition
`canonicalCompletedC3OrdinaryLogJetTraceCrosswalkDefect` records the
remaining comparison for the concrete ordinary/log edge cores:

```text
scalar C3 mixed head wedge
  - native finite glued Hilbert trace defect.
```

Its theorem
`canonicalCompletedC3OrdinaryLogJetTraceCrosswalkDefect_eq_head_sub_verticalWronskian`
reduces this difference exactly to the scalar C3 head wedge minus the vertical
Wronskian of the two canonical prefix states.  No theorem in the current
pin identifies this defect with zero.  In particular, the existing
`canonicalC3FiniteMixedStructuralDefect` is not replaced by the generic native
trace glue.

The theorem
`canonicalCompletedC3OrdinaryLogJetTraceCrosswalkDefect_eq_structural_add_nativeGreenMismatch`
then gives the exact two-term decomposition

```text
C3-to-native crosswalk defect
  = canonicalC3FiniteMixedStructuralDefect
  + (finite reflected C3 Green form - native vertical Wronskian).
```

This is an algebraic decomposition of independently defined quantities.  It
is not a positivity claim and it does not assert cancellation of either term.

The completed scalar Wronskian also has the independent
`canonicalC3MixedTailCompletionDefect`.  The current CPFormal boundary pencil
has no proved completion boundary channel whose Green defect is this term.
Consequently the completion term remains an explicit global residual.  The
same is true of the C3 scalar source/readout map: there is no existing
canonical map from the mixed C3 scalar four-leg data to one
`NativeGpreComplexEdgeCore` that would justify identifying the two readouts.

## Required two-parameter and positive-kernel steps

The exact results available here are:

| Step | Status | Evidence |
|---|---|---|
| native finite glued trace defect = vertical Wronskian | CLOSED EXISTING / exposed here | `nativeGpreFiniteGluedHilbertGreenDefect_eq_verticalWronskian`, new wrapper |
| native full Hilbert glued trace defect = vertical Wronskian | CLOSED EXISTING / exposed here | `nativeGpreHilbertGluedGreenDefect_eq_verticalWronskian` |
| provenance cancellation inside the Green defect | CLOSED EXISTING | CPFormal provenance Green-symmetry theorem |
| ordinary and log C3 cores | CLOSED EXISTING / exposed here | seeded ledger and core theorems |
| scalar C3 head wedge = native trace defect | OPEN | crosswalk defect above |
| completion as a Hilbert boundary channel | OPEN | no current channel theorem |
| total completed trace-glue | OPEN | requires the preceding channel |
| common defect/source equation | OPEN | no common relation instance |
| divided difference as a native Gram | OPEN | needs the source relation and normalization |
| native Green jet and shifted Hankel factorization | OPEN | downstream of the Gram bridge |
| `K_N = B_N* B_N` and HP certificate | OPEN in this route | existing factorization remains conditional on Gram representation |

The finite and full trace-glue identities do not by themselves say that a
boundary Green form is a Hilbert norm. They only supply the exact skew Green
form. A separate defect/source relation is required to convert it into
spectral separation times a positive inner product.

## Relation to the requested 29 questions

1. **Two edge states:** the ordinary core at `w` and log-jet core at `z`, with their vertical realizations and product states as defined above.
2. **Built without moments:** yes; they come from `seededCompletedTfvdGreenLedger` and the finite TFVD cores.
3. **Canonical realization:** yes, `nativeGpreCanonicalVerticalRealization` is used literally.
4. **Vertical Wronskian:** `carryWeightedVerticalBoundaryWronskian q (realization x) (realization y)`.
5. **Scalar trace wedge:** equal after the explicit orientation minus sign in `canonicalNativeVerticalTraceBoundaryWedge`.
6. **Mixed C3 head Wronskian:** not identified; the exact head-minus-vertical-Wronskian defect is named and proved.
7. **Residual:** `canonicalCompletedC3OrdinaryLogJetTraceCrosswalkDefect`, equivalently scalar head wedge minus vertical Wronskian.
8. **Provenance channels:** present in the finite glued value and flux traces.
9. **Cancellation:** yes, by the existing CPFormal Green-symmetry theorem.
10. **`canonicalC3FiniteMixedStructuralDefect`:** it remains the scalarization residual; it does not disappear.
11. **Dormant compensation:** it belongs to the finite seeded TFVD identity, but no theorem currently maps it into the glued Hilbert trace for the mixed C3 scalar pair.
12. **Completion channel:** no canonical channel is available; the scalar term is `canonicalC3MixedTailCompletionDefect`.
13. **Completion Green defect:** not proved equal to that term.
14. **Total Hilbert boundary:** the native finite/full glue exists, but the completed C3 direct-sum boundary does not.
15. **Total boundary defect:** only the native vertical Wronskian identity is closed.
16. **`β(z)`:** not constructed.
17. **Defect/source equation:** not constructed.
18. **Spectral parameter:** no common `λ(z)` was introduced; the native pencil uses the real parameter `q` and the C3 scalar ledger uses independent complex parameters.
19. **Wronskian = separation × inner product:** open because the common relation instance is open.
20. **Divided difference of `q`:** open.
21. **Native Green jet:** not constructed from this crosswalk.
22. **`momentKernel` unconditional:** no.
23. **`K_N = B_N*B_N` unconditional:** no; the earlier factorization API remains conditional on a Green Gram representation.
24. **Shifted Hankel PSD:** not discharged by this branch.
25. **HP certificate:** not discharged by this branch.
26. **Outcome:** C — native Hilbert trace glue is exact, while the C3/completion/source crosswalk remains as an explicit seam.
27. **Next theorem:** construct a canonical lossless map from the C3 mixed ordinary/log/completion data to one native glued boundary state, prove equality of its traces with the C3 readout, and then prove the common defect/source relation.
28. **Build/audit:** see the final validation record below.
29. **Axioms:** the new load-bearing theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

## Non-circularity and exclusions

No camera, six-camera specialization, atlas limit, cutoff limit, moment
sequence, Hankel matrix, Cholesky factor, `Y_N`, `B_N`, zeros, zeta, RH,
Taylor-complex carrier, ordinary return metric, or refuted static positive
carrier is used to define the native edge cores or the trace defect.  The
existing `G_pre` provenance is used only through the pinned finite TFVD ledger
and its canonical vertical realization.

The no-go results against the old scalarized C3 positive carriers therefore do
not apply to the native trace-glue theorem itself.  They do apply to any
attempt to identify those scalar carriers with the native positive boundary
without first proving the missing map.

## Remaining exact seam

The remaining seam is not “positivity is unknown” in the abstract.  It is the
specific equality needed to pass from the scalar completed C3 readout to the
native glued boundary:

```text
canonical C3 mixed head + completion readout
  = Green defect of one completed native Hilbert state.
```

The first finite part is already exposed as
`canonicalCompletedC3OrdinaryLogJetTraceCrosswalkDefect`; the second part is
the missing completion boundary channel.  Once these are supplied, the next
load-bearing theorem is the two-parameter defect/source identity, followed by
coefficient extraction.  Until then, claiming a native positive kernel or
`K_N = B_N* B_N` from this trace-glue alone would be circular.
