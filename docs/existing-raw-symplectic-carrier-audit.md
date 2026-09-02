# Existing raw symplectic carrier audit

## Scope and conclusion

This audit asks whether the fixed-cutoff raw no-leak readout must be given a
new operator carrier, or whether the required response/source separation is
already present in the repository.

The answer is the second one.  The required raw carrier is already the first
block of `CanonicalCompletedC3FullWronskianOperatorCarrier`.  At every fixed
cutoff `M` it has:

- a one-variable response state and a one-variable source state;
- a bounded operator independent of `M`, `z`, and `w`;
- the exact xi-weighted raw C3 Wronskian as its inner-product readout;
- exact compatibility with the no-leak radial, Green-provenance,
  off-diagonal, readout-residual, and head--tail channels;
- the constant seed retained before the bounded trace projection.

No new carrier, fitted weight, positivity assertion, theta representation,
zero hypothesis, confinement statement, `h1`, or all-order construction is
used.  The Lean implementation is
`CarrySelfAdjointOperator/CompletedC3ExistingRawSymplecticCarrierAudit.lean`.

## 1. The existing one-point factorization

The permanent state

```text
canonicalCompletedC3AllCutoffOnePointState M z
```

already stores three Naimark ports and the four boundary coordinates

```text
valueHead, logJetHead, valueTail, logJetTail.
```

The bounded map

```text
canonicalCompletedC3OnePointCompletedTraceProjection
```

joins the head and tail only at the last step and returns the completed
boundary trace `(companion,value)`.  It is real-linear because the permanent
Naimark carrier was deliberately realified.  The target boundary carrier is
complex Hilbert, and the fixed complex-linear operator on it is the existing
rotation

```text
completedScalarBoundarySymplecticRotation.
```

Define the raw one-point state by taking the first block of the old full
operator state:

\[
 X_{\mathrm{raw},M}(z)
 = A(z)\,T\bigl(S_M(z)\bigr),
\]

where `A = nativeXiCompletionFactor`, `S_M` is the permanent one-point state,
and `T` is the completed-trace projection.  Lean proves

\[
 \langle X_{\mathrm{raw},M}(w),
 J_\partial X_{\mathrm{raw},M}(z)\rangle
 = A(z)\overline{A(w)}\,W_{\mathrm{raw}}(z,w).
\]

This is
`canonicalCompletedC3RawWronskianOperator_inner_eq`.  Response and source are
therefore separated before scalarization, while `J_boundary` is fixed and
bounded.

## 2. The seed is not lost

The apparent obstruction in the mixed-source `valueHeadReadout` is real: its
formula is affine because it contains `1 + sum ...`.  The operator
factorization does not try to linearize that formula on a seedless prefix.
Instead, `finiteBracketedDirichletChart` is already stored as the scalar
`valueHead` coordinate of the one-point Hilbert state.  The bounded trace
projection is linear in that stored coordinate.

The theorem
`canonicalCompletedC3RawWronskianOperatorState_value_eq_seed_head_tail`
spells this out:

\[
 X_{\mathrm{raw},M}(z)_{\mathrm{value}}
 = A(z)\left(1+\operatorname{trace}_M(s(z))+
                   \operatorname{tail}_M(s(z))\right).
\]

Thus no homogenizing coordinate has to be invented: the necessary seed
coordinate was already present.

## 3. Compatibility with the no-leak and Green-frame ledgers

The pair-dependent structural state is not itself replaced by an assumed
separable vector.  The bounded Green-frame synthesis theorem first recovers
it exactly as

```text
canonicalCompletedC3AllCutoffOrientedStructuralState M z w
  = ledger.structural.
```

Combining this vector equality with the old no-leak identity gives

\[
 \langle X_{\mathrm{raw},M}(w),J_\partial
 X_{\mathrm{raw},M}(z)\rangle
 =\omega_\xi(z,w)
 \bigl(R+P+O+E+T\bigr),
\]

where the five displayed raw terms are radial, Green provenance,
off-diagonal, readout residual, and head--tail completion.  This is formalized
both in compact form and with the three structural coordinates exposed in

```text
canonicalCompletedC3RawWronskianOperator_inner_eq_greenFrameLedger
canonicalCompletedC3RawWronskianOperator_inner_eq_greenFrameChannels.
```

So the one-point operator factorization and the pair-dependent Green-frame
state are two exact representations of the same raw readout.  The final
two-dimensional boundary block does not retain the structural channels as
orthogonal coordinates, but their lossless provenance is certified before
the projection by the vector-level Green-frame sewing.  Adding those channels
again to the operator carrier would be redundant, not a missing mathematical
step.

## 4. Fixed-center variation

After the already established central-ledger normalization, the raw operator
branch is pointwise identical to the raw scalar branch from the preceding
collision audit.  Hence Lean proves directly

\[
 B_{\mathrm{raw},M}'(0)
 = \operatorname{canonicalCompletedC3RawHeightResponseTaylorCoefficient}(1).
\]

This is
`deriv_canonicalCompletedC3FixedCenterRawOperatorRealBranch_zero`.  It proves
that the operator realization retains precisely the raw variation which the
smaller global Green carrier had lost.

## 5. Existing full direct sum

The second block of `CanonicalCompletedC3FullWronskianOperatorCarrier` is the
already constructed archimedean/chart state.  Its fixed operator is
`canonicalCompletedC3ArchimedeanChartOperator`.  Therefore the old full
operator is exactly

\[
 J_{\mathrm{full}}=J_\partial\oplus J_{\mathrm{arch}},
\qquad
 X_{\mathrm{full},M}=X_{\mathrm{raw},M}\oplus X_{\mathrm{arch}}.
\]

The new sewing theorem
`canonicalCompletedC3FullWronskianOperator_inner_eq_greenFrameFinalLedger`
identifies its readout with the complete Green-frame/no-leak ledger, channel
by channel before the final scalar sum.

At the unnormalized central collision,

\[
 \langle X_{\mathrm{full},M}(0),
 J_{\mathrm{full}}X_{\mathrm{full},M}(0)\rangle=0.
\]

After normalization its real collision branch is pointwise the total branch
isolated previously, and Lean proves

\[
 B_{\mathrm{total},M}(0)=0,
 \qquad
 B_{\mathrm{total},M}'(0)=h_0.
\]

The derivative proof uses the existing first completed response coefficient
theorem; it neither imports nor asserts any higher-order positivity.

## 6. Exact status of the requested promotion

The raw branch already contains all states required for the fixed-cutoff
operator readout.  What looked like a missing promotion was an identification
gap between two pre-existing representations:

```text
pair-dependent no-leak / Green-frame ledger
              =
xi-weighted completed boundary trace with fixed J_boundary.
```

There is one important type qualification.  Since the permanent enriched
carrier is realified, its completed-trace projection is only real-linear.
Consequently the repository does not literally define a complex-linear
pullback `T* J T` on the whole enriched one-point carrier.  It instead performs
the canonical bounded real-linear projection into the complex boundary-trace
carrier and applies the fixed complex-linear symplectic rotation there.  This
is sufficient for the requested response/source factorization and avoids a
false identification of real and complex carriers.

Thus the narrow lacuna is now closed without constructing another channel:
the old full Wronskian operator carrier is the complete raw-plus-archimedean
collision carrier that the smaller global Green operator carrier was not.
