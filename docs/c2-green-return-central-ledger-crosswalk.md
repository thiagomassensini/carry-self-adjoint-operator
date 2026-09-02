# C2 Green-return scouts versus the completed C3 central ledger

## Decision

The old C2 return experiments recover the correct algebraic architecture,
but they do not provide the missing dressed state or a contraction on the
current carrier.  The shortest honest route is therefore the central-ledger
collision, not reconstruction of the old finite return operators.

The useful inheritance is structural:

```text
unreduced pair provenance
  -> skew Green identity before quotient
  -> chiral polarization
  -> difference of positive Gram channels
  -> contraction/defect gate.
```

All four steps already have exact completed-C3 realizations.  What the old
files do not supply is the final contraction or the channelwise diagonal
extension needed at the Taylor center.

## What the archived scouts actually prove

The audit used the frozen sources and reports under
`/mnt/hd500/covariantes/`, especially:

- `Teoria_De_Defeitos/c2_green_tower_return_operator.py`;
- `script/c2_green_carry_canonical_source/c2_green_unreduced_phase_lift.py`;
- `docs/C2_GREEN_TOWER_RETURN_EXTENSAO_N144.md`;
- `C2_GREEN_CARRY_CURRENT_AUDIT_REPORT.md`;
- `C2_GREEN_RECOVERED_RETURN_CROSSWALK_REPORT.md`;
- `C2_UNREDUCED_PAIR_SIGNED_STOKES_REPORT.md`;
- `C2_GREEN_CLOSED_NATIVE_ENDPOINT_GRAPH_LIFT.md`.

There are three exact or reproducible positive results.

1. The valuation--Naimark port fibres are Parseval to machine precision.
2. The unreduced phase lift uses the exact pair equation

   ```text
   Z^T R^T Gamma - Gamma^T R Z = H_Green
   ```

   and transports height by a unit-modulus gauge.
3. The reduced finite systems admit numerically contractive solutions on the
   tested cuts.  In the extended scan through `N=144`, the observed spectral
   norms lie in `[0.590965, 0.791817]`.

These facts are not an infinite completed contraction.  The same reports
record the decisive failures:

- proof status `FINITE_TOWER_RETURN_OPERATOR_SCOUT_ONLY`;
- exterior residual grows from about `1.40` to `3.36`;
- consecutive returns differ by order one even on fixed old coordinates;
- freezing the old block makes every tested `N -> N+1` extension infeasible;
- the recovered return factors only the compressed target `Q_N H_N`;
- endpoint mismatch and transverse dyadic tail remain in the completed
  ledger;
- the contragredient scalar collapse is not bounded by the frozen Schur
  control;
- the direct sum of tower families has no proved physical Riesz/Parseval
  metric, so the absolute threshold `||R|| <= 1` in the unreduced phase lift
  is not intrinsic.

Thus the old `R_N` is a finite compressed witness in a cutoff-dependent
coordinate system.  It is not a map between the positive and negative
chiral subspaces of the current completed carrier.

## Exact current-carrier obstruction to importing the old return

The completed repository has already tested the natural fixed-parameter
version of that import.

`CompletedC3CausalChiralDefectGram.lean` separates the two necessary gates:

```text
ker(positive readout) <= ker(camera/chiral readout),
||camera/chiral readout|| <= ||positive readout||.
```

The first is required merely to define a response-from-positive-readout map;
the second is its contractivity.  Then
`CompletedC3CausalChiralKernelObstruction.lean` constructs thirteen exact
causal camera states that are real-linearly independent.  The fixed positive
Wronskian trace carrier has real dimension twelve.  Therefore kernel
compatibility fails, and hence so does the proposed fixed-parameter
defect-Gram contraction, at every point in the open upper half-plane.

This refutes the direct identification

```text
old tower return R_N = completed dressed sewing operator R.
```

It does not refute the point-dependent radial multiplier already constructed
in `CompletedNativeRadialChiralMultiplier.lean`.  That multiplier has the
correct Cauchy metric and its defect Gram is exactly the radial Pick matrix.
But proving its contractivity is equivalent to the existing Pick/dslope gate;
the archived finite returns do not prove it.

## The central ledger is now opened at the total level

`CompletedC3CentralLedgerCollisionAudit.lean` fixes the first Hermitian leg at
zero and displays the normalized numerator with all current channels still
visible:

```text
xi weight * (
    radial Gram
  + Green provenance
  + ordered off-diagonal provenance
  + readout residual
  + head-tail completion defect)
+ archimedean chart,
```

followed only by the already-proved nonzero chart/characteristic
normalization.

Lean proves, without theta and without a separation hypothesis,

```text
N_M(0) = 0,
N_M'(0) = h0.
```

The first equality is cancellation of the total ledger at collision; it does
not say that any individual channel vanishes.  The second fixes the exact sum
of their first variations.  It is cutoff-independent because the total
numerator is the Hermitian-polarized completed response germ.

The comparison with the concrete dressed state is now literal:

```text
Re N_M'(0) = Re <P(0),P(0)>
```

if and only if

```text
Re <rawTFVD(0),rawTFVD(0)> - h0
  = -||residual(0)||^2.
```

Here the residual square is already known exactly as

```text
infiniteReflectedGreenEnergy(1/2)^2 > 0.
```

## Channel derivative and first genuinely missing equality

`CompletedC3CentralLedgerChannelDerivative.lean` now performs the first
channelwise diagonal extension.  It splits the central ledger into two
holomorphic blocks before differentiating:

```text
N_M = raw completed-C3 Wronskian branch + xi-minus-chart branch.
```

Their center derivatives are exactly the first raw-C3 response coefficient
and the first chart-replacement coefficient.  On the real collision line the
finite radial channel vanishes identically.  The surviving raw branch is the
exact sum

```text
Green provenance
  + ordered off-diagonal provenance
  + height-readout residual
  + head-tail completion.
```

This identity holds for every cutoff, and the derivative of that four-channel
sum is the first raw-C3 response coefficient.  Individual subchannels remain
real-axis functions because the radial reflection and real-part operations
are not holomorphic; the proof differentiates their exact sum through the
holomorphic raw branch rather than imposing false complex analyticity on the
pieces.

The zeroth dressed sewing is therefore equivalent to the single explicit
balance

```text
Re <rawTFVD(0), rawTFVD(0)> - Re(raw-C3 coefficient 1)
  = Re(xi-completion coefficient 1 - C3-chart coefficient 1)
      - ||residual(0)||^2.
```

This is the first genuinely missing equality.  It distinguishes three terms
which cannot honestly be identified by naming: the raw TFVD/response
mismatch, completion curvature relative to the C3 chart, and the retained
carrier residual square.  No new carrier and no finite return solver are
needed before this balance is addressed.
