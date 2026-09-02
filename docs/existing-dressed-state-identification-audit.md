# Existing dressed-state identification audit

## Verdict

The dressed geometry has already been constructed **in substantial part**, but
the objects in the proposed chain are not all representations of one vector.
There are two complementary completed constructions:

1. a canonical one-point positive state, retaining ordinary TFVD, log-jet
   TFVD, and the precompression residual;
2. a channel-complete two-point ledger, retaining radial, structural,
   head-tail, completion-weight, and archimedean channels.

The first is an honest Hilbert Gram carrier.  The second has the correct
completed scalar readout.  The missing theorem is precisely the sewing of
those two descriptions.  It is already named
`CanonicalCompletedC3ConcreteRealAxisPositiveSewing`, but is not proved.

Thus no new carrier should be invented before this seam is tested.  On the
other hand, the complementary Naimark escape of the **completed response** is
not the desired defect: it is identically zero.  The nonzero Naimark escape
belongs to the induced source and returns through the resolvent as part of a
signed correction with nonvanishing cross terms.

## The proved vector chain

The shortest proved chain is

```text
completed TFVD ledger
  |
  |  retain ordinary / log-jet / precompression residual
  v
oriented Green-frame state O(s)
  |
  |  bounded synthesis + Parseval analysis + residual complexification
  v
concrete one-point positive state P(t)
  |
  |  ordinary Gram construction
  v
positive kernel <P(x), P(z)>
```

The exact vector identification is

```text
P(t) = completedC3OrientedGreenFrameToPositiveCarrier(O(nativeLine(t))).
```

It is proved before Gram formation, scalarization, Taylor extraction, or a
zero condition.  The state has the fixed complex Hilbert carrier

```text
ParsevalGreenFrame(ordinary)
  ⊕ ParsevalGreenFrame(log-jet)
  ⊕ complexification(precompression residual).
```

The corresponding unnormalized state is

```text
sqrt(2) * completedNativeOperatorCharacteristic(z) * P(z).
```

Away from a characteristic zero, completed normalization recovers `P(z)`
exactly.

What is not proved is

```text
completed oriented ledger readout(x,z) = <P(x), P(z)>.
```

That equality is exactly
`CanonicalCompletedC3ConcreteRealAxisPositiveSewing`.  It is equivalent to
the normalized real-axis Green-kernel premise consumed by the Parseval
`dslope` construction.

## Type and normalization audit

| Stage | Scalar field and carrier | Parameter/domain | What is retained | What it does not prove |
|---|---|---|---|---|
| Naimark port+escape | Real Hilbert map from `RealifiedNaimarkComplexification` to `WithLp 2 (RealifiedCameraComplexification × RealifiedNaimarkComplexification)` | Ambient vector; completed source uses `z : ℂ` with positive real height parameter | `U* x` and `(I-UU*)x`, exact reconstruction and Pythagoras | No chiral sign, product completion, or `dslope` normalization |
| Ambient/Gamma correction | Complex Hilbert view `CarryGammaComplexNaimark` of the same two real quadratures | `z.im ≠ 0` and positive real height parameter | Exact vector equation `ambient = Gamma + correction` | The correction is not orthogonal to Gamma in general |
| Coisometric chiral block | Complex direct sum of scaled ambient response and negative chirality | Upper half-plane; contains `sqrt(2 Im z)` | A positive diagonal/direct-sum Gram | Its separable square-root weight is not the off-diagonal Hermitian separation |
| Oriented Green-frame state | Two complex Green-frame channels plus a real residual | `s` in the genuine strip | Ordinary, log-jet, residual; orientation fixed before Gram | No product/completion scalar sewing |
| Concrete positive state `P` | Complex Hilbert direct sum; residual complexified only at the last step | Real-axis wrapper uses `z.re` | Canonical one-point positive carrier | Equality of its Gram with the completed ledger remains a premise |
| Parseval `dslope` state | Complex `CanonicalCompletedGreenFrameCarrier` | Real-axis points away from zeros | Isometric presentation and four orthogonal Green channels | Requires `HasCompletedNativeRealAxisNormalizedGreenKernel state` |
| BR2 jet bridge | Same complex all-bases Green-frame carrier | Every parity/order forward-difference component | Exact vector-defect criterion and phase visibility | The vector defect limit is not proved; scalar kernel data cannot fix phase |
| Green-jet height carrier | Real Hilbert closed span of parity jets | All orders | Hankel/shifted-Hankel Gram, whitening, Jacobi and height tower | Requires exact real moment Gram and global independence |

The real/complex distinction is substantive.  The lossless Naimark block is
canonically real-linear.  The complex forward-difference jets are formed only
after choosing the two-quadrature complex presentation.  Conversely, the
height construction deliberately restricts the final complex positive carrier
back to its real inner product.

## Why the direct Naimark identification is false

For an arbitrary ambient vector `x`, the coisometric readout

```text
x |-> (U* x, (I - UU*)x)
```

is lossless and isometric.  This is genuine defect geometry.

However, the completed ambient **response** is already a promoted camera
vector.  The repository proves

```text
UU* completedResponse = completedResponse,
```

and the present audit records the immediate vector consequence

```text
(I - UU*) completedResponse = 0.
```

Therefore its direct Naimark escape cannot provide either nonzero low-order
defect jet.  This refutes the simplest proposed identification without using
theta or a numerical comparison.

The nonzero escape theorem applies instead to the completed induced
**source**.  After applying the logarithmic resolvent, source-level
orthogonality is not preserved: the port projection does not commute with
that resolvent, and the repository contains a nonzero commutator witness.

## What the Gamma correction really contains

In the common complex Naimark Hilbert carrier,

```text
AmbientResponse = GammaState + ResolvedCorrectionState.
```

The port/escape audit sharpens this to

```text
GammaState      = projectedGammaPort + gammaEscape,
CorrectionState = ambientPortDifference - gammaEscape.
```

Thus the correction cancels the Gamma escape so that the total ambient
response returns to the port.  Polarization gives

```text
Gram(Ambient) - Gram(Gamma)
  = <Gamma, correction>
  + <correction, Gamma>
  + <correction, correction>.
```

Only the last term is automatically positive.  The first two are genuine
cross channels.  Response-level Pythagoras is equivalent to their real
cancellation, and the existing theorems expose that cancellation as a
camera-port balance against the squared Gamma escape.  It is not a
consequence of the source coisometry.

Consequently `ResolvedCorrectionState` is a retained completion remainder,
but it is not yet a defect operator `D` satisfying

```text
K_plus - K_minus = <D Psi, D Psi>.
```

The first missing equality on this route is the response cross-balance, not
the existence of the correction vector.

## Where the full completion already lives

The recovered enriched all-cutoff ledger keeps, in orthogonal coordinates,

```text
recovered radial pair
  ⊕ structural triple
  ⊕ head-tail completion defect
  ⊕ xi completion weight
  ⊕ archimedean response/source pair.
```

Its scalar readout converges unconditionally to the completed crossed
Wronskian.  This is the closest existing object to a product/completion
dressed two-variable state.

It is nevertheless not yet the desired `Psi`: the ledger state depends on
the pair `(z,w)`, and its final readout multiplies coordinates and applies a
crossed operator.  Its positive Hilbert norm is not its Wronskian readout.
It is therefore a channel-complete ledger, not a one-point Gram
factorization.

The exact missing bridge can be summarized as

```text
channel-complete two-point readout L(w,z)
              ?=
one-point positive Gram <P(w), P(z)>.
```

## Low-order test: orders zero through three

Let `jet` be the real forward-difference limit family of the concrete state
`P`.  If the concrete sewing equality is supplied, existing theorems give,
without theta,

```text
<jet(even 0), jet(even 0)> = h0,
<jet(odd  0), jet(odd  0)> = h1,
jet(even 0) != 0,
jet(odd  0)  != 0.
```

This is now packaged by
`canonicalCompletedC3ExistingDressedJets_lowOrder_of_sewing`.  It is exactly
the desired low-order handoff: the first and third chiral variations become
the unshifted and shifted `1 x 1` Hankel Grams.

The result is conditional because the sewing premise has not been derived.
At coefficient order zero, the target `h0` is the full second product jet

```text
-(A'' G + 2 A' G' + A G'') / (2 A G),
```

where `A` is the completion factor and `G` the native height scalar.  The
factor `2` in the mixed completion/native channel is forced by Leibniz.  The
existing enriched TFVD Taylor audit proves that the ordinary/log-jet Gram
would have to equal this full expression, but does not prove the equality.
This is the first central coefficient that must be checked.  The next
independent check is the odd `(1,1)` Gram giving `h1`.

Therefore the current carrier does not close `h0/h1` geometrically without
theta yet.  It does reduce that problem to two explicit low-order Gram
equalities in an already constructed carrier.

## Result of the direct coefficient attack

`CompletedC3ConcreteDressedLowOrderAudit.lean` now performs the recommended
test without assuming the concrete sewing and without using theta.

At `(0,0)` the answer is an exact strict split:

```text
Re <P(0),P(0)>
  = Re <rawTFVD(0),rawTFVD(0)> + ||residual(0)||^2,

||residual(0)||^2
  = infiniteReflectedGreenEnergy(1/2)^2 > 0.
```

Thus the old ordinary-plus-logarithmic identification and the concrete
dressed identification cannot both equal `h0`.  Equivalently, the remaining
dressed central gate is

```text
Re <rawTFVD(0),rawTFVD(0)> - h0
  = -||residual(0)||^2.
```

This does **not** by itself prove that `Re <P(0),P(0)> != h0`: it proves that
the old two-channel `h0` identification cannot be reused unchanged after the
residual is installed as a third orthogonal coordinate.  The distinction is
important.  The one-point carrier makes the residual contribution quadratic,
whereas the completed two-point ledger also has linear and crossed residual
channels.  The first equality still to compare is therefore precisely the
ledger readout against this quadratic residual normalization.

At first odd order the outcome is different.  The residual coefficient is
proved even on the native line, and termwise differentiation is justified on
`(-1,1)` by the summable majorant

```text
36 (n + 1)^(-11/4).
```

Consequently its derivative at the center vanishes:

```text
residualJet(1) = 0.
```

The dressed first-odd coefficient jet is therefore the isometric image of
the existing enriched TFVD raw jet, and Lean proves

```text
<dressedJet(1), dressedJet(1)>
  = <rawTFVD(1), rawTFVD(1)>,

dressedJet(1) != 0.
```

Its identification with `h1` is literally equivalent to the already named
`CanonicalCompletedNativeTfvdFirstOddDiagonalMomentIdentification`.  Hence
there is no missing Naimark escape or residual correction at this order, but
the scalar equality with `h1` remains open.

## All-order consequence if the seam closes

If the same sewing holds at all orders, no additional operator carrier is
needed.  Existing code already performs

```text
concrete dressed real-axis state
  -> real forward-difference parity jets
  -> exact Green moment Gram + global parity independence
  -> Hankel and shifted-Hankel positivity
  -> Green energy factor B
  -> positive maximal self-adjoint J = B* B
  -> reduced signed reciprocal height operator.
```

The BR2 fixed-camera route is not required for this shortest handoff.  Its
value is an independent incidence realization, but it introduces an
additional vector convergence/phase gate.  In particular, a state and its
global negative have the same scalar kernel and cannot both equal the fixed
oriented BR2 jet.

## Recommended next proof target

Do not construct another ambient carrier.  The residual profile has already
decided where the two orders separate:

```text
order 0: nonzero quadratic residual correction,
order 1: zero residual correction; old TFVD h1 gate unchanged.
```

The next attack should stay at `(0,0)` and open the recovered completed
two-point ledger until its linear/cross residual and completion-curvature
terms are compared with

```text
||residual(0)||^2 = infiniteReflectedGreenEnergy(1/2)^2.
```

If the ledger supplies exactly the negative old-carrier defect recorded
above, then `P` closes `h0`; otherwise the first failed equality gives the
required change of normalization or the missing cross coordinate.  In
parallel, the independent `(1,1)=h1` equality remains the existing named
TFVD normalization gate.  Promotion to all orders should wait for both
scalar identities.
