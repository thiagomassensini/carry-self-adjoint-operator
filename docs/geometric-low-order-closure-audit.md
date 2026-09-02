# Geometric low-order closure audit

## Outcome

The low-order Herglotz/Pick gate now has a complete geometric **spelling**,
but not yet a second, theta-free geometric proof.

The exact proved chain is

```text
theta-tail moment inequality
        |
        v
      h0 > 0 and h1 > 0
        |
        +--> positive first and third chiral-signature variations
        |
        +--> positive-definite 1x1 even and shifted Loewner defects
        |
        `--> eventual 2-point Herglotz/Pick positivity
```

The geometric identifications in the lower three lines predate the theta
estimate.  `CompletedNativeGeometricLowOrderClosure.lean` now packages their
unconditional consequences without hiding the theta dependency.

## Relation with the self-adjoint height operator

The two low-order signs are exactly the data needed by the first Jacobi
section:

```text
G1 = [h0] > 0,
K1 = [h1] > 0.
```

Consequently the canonical LDL whitening constructs, without any additional
premise,

```text
J1 = whitening(G1) K1 whitening(G1)^T > 0,
T1 = J1^(-1/2),
H_Gamma,1 = T1 ⊕ (-T1).
```

The Lean module now defines these three concrete objects and proves that
`T1` and `H_Gamma,1` are exactly symmetric.  It also proves that the canonical
sector reflection conjugates `H_Gamma,1` to its negative.

This is the precise operator-theoretic gain from the present theorem: the
first canonical self-adjoint height compression is unconditional.

It does **not** yet instantiate the global operator `J = B* B`.  That
construction consumes an all-order Green--Wronskian moment-kernel
realization, global independence of both parity jet families, and, for the
full rather than reduced reciprocal carrier, the zero-mass/head-in-tail
gate.  Equivalently on the purely momental route, it needs strict positivity
of both Hankel towers for every order.  The present theorem proves only the
`N = 1` member of that tower.

## What the defect geometry already proves

The formal development contains four genuinely geometric positive objects.

1. Every nonempty finite bracket-coupled Green bulk has strictly positive
   centered first variation, and these variations converge to a strictly
   positive infinite reflected Green energy.
2. The two-channel full-Wronskian kernel is an honest Hilbert Gram and hence
   positive semidefinite.
3. The coisometric Naimark ambient response kernel is positive definite on
   every finite family of distinct positive real exponents.
4. The completed logarithmic moments are exactly the odd Taylor readouts of
   the signed chiral block.  In particular, its first and third variations
   are `h0` and `h1`.

The obstruction is the word **signed**.  The scalar readout is the positive
chiral diagonal minus the negative chiral diagonal.  Positivity of the
uncollapsed block Gram therefore does not imply positivity of the readout.

## Why the raw coisometric flatness route does not close

The unregularized ambient sewing defect vanishes on the collapsing radial
grid because it contains the Hermitian separation as a factor.  After
division by that separation, its central limit is the nontrivial mismatch

```text
||normalized ambient response at 0||^2 - h0.
```

Thus first-order flatness is equivalent to identifying the naked ambient
gradient energy with `h0`; it is not a consequence of coisometry alone.

A high-precision diagnostic of the concrete quantities gives

```text
h0                                             ~= 0.0231049931154
||normalized naked ambient response at 0||^2  ~= 0.470904737591
```

These numbers are included only as a route diagnostic, not as a formal
inequality theorem.  They show that the old naked-gradient identification is
not the identity to pursue.  The same issue is visible in the exact product
ledger: completion curvature and the mixed completion/native jet cannot be
discarded.

## The honest independent geometric gate

The note on the old defect route points to the correct repair: scalarization
must occur only after completion dressing and triangular transport.  The
target should be an identity on an honest two-variable Hilbert carrier of the
form

```text
K_plus(w,z) - K_minus(w,z)
  = <D Psi(w), D Psi(z)>,
```

or equivalently a contraction identity

```text
I - C* C = D* D.
```

Here `Psi` must be the dressed product/completion state, not the naked
Dirichlet-gradient state.  The triangular cumulant recurrence must be applied
before taking scalar Taylor coefficients; at coefficient level the two
centered chiral contributions are already additive inverses, so a defect-Gram
argument there is circular.

For the current two-point gate, the minimal independent construction only
needs the first two nonzero defect jets.  Their squared norms must realize
`h0` and `h1`, with the second jet nonzero.  Differentiating the defect-Gram
identity would then give the first and third chiral variations, the two
one-dimensional Loewner defects, and hence the two-point Herglotz/Pick gate
without using the theta moment inequality.

For the global self-adjoint height operator the same identity must hold to
all orders.  Its even and shifted jets then supply the complete pair of
Hankel towers, the closed Green energy factor `B`, the positive maximal
adjoint square `J = B* B`, and finally the reduced signed reciprocal height
operator.  Thus the defect identity missing from the independent geometric
proof is also exactly the missing input for the unconditional global height
construction.

## Follow-up: the dressed carrier already exists in part

The subsequent carrier audit is recorded in
`docs/existing-dressed-state-identification-audit.md`.  Its conclusion is
more precise than the original instruction to build a new state.

The repository already contains a canonical one-point positive carrier with
ordinary TFVD, log-jet TFVD, and retained precompression-residual channels,
as well as a channel-complete two-point ledger containing the remaining
completion data.  The open gate is their concrete Gram/readout sewing, named
`CanonicalCompletedC3ConcreteRealAxisPositiveSewing`.

The direct Naimark escape of the completed response is identically zero, so
it cannot be the desired nonzero defect.  The nonzero source escape returns
through the resolvent inside the resolved Gamma correction, where genuine
Gamma/correction cross terms remain.  Thus Naimark geometry participates in
the dressing audit but does not by itself supply `D* D`.

## Result of that attack and next gate

The direct low-order test is now formalized in
`CompletedC3ConcreteDressedLowOrderAudit.lean`.

At `(0,0)`, the concrete dressed Gram is strictly the old enriched TFVD Gram
plus the squared norm of a nonzero residual.  That residual norm is exactly
the square of `infiniteReflectedGreenEnergy (1/2)`.  Therefore the old
two-channel `h0` identification and the new dressed `h0` identification are
mutually incompatible; closing the dressed equality requires the old
central defect to be the negative of this residual square.

At `(1,1)`, the same residual coefficient is even and differentiable at the
center, with derivative zero.  The dressed first odd coefficient jet is
therefore the isometric image of the old enriched TFVD jet, is nonzero, and
its `h1` identification is exactly the already named
`CanonicalCompletedNativeTfvdFirstOddDiagonalMomentIdentification`.

The next honest attack is thus asymmetric:

1. At order zero, compare the recovered two-point ledger's linear and crossed
   completion/residual channels with the quadratic one-point residual norm.
2. At order one, prove the existing TFVD `(1,1)=h1` normalization gate; no
   Naimark escape or residual enlargement is needed there.
3. Promote to all orders only after those two independent scalar identities
   close.

This is now the precise remaining geometric problem.  Reusing the naked
ambient state or proving only that the unregularized ledger tends to zero
cannot close it.

## Follow-up: archived C2 return route and the central collision

The archived Green-return scouts were compared with the current completed
carrier in `docs/c2-green-return-central-ledger-crosswalk.md`.  They recover
the correct unreduced skew/chiral architecture, but only as cutoff-dependent
finite compressed witnesses.  Their exterior endpoint/tail defect is not
closed, their returns are not compatible between cutoffs, and their direct
sum lacks a proved physical metric.  More strongly, the natural
fixed-parameter return on the current completed carrier is already excluded
by the thirteen-state kernel obstruction.

`CompletedC3CentralLedgerCollisionAudit.lean` therefore opens the current
ledger instead.  With every radial, provenance, off-diagonal, residual, tail,
xi, and archimedean term retained, its fixed-center normalized numerator
`N_M` satisfies

```text
N_M(0) = 0,
N_M'(0) = h0.
```

Consequently the remaining zeroth-order sewing is exactly

```text
Re N_M'(0) = Re <P(0),P(0)>
```

and Lean reduces it to the negative residual-square balance already isolated
above.

`CompletedC3CentralLedgerChannelDerivative.lean` carries out the next
channelwise step.  It proves that the radial term vanishes identically on the
real collision line and that the other four raw channels sum to a holomorphic
raw-C3 branch whose first derivative is the first raw response coefficient.
The complementary holomorphic branch is exactly the xi-minus-C3-chart
replacement coefficient.  Hence the precise remaining equality is

```text
Re <rawTFVD(0), rawTFVD(0)> - Re(raw-C3 coefficient 1)
  = Re(xi-completion coefficient 1 - C3-chart coefficient 1)
      - ||residual(0)||^2.
```

This is the first place where a genuinely new proof is required.  Total
response Taylor theory determines the sum, but does not assign the raw
mismatch, completion curvature, and retained residual square to one another.
The archived returns and the direct Naimark escape do not supply this
assignment.
